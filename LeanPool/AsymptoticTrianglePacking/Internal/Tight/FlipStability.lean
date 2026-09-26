/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini, Aristotle
-/

module

public import LeanPool.AsymptoticTrianglePacking.Internal.Round
public import LeanPool.AsymptoticTrianglePacking.Internal.Tight.SafeDegree
public import LeanPool.AsymptoticTrianglePacking.Internal.Tight.LossVariance

/-!
# LeanPool.AsymptoticTrianglePacking.Internal — stability of the covered set under a single-edge
flip

The one remaining analytic input of the tight-band nibble (see
`LeanPool.AsymptoticTrianglePacking.Internal.Tight.SharpRound`) is the
SHARP per-vertex safe-degree variance bound

  `Var(safeDeg(v)) ≤ C(r)·(γΔ + κγΔ)`,

i.e. a bound with NO term of the shape `c·γ^a·Δ²`.  The Bonferroni route of
`LeanPool.AsymptoticTrianglePacking.Internal.Tight.SafeDegreeVariance` leaves a residue `Θ(γ³Δ²)`,
which is a constant factor (depending
on the target `β`) too large to iterate.

This file provides the key COMBINATORIAL input of the bounded-differences (Efron–Stein) route to
that bound: the round's covered set is *locally* stable — flipping the retention status of a single
edge `e` only moves vertices that lie on `e` itself or on a retained edge meeting `e`.

Concretely, with

  `flipInfluence R e = insert e (R.filter (fun f => ¬ Disjoint f e))`,

`LeanPool.AsymptoticTrianglePacking.Internal.mem_roundMatching_insert_iff_erase` says that every
edge outside `flipInfluence R e` belongs
to `roundMatching (insert e R)` exactly when it belongs to `roundMatching (R.erase e)`, and hence
`LeanPool.AsymptoticTrianglePacking.Internal.covered_insert_sdiff_subset` /
`LeanPool.AsymptoticTrianglePacking.Internal.covered_erase_sdiff_subset` bound the symmetric
difference of the two covered sets by `⋃ (flipInfluence R e)`.  For an `r`-uniform hypergraph this
has at most `r·(1 + #{f ∈ R : f meets e})` vertices
(`LeanPool.AsymptoticTrianglePacking.Internal.card_biUnion_flipInfluence_le`), so the safe degree at
`v` moves by at most
`∑_{u} codeg(v,u)` over that set
(`LeanPool.AsymptoticTrianglePacking.Internal.abs_safeDegree_sub_le_codegree_sum`).

Summing `p·𝔼[(ΔsafeDeg)²]` over the edges `e` and using `∑_{u ≠ v} codeg(v,u)² ≤ κ(r−1)deg(v)`
gives exactly `O_r(γΔ(1 + κ))`, the sharp bound — the arithmetic is recorded in the header of
`LeanPool.AsymptoticTrianglePacking.Internal.Tight.SharpRound`.

placeholder-free and axiom-clean `[propext, Classical.choice, Quot.sound]`.
-/

public section

open Finset Hypergraph

namespace LeanPool.AsymptoticTrianglePacking.Internal

variable {V : Type*} [DecidableEq V]

/-! ## The influence set of a single edge -/

/-- The edges whose membership in the round matching can be affected by flipping the retention
status of `e`: the edge `e` itself, and the retained edges meeting `e`. -/
def flipInfluence (R : Finset (Finset V)) (e : Finset V) : Finset (Finset V) :=
  insert e (R.filter (fun f => ¬ Disjoint f e))

theorem notMem_flipInfluence_ne {R : Finset (Finset V)} {e f : Finset V}
    (hf : f ∉ flipInfluence R e) : f ≠ e := by
  intro h; exact hf (by simp [flipInfluence, h])

theorem notMem_flipInfluence_disjoint {R : Finset (Finset V)} {e f : Finset V}
    (hf : f ∉ flipInfluence R e) (hfR : f ∈ R) : Disjoint f e := by
  by_contra hd
  exact hf (Finset.mem_insert_of_mem (Finset.mem_filter.mpr ⟨hfR, hd⟩))

/-- **Local stability of the round matching.**  An edge outside the influence set of `e` is in the
round matching of `insert e R` exactly when it is in the round matching of `R.erase e`. -/
theorem mem_roundMatching_insert_iff_erase {R : Finset (Finset V)} {e f : Finset V}
    (hf : f ∉ flipInfluence R e) :
    f ∈ roundMatching (insert e R) ↔ f ∈ roundMatching (R.erase e) := by
  have hfe : f ≠ e := notMem_flipInfluence_ne hf
  constructor
  · intro h
    rw [roundMatching, Finset.mem_filter] at h ⊢
    obtain ⟨hmem, hdisj⟩ := h
    have hfR : f ∈ R := (Finset.mem_insert.mp hmem).resolve_left hfe
    refine ⟨Finset.mem_erase.mpr ⟨hfe, hfR⟩, ?_⟩
    intro g hg hgf
    exact hdisj g (Finset.mem_insert_of_mem (Finset.mem_of_mem_erase hg)) hgf
  · intro h
    rw [roundMatching, Finset.mem_filter] at h ⊢
    obtain ⟨hmem, hdisj⟩ := h
    have hfR : f ∈ R := Finset.mem_of_mem_erase hmem
    refine ⟨Finset.mem_insert_of_mem hfR, ?_⟩
    intro g hg hgf
    by_cases hge : g = e
    · subst hge; exact notMem_flipInfluence_disjoint hf hfR
    · exact hdisj g (Finset.mem_erase.mpr ⟨hge, (Finset.mem_insert.mp hg).resolve_left hge⟩) hgf

/-! ## Stability of the covered set -/

theorem covered_insert_sdiff_subset (R : Finset (Finset V)) (e : Finset V) :
    covered (insert e R) \ covered (R.erase e) ⊆ (flipInfluence R e).biUnion id := by
  intro u hu
  rw [Finset.mem_sdiff] at hu
  obtain ⟨f, hfM, huf⟩ := Finset.mem_biUnion.mp hu.1
  by_cases hfl : f ∈ flipInfluence R e
  · exact Finset.mem_biUnion.mpr ⟨f, hfl, huf⟩
  · exact absurd (Finset.mem_biUnion.mpr
      ⟨f, (mem_roundMatching_insert_iff_erase hfl).mp hfM, huf⟩) hu.2

theorem covered_erase_sdiff_subset (R : Finset (Finset V)) (e : Finset V) :
    covered (R.erase e) \ covered (insert e R) ⊆ (flipInfluence R e).biUnion id := by
  intro u hu
  rw [Finset.mem_sdiff] at hu
  obtain ⟨f, hfM, huf⟩ := Finset.mem_biUnion.mp hu.1
  by_cases hfl : f ∈ flipInfluence R e
  · exact Finset.mem_biUnion.mpr ⟨f, hfl, huf⟩
  · exact absurd (Finset.mem_biUnion.mpr
      ⟨f, (mem_roundMatching_insert_iff_erase hfl).mpr hfM, huf⟩) hu.2

/-- **The flip only moves few vertices.**  For an `r`-uniform hypergraph the influence set of `e`
spans at most `r·(1 + #{f ∈ R : f meets e})` vertices. -/
theorem card_biUnion_flipInfluence_le {H : Finset (Finset V)} {r : ℕ} (hunif : IsUniform H r)
    {R : Finset (Finset V)} (hRH : R ⊆ H) {e : Finset V} (he : e ∈ H) :
    ((flipInfluence R e).biUnion id).card
      ≤ r * (1 + (R.filter (fun f => ¬ Disjoint f e)).card) := by
  classical
  refine le_trans (Finset.card_biUnion_le) ?_
  have hcard : ∀ f ∈ flipInfluence R e, (id f).card = r := by
    intro f hf
    rcases Finset.mem_insert.mp hf with rfl | hf'
    · exact hunif _ he
    · exact hunif _ (hRH (Finset.mem_filter.mp hf').1)
  rw [Finset.sum_congr rfl hcard, Finset.sum_const, smul_eq_mul, mul_comm]
  have hle : (flipInfluence R e).card ≤ 1 + (R.filter (fun f => ¬ Disjoint f e)).card := by
    simpa [flipInfluence, Nat.add_comm] using
      Finset.card_insert_le e (R.filter (fun f => ¬ Disjoint f e))
  exact Nat.mul_le_mul_left r hle

/-! ## The safe degree moves by at most a codegree sum -/

/-- If two covered sets differ only inside `D`, the safe degrees at `v` differ by at most the number
of edges at `v` meeting `D` away from `v`. -/
theorem abs_safeDegree_sub_le_card_meeting {H : Finset (Finset V)} {C C' D : Finset V} {v : V}
    (hCC' : C \ C' ⊆ D) (hC'C : C' \ C ⊆ D) :
    ((safeDegree H C v : ℤ) - (safeDegree H C' v : ℤ)).natAbs
      ≤ (H.filter (fun e => v ∈ e ∧ ¬ Disjoint (e.erase v) D)).card := by
  classical
  set T := H.filter (fun e => v ∈ e ∧ ¬ Disjoint (e.erase v) D) with hT
  have key : ∀ (X Y : Finset V), X \ Y ⊆ D →
      (H.filter (fun e => v ∈ e ∧ Disjoint (e.erase v) Y)).card
        ≤ (H.filter (fun e => v ∈ e ∧ Disjoint (e.erase v) X)).card + T.card := by
    intro X Y hXY
    have hsub : H.filter (fun e => v ∈ e ∧ Disjoint (e.erase v) Y)
        ⊆ H.filter (fun e => v ∈ e ∧ Disjoint (e.erase v) X) ∪ T := by
      intro e hmem'
      rw [Finset.mem_filter] at hmem'
      obtain ⟨heH, hve, hdY⟩ := hmem'
      by_cases hdX : Disjoint (e.erase v) X
      · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨heH, hve, hdX⟩)
      · refine Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨heH, hve, ?_⟩)
        rw [Finset.not_disjoint_iff] at hdX ⊢
        obtain ⟨u, hu1, hu2⟩ := hdX
        refine ⟨u, hu1, hXY (Finset.mem_sdiff.mpr ⟨hu2, ?_⟩)⟩
        exact fun hY => (Finset.disjoint_left.mp hdY hu1) hY
    exact le_trans (Finset.card_le_card hsub) (Finset.card_union_le _ _)
  have h1 := key C C' hCC'
  have h2 := key C' C hC'C
  simp only [safeDegree]
  omega

/-- The number of edges at `v` meeting a set `D` away from `v` is at most `∑_{u ∈ D} codeg(v,u)`. -/
theorem card_meeting_le_codegree_sum {H : Finset (Finset V)} {D : Finset V} {v : V} :
    (H.filter (fun e => v ∈ e ∧ ¬ Disjoint (e.erase v) D)).card
      ≤ ∑ u ∈ D.erase v, codegree H v u := by
  classical
  have hsub : H.filter (fun e => v ∈ e ∧ ¬ Disjoint (e.erase v) D)
      ⊆ (D.erase v).biUnion (fun u => H.filter (fun e => v ∈ e ∧ u ∈ e)) := by
    intro e he
    rw [Finset.mem_filter] at he
    obtain ⟨heH, hve, hd⟩ := he
    rw [Finset.not_disjoint_iff] at hd
    obtain ⟨u, hu1, hu2⟩ := hd
    exact Finset.mem_biUnion.mpr ⟨u, Finset.mem_erase.mpr ⟨Finset.ne_of_mem_erase hu1, hu2⟩,
      Finset.mem_filter.mpr ⟨heH, hve, Finset.mem_of_mem_erase hu1⟩⟩
  refine le_trans (Finset.card_le_card hsub) (le_trans (Finset.card_biUnion_le) (le_of_eq ?_))
  exact Finset.sum_congr rfl fun u _ => rfl

/-- **The bounded-differences estimate for the safe degree.**  If the covered sets `C`, `C'` differ
only inside `D`, then the safe degrees at `v` differ by at most `∑_{u ∈ D \ {v}} codeg(v,u)`. -/
theorem abs_safeDegree_sub_le_codegree_sum {H : Finset (Finset V)} {C C' D : Finset V}
    {v : V} (hCC' : C \ C' ⊆ D) (hC'C : C' \ C ⊆ D) :
    ((safeDegree H C v : ℤ) - (safeDegree H C' v : ℤ)).natAbs
      ≤ ∑ u ∈ D.erase v, codegree H v u :=
  le_trans (abs_safeDegree_sub_le_card_meeting hCC' hC'C) card_meeting_le_codegree_sum

/-- **The safe degree is stable under a single-edge flip.**  Flipping the retention status of `e`
changes the safe degree at `v` by at most the codegree sum over the vertices spanned by the
influence set of `e`. -/
theorem abs_safeDegree_flip_le (H : Finset (Finset V)) (R : Finset (Finset V))
    (e : Finset V) (v : V) :
    ((safeDegree H (covered (insert e R)) v : ℤ)
        - (safeDegree H (covered (R.erase e)) v : ℤ)).natAbs
      ≤ ∑ u ∈ (((flipInfluence R e).biUnion id).erase v), codegree H v u :=
  abs_safeDegree_sub_le_codegree_sum (covered_insert_sdiff_subset R e)
    (covered_erase_sdiff_subset R e)

/-- **The squared codegree sum.**  With all codegrees at `v` bounded by `κ`,
`∑_{u ≠ v} codeg(v,u)² ≤ κ·(r−1)·deg(v)` — the weight that drives the Efron–Stein estimate. -/
theorem sum_sq_codegree_le [Fintype V] {H : Finset (Finset V)} {r : ℕ} (hr : IsUniform H r)
    {κ : ℝ} (v : V) (hκ : ∀ u : V, u ≠ v → (codegree H v u : ℝ) ≤ κ) :
    ∑ u ∈ (Finset.univ : Finset V).erase v, (codegree H v u : ℝ) ^ 2
      ≤ κ * (((r - 1) * degree H v : ℕ) : ℝ) := by
  classical
  have hstep : ∀ u ∈ (Finset.univ : Finset V).erase v,
      ((codegree H v u : ℝ)) ^ 2 ≤ κ * (codegree H v u : ℝ) := by
    intro u hu
    have hne : u ≠ v := Finset.ne_of_mem_erase hu
    have h0 : (0 : ℝ) ≤ (codegree H v u : ℝ) := Nat.cast_nonneg _
    nlinarith only [hκ u hne]
  calc ∑ u ∈ (Finset.univ : Finset V).erase v, (codegree H v u : ℝ) ^ 2
      ≤ ∑ u ∈ (Finset.univ : Finset V).erase v, κ * (codegree H v u : ℝ) :=
        Finset.sum_le_sum hstep
    _ = κ * ∑ u ∈ (Finset.univ : Finset V).erase v, (codegree H v u : ℝ) := by
        rw [Finset.mul_sum]
    _ = κ * (((r - 1) * degree H v : ℕ) : ℝ) := by
        rw [← Nat.cast_sum, sum_codegree_erase_eq hr v]

end LeanPool.AsymptoticTrianglePacking.Internal
