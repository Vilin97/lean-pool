/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini, Aristotle
-/

module

/-
# Nibble — the **cluster (host) graph** and the aggregation of the LP along it

The block-allocation route needs the fractional triangle packing LP of the regularity-reduced graph
`R = G.regularityReduced P ep de` to be compared with the LP of the *cluster* graph: the graph whose
vertices are the parts of `P` and whose edges are the uniform, dense cluster pairs.

* `Nibble.AX1.hostGraph` — the cluster graph, on the subtype of the parts of `P` (so that its vertex
  count is the number of clusters, not `2^|V|`);
* `Nibble.AX1.hostTri` — the cluster triple of a triangle;
* `Nibble.AX1.nu3star_regularityReduced_le_host` — **the aggregation**: if every cluster pair
  carries at most `c` edges then `ν₃*(R) ≤ c·ν₃*(cluster graph)`.  The proof aggregates a fractional
  packing of `R` along cluster triples; the per-cluster-pair capacity constraint
  (`Nibble.AX1.sum_fracPacking_cluster_pair_le`) is exactly the edge constraint of the aggregated
  weighting.

Must be sorry-free and axiom-clean `[propext, Classical.choice, Quot.sound]`.
-/
public import LeanPool.AsymptoticTrianglePacking.Internal.AX1.CoreGapClusterLP
public import LeanPool.AsymptoticTrianglePacking.Internal.AX1.CoreGapPackingEdges
public import LeanPool.AsymptoticTrianglePacking.Internal.AX1.CoreGapRegularCover
public import LeanPool.AsymptoticTrianglePacking.Internal.AX1.YusterEdge
public import Mathlib.Tactic.IntervalCases
public import LeanPool.AsymptoticTrianglePacking.Internal.AX1.CoreGapClusterCapacity
public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Algebra.Order.Ring.Star


/-! # CoreGapBlowUp -/

public section

open Finset SimpleGraph Hypergraph Nibble.YusterE

namespace Nibble.AX1

/-! ### Triangle hyperedges and their vertex sets

A hyperedge of `Nibble.YusterE.triangleHypergraphE` is the set of the three *edges* of a triangle.
`Nibble.AX1.vtxSet` recovers the three vertices, so that sums over the triangle hypergraph can be
rewritten as sums over `cliqueFinset 3`. -/

/-- The set of vertices covered by a set of edges. -/
def vtxSet {X : Type} [DecidableEq X] (T : Finset (Finset X)) : Finset X := T.biUnion id

/-- The vertex set of the edge set of a set with at least two elements is the set itself. -/
theorem vtxSet_powersetCard_two {X : Type} [DecidableEq X] {t : Finset X} (ht : 2 ≤ #t) :
    vtxSet (t.powersetCard 2) = t := by
  classical
  ext v
  simp only [vtxSet, Finset.mem_biUnion, id_eq, Finset.mem_powersetCard]
  constructor
  · rintro ⟨e, ⟨hsub, -⟩, hve⟩
    exact hsub hve
  · intro hv
    obtain ⟨u, hu, hune⟩ : ∃ u ∈ t, u ≠ v := by
      by_contra hcon
      push Not at hcon
      have hsub : t ⊆ {v} := fun x hx => by simp [hcon x hx]
      have := Finset.card_le_card hsub
      simp at this
      omega
    refine ⟨{v, u}, ⟨?_, ?_⟩, by simp⟩
    · intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl
      · exact hv
      · exact hu
    · rw [Finset.card_insert_of_notMem (by simp [Ne.symm hune]), Finset.card_singleton]

/-- A sum over the triangle hypergraph is a sum over the triangles. -/
theorem sum_triangleHypergraphE {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (f : Finset (Finset V) → ℝ) :
    ∑ T ∈ triangleHypergraphE G, f T = ∑ t ∈ G.cliqueFinset 3, f (t.powersetCard 2) := by
  classical
  unfold triangleHypergraphE
  rw [Finset.sum_image]
  intro s hs t ht hst
  simp only [Finset.mem_coe, SimpleGraph.mem_cliqueFinset_iff] at hs ht
  exact powersetCard_two_inj (by have := hs.card_eq; omega) (by have := ht.card_eq; omega) hst

/-- A sum over the triangle hyperedges through a fixed edge is a sum over the triangles containing
that edge. -/
theorem sum_triangleHypergraphE_filter {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] {e : Finset V} (he : #e = 2) (f : Finset (Finset V) → ℝ) :
    ∑ T ∈ (triangleHypergraphE G).filter (fun T => e ∈ T), f T
      = ∑ t ∈ (G.cliqueFinset 3).filter (fun t => e ⊆ t), f (t.powersetCard 2) := by
  classical
  have hfil : (triangleHypergraphE G).filter (fun T => e ∈ T)
      = ((G.cliqueFinset 3).filter (fun t => e ⊆ t)).image (fun t => t.powersetCard 2) := by
    ext T
    simp only [triangleHypergraphE, Finset.mem_filter, Finset.mem_image]
    constructor
    · rintro ⟨⟨t, ht, rfl⟩, heT⟩
      rw [Finset.mem_powersetCard] at heT
      exact ⟨t, ⟨ht, heT.1⟩, rfl⟩
    · rintro ⟨t, ⟨ht, hsub⟩, rfl⟩
      exact ⟨⟨t, ht, rfl⟩, Finset.mem_powersetCard.mpr ⟨hsub, he⟩⟩
  rw [hfil, Finset.sum_image]
  intro s hs t ht hst
  simp only [Finset.mem_coe, Finset.mem_filter, SimpleGraph.mem_cliqueFinset_iff] at hs ht
  exact powersetCard_two_inj (by have := hs.1.card_eq; omega) (by have := ht.1.card_eq; omega) hst

/-! ### The blow-up -/

variable {W : Type} [Fintype W] [DecidableEq W]

/-- **The `q`-blow-up of `H`**: every vertex is replaced by `q` copies, and two copies are adjacent
exactly when the vertices they lie above are. -/
def blowUp (H : SimpleGraph W) (q : ℕ) : SimpleGraph (W × Fin q) := SimpleGraph.comap Prod.fst H

instance instDecidableRelBlowUpAdj (H : SimpleGraph W) [DecidableRel H.Adj] (q : ℕ) :
    DecidableRel (blowUp H q).Adj := fun x y => inferInstanceAs (Decidable (H.Adj x.1 y.1))

omit [Fintype W] [DecidableEq W] in
@[simp] theorem blowUp_adj {H : SimpleGraph W} {q : ℕ} {x y : W × Fin q} :
    (blowUp H q).Adj x y ↔ H.Adj x.1 y.1 := Iff.rfl

omit [Fintype W] in
/-- The projection of a triangle of the blow-up is a triangle of `H`. -/
theorem isNClique_image_fst {H : SimpleGraph W} {q : ℕ} {t' : Finset (W × Fin q)}
    (ht' : (blowUp H q).IsNClique 3 t') : H.IsNClique 3 (t'.image Prod.fst) := by
  classical
  have hinj : Set.InjOn Prod.fst (t' : Set (W × Fin q)) := by
    intro x hx y hy hxy
    by_contra hne
    have := ht'.1 hx hy hne
    rw [blowUp_adj, hxy] at this
    exact this.ne rfl
  refine ⟨?_, ?_⟩
  · intro a ha b hb hab
    rw [Finset.mem_coe, Finset.mem_image] at ha hb
    obtain ⟨x, hx, rfl⟩ := ha
    obtain ⟨y, hy, rfl⟩ := hb
    have hxy : x ≠ y := fun h => hab (by rw [h])
    exact ht'.1 hx hy hxy
  · rw [Finset.card_image_of_injOn hinj, ht'.card_eq]

/-- **The fibre of the projection has `q³` elements**: a triangle of `H` is the projection of
exactly `q³` triangles of the blow-up. -/
theorem card_blowUp_fiber (H : SimpleGraph W) [DecidableRel H.Adj] (q : ℕ) {t : Finset W}
    (ht : H.IsNClique 3 t) :
    #(((blowUp H q).cliqueFinset 3).filter (fun t' => t'.image Prod.fst = t)) = q ^ 3 := by
  classical
  obtain ⟨a, b, c, hab, hac, hbc, rfl⟩ := Finset.card_eq_three.mp ht.card_eq
  have hAab : H.Adj a b := ht.1 (by simp) (by simp) hab
  have hAac : H.Adj a c := ht.1 (by simp) (by simp) hac
  have hAbc : H.Adj b c := ht.1 (by simp) (by simp) hbc
  set f : Fin q × Fin q × Fin q → Finset (W × Fin q) :=
    fun p => {(a, p.1), (b, p.2.1), (c, p.2.2)} with hf
  have hinj : Function.Injective f := by
    rintro ⟨i, j, k⟩ ⟨i', j', k'⟩ h
    simp only [hf] at h
    have h1 : ((a, i) : W × Fin q) ∈ ({(a, i'), (b, j'), (c, k')} : Finset (W × Fin q)) := by
      rw [← h]; simp
    have h2 : ((b, j) : W × Fin q) ∈ ({(a, i'), (b, j'), (c, k')} : Finset (W × Fin q)) := by
      rw [← h]; simp
    have h3 : ((c, k) : W × Fin q) ∈ ({(a, i'), (b, j'), (c, k')} : Finset (W × Fin q)) := by
      rw [← h]; simp
    simp only [Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq] at h1 h2 h3
    have e1 : i = i' := by
      rcases h1 with ⟨-, h⟩ | ⟨h, -⟩ | ⟨h, -⟩
      · exact h
      · exact absurd h hab
      · exact absurd h hac
    have e2 : j = j' := by
      rcases h2 with ⟨h, -⟩ | ⟨-, h⟩ | ⟨h, -⟩
      · exact absurd h.symm hab
      · exact h
      · exact absurd h hbc
    have e3 : k = k' := by
      rcases h3 with ⟨h, -⟩ | ⟨h, -⟩ | ⟨-, h⟩
      · exact absurd h.symm hac
      · exact absurd h.symm hbc
      · exact h
    simp [e1, e2, e3]
  have himg : ((blowUp H q).cliqueFinset 3).filter
        (fun t' => t'.image Prod.fst = ({a, b, c} : Finset W))
      = (univ : Finset (Fin q × Fin q × Fin q)).image f := by
    ext t'
    simp only [Finset.mem_filter, Finset.mem_image, Finset.mem_univ, true_and,
      SimpleGraph.mem_cliqueFinset_iff]
    constructor
    · rintro ⟨hcl, himg⟩
      have hax : ∃ x ∈ t', x.1 = a := by
        have : a ∈ t'.image Prod.fst := by rw [himg]; simp
        simpa [Finset.mem_image] using this
      have hbx : ∃ x ∈ t', x.1 = b := by
        have : b ∈ t'.image Prod.fst := by rw [himg]; simp
        simpa [Finset.mem_image] using this
      have hcx : ∃ x ∈ t', x.1 = c := by
        have : c ∈ t'.image Prod.fst := by rw [himg]; simp
        simpa [Finset.mem_image] using this
      obtain ⟨x, hx, hxa⟩ := hax
      obtain ⟨y, hy, hyb⟩ := hbx
      obtain ⟨z, hz, hzc⟩ := hcx
      have hxy : x ≠ y := fun h => hab (by rw [← hxa, ← hyb, h])
      have hxz : x ≠ z := fun h => hac (by rw [← hxa, ← hzc, h])
      have hyz : y ≠ z := fun h => hbc (by rw [← hyb, ← hzc, h])
      have hsub : ({x, y, z} : Finset (W × Fin q)) ⊆ t' := by
        intro v hv
        simp only [Finset.mem_insert, Finset.mem_singleton] at hv
        rcases hv with rfl | rfl | rfl <;> assumption
      have hcard : #({x, y, z} : Finset (W × Fin q)) = 3 := by
        rw [Finset.card_insert_of_notMem (by simp [hxy, hxz]),
          Finset.card_insert_of_notMem (by simp [hyz]), Finset.card_singleton]
      have heq : ({x, y, z} : Finset (W × Fin q)) = t' :=
        Finset.eq_of_subset_of_card_le hsub (by rw [hcl.card_eq, hcard])
      have ex : ((a, x.2) : W × Fin q) = x := by rw [Prod.ext_iff]; exact ⟨hxa.symm, rfl⟩
      have ey : ((b, y.2) : W × Fin q) = y := by rw [Prod.ext_iff]; exact ⟨hyb.symm, rfl⟩
      have ez : ((c, z.2) : W × Fin q) = z := by rw [Prod.ext_iff]; exact ⟨hzc.symm, rfl⟩
      refine ⟨(x.2, y.2, z.2), ?_⟩
      rw [← heq]
      simp only [hf]
      rw [ex, ey, ez]
    · rintro ⟨⟨i, j, k⟩, rfl⟩
      constructor
      · constructor
        · intro u hu v hv huv
          simp only [hf, Finset.coe_insert, Set.mem_insert_iff, Finset.coe_singleton,
            Set.mem_singleton_iff] at hu hv
          rcases hu with rfl | rfl | rfl <;> rcases hv with rfl | rfl | rfl <;>
            simp_all [blowUp_adj, hAab.symm, hAac.symm, hAbc.symm]
        · simp only [hf]
          rw [Finset.card_insert_of_notMem (by simp [hab, hac]),
            Finset.card_insert_of_notMem (by simp [hbc]), Finset.card_singleton]
      · simp [hf]
  rw [himg, Finset.card_image_of_injective _ hinj]
  simp [Finset.card_univ, pow_succ, mul_assoc]

/-- **The fibre of the projection through a fixed blow-up edge has `q` elements.** -/
theorem card_blowUp_fiber_edge (H : SimpleGraph W) [DecidableRel H.Adj] (q : ℕ) {t : Finset W}
    (ht : H.IsNClique 3 t) {x y : W × Fin q} (hne : x.1 ≠ y.1) (hx : x.1 ∈ t) (hy : y.1 ∈ t) :
    #(((blowUp H q).cliqueFinset 3).filter
        (fun t' => t'.image Prod.fst = t ∧ ({x, y} : Finset (W × Fin q)) ⊆ t')) = q := by
  classical
  have hxy : x ≠ y := fun h => hne (by rw [h])
  have hsub : ({x.1, y.1} : Finset W) ⊆ t := by
    intro v hv
    simp only [Finset.mem_insert, Finset.mem_singleton] at hv
    rcases hv with rfl | rfl <;> assumption
  have hcard2 : #({x.1, y.1} : Finset W) = 2 := by
    rw [Finset.card_insert_of_notMem (by simp [hne]), Finset.card_singleton]
  have hcard1 : #(t \ ({x.1, y.1} : Finset W)) = 1 := by
    rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hsub, ht.card_eq, hcard2]
  obtain ⟨c, hc⟩ := Finset.card_eq_one.mp hcard1
  have hcmem : c ∈ t \ ({x.1, y.1} : Finset W) := by rw [hc]; simp
  have hct : c ∈ t := (Finset.mem_sdiff.mp hcmem).1
  have hcab : c ∉ ({x.1, y.1} : Finset W) := (Finset.mem_sdiff.mp hcmem).2
  have hca : c ≠ x.1 := by intro h; exact hcab (by simp [h])
  have hcb : c ≠ y.1 := by intro h; exact hcab (by simp [h])
  have htabc : t = ({x.1, y.1, c} : Finset W) := by
    refine (Finset.eq_of_subset_of_card_le ?_ ?_).symm
    · intro v hv
      simp only [Finset.mem_insert, Finset.mem_singleton] at hv
      rcases hv with rfl | rfl | rfl <;> assumption
    · rw [ht.card_eq, Finset.card_insert_of_notMem (by simp [hne, Ne.symm hca]),
        Finset.card_insert_of_notMem (by simp [Ne.symm hcb]), Finset.card_singleton]
  have hAab : H.Adj x.1 y.1 := ht.1 hx hy hne
  have hAac : H.Adj x.1 c := (ht.1 hct hx hca).symm
  have hAbc : H.Adj y.1 c := (ht.1 hct hy hcb).symm
  set f : Fin q → Finset (W × Fin q) := fun k => {x, y, (c, k)} with hf
  have hinj : Function.Injective f := by
    intro k k' h
    simp only [hf] at h
    have hmem : ((c, k) : W × Fin q) ∈ ({x, y, (c, k')} : Finset (W × Fin q)) := by
      rw [← h]; simp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
    rcases hmem with h1 | h1 | h1
    · exact absurd (congrArg Prod.fst h1) hca
    · exact absurd (congrArg Prod.fst h1) hcb
    · exact (Prod.ext_iff.mp h1).2
  have himg : ((blowUp H q).cliqueFinset 3).filter
      (fun t' => t'.image Prod.fst = t ∧ ({x, y} : Finset (W × Fin q)) ⊆ t')
      = (univ : Finset (Fin q)).image f := by
    ext t'
    simp only [Finset.mem_filter, Finset.mem_image, Finset.mem_univ, true_and,
      SimpleGraph.mem_cliqueFinset_iff]
    constructor
    · rintro ⟨hcl, himgt, hxysub⟩
      have hxt : x ∈ t' := hxysub (by simp)
      have hyt : y ∈ t' := hxysub (by simp)
      have hcx : ∃ z ∈ t', z.1 = c := by
        have : c ∈ t'.image Prod.fst := by rw [himgt]; exact hct
        simpa [Finset.mem_image] using this
      obtain ⟨z, hz, hzc⟩ := hcx
      have hxz : x ≠ z := fun h => hca (by rw [← hzc, ← h])
      have hyz : y ≠ z := fun h => hcb (by rw [← hzc, ← h])
      have hsub' : ({x, y, z} : Finset (W × Fin q)) ⊆ t' := by
        intro v hv
        simp only [Finset.mem_insert, Finset.mem_singleton] at hv
        rcases hv with rfl | rfl | rfl <;> assumption
      have hcard : #({x, y, z} : Finset (W × Fin q)) = 3 := by
        rw [Finset.card_insert_of_notMem (by simp [hxy, hxz]),
          Finset.card_insert_of_notMem (by simp [hyz]), Finset.card_singleton]
      have heq : ({x, y, z} : Finset (W × Fin q)) = t' :=
        Finset.eq_of_subset_of_card_le hsub' (by rw [hcl.card_eq, hcard])
      have ez : ((c, z.2) : W × Fin q) = z := by rw [Prod.ext_iff]; exact ⟨hzc.symm, rfl⟩
      exact ⟨z.2, by rw [← heq]; simp only [hf]; rw [ez]⟩
    · rintro ⟨k, rfl⟩
      have hxck : x ≠ (c, k) := fun h => hca (congrArg Prod.fst h).symm
      have hyck : y ≠ (c, k) := fun h => hcb (congrArg Prod.fst h).symm
      refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
      · intro u hu v hv huv
        simp only [blowUp_adj]
        simp only [hf, Finset.coe_insert, Set.mem_insert_iff, Finset.coe_singleton,
          Set.mem_singleton_iff] at hu hv
        rcases hu with rfl | rfl | rfl <;> rcases hv with rfl | rfl | rfl <;>
          first
            | exact absurd rfl huv
            | exact hAab
            | exact hAab.symm
            | exact hAac
            | exact hAac.symm
            | exact hAbc
            | exact hAbc.symm
      · simp only [hf]
        rw [Finset.card_insert_of_notMem (by simp [hxy, hxck]),
          Finset.card_insert_of_notMem (by simp [hyck]), Finset.card_singleton]
      · simp only [hf, Finset.image_insert, Finset.image_singleton]
        exact htabc.symm
      · simp [hf]
  rw [himg, Finset.card_image_of_injective _ hinj]
  simp

/-! ### Lifting a fractional packing to the blow-up -/

/-- The lift of a weight function on the triangles of `H` to the triangles of the blow-up: the
weight of a triangle is `1/q` of the weight of the triangle below it. -/
noncomputable def liftWeight (H : SimpleGraph W) [DecidableRel H.Adj] (q : ℕ)
    (w : Finset (Finset W) → ℝ) : Finset (Finset (W × Fin q)) → ℝ :=
  fun T' => if T' ∈ triangleHypergraphE (blowUp H q) then
    w (((vtxSet T').image Prod.fst).powersetCard 2) / q else 0

/-- **The lift of a fractional packing is a fractional packing.** -/
theorem isFracPacking_liftWeight (H : SimpleGraph W) [DecidableRel H.Adj] {q : ℕ} (hq : 0 < q)
    {w : Finset (Finset W) → ℝ} (hw : IsFracPacking H w) :
    IsFracPacking (blowUp H q) (liftWeight H q w) := by
  classical
  have hqR : (0:ℝ) < q := by exact_mod_cast hq
  refine ⟨fun T' => ?_, fun T' hT' => ?_, fun e' => ?_⟩
  · rw [liftWeight]; split_ifs
    · exact div_nonneg (hw.1 _) hqR.le
    · exact le_rfl
  · rw [liftWeight, ite_eq_right hT']
  · by_cases he2 : #e' = 2
    swap
    · have hemp : (triangleHypergraphE (blowUp H q)).filter (fun T => e' ∈ T) = ∅ := by
        ext T
        simp only [Finset.mem_filter, Finset.notMem_empty, iff_false, not_and]
        intro hT heT
        rw [triangleHypergraphE, Finset.mem_image] at hT
        obtain ⟨t', ht', rfl⟩ := hT
        rw [Finset.mem_powersetCard] at heT
        exact he2 heT.2
      rw [hemp, Finset.sum_empty]; norm_num
    obtain ⟨x, y, hxy, rfl⟩ := Finset.card_eq_two.mp he2
    rw [sum_triangleHypergraphE_filter (blowUp H q) he2]
    have hstep : ∀ t' ∈ ((blowUp H q).cliqueFinset 3).filter
        (fun t' => ({x, y} : Finset (W × Fin q)) ⊆ t'),
        liftWeight H q w (t'.powersetCard 2) = w ((t'.image Prod.fst).powersetCard 2) / q := by
      intro t' ht'
      rw [Finset.mem_filter, SimpleGraph.mem_cliqueFinset_iff] at ht'
      have hmem : t'.powersetCard 2 ∈ triangleHypergraphE (blowUp H q) := by
        rw [triangleHypergraphE, Finset.mem_image]
        exact ⟨t', SimpleGraph.mem_cliqueFinset_iff.mpr ht'.1, rfl⟩
      rw [liftWeight, ite_eq_left hmem, vtxSet_powersetCard_two (by rw [ht'.1.card_eq]; norm_num)]
    by_cases hfst : x.1 = y.1
    · have hempty : ((blowUp H q).cliqueFinset 3).filter
          (fun t' => ({x, y} : Finset (W × Fin q)) ⊆ t') = ∅ := by
        ext t'
        simp only [Finset.mem_filter, Finset.notMem_empty, iff_false, not_and]
        intro ht' hsub
        rw [SimpleGraph.mem_cliqueFinset_iff] at ht'
        have hx : x ∈ t' := hsub (by simp)
        have hy : y ∈ t' := hsub (by simp)
        have := ht'.1 (Finset.mem_coe.mpr hx) (Finset.mem_coe.mpr hy) hxy
        rw [blowUp_adj, hfst] at this
        exact this.ne rfl
      rw [hempty, Finset.sum_empty]; norm_num
    · have hcard2 : #({x.1, y.1} : Finset W) = 2 := by
        rw [Finset.card_insert_of_notMem (by simp [hfst]), Finset.card_singleton]
      rw [Finset.sum_congr rfl hstep,
        ← Finset.sum_fiberwise_of_maps_to (g := fun t' => t'.image Prod.fst)
          (t := (H.cliqueFinset 3).filter (fun t => ({x.1, y.1} : Finset W) ⊆ t))
          (fun t' ht' => by
            rw [Finset.mem_filter, SimpleGraph.mem_cliqueFinset_iff] at ht' ⊢
            refine ⟨isNClique_image_fst ht'.1, ?_⟩
            intro v hv
            simp only [Finset.mem_insert, Finset.mem_singleton] at hv
            rcases hv with rfl | rfl
            · exact Finset.mem_image.mpr ⟨x, ht'.2 (by simp), rfl⟩
            · exact Finset.mem_image.mpr ⟨y, ht'.2 (by simp), rfl⟩)]
      refine le_trans (le_of_eq ?_) (hw.2.2 ({x.1, y.1} : Finset W))
      rw [sum_triangleHypergraphE_filter H hcard2 w]
      refine Finset.sum_congr rfl (fun t ht => ?_)
      rw [Finset.mem_filter, SimpleGraph.mem_cliqueFinset_iff] at ht
      have hconst : ∀ t' ∈ (((blowUp H q).cliqueFinset 3).filter
          (fun t' => ({x, y} : Finset (W × Fin q)) ⊆ t')).filter
            (fun t' => t'.image Prod.fst = t),
          w ((t'.image Prod.fst).powersetCard 2) / q = w (t.powersetCard 2) / q :=
        fun t' ht' => by rw [(Finset.mem_filter.mp ht').2]
      rw [Finset.sum_congr rfl hconst, Finset.sum_const]
      have hcardeq : #((((blowUp H q).cliqueFinset 3).filter
          (fun t' => ({x, y} : Finset (W × Fin q)) ⊆ t')).filter
            (fun t' => t'.image Prod.fst = t)) = q := by
        rw [Finset.filter_filter]
        have hcomm : ((blowUp H q).cliqueFinset 3).filter
            (fun t' => ({x, y} : Finset (W × Fin q)) ⊆ t' ∧ t'.image Prod.fst = t)
            = ((blowUp H q).cliqueFinset 3).filter
            (fun t' => t'.image Prod.fst = t ∧ ({x, y} : Finset (W × Fin q)) ⊆ t') := by
          apply Finset.filter_congr
          intro t' _
          exact and_comm
        rw [hcomm]
        exact card_blowUp_fiber_edge H q ht.1 hfst (ht.2 (by simp)) (ht.2 (by simp))
      rw [hcardeq, nsmul_eq_mul]
      field_simp

/-- **The value of the lift is `q²` times the value.** -/
theorem sum_liftWeight (H : SimpleGraph W) [DecidableRel H.Adj] {q : ℕ} (hq : 0 < q)
    (w : Finset (Finset W) → ℝ) :
    ∑ T' ∈ triangleHypergraphE (blowUp H q), liftWeight H q w T'
      = (q : ℝ) ^ 2 * ∑ T ∈ triangleHypergraphE H, w T := by
  classical
  have hqR : (q : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hq.ne'
  rw [sum_triangleHypergraphE (blowUp H q) (liftWeight H q w)]
  have hstep : ∀ t' ∈ (blowUp H q).cliqueFinset 3,
      liftWeight H q w (t'.powersetCard 2) = w ((t'.image Prod.fst).powersetCard 2) / q := by
    intro t' ht'
    rw [SimpleGraph.mem_cliqueFinset_iff] at ht'
    have hmem : t'.powersetCard 2 ∈ triangleHypergraphE (blowUp H q) := by
      rw [triangleHypergraphE, Finset.mem_image]
      exact ⟨t', SimpleGraph.mem_cliqueFinset_iff.mpr ht', rfl⟩
    rw [liftWeight, ite_eq_left hmem, vtxSet_powersetCard_two (by rw [ht'.card_eq]; norm_num)]
  rw [Finset.sum_congr rfl hstep,
    ← Finset.sum_fiberwise_of_maps_to (g := fun t' => t'.image Prod.fst)
      (t := H.cliqueFinset 3) (fun t' ht' => by
        rw [SimpleGraph.mem_cliqueFinset_iff] at ht' ⊢
        exact isNClique_image_fst ht')]
  rw [sum_triangleHypergraphE H w, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun t ht => ?_)
  rw [SimpleGraph.mem_cliqueFinset_iff] at ht
  have hconst : ∀ t' ∈ ((blowUp H q).cliqueFinset 3).filter (fun t' => t'.image Prod.fst = t),
      w ((t'.image Prod.fst).powersetCard 2) / q = w (t.powersetCard 2) / q := by
    intro t' ht'
    rw [(Finset.mem_filter.mp ht').2]
  rw [Finset.sum_congr rfl hconst, Finset.sum_const, card_blowUp_fiber H q ht, nsmul_eq_mul]
  push_cast
  field_simp

/-- **The blow-up bound `q²·ν₃*(H) ≤ ν₃*(H[q])`.** -/
theorem nu3star_blowUp_ge (H : SimpleGraph W) [DecidableRel H.Adj] {q : ℕ} (hq : 0 < q) :
    (q : ℝ) ^ 2 * nu3star H ≤ nu3star (blowUp H q) := by
  classical
  have hq2 : (0:ℝ) < (q:ℝ)^2 := by
    have : (0:ℝ) < q := by exact_mod_cast hq
    positivity
  have hne : {x : ℝ | ∃ w, IsFracPacking H w ∧ x = ∑ T ∈ triangleHypergraphE H, w T}.Nonempty :=
    ⟨0, fun _ => 0, ⟨fun _ => le_rfl, fun _ _ => rfl, fun e => by simp⟩, by simp⟩
  have hbound : nu3star H ≤ nu3star (blowUp H q) / (q:ℝ)^2 := by
    rw [nu3star]
    refine csSup_le hne ?_
    rintro x ⟨w, hw, rfl⟩
    rw [le_div_iff₀ hq2]
    calc (∑ T ∈ triangleHypergraphE H, w T) * (q:ℝ)^2
        = ∑ T' ∈ triangleHypergraphE (blowUp H q), liftWeight H q w T' := by
          rw [sum_liftWeight H hq w]; ring
      _ ≤ nu3star (blowUp H q) :=
          le_csSup (nu3star_bddAbove _) ⟨liftWeight H q w, isFracPacking_liftWeight H hq hw, rfl⟩
  rw [mul_comm]
  exact (le_div_iff₀ hq2).mp hbound

omit [Fintype W] in
/-- A triangle of the blow-up whose projection contains the edge `{a, b}` contains exactly one
vertex over `a` and one over `b`. -/
theorem blowUp_filter_pair {H : SimpleGraph W} {q : ℕ} {a b : W}
    {t' : Finset (W × Fin q)} (ht' : (blowUp H q).IsNClique 3 t')
    (hsub : ({a, b} : Finset W) ⊆ t'.image Prod.fst) :
    ∃ i j : Fin q, t'.filter (fun v => v.1 = a ∨ v.1 = b) = {(a, i), (b, j)} ∧
      ({(a, i), (b, j)} : Finset (W × Fin q)) ⊆ t' := by
  classical
  obtain ⟨x, hx, hxa⟩ : ∃ x ∈ t', x.1 = a := by
    simpa [Finset.mem_image] using hsub (by simp : a ∈ ({a, b} : Finset W))
  obtain ⟨y, hy, hyb⟩ : ∃ y ∈ t', y.1 = b := by
    simpa [Finset.mem_image] using hsub (by simp : b ∈ ({a, b} : Finset W))
  have hunique : ∀ v ∈ t', v.1 = a → v = x := by
    intro v hv hva
    by_contra hne
    have := ht'.1 (Finset.mem_coe.mpr hv) (Finset.mem_coe.mpr hx) hne
    rw [blowUp_adj, hva, hxa] at this
    exact this.ne rfl
  have hunique' : ∀ v ∈ t', v.1 = b → v = y := by
    intro v hv hvb
    by_contra hne
    have := ht'.1 (Finset.mem_coe.mpr hv) (Finset.mem_coe.mpr hy) hne
    rw [blowUp_adj, hvb, hyb] at this
    exact this.ne rfl
  have ex : ((a, x.2) : W × Fin q) = x := by rw [Prod.ext_iff]; exact ⟨hxa.symm, rfl⟩
  have ey : ((b, y.2) : W × Fin q) = y := by rw [Prod.ext_iff]; exact ⟨hyb.symm, rfl⟩
  refine ⟨x.2, y.2, ?_, ?_⟩
  · rw [ex, ey]
    ext v
    simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨hv, hva | hvb⟩
      · exact Or.inl (hunique v hv hva)
      · exact Or.inr (hunique' v hv hvb)
    · rintro (rfl | rfl)
      · exact ⟨hx, Or.inl hxa⟩
      · exact ⟨hy, Or.inr hyb⟩
  · intro v hv
    simp only [Finset.mem_insert, Finset.mem_singleton] at hv
    rcases hv with rfl | rfl
    · rw [ex]; exact hx
    · rw [ey]; exact hy

/-! ### Projecting a fractional packing of the blow-up -/

/-- The projection of a weight function on the triangles of the blow-up: a triangle of `H` receives
`1/q²` of the total weight of the triangles above it. -/
noncomputable def projWeight (H : SimpleGraph W) [DecidableRel H.Adj] (q : ℕ)
    (w' : Finset (Finset (W × Fin q)) → ℝ) : Finset (Finset W) → ℝ :=
  fun T => if T ∈ triangleHypergraphE H then
    (∑ t' ∈ ((blowUp H q).cliqueFinset 3).filter (fun t' => t'.image Prod.fst = vtxSet T),
      w' (t'.powersetCard 2)) / (q : ℝ) ^ 2 else 0

/-- **The projection of a fractional packing is a fractional packing.** -/
theorem isFracPacking_projWeight (H : SimpleGraph W) [DecidableRel H.Adj] {q : ℕ} (hq : 0 < q)
    {w' : Finset (Finset (W × Fin q)) → ℝ} (hw' : IsFracPacking (blowUp H q) w') :
    IsFracPacking H (projWeight H q w') := by
  classical
  have hq2 : (0:ℝ) < (q:ℝ)^2 := by
    have : (0:ℝ) < q := by exact_mod_cast hq
    positivity
  refine ⟨fun T => ?_, fun T hT => ?_, fun e => ?_⟩
  · rw [projWeight]; split_ifs
    · exact div_nonneg (Finset.sum_nonneg fun _ _ => hw'.1 _) hq2.le
    · exact le_rfl
  · rw [projWeight, ite_eq_right hT]
  · by_cases he2 : #e = 2
    swap
    · have hemp : (triangleHypergraphE H).filter (fun T => e ∈ T) = ∅ := by
        ext T
        simp only [Finset.mem_filter, Finset.notMem_empty, iff_false, not_and]
        intro hT heT
        rw [triangleHypergraphE, Finset.mem_image] at hT
        obtain ⟨t, ht, rfl⟩ := hT
        rw [Finset.mem_powersetCard] at heT
        exact he2 heT.2
      rw [hemp, Finset.sum_empty]; norm_num
    obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.mp he2
    set S : Finset (Finset (W × Fin q)) := ((blowUp H q).cliqueFinset 3).filter
      (fun t' => ({a, b} : Finset W) ⊆ t'.image Prod.fst) with hSdef
    set E₀ : Finset (Finset (W × Fin q)) := (univ : Finset (Fin q × Fin q)).image
      (fun p => ({(a, p.1), (b, p.2)} : Finset (W × Fin q))) with hE₀
    rw [sum_triangleHypergraphE_filter H he2 (projWeight H q w')]
    have hstep : ∀ t ∈ (H.cliqueFinset 3).filter (fun t => ({a, b} : Finset W) ⊆ t),
        projWeight H q w' (t.powersetCard 2)
          = (∑ t' ∈ ((blowUp H q).cliqueFinset 3).filter (fun t' => t'.image Prod.fst = t),
              w' (t'.powersetCard 2)) / (q:ℝ)^2 := by
      intro t ht
      rw [Finset.mem_filter, SimpleGraph.mem_cliqueFinset_iff] at ht
      have hmem : t.powersetCard 2 ∈ triangleHypergraphE H := by
        rw [triangleHypergraphE, Finset.mem_image]
        exact ⟨t, SimpleGraph.mem_cliqueFinset_iff.mpr ht.1, rfl⟩
      rw [projWeight, ite_eq_left hmem, vtxSet_powersetCard_two (by rw [ht.1.card_eq]; norm_num)]
    rw [Finset.sum_congr rfl hstep, ← Finset.sum_div, div_le_one hq2]
    have hfibeq : ∀ t ∈ (H.cliqueFinset 3).filter (fun t => ({a, b} : Finset W) ⊆ t),
        ((blowUp H q).cliqueFinset 3).filter (fun t' => t'.image Prod.fst = t)
          = S.filter (fun t' => t'.image Prod.fst = t) := by
      intro t ht
      ext t'
      simp only [hSdef, Finset.mem_filter]
      constructor
      · rintro ⟨h1, h2⟩
        exact ⟨⟨h1, by rw [h2]; exact (Finset.mem_filter.mp ht).2⟩, h2⟩
      · rintro ⟨⟨h1, -⟩, h2⟩
        exact ⟨h1, h2⟩
    rw [Finset.sum_congr rfl (fun t ht => by rw [hfibeq t ht])]
    have hfib : ∑ t ∈ (H.cliqueFinset 3).filter (fun t => ({a, b} : Finset W) ⊆ t),
        ∑ t' ∈ S.filter (fun t' => t'.image Prod.fst = t), w' (t'.powersetCard 2)
        = ∑ t' ∈ S, w' (t'.powersetCard 2) := by
      apply Finset.sum_fiberwise_of_maps_to
      intro t' ht'
      rw [hSdef, Finset.mem_filter, SimpleGraph.mem_cliqueFinset_iff] at ht'
      rw [Finset.mem_filter, SimpleGraph.mem_cliqueFinset_iff]
      exact ⟨isNClique_image_fst ht'.1, ht'.2⟩
    rw [hfib]
    have hmaps : ∀ t' ∈ S, t'.filter (fun v => v.1 = a ∨ v.1 = b) ∈ E₀ := by
      intro t' ht'
      rw [hSdef, Finset.mem_filter, SimpleGraph.mem_cliqueFinset_iff] at ht'
      obtain ⟨i, j, hij, -⟩ := blowUp_filter_pair ht'.1 ht'.2
      rw [hij, hE₀, Finset.mem_image]
      exact ⟨(i, j), Finset.mem_univ _, rfl⟩
    rw [← Finset.sum_fiberwise_of_maps_to hmaps]
    have hinner : ∀ e' ∈ E₀,
        ∑ t' ∈ S.filter (fun t' => t'.filter (fun v => v.1 = a ∨ v.1 = b) = e'),
          w' (t'.powersetCard 2) ≤ 1 := by
      intro e' _
      have hinj : Set.InjOn (fun t' : Finset (W × Fin q) => t'.powersetCard 2)
          ↑(S.filter (fun t' => t'.filter (fun v => v.1 = a ∨ v.1 = b) = e')) := by
        intro s hs t ht hst
        rw [Finset.mem_coe, Finset.mem_filter, hSdef, Finset.mem_filter,
          SimpleGraph.mem_cliqueFinset_iff] at hs ht
        exact powersetCard_two_inj (by have := hs.1.1.card_eq; omega)
          (by have := ht.1.1.card_eq; omega) hst
      rw [← Finset.sum_image (f := w') hinj]
      have hsub : (S.filter (fun t' => t'.filter (fun v => v.1 = a ∨ v.1 = b) = e')).image
          (fun t' => t'.powersetCard 2)
          ⊆ (triangleHypergraphE (blowUp H q)).filter (fun T => e' ∈ T) := by
        intro T hT
        rw [Finset.mem_image] at hT
        obtain ⟨t', ht', rfl⟩ := hT
        rw [Finset.mem_filter, hSdef, Finset.mem_filter,
          SimpleGraph.mem_cliqueFinset_iff] at ht'
        obtain ⟨i, j, hij, -⟩ := blowUp_filter_pair ht'.1.1 ht'.1.2
        have he'2 : #e' = 2 := by
          rw [← ht'.2, hij, Finset.card_insert_of_notMem (by simp [hab]), Finset.card_singleton]
        refine Finset.mem_filter.mpr ⟨?_, ?_⟩
        · rw [triangleHypergraphE, Finset.mem_image]
          exact ⟨t', SimpleGraph.mem_cliqueFinset_iff.mpr ht'.1.1, rfl⟩
        · rw [Finset.mem_powersetCard]
          refine ⟨?_, he'2⟩
          rw [← ht'.2]
          exact Finset.filter_subset _ _
      exact le_trans (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun T' _ _ => hw'.1 T'))
        (hw'.2.2 e')
    calc ∑ e' ∈ E₀, ∑ t' ∈ S.filter (fun t' => t'.filter (fun v => v.1 = a ∨ v.1 = b) = e'),
          w' (t'.powersetCard 2)
        ≤ ∑ _e' ∈ E₀, (1:ℝ) := Finset.sum_le_sum hinner
      _ = (#E₀ : ℝ) := by rw [Finset.sum_const, nsmul_eq_mul, mul_one]
      _ ≤ (q:ℝ)^2 := by
          have hcard : #E₀ ≤ q * q := by
            calc #E₀ ≤ #(univ : Finset (Fin q × Fin q)) := Finset.card_image_le
              _ = q * q := by simp
          calc (#E₀ : ℝ) ≤ ((q * q : ℕ) : ℝ) := by exact_mod_cast hcard
            _ = (q:ℝ)^2 := by push_cast; ring

/-- **The value of the projection is `1/q²` of the value.** -/
theorem sum_projWeight (H : SimpleGraph W) [DecidableRel H.Adj] {q : ℕ} (hq : 0 < q)
    (w' : Finset (Finset (W × Fin q)) → ℝ) :
    (q : ℝ) ^ 2 * ∑ T ∈ triangleHypergraphE H, projWeight H q w' T
      = ∑ T' ∈ triangleHypergraphE (blowUp H q), w' T' := by
  classical
  have hq2 : (0:ℝ) < (q:ℝ)^2 := by
    have : (0:ℝ) < q := by exact_mod_cast hq
    positivity
  have hfib : ∑ t ∈ H.cliqueFinset 3,
      ∑ t' ∈ ((blowUp H q).cliqueFinset 3).filter (fun t' => t'.image Prod.fst = t),
        w' (t'.powersetCard 2)
      = ∑ t' ∈ (blowUp H q).cliqueFinset 3, w' (t'.powersetCard 2) := by
    apply Finset.sum_fiberwise_of_maps_to
    intro t' ht'
    rw [SimpleGraph.mem_cliqueFinset_iff] at ht' ⊢
    exact isNClique_image_fst ht'
  rw [sum_triangleHypergraphE H, sum_triangleHypergraphE (blowUp H q) w']
  have hstep : ∀ t ∈ H.cliqueFinset 3, projWeight H q w' (t.powersetCard 2)
      = (∑ t' ∈ ((blowUp H q).cliqueFinset 3).filter (fun t' => t'.image Prod.fst = t),
          w' (t'.powersetCard 2)) / (q:ℝ)^2 := by
    intro t ht
    rw [SimpleGraph.mem_cliqueFinset_iff] at ht
    have hmem : t.powersetCard 2 ∈ triangleHypergraphE H := by
      rw [triangleHypergraphE, Finset.mem_image]
      exact ⟨t, SimpleGraph.mem_cliqueFinset_iff.mpr ht, rfl⟩
    rw [projWeight, ite_eq_left hmem, vtxSet_powersetCard_two (by rw [ht.card_eq]; norm_num)]
  rw [Finset.sum_congr rfl hstep, ← Finset.sum_div, hfib, mul_comm, div_mul_cancel₀ _ hq2.ne']

/-- **The blow-up bound `ν₃*(H[q]) ≤ q²·ν₃*(H)`.** -/
theorem nu3star_blowUp_le (H : SimpleGraph W) [DecidableRel H.Adj] {q : ℕ} (hq : 0 < q) :
    nu3star (blowUp H q) ≤ (q : ℝ) ^ 2 * nu3star H := by
  classical
  have hq2 : (0:ℝ) < (q:ℝ)^2 := by
    have : (0:ℝ) < q := by exact_mod_cast hq
    positivity
  have hne : {x : ℝ | ∃ w, IsFracPacking (blowUp H q) w ∧
      x = ∑ T ∈ triangleHypergraphE (blowUp H q), w T}.Nonempty :=
    ⟨0, fun _ => 0, ⟨fun _ => le_rfl, fun _ _ => rfl, fun e => by simp⟩, by simp⟩
  rw [nu3star]
  refine csSup_le hne ?_
  rintro x ⟨w', hw', rfl⟩
  rw [← sum_projWeight H hq w']
  exact mul_le_mul_of_nonneg_left
    (le_csSup (nu3star_bddAbove H)
      ⟨projWeight H q w', isFracPacking_projWeight H hq hw', rfl⟩) hq2.le

/-- **The blow-up scaling of the fractional triangle packing number.** -/
theorem nu3star_blowUp (H : SimpleGraph W) [DecidableRel H.Adj] {q : ℕ} (hq : 0 < q) :
    nu3star (blowUp H q) = (q : ℝ) ^ 2 * nu3star H :=
  le_antisymm (nu3star_blowUp_le H hq) (nu3star_blowUp_ge H hq)

/-! ### Axiom check -/

section AxCheck

open Nibble.AX1



end AxCheck

end Nibble.AX1

end




/-! # YusterBridgeFrac -/

public section

open Finset SimpleGraph Hypergraph

namespace Nibble.YusterE

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- PaperIII-style fractional triangle packing, with weights on vertex-sets. -/
def IsTriangleFracPacking (w : Finset V → ℝ) : Prop :=
  (∀ t, 0 ≤ w t) ∧
    (∀ t, w t ≠ 0 → G.IsNClique 3 t) ∧
    ∀ e : Finset V, e.card = 2 →
      (∑ t ∈ (G.cliqueFinset 3).filter (fun t => e ⊆ t), w t) ≤ 1

/-- Taking all two-element subsets is injective on triangles. -/
theorem triangle_powersetCard_two_injOn :
    Set.InjOn (fun t : Finset V => t.powersetCard 2)
      (G.cliqueFinset 3 : Set (Finset V)) := by
  intro t1 ht1 t2 ht2 heq
  simp only [Finset.mem_coe, SimpleGraph.mem_cliqueFinset_iff] at ht1 ht2
  simp only at heq
  apply Finset.Subset.antisymm
  · intro a ha
    obtain ⟨b, hb, hab⟩ : ∃ b ∈ t1, b ≠ a := by
      have hne : (t1.erase a).Nonempty := by
        rw [← Finset.card_pos, Finset.card_erase_of_mem ha, ht1.2]; omega
      obtain ⟨b, hbm⟩ := hne
      exact ⟨b, Finset.mem_of_mem_erase hbm, Finset.ne_of_mem_erase hbm⟩
    have hmem : ({a, b} : Finset V) ∈ t1.powersetCard 2 := by
      rw [Finset.mem_powersetCard]
      refine ⟨?_, Finset.card_pair (fun h => hab h.symm)⟩
      intro z hz
      simp only [Finset.mem_insert, Finset.mem_singleton] at hz
      rcases hz with rfl | rfl
      · exact ha
      · exact hb
    rw [heq] at hmem
    rw [Finset.mem_powersetCard] at hmem
    exact hmem.1 (by simp)
  · intro a ha
    obtain ⟨b, hb, hab⟩ : ∃ b ∈ t2, b ≠ a := by
      have hne : (t2.erase a).Nonempty := by
        rw [← Finset.card_pos, Finset.card_erase_of_mem ha, ht2.2]; omega
      obtain ⟨b, hbm⟩ := hne
      exact ⟨b, Finset.mem_of_mem_erase hbm, Finset.ne_of_mem_erase hbm⟩
    have hmem : ({a, b} : Finset V) ∈ t2.powersetCard 2 := by
      rw [Finset.mem_powersetCard]
      refine ⟨?_, Finset.card_pair (fun h => hab h.symm)⟩
      intro z hz
      simp only [Finset.mem_insert, Finset.mem_singleton] at hz
      rcases hz with rfl | rfl
      · exact ha
      · exact hb
    rw [← heq] at hmem
    rw [Finset.mem_powersetCard] at hmem
    exact hmem.1 (by simp)

omit [Fintype V] [DecidableRel G.Adj] in
/-- The union of the two-element subsets of a triangle recovers its vertices. -/
theorem triangle_powersetCard_two_sup {t : Finset V} (ht : G.IsNClique 3 t) :
    (t.powersetCard 2).sup id = t := by
  apply Finset.ext
  intro v
  simp only [mem_sup, mem_powersetCard, id_eq]
  constructor
  · rintro ⟨s, hs, hv⟩
    exact hs.1 hv
  · intro hv
    have hcard : t.card = 3 := ht.card_eq
    have hne : (t.erase v).Nonempty := by
      have h2 : (t.erase v).card = 2 := by rw [Finset.card_erase_of_mem hv]; omega
      exact Finset.card_pos.mp (by omega)
    obtain ⟨u, hu⟩ := hne
    use {v, u}
    refine ⟨⟨?subset, ?card⟩, ?mem⟩
    · intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl
      · exact hv
      · exact Finset.mem_of_mem_erase hu
    · rw [Finset.card_pair]; exact fun h => Finset.ne_of_mem_erase hu h.symm
    · simp

omit [Fintype V] [DecidableEq V] in
/-- For a two-element set `e`, membership among a triangle's edges is inclusion
in the triangle. -/
theorem mem_powersetCard_two_iff_subset {e t : Finset V} (he : e.card = 2) :
    e ∈ t.powersetCard 2 ↔ e ⊆ t := by
  simp [Finset.mem_powersetCard, he]

/-- Filtering the edge-set triangle hypergraph at an edge is the image of the
vertex-set triangles containing that edge. -/
theorem triangleHypergraphE_filter_eq_image (e : Finset V) (he : e.card = 2) :
    (triangleHypergraphE G).filter (fun T => e ∈ T) =
      ((G.cliqueFinset 3).filter (fun t => e ⊆ t)).image
        (fun t => t.powersetCard 2) := by
  ext T
  simp only [triangleHypergraphE, Finset.mem_filter, Finset.mem_image]
  constructor
  · rintro ⟨⟨t, ht, rfl⟩, heT⟩
    exact ⟨t, ⟨ht, by rw [mem_powersetCard_two_iff_subset he] at heT; exact heT⟩, rfl⟩
  · rintro ⟨t, ⟨ht, ht_sub⟩, rfl⟩
    exact ⟨⟨t, ht, rfl⟩, by rw [mem_powersetCard_two_iff_subset he]; exact ht_sub⟩

/-- Reindex the fractional objective from triangle vertex-sets to triangle
edge-sets. -/
theorem sum_triangleHypergraphE_sup (w : Finset V → ℝ) :
    ∑ T ∈ triangleHypergraphE G, w (T.sup id) =
      ∑ t ∈ G.cliqueFinset 3, w t := by
  rw [triangleHypergraphE]
  rw [Finset.sum_image]
  · refine Finset.sum_congr rfl (fun t ht => ?_)
    rw [SimpleGraph.mem_cliqueFinset_iff] at ht
    rw [triangle_powersetCard_two_sup G ht]
  · exact triangle_powersetCard_two_injOn G

/-- Reindex the fractional objective from triangle edge-sets to triangle
vertex-sets. -/
theorem sum_clique_powersetCard_two (w : Finset (Finset V) → ℝ) :
    ∑ t ∈ G.cliqueFinset 3, w (t.powersetCard 2) =
      ∑ T ∈ triangleHypergraphE G, w T := by
  rw [triangleHypergraphE, Finset.sum_image (triangle_powersetCard_two_injOn G)]

/-- A fractional packing on triangle edge-sets transports to one on triangle
vertex-sets, preserving its objective. -/
theorem fracPacking_to_triangleFracPacking
    {w' : Finset (Finset V) → ℝ} (hw' : IsFracPacking G w') :
    IsTriangleFracPacking G (fun t => w' (t.powersetCard 2)) ∧
      (∑ t ∈ G.cliqueFinset 3, w' (t.powersetCard 2)) =
        ∑ T ∈ triangleHypergraphE G, w' T := by
  refine ⟨⟨?nneg, ?ncard, ?cap⟩, ?sum⟩
  case nneg =>
    intro t
    exact hw'.1 _
  case ncard =>
    intro t ht
    by_contra hnot
    apply ht
    have : t.powersetCard 2 ∉ triangleHypergraphE G := by
      rw [triangleHypergraphE, Finset.mem_image]
      intro ⟨s, hs, hs_eq⟩
      rw [SimpleGraph.mem_cliqueFinset_iff] at hs
      have hscard : s.card = 3 := hs.card_eq
      have htcard : t.card = 3 := by
        have h1 : (powersetCard 2 s).card = 3 := by simp [hscard]
        rw [hs_eq] at h1
        simp [Finset.card_powersetCard] at h1
        have hle : t.card ≤ 3 := by
          by_contra h
          push Not at h
          have : (t.card).choose 2 ≥ (4).choose 2 :=
            Nat.choose_le_choose _ (by omega : (4 : ℕ) ≤ t.card)
          simp [Nat.choose] at this
          omega
        interval_cases t.card <;> simp at h1 ⊢
      have hs2 : 2 ≤ s.card := by omega
      have ht2 : 2 ≤ t.card := by omega
      have hst : s = t := powersetCard_two_inj hs2 ht2 hs_eq
      exact hnot (hst ▸ ⟨hs.isClique, hs.card_eq⟩)
    exact hw'.2.1 _ this
  case cap =>
    intro e he
    have hfilter := triangleHypergraphE_filter_eq_image G e he
    have hinj := triangle_powersetCard_two_injOn G
    have hset_eq : ((G.cliqueFinset 3).filter (fun t => e ⊆ t) : Set (Finset V)) =
        {t | t ∈ G.cliqueFinset 3 ∧ e ⊆ t} := by ext; simp
    have hinj' : Set.InjOn (fun t => t.powersetCard 2)
        ((G.cliqueFinset 3).filter (fun t => e ⊆ t) : Set (Finset V)) := by
      rw [hset_eq]
      exact hinj.mono (fun x hx => hx.1)
    have heq : ∑ t ∈ (G.cliqueFinset 3).filter (fun t => e ⊆ t), w' (t.powersetCard 2) =
               ∑ T ∈ (triangleHypergraphE G).filter (fun T => e ∈ T), w' T := by
      rw [hfilter]
      rw [Finset.sum_image hinj']
    rw [heq]
    exact hw'.2.2 e
  case sum =>
    exact sum_clique_powersetCard_two G w'

/-- A fractional packing on triangle vertex-sets transports to one on triangle
edge-sets, preserving its objective. -/
theorem triangleFracPacking_to_fracPacking
    {w : Finset V → ℝ} (hw : IsTriangleFracPacking G w) :
    let w' : Finset (Finset V) → ℝ :=
      fun T => if T ∈ triangleHypergraphE G then w (T.sup id) else 0
    IsFracPacking G w' ∧
      (∑ T ∈ triangleHypergraphE G, w' T) =
        ∑ t ∈ G.cliqueFinset 3, w t := by
  refine ⟨⟨?nneg, ?zero_outside, ?edge_constr⟩, ?sum_eq⟩
  case nneg =>
    intro T
    simp only
    split_ifs with h <;> [exact hw.1 _; exact le_refl 0]
  case zero_outside =>
    intro T hT
    simp [hT]
  case edge_constr =>
    intro e
    have hsimp : ∀ T ∈ (triangleHypergraphE G).filter (fun T => e ∈ T),
        (if T ∈ triangleHypergraphE G then w (T.sup id) else 0) = w (T.sup id) := by
      intro T hT
      simp only [Finset.mem_filter] at hT
      simp [hT.1]
    rw [Finset.sum_congr rfl hsimp]
    by_cases he : e.card = 2
    · rw [triangleHypergraphE_filter_eq_image G e he]
      have hinj : Set.InjOn (fun t => t.powersetCard 2)
          ((G.cliqueFinset 3).filter (fun t => e ⊆ t) : Set (Finset V)) :=
        (triangle_powersetCard_two_injOn G).mono (fun t ht => by simp_all)
      rw [Finset.sum_image hinj]
      have hconv : ∀ t ∈ (G.cliqueFinset 3).filter (fun t => e ⊆ t),
          (t.powersetCard 2).sup id = t := by
        intro t ht
        simp only [Finset.mem_filter, SimpleGraph.mem_cliqueFinset_iff] at ht
        exact triangle_powersetCard_two_sup G ht.1
      rw [Finset.sum_congr rfl (fun t ht => congr_arg w (hconv t ht))]
      exact hw.2.2 e he
    · have hempty : (triangleHypergraphE G).filter (fun T => e ∈ T) = ∅ := by
        apply Finset.filter_eq_empty_iff.mpr
        intro T hT
        rw [triangleHypergraphE, Finset.mem_image] at hT
        obtain ⟨t, ht, hTe⟩ := hT
        simp only [SimpleGraph.mem_cliqueFinset_iff] at ht
        rw [← hTe]
        rw [Finset.mem_powersetCard]
        exact fun h => he h.2
      simp [hempty]
  case sum_eq =>
    conv_lhs =>
      simp only [Finset.sum_ite_mem, Finset.inter_self]
    exact sum_triangleHypergraphE_sup G w

/-- The Nibble edge-set fractional triangle-packing optimum is exactly the
PaperIII-style optimum over weights on triangle vertex-sets. -/
theorem nu3star_eq_triangleFrac_sSup :
    nu3star G =
      sSup {x : ℝ | ∃ w : Finset V → ℝ, IsTriangleFracPacking G w ∧
        x = ∑ t ∈ G.cliqueFinset 3, w t} := by
  unfold nu3star
  congr 1
  ext x
  constructor
  · rintro ⟨w', hw', rfl⟩
    obtain ⟨hpack, hsum⟩ := fracPacking_to_triangleFracPacking G hw'
    exact ⟨fun t => w' (t.powersetCard 2), hpack, hsum.symm⟩
  · rintro ⟨w, hw, rfl⟩
    let w' : Finset (Finset V) → ℝ :=
      fun T => if T ∈ triangleHypergraphE G then w (T.sup id) else 0
    obtain ⟨hpack, hsum⟩ := triangleFracPacking_to_fracPacking G hw
    exact ⟨w', hpack, hsum.symm⟩

end Nibble.YusterE

end


/-! # CoreGapPackingSplit -/

public section

open Finset SimpleGraph Hypergraph Nibble.YusterE

namespace Nibble.AX1

variable {V : Type} [Fintype V] [DecidableEq V]

/-- The set of parts of `P` met by `t`.  For a triangle of a regularity-reduced graph this is a
triple of distinct parts. -/
def partClass (P : Finpartition (univ : Finset V)) (t : Finset V) : Finset (Finset V) :=
  t.image P.part

theorem mem_partClass_iff (P : Finpartition (univ : Finset V)) (t : Finset V) (U : Finset V) :
    U ∈ partClass P t ↔ ∃ x ∈ t, P.part x = U := by
  simp [partClass]

theorem partClass_subset_parts (P : Finpartition (univ : Finset V)) (t : Finset V) :
    partClass P t ⊆ P.parts := by
  intro U hU
  obtain ⟨x, -, rfl⟩ := (mem_partClass_iff P t U).mp hU
  exact P.part_mem.mpr (mem_univ x)

theorem partClass_mem_powersetCard_three (P : Finpartition (univ : Finset V)) {t : Finset V}
    (h3 : #(partClass P t) = 3) : partClass P t ∈ P.parts.powersetCard 3 :=
  Finset.mem_powersetCard.mpr ⟨partClass_subset_parts P t, h3⟩

/-- In a regularity-reduced graph every triangle meets exactly three parts: this is the hypothesis
of `Nibble.AX1.sum_split_partClass`, discharged. -/
theorem partClass_card_three_of_isNClique (G : SimpleGraph V) [DecidableRel G.Adj]
    (P : Finpartition (univ : Finset V)) (ep de : ℝ) {t : Finset V}
    (ht : (G.regularityReduced P ep de).IsNClique 3 t) : #(partClass P t) = 3 := by
  classical
  obtain ⟨x, y, z, hxy, hxz, hyz, rfl⟩ := Finset.card_eq_three.mp ht.card_eq
  have haxy : (G.regularityReduced P ep de).Adj x y := ht.1 (by simp) (by simp) hxy
  have haxz : (G.regularityReduced P ep de).Adj x z := ht.1 (by simp) (by simp) hxz
  have hayz : (G.regularityReduced P ep de).Adj y z := ht.1 (by simp) (by simp) hyz
  obtain ⟨U, W, X, hgood, hxU, hyW, hzX⟩ :=
    regularityReduced_triangle_parts G P ep de haxy haxz hayz
  obtain ⟨hUp, hWp, hXp, hUW, hUX, hWX, -⟩ := hgood
  have h1 : P.part x = U := P.part_eq_of_mem hUp hxU
  have h2 : P.part y = W := P.part_eq_of_mem hWp hyW
  have h3 : P.part z = X := P.part_eq_of_mem hXp hzX
  have himg : partClass P {x, y, z} = {U, W, X} := by
    simp [partClass, Finset.image_insert, h1, h2, h3]
  rw [himg, Finset.card_insert_of_notMem (by simp [hUW, hUX]),
    Finset.card_insert_of_notMem (by simp [hWX]), Finset.card_singleton]

/-- **The objective splits along the triples of parts.**  If every triangle of `G` meets three
distinct parts of `P` — which is the case for a regularity-reduced graph, by
`Nibble.AX1.regularityReduced_triangle_parts` — then the sum of any weight function over the
triangles is the sum, over triples of parts, of its weight on that triple. -/
theorem sum_split_partClass (G : SimpleGraph V) [DecidableRel G.Adj]
    (P : Finpartition (univ : Finset V)) (f : Finset V → ℝ)
    (hdist : ∀ t ∈ G.cliqueFinset 3, #(partClass P t) = 3) :
    ∑ S ∈ P.parts.powersetCard 3,
        ∑ t ∈ (G.cliqueFinset 3).filter (fun t => partClass P t = S), f t
      = ∑ t ∈ G.cliqueFinset 3, f t :=
  Finset.sum_fiberwise_of_maps_to
    (fun t ht => partClass_mem_powersetCard_three P (hdist t ht)) f

/-- **The per-pair LP constraint.**  For two distinct parts `U ≠ W`, a fractional triangle packing
puts total weight at most `e(U, W)` on the triangles whose triple of parts contains both `U`
and `W`. -/
theorem sum_pair_classes_le (G : SimpleGraph V) [DecidableRel G.Adj]
    (P : Finpartition (univ : Finset V)) {w : Finset (Finset V) → ℝ} (hw : IsFracPacking G w)
    (hdist : ∀ t ∈ G.cliqueFinset 3, #(partClass P t) = 3) {U W : Finset V} (hUW : U ≠ W) :
    ∑ S ∈ (P.parts.powersetCard 3).filter (fun S => U ∈ S ∧ W ∈ S),
        ∑ t ∈ (G.cliqueFinset 3).filter (fun t => partClass P t = S), w (t.powersetCard 2)
      ≤ (#(G.interedges U W) : ℝ) := by
  classical
  have hnn : ∀ T, 0 ≤ w T := hw.1
  set s' := (G.cliqueFinset 3).filter (fun t => U ∈ partClass P t ∧ W ∈ partClass P t) with hs'
  -- the inner sums only ever see triangles of `s'`
  have hfib : ∑ S ∈ (P.parts.powersetCard 3).filter (fun S => U ∈ S ∧ W ∈ S),
      ∑ t ∈ (G.cliqueFinset 3).filter (fun t => partClass P t = S), w (t.powersetCard 2)
      = ∑ t ∈ s', w (t.powersetCard 2) := by
    have hcongr : ∀ S ∈ (P.parts.powersetCard 3).filter (fun S => U ∈ S ∧ W ∈ S),
        (G.cliqueFinset 3).filter (fun t => partClass P t = S)
          = s'.filter (fun t => partClass P t = S) := by
      intro S hS
      rw [Finset.mem_filter] at hS
      ext t
      simp only [hs', Finset.mem_filter]
      constructor
      · rintro ⟨ht, rfl⟩; exact ⟨⟨ht, hS.2.1, hS.2.2⟩, rfl⟩
      · rintro ⟨⟨ht, -, -⟩, hEq⟩; exact ⟨ht, hEq⟩
    rw [Finset.sum_congr rfl (fun S hS => by rw [hcongr S hS])]
    refine Finset.sum_fiberwise_of_maps_to (fun t ht => ?_) _
    rw [Finset.mem_filter]
    refine ⟨partClass_mem_powersetCard_three P (hdist t (Finset.mem_filter.mp (hs' ▸ ht)).1), ?_⟩
    exact ⟨(Finset.mem_filter.mp (hs' ▸ ht)).2.1, (Finset.mem_filter.mp (hs' ▸ ht)).2.2⟩
  rw [hfib]
  -- pass to the edge-set picture and use the packing constraint on the `U–W` edges
  set E : Finset (Finset V) :=
    (G.interedges U W).image (fun p : V × V => ({p.1, p.2} : Finset V)) with hE
  have hinj : Set.InjOn (fun t : Finset V => t.powersetCard 2) (s' : Set (Finset V)) := by
    refine (triangle_powersetCard_two_injOn G).mono ?_
    intro t ht
    exact Finset.mem_coe.mpr (Finset.mem_filter.mp (hs' ▸ Finset.mem_coe.mp ht)).1
  have himg : ∑ t ∈ s', w (t.powersetCard 2)
      = ∑ T ∈ s'.image (fun t => t.powersetCard 2), w T := (Finset.sum_image hinj).symm
  have hsub : s'.image (fun t => t.powersetCard 2)
      ⊆ (triangleHypergraphE G).filter (fun T => ∃ e ∈ E, e ∈ T) := by
    intro T hT
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hT
    have ht3 : t ∈ G.cliqueFinset 3 := (Finset.mem_filter.mp (hs' ▸ ht)).1
    have hclique : G.IsNClique 3 t := SimpleGraph.mem_cliqueFinset_iff.mp ht3
    obtain ⟨x, hxt, hxU⟩ := (mem_partClass_iff P t U).mp (Finset.mem_filter.mp (hs' ▸ ht)).2.1
    obtain ⟨y, hyt, hyW⟩ := (mem_partClass_iff P t W).mp (Finset.mem_filter.mp (hs' ▸ ht)).2.2
    have hxU' : x ∈ U := hxU ▸ P.mem_part (mem_univ x)
    have hyW' : y ∈ W := hyW ▸ P.mem_part (mem_univ y)
    have hxy : x ≠ y := by
      rintro rfl
      exact hUW (hxU ▸ hyW ▸ rfl)
    have hadj : G.Adj x y := hclique.1 hxt hyt hxy
    refine Finset.mem_filter.mpr ⟨?_, ⟨({x, y} : Finset V), ?_, ?_⟩⟩
    · exact Finset.mem_image.mpr ⟨t, ht3, rfl⟩
    · refine Finset.mem_image.mpr ⟨(x, y), ?_, rfl⟩
      rw [SimpleGraph.mem_interedges_iff]
      exact ⟨hxU', hyW', hadj⟩
    · rw [Finset.mem_powersetCard]
      refine ⟨?_, Finset.card_pair hxy⟩
      intro z hz
      rcases Finset.mem_insert.mp hz with rfl | hz'
      · exact hxt
      · rw [Finset.mem_singleton] at hz'; exact hz' ▸ hyt
  calc ∑ t ∈ s', w (t.powersetCard 2)
      = ∑ T ∈ s'.image (fun t => t.powersetCard 2), w T := himg
    _ ≤ ∑ T ∈ (triangleHypergraphE G).filter (fun T => ∃ e ∈ E, e ∈ T), w T :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun T _ _ => hnn T)
    _ ≤ (#E : ℝ) := sum_fracPacking_over_edges_le G hw E
    _ ≤ (#(G.interedges U W) : ℝ) := by
        exact_mod_cast Finset.card_image_le

end Nibble.AX1

end


/-! # CoreGapClusterHost -/

public section

open Finset SimpleGraph Hypergraph Nibble.YusterE

namespace Nibble.AX1

variable {V : Type} [Fintype V] [DecidableEq V]

/-! ### The cluster graph -/

/-- **The cluster graph** of `G` along `P` at scales `ep`, `de`: the vertices are the parts of `P`
and two distinct parts are joined when the pair is `ep`-uniform of density at least `de`. -/
@[expose]
def hostGraph (G : SimpleGraph V) [DecidableRel G.Adj] (P : Finpartition (univ : Finset V))
    (ep de : ℝ) : SimpleGraph {S : Finset V // S ∈ P.parts} where
  Adj S T := (S : Finset V) ≠ (T : Finset V) ∧ G.IsUniform ep (S : Finset V) (T : Finset V) ∧
    de ≤ (G.edgeDensity (S : Finset V) (T : Finset V) : ℝ)
  symm := ⟨by
    rintro S T ⟨h1, h2, h3⟩
    refine ⟨h1.symm, h2.symm, ?_⟩
    rwa [SimpleGraph.edgeDensity_comm]⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

noncomputable instance hostGraph.instDecidableRelAdj (G : SimpleGraph V) [DecidableRel G.Adj]
    (P : Finpartition (univ : Finset V)) (ep de : ℝ) : DecidableRel (hostGraph G P ep de).Adj :=
  Classical.decRel _

theorem hostGraph_adj {G : SimpleGraph V} [DecidableRel G.Adj]
    {P : Finpartition (univ : Finset V)} {ep de : ℝ} {S T : {S : Finset V // S ∈ P.parts}} :
    (hostGraph G P ep de).Adj S T ↔ (S : Finset V) ≠ (T : Finset V) ∧
      G.IsUniform ep (S : Finset V) (T : Finset V) ∧
      de ≤ (G.edgeDensity (S : Finset V) (T : Finset V) : ℝ) := Iff.rfl

/-- The number of vertices of the cluster graph is the number of clusters. -/
theorem card_hostGraph_vertices (P : Finpartition (univ : Finset V)) :
    Fintype.card {S : Finset V // S ∈ P.parts} = #P.parts := Fintype.card_coe _

/-- The cluster of a vertex, as a vertex of the cluster graph. -/
def clusterOf (P : Finpartition (univ : Finset V)) (v : V) : {S : Finset V // S ∈ P.parts} :=
  ⟨P.part v, P.part_mem.mpr (mem_univ v)⟩

/-- **The cluster triple of a triangle**. -/
def hostTri (P : Finpartition (univ : Finset V)) (t : Finset V) :
    Finset {S : Finset V // S ∈ P.parts} := t.image (clusterOf P)

theorem image_hostTri (P : Finpartition (univ : Finset V)) (t : Finset V) :
    (hostTri P t).image Subtype.val = partClass P t := by
  classical
  rw [hostTri, partClass, Finset.image_image]
  rfl

/-- A triangle of a regularity-reduced graph has a cluster triple that is a triangle of the cluster
graph at the same scales. -/
theorem hostTri_mem_cliqueFinset (G : SimpleGraph V) [DecidableRel G.Adj]
    (P : Finpartition (univ : Finset V)) (ep de : ℝ) {t : Finset V}
    (ht : t ∈ (G.regularityReduced P ep de).cliqueFinset 3) :
    hostTri P t ∈ (hostGraph G P ep de).cliqueFinset 3 := by
  classical
  have htc : (G.regularityReduced P ep de).IsNClique 3 t :=
    SimpleGraph.mem_cliqueFinset_iff.mp ht
  obtain ⟨x, y, z, hxy, hxz, hyz, rfl⟩ := Finset.card_eq_three.mp htc.card_eq
  have haxy : (G.regularityReduced P ep de).Adj x y := htc.1 (by simp) (by simp) hxy
  have haxz : (G.regularityReduced P ep de).Adj x z := htc.1 (by simp) (by simp) hxz
  have hayz : (G.regularityReduced P ep de).Adj y z := htc.1 (by simp) (by simp) hyz
  obtain ⟨U, W, X, hgood, hxU, hyW, hzX⟩ :=
    regularityReduced_triangle_parts G P ep de haxy haxz hayz
  obtain ⟨hUp, hWp, hXp, hUW, hUX, hWX, huUW, hdUW, huUX, hdUX, huWX, hdWX⟩ := hgood
  have h1 : P.part x = U := P.part_eq_of_mem hUp hxU
  have h2 : P.part y = W := P.part_eq_of_mem hWp hyW
  have h3 : P.part z = X := P.part_eq_of_mem hXp hzX
  have himg : hostTri P {x, y, z}
      = {(⟨U, hUp⟩ : {S : Finset V // S ∈ P.parts}), ⟨W, hWp⟩, ⟨X, hXp⟩} := by
    simp only [hostTri, Finset.image_insert, Finset.image_singleton]
    congr 1
    · exact Subtype.ext (by simp [clusterOf, h1])
    · congr 1
      · exact Subtype.ext (by simp [clusterOf, h2])
      · congr 1
        exact Subtype.ext (by simp [clusterOf, h3])
  rw [himg, SimpleGraph.mem_cliqueFinset_iff]
  refine ⟨?_, ?_⟩
  · intro a ha b hb hab
    simp only [Finset.coe_insert, Set.mem_insert_iff, Finset.coe_singleton,
      Set.mem_singleton_iff] at ha hb
    rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl <;>
      first
        | exact absurd rfl hab
        | exact ⟨hUW, huUW, hdUW⟩
        | exact ⟨hUX, huUX, hdUX⟩
        | exact ⟨hWX, huWX, hdWX⟩
        | exact ⟨hUW.symm, huUW.symm, by rwa [SimpleGraph.edgeDensity_comm]⟩
        | exact ⟨hUX.symm, huUX.symm, by rwa [SimpleGraph.edgeDensity_comm]⟩
        | exact ⟨hWX.symm, huWX.symm, by rwa [SimpleGraph.edgeDensity_comm]⟩
  · rw [Finset.card_insert_of_notMem (by simp [Subtype.ext_iff, hUW, hUX]),
      Finset.card_insert_of_notMem (by simp [Subtype.ext_iff, hWX]), Finset.card_singleton]

/-- Two clusters of the cluster triple of a triangle are joined by an edge of the triangle. -/
theorem exists_edge_of_mem_hostTri (P : Finpartition (univ : Finset V)) {t : Finset V}
    {S T : {S : Finset V // S ∈ P.parts}} (hST : S ≠ T)
    (hS : S ∈ hostTri P t) (hT : T ∈ hostTri P t) :
    ∃ x ∈ (S : Finset V), ∃ y ∈ (T : Finset V), ({x, y} : Finset V) ∈ t.powersetCard 2 := by
  classical
  rw [hostTri, Finset.mem_image] at hS hT
  obtain ⟨x, hx, hxS⟩ := hS
  obtain ⟨y, hy, hyT⟩ := hT
  have hxy : x ≠ y := by
    rintro rfl
    exact hST (hxS ▸ hyT ▸ rfl)
  refine ⟨x, ?_, y, ?_, ?_⟩
  · rw [← hxS]; exact P.mem_part (mem_univ x)
  · rw [← hyT]; exact P.mem_part (mem_univ y)
  · rw [Finset.mem_powersetCard]
    refine ⟨?_, by rw [Finset.card_insert_of_notMem (by simpa using hxy), Finset.card_singleton]⟩
    intro v hv
    simp only [Finset.mem_insert, Finset.mem_singleton] at hv
    rcases hv with rfl | rfl <;> assumption

/-! ### The aggregation -/

/-- **Aggregating the LP along the cluster triples.**  If every cluster pair of `P` carries at most
`c` edges of `G`, then the fractional triangle packing number of the regularity-reduced graph is at
most `c` times that of the cluster graph.

The aggregated weighting gives a cluster triple the total weight of the triangles lying on it,
scaled by `1/c`; the capacity constraint of a cluster pair
(`Nibble.AX1.sum_fracPacking_cluster_pair_le`) is exactly the edge constraint of the aggregate. -/
theorem nu3star_regularityReduced_le_host (G : SimpleGraph V) [DecidableRel G.Adj]
    (P : Finpartition (univ : Finset V)) (ep de : ℝ) {c : ℝ} (hc : 0 < c)
    (hcap : ∀ S ∈ P.parts, ∀ T ∈ P.parts, S ≠ T → (#(G.interedges S T) : ℝ) ≤ c) :
    nu3star (G.regularityReduced P ep de) ≤ c * nu3star (hostGraph G P ep de) := by
  classical
  set R : SimpleGraph V := G.regularityReduced P ep de with hR
  set Hst : SimpleGraph {S : Finset V // S ∈ P.parts} := hostGraph G P ep de with hHst
  refine csSup_le ⟨0, ⟨fun _ => 0, isFracPacking_zero R, by simp⟩⟩ ?_
  rintro x ⟨w, hw, rfl⟩
  -- the aggregate weighting of the cluster triples
  set val : Finset {S : Finset V // S ∈ P.parts} → ℝ := fun th =>
    (∑ t ∈ (R.cliqueFinset 3).filter (fun t => hostTri P t = th), w (t.powersetCard 2)) / c
    with hvaldef
  set wH : Finset (Finset {S : Finset V // S ∈ P.parts}) → ℝ := fun T =>
    if T ∈ triangleHypergraphE Hst then val (vtxSet T) else 0 with hwHdef
  have hval0 : ∀ th, 0 ≤ val th := fun th =>
    div_nonneg (Finset.sum_nonneg fun t _ => hw.1 _) hc.le
  -- the sum over a set of cluster triples is a sum over the triangles lying on them
  have hfiber : ∀ A : Finset (Finset {S : Finset V // S ∈ P.parts}),
      A ⊆ Hst.cliqueFinset 3 →
      ∑ th ∈ A, (∑ t ∈ (R.cliqueFinset 3).filter (fun t => hostTri P t = th),
            w (t.powersetCard 2))
        = ∑ t ∈ (R.cliqueFinset 3).filter (fun t => hostTri P t ∈ A), w (t.powersetCard 2) := by
    intro A hA
    rw [← Finset.sum_fiberwise_of_maps_to
      (g := hostTri P) (s := (R.cliqueFinset 3).filter (fun t => hostTri P t ∈ A)) (t := A)
      (fun t ht => (Finset.mem_filter.mp ht).2) (fun t => w (t.powersetCard 2))]
    refine Finset.sum_congr rfl fun th hth => ?_
    refine Finset.sum_congr ?_ fun _ _ => rfl
    ext t
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨ht, rfl⟩; exact ⟨⟨ht, hth⟩, rfl⟩
    · rintro ⟨⟨ht, -⟩, hEq⟩; exact ⟨ht, hEq⟩
  -- the capacity constraint of a cluster pair
  have hpair : ∀ Sv Tv : {S : Finset V // S ∈ P.parts}, Sv ≠ Tv →
      ∑ t ∈ (R.cliqueFinset 3).filter (fun t => Sv ∈ hostTri P t ∧ Tv ∈ hostTri P t),
        w (t.powersetCard 2) ≤ c := by
    intro Sv Tv hST
    set C := (R.cliqueFinset 3).filter (fun t => Sv ∈ hostTri P t ∧ Tv ∈ hostTri P t) with hC
    have hinj : Set.InjOn (fun t : Finset V => t.powersetCard 2) (C : Set (Finset V)) :=
      (triangle_powersetCard_two_injOn R).mono (by
        intro t ht
        exact Finset.mem_coe.mpr (Finset.mem_filter.mp (Finset.mem_coe.mp ht)).1)
    have himg : ∑ t ∈ C, w (t.powersetCard 2)
        = ∑ T ∈ C.image (fun t => t.powersetCard 2), w T := (Finset.sum_image hinj).symm
    have hsub : C.image (fun t => t.powersetCard 2)
        ⊆ (triangleHypergraphE R).filter
          (fun T => ∃ x ∈ (Sv : Finset V), ∃ y ∈ (Tv : Finset V), ({x, y} : Finset V) ∈ T) := by
      intro T hT
      obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hT
      rw [Finset.mem_filter] at ht
      rw [Finset.mem_filter]
      refine ⟨Finset.mem_image_of_mem _ ht.1, ?_⟩
      exact exists_edge_of_mem_hostTri P hST ht.2.1 ht.2.2
    have hmono : ∑ T ∈ C.image (fun t => t.powersetCard 2), w T
        ≤ ∑ T ∈ (triangleHypergraphE R).filter
            (fun T => ∃ x ∈ (Sv : Finset V), ∃ y ∈ (Tv : Finset V), ({x, y} : Finset V) ∈ T), w T :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub fun T _ _ => hw.1 T
    have hcapR := sum_fracPacking_cluster_pair_le R hw (Sv : Finset V) (Tv : Finset V)
    have hmono2 : (#(R.interedges (Sv : Finset V) (Tv : Finset V)) : ℝ)
        ≤ (#(G.interedges (Sv : Finset V) (Tv : Finset V)) : ℝ) := by
      exact_mod_cast card_interedges_mono (G := G) (H := R)
        (hR ▸ SimpleGraph.regularityReduced_le) (Sv : Finset V) (Tv : Finset V)
    have hcapG := hcap (Sv : Finset V) Sv.2 (Tv : Finset V) Tv.2 fun h => hST (Subtype.ext h)
    rw [himg]
    linarith
  -- the aggregate is a fractional packing of the cluster graph
  have hpack : IsFracPacking Hst wH := by
    refine ⟨fun T => ?_, fun T hT => ?_, fun e => ?_⟩
    · rw [hwHdef]; dsimp only; split_ifs
      · exact hval0 _
      · exact le_rfl
    · rw [hwHdef]; dsimp only; rw [ite_eq_right hT]
    · by_cases he2 : #e = 2
      swap
      · have hemp : (triangleHypergraphE Hst).filter (fun T => e ∈ T) = ∅ := by
          ext T
          simp only [Finset.mem_filter, Finset.notMem_empty, iff_false, not_and]
          intro hT heT
          rw [triangleHypergraphE, Finset.mem_image] at hT
          obtain ⟨th, hth, rfl⟩ := hT
          rw [Finset.mem_powersetCard] at heT
          exact he2 heT.2
        rw [hemp, Finset.sum_empty]; norm_num
      obtain ⟨Sv, Tv, hST, rfl⟩ := Finset.card_eq_two.mp he2
      rw [sum_triangleHypergraphE_filter Hst he2 wH]
      have hstep : ∀ th ∈ (Hst.cliqueFinset 3).filter
          (fun th => ({Sv, Tv} : Finset {S : Finset V // S ∈ P.parts}) ⊆ th),
          wH (th.powersetCard 2) = val th := by
        intro th hth
        rw [Finset.mem_filter, SimpleGraph.mem_cliqueFinset_iff] at hth
        have hmem : th.powersetCard 2 ∈ triangleHypergraphE Hst := by
          rw [triangleHypergraphE, Finset.mem_image]
          exact ⟨th, SimpleGraph.mem_cliqueFinset_iff.mpr hth.1, rfl⟩
        rw [hwHdef]
        dsimp only
        rw [ite_eq_left hmem, vtxSet_powersetCard_two (by rw [hth.1.card_eq]; norm_num)]
      rw [Finset.sum_congr rfl hstep]
      have hAsub : (Hst.cliqueFinset 3).filter
          (fun th => ({Sv, Tv} : Finset {S : Finset V // S ∈ P.parts}) ⊆ th)
          ⊆ Hst.cliqueFinset 3 := Finset.filter_subset _ _
      have hsum : ∑ th ∈ (Hst.cliqueFinset 3).filter
            (fun th => ({Sv, Tv} : Finset {S : Finset V // S ∈ P.parts}) ⊆ th), val th
          = (∑ t ∈ (R.cliqueFinset 3).filter (fun t => hostTri P t ∈
              (Hst.cliqueFinset 3).filter
                (fun th => ({Sv, Tv} : Finset {S : Finset V // S ∈ P.parts}) ⊆ th)),
              w (t.powersetCard 2)) / c := by
        rw [← hfiber _ hAsub, hvaldef, ← Finset.sum_div]
      rw [hsum, div_le_one hc]
      refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun t _ _ => hw.1 _))
        (hpair Sv Tv hST)
      intro t ht
      rw [Finset.mem_filter] at ht ⊢
      refine ⟨ht.1, ?_, ?_⟩
      · exact (Finset.mem_filter.mp ht.2).2 (by simp)
      · exact (Finset.mem_filter.mp ht.2).2 (by simp)
  -- the value of the aggregate
  have htot : ∑ T ∈ triangleHypergraphE Hst, wH T
      = (∑ T ∈ triangleHypergraphE R, w T) / c := by
    rw [sum_triangleHypergraphE Hst wH, sum_triangleHypergraphE R w]
    have hstep : ∀ th ∈ Hst.cliqueFinset 3, wH (th.powersetCard 2) = val th := by
      intro th hth
      rw [SimpleGraph.mem_cliqueFinset_iff] at hth
      have hmem : th.powersetCard 2 ∈ triangleHypergraphE Hst := by
        rw [triangleHypergraphE, Finset.mem_image]
        exact ⟨th, SimpleGraph.mem_cliqueFinset_iff.mpr hth, rfl⟩
      rw [hwHdef]
      dsimp only
      rw [ite_eq_left hmem, vtxSet_powersetCard_two (by rw [hth.card_eq]; norm_num)]
    rw [Finset.sum_congr rfl hstep, hvaldef, ← Finset.sum_div]
    congr 1
    rw [hfiber (Hst.cliqueFinset 3) (Finset.Subset.refl _)]
    refine Finset.sum_congr ?_ fun _ _ => rfl
    refine Finset.filter_true_of_mem fun t ht => ?_
    exact hostTri_mem_cliqueFinset G P ep de ht
  have hle : ∑ T ∈ triangleHypergraphE Hst, wH T ≤ nu3star Hst :=
    le_csSup (nu3star_bddAbove Hst) ⟨wH, hpack, rfl⟩
  rw [htot, div_le_iff₀ hc] at hle
  linarith only [hle]

/-! ### Axiom check -/

section AxCheck




end AxCheck

end Nibble.AX1
