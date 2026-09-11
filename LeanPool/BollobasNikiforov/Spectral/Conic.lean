/-
Copyright (c) 2026 Shengtong Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shengtong Zhang
-/

import LeanPool.BollobasNikiforov.Basic.Graph
import LeanPool.BollobasNikiforov.Basic.Inner
import LeanPool.BollobasNikiforov.Spectral.Gram
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Combinatorics.SimpleGraph.AdjMatrix
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Topology.Instances.Matrix
import Mathlib.Topology.Order.Compact

/-!
# The rank-two conic parameter `χ''_{vec,3}`

`chiVec3 G` is the supremum of the Frobenius mass `inner X X` over PSD matrices
of rank at most two, nonnegative on the edges of `G`, and normalized so that
the mass of `X ⊙ X` off those edges equals `1`. The feasible set is nonempty
and compact, so the supremum is attained.
-/

namespace BollobasNikiforov

open Matrix Set Submodule
open scoped Matrix

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]


/-- The all-ones matrix `J`. -/
def onesMatrix : Matrix V V ℝ :=
  of fun _ _ => 1

/-- Off-edge indicator `I + A_{Gᶜ} = J - A_G`. Equals `1` on the diagonal and
on non-edges of `G`, and `0` on edges. -/
def offEdgeMatrix (G : SimpleGraph V) [DecidableRel G.Adj] : Matrix V V ℝ :=
  1 + Gᶜ.adjMatrix ℝ

omit [Fintype V] [DecidableEq V] in
lemma onesMatrix_apply (i j : V) : onesMatrix i j = 1 :=
  rfl

omit [Fintype V] in
lemma offEdgeMatrix_apply (i j : V) :
    offEdgeMatrix G i j = if G.Adj i j then (0 : ℝ) else 1 := by
  simp [offEdgeMatrix, Matrix.one_apply, SimpleGraph.adjMatrix_apply, SimpleGraph.compl_adj]
  by_cases hij : G.Adj i j
  · have hne : i ≠ j := G.ne_of_adj hij
    simp [hne]
  · by_cases hii : i = j
    · simp [hii]
    · simp [hii]

omit [DecidableEq V] in
lemma inner_onesMatrix_hadamard_self (X : Matrix V V ℝ) :
    inner (onesMatrix (V := V)) (X ⊙ X) = inner X X := by
  simp [inner_eq_sum, onesMatrix_apply, hadamard_apply]

lemma inner_offEdgeMatrix_hadamard_self (X : Matrix V V ℝ) :
    inner (offEdgeMatrix G) (X ⊙ X) =
      ∑ i, ∑ j, if G.Adj i j then (0 : ℝ) else X i j ^ 2 := by
  simp [inner_eq_sum, offEdgeMatrix_apply, hadamard_apply, pow_two]

/-- The mass on the diagonal is at most the off-edge normalization. -/
lemma sum_diag_sq_le_inner_offEdgeMatrix (X : Matrix V V ℝ) :
    ∑ i, X i i ^ 2 ≤ inner (offEdgeMatrix G) (X ⊙ X) := by
  rw [inner_offEdgeMatrix_hadamard_self]
  refine Finset.sum_le_sum fun i _ => ?_
  have hterm (j : V) : 0 ≤ (if G.Adj i j then (0 : ℝ) else X i j ^ 2) := by
    split_ifs <;> simp [sq_nonneg]
  have heq : X i i ^ 2 = if G.Adj i i then (0 : ℝ) else X i i ^ 2 :=
    (ite_eq_right G.irrefl).symm
  rw [heq]
  exact Finset.single_le_sum (fun j _ => hterm j) (Finset.mem_univ i)

/-! ### CG06 — feasible set and the parameter -/

/-- Feasible matrices for `χ''_{vec,3}`. -/
def ChiVec3Feasible (G : SimpleGraph V) [DecidableRel G.Adj] (X : Matrix V V ℝ) : Prop :=
  X.PosSemidef ∧ X.rank ≤ 2 ∧
    inner (offEdgeMatrix G) (X ⊙ X) = 1 ∧
    ∀ i j, G.Adj i j → 0 ≤ X i j

/-- **CG06.** The parameter `χ''_{vec,3}(G)`. -/
noncomputable def chiVec3 (G : SimpleGraph V) [DecidableRel G.Adj] : ℝ :=
  sSup ((fun X : Matrix V V ℝ => inner X X) '' {X | ChiVec3Feasible G X})

/-! ### Rank-two writing -/

omit [DecidableEq V] [Fintype V] in
variable [Finite V] in
lemma posSemidef_add_vecMulVec (u v : V → ℝ) :
    (vecMulVec u u + vecMulVec v v).PosSemidef :=
  ((posSemidef_vecMulVec_self_star (R := ℝ) u).add
    (posSemidef_vecMulVec_self_star (R := ℝ) v))

omit [DecidableEq V] in
lemma rank_add_vecMulVec_le (u v : V → ℝ) :
    (vecMulVec u u + vecMulVec v v).rank ≤ 2 := by
  rw [rank_eq_finrank_span_cols]
  let W := span ℝ ({u, v} : Set (V → ℝ))
  have hle : span ℝ (range (vecMulVec u u + vecMulVec v v).col) ≤ W := by
    refine span_le.mpr ?_
    intro x hx
    obtain ⟨j, rfl⟩ := mem_range.mp hx
    have hcol : (vecMulVec u u + vecMulVec v v).col j = u j • u + v j • v := by
      ext i
      simp [col_apply, vecMulVec_apply, smul_eq_mul]
      ring
    rw [hcol]
    exact W.add_mem (W.smul_mem _ (subset_span (by simp)))
      (W.smul_mem _ (subset_span (by simp : v ∈ ({u, v} : Set _))))
  refine (finrank_mono hle).trans ?_
  refine (finrank_span_le_card (R := ℝ) ({u, v} : Set (V → ℝ))).trans ?_
  have : ({u, v} : Set (V → ℝ)).toFinset.card ≤ 2 := by
    rw [Set.toFinset_insert, Set.toFinset_singleton]
    exact (Finset.card_insert_le _ _).trans (by simp)
  exact this

omit [DecidableEq V] in
/-- A real PSD matrix of rank at most two is a sum of two real outer products. -/
lemma exists_add_vecMulVec_of_posSemidef_rank_le_two
    {X : Matrix V V ℝ} (hX : X.PosSemidef) (hr : X.rank ≤ 2) :
    ∃ u v : V → ℝ, X = vecMulVec u u + vecMulVec v v := by
  classical
  let hA := hX.isHermitian
  let scaled (k : V) : V → ℝ :=
    Real.sqrt (hA.eigenvalues k) • (hA.eigenvectorBasis k : V → ℝ)
  have hdecomp : X = ∑ k, vecMulVec (scaled k) (scaled k) := by
    have hx : X = ∑ k, hA.eigenvalues k •
        vecMulVec (hA.eigenvectorBasis k : V → ℝ)
          (hA.eigenvectorBasis k : V → ℝ) := by
      simpa [IsHermitian.eigenvectorUnitary_col_eq] using
        isHermitian_eq_sum_smul_vecMulVec hA
    refine hx.trans (Finset.sum_congr rfl fun k _ => ?_)
    have hlam : 0 ≤ hA.eigenvalues k := hX.eigenvalues_nonneg k
    ext i j
    simp only [scaled, vecMulVec_apply, Pi.smul_apply, smul_eq_mul, Matrix.smul_apply]
    rw [mul_mul_mul_comm, Real.mul_self_sqrt hlam]
  let s := Finset.univ.filter fun k => hA.eigenvalues k ≠ 0
  have hsum : X = ∑ k ∈ s, vecMulVec (scaled k) (scaled k) := by
    rw [hdecomp]
    refine (Finset.sum_subset (Finset.filter_subset _ _) ?_).symm
    intro k _ hk
    have hlam : hA.eigenvalues k = 0 := by simpa [s, Finset.mem_filter] using hk
    have : scaled k = 0 := by simp [scaled, hlam, Real.sqrt_zero]
    simp [this]
  have hcard : s.card ≤ 2 := by
    have : s.card = Fintype.card {k // hA.eigenvalues k ≠ 0} :=
      (Fintype.card_subtype _).symm
    rwa [this, ← hA.rank_eq_card_non_zero_eigs]
  have hc : s.card = 0 ∨ s.card = 1 ∨ s.card = 2 := by omega
  rw [hsum]
  rcases hc with hc | hc | hc
  · refine ⟨0, 0, ?_⟩
    simp [Finset.card_eq_zero.mp hc]
  · obtain ⟨a, ha⟩ := Finset.card_eq_one.mp hc
    refine ⟨scaled a, 0, ?_⟩
    simp [ha]
  · obtain ⟨a, b, hab, hs⟩ := Finset.card_eq_two.mp hc
    refine ⟨scaled a, scaled b, ?_⟩
    simp [hs, Finset.sum_pair hab]

/-! ### CG07 — nonempty compact feasible set -/

/-- Parameter domain for the rank-two writing: bounded outer-product data
satisfying the normalization and edge-nonnegativity constraints. -/
def chiVec3Param (G : SimpleGraph V) [DecidableRel G.Adj] :
    Set ((V → ℝ) × (V → ℝ)) :=
  {p | (∀ i, p.1 i ∈ Icc (-1 : ℝ) 1) ∧ (∀ i, p.2 i ∈ Icc (-1 : ℝ) 1) ∧
    inner (offEdgeMatrix G)
        ((vecMulVec p.1 p.1 + vecMulVec p.2 p.2) ⊙
          (vecMulVec p.1 p.1 + vecMulVec p.2 p.2)) = 1 ∧
    ∀ i j, G.Adj i j → 0 ≤ (vecMulVec p.1 p.1 + vecMulVec p.2 p.2) i j}

omit [Fintype V] [DecidableEq V] in
lemma continuous_add_vecMulVec :
    Continuous fun p : (V → ℝ) × (V → ℝ) =>
      vecMulVec p.1 p.1 + vecMulVec p.2 p.2 :=
  (continuous_id.matrix_vecMulVec continuous_id).comp continuous_fst |>.add <|
    (continuous_id.matrix_vecMulVec continuous_id).comp continuous_snd

omit [DecidableEq V] in
lemma continuous_inner_self : Continuous fun X : Matrix V V ℝ => inner X X := by
  simp_rw [inner_self]
  exact continuous_finsetSum _ fun i _ =>
    continuous_finsetSum _ fun j _ => (continuous_apply_apply i j).pow 2

lemma continuous_inner_offEdge_hadamard :
    Continuous fun X : Matrix V V ℝ => inner (offEdgeMatrix G) (X ⊙ X) := by
  simp_rw [inner_offEdgeMatrix_hadamard_self]
  exact continuous_finsetSum _ fun i _ =>
    continuous_finsetSum _ fun j _ => by
      split_ifs
      · exact continuous_const
      · exact (continuous_apply_apply i j).pow 2

omit [Fintype V] [DecidableEq V] in
lemma mem_pi_Icc_iff {u : V → ℝ} :
    u ∈ univ.pi (fun _ : V => Icc (-1 : ℝ) 1) ↔ ∀ i, u i ∈ Icc (-1 : ℝ) 1 :=
  ⟨fun h i => h i (mem_univ i), fun h i _ => h i⟩

lemma isClosed_chiVec3Param : IsClosed (chiVec3Param G) := by
  have hbox1 : IsClosed {p : (V → ℝ) × (V → ℝ) | ∀ i, p.1 i ∈ Icc (-1 : ℝ) 1} := by
    have : {p : (V → ℝ) × (V → ℝ) | ∀ i, p.1 i ∈ Icc (-1 : ℝ) 1} =
        Prod.fst ⁻¹' univ.pi fun _ => Icc (-1 : ℝ) 1 := by
      ext p
      exact (mem_pi_Icc_iff (u := p.1)).symm
    rw [this]
    exact (isClosed_set_pi fun _ _ => isClosed_Icc).preimage continuous_fst
  have hbox2 : IsClosed {p : (V → ℝ) × (V → ℝ) | ∀ i, p.2 i ∈ Icc (-1 : ℝ) 1} := by
    have : {p : (V → ℝ) × (V → ℝ) | ∀ i, p.2 i ∈ Icc (-1 : ℝ) 1} =
        Prod.snd ⁻¹' univ.pi fun _ => Icc (-1 : ℝ) 1 := by
      ext p
      exact (mem_pi_Icc_iff (u := p.2)).symm
    rw [this]
    exact (isClosed_set_pi fun _ _ => isClosed_Icc).preimage continuous_snd
  have hnorm : IsClosed {p : (V → ℝ) × (V → ℝ) |
      inner (offEdgeMatrix G)
          ((vecMulVec p.1 p.1 + vecMulVec p.2 p.2) ⊙
            (vecMulVec p.1 p.1 + vecMulVec p.2 p.2)) = 1} :=
    isClosed_eq (continuous_inner_offEdge_hadamard.comp continuous_add_vecMulVec)
      continuous_const
  have hnn : IsClosed {p : (V → ℝ) × (V → ℝ) |
      ∀ i j, G.Adj i j → 0 ≤ (vecMulVec p.1 p.1 + vecMulVec p.2 p.2) i j} := by
    have heq : {p : (V → ℝ) × (V → ℝ) |
        ∀ i j, G.Adj i j → 0 ≤ (vecMulVec p.1 p.1 + vecMulVec p.2 p.2) i j} =
        ⋂ i, ⋂ j, {p | G.Adj i j → 0 ≤ (vecMulVec p.1 p.1 + vecMulVec p.2 p.2) i j} := by
      ext p
      simp
    rw [heq]
    refine isClosed_iInter fun i => isClosed_iInter fun j => ?_
    by_cases hij : G.Adj i j
    · simpa [hij] using
        (isClosed_le continuous_const (continuous_add_vecMulVec.matrix_elem i j))
    · simp [hij]
  have : chiVec3Param G =
      {p | ∀ i, p.1 i ∈ Icc (-1 : ℝ) 1} ∩ {p | ∀ i, p.2 i ∈ Icc (-1 : ℝ) 1} ∩
        {p | inner (offEdgeMatrix G)
            ((vecMulVec p.1 p.1 + vecMulVec p.2 p.2) ⊙
              (vecMulVec p.1 p.1 + vecMulVec p.2 p.2)) = 1} ∩
        {p | ∀ i j, G.Adj i j → 0 ≤ (vecMulVec p.1 p.1 + vecMulVec p.2 p.2) i j} := by
    ext p
    simp [chiVec3Param, and_assoc]
  rw [this]
  exact ((hbox1.inter hbox2).inter hnorm).inter hnn

lemma isCompact_chiVec3Param : IsCompact (chiVec3Param G) := by
  have hbox : IsCompact
      {p : (V → ℝ) × (V → ℝ) |
        (∀ i, p.1 i ∈ Icc (-1 : ℝ) 1) ∧ ∀ i, p.2 i ∈ Icc (-1 : ℝ) 1} := by
    have hi : IsCompact (univ.pi fun _ : V => Icc (-1 : ℝ) 1) :=
      isCompact_univ_pi fun _ => isCompact_Icc
    have : {p : (V → ℝ) × (V → ℝ) |
        (∀ i, p.1 i ∈ Icc (-1 : ℝ) 1) ∧ ∀ i, p.2 i ∈ Icc (-1 : ℝ) 1} =
        (univ.pi fun _ : V => Icc (-1 : ℝ) 1) ×ˢ
          (univ.pi fun _ : V => Icc (-1 : ℝ) 1) := by
      ext p
      exact ⟨fun h => ⟨mem_pi_Icc_iff.2 h.1, mem_pi_Icc_iff.2 h.2⟩,
        fun h => ⟨mem_pi_Icc_iff.1 h.1, mem_pi_Icc_iff.1 h.2⟩⟩
    rw [this]
    exact hi.prod hi
  refine hbox.of_isClosed_subset isClosed_chiVec3Param ?_
  intro p hp
  exact ⟨hp.1, hp.2.1⟩

lemma mem_chiVec3Param_of_add_vecMulVec {X : Matrix V V ℝ} {u v : V → ℝ}
    (hX : X = vecMulVec u u + vecMulVec v v)
    (hnorm : inner (offEdgeMatrix G) (X ⊙ X) = 1)
    (hnn : ∀ i j, G.Adj i j → 0 ≤ X i j) :
    (u, v) ∈ chiVec3Param G := by
  have hdiag (i : V) : X i i = u i ^ 2 + v i ^ 2 := by
    simp [hX, vecMulVec_apply, pow_two]
  have hsum : ∑ i, X i i ^ 2 ≤ 1 := by
    simpa [hnorm] using sum_diag_sq_le_inner_offEdgeMatrix (G := G) X
  have hbound (w : V → ℝ) (hw : ∀ i, w i ^ 2 ≤ X i i) (i : V) :
      w i ∈ Icc (-1 : ℝ) 1 := by
    have hXii : 0 ≤ X i i := by
      rw [hdiag]
      exact add_nonneg (sq_nonneg _) (sq_nonneg _)
    have hXle : X i i ≤ 1 := by
      have : X i i ^ 2 ≤ 1 :=
        (Finset.single_le_sum (fun j _ => sq_nonneg (X j j)) (Finset.mem_univ i)).trans hsum
      exact (sq_le_one_iff₀ hXii).1 this
    have : w i ^ 2 ≤ 1 := (hw i).trans hXle
    exact abs_le.mp ((sq_le_one_iff_abs_le_one (w i)).1 this)
  refine ⟨fun i => hbound u (fun i => by rw [hdiag]; linarith [sq_nonneg (v i)]) i,
    fun i => hbound v (fun i => by rw [hdiag]; linarith [sq_nonneg (u i)]) i, ?_, ?_⟩
  · simpa [hX] using hnorm
  · simpa [hX] using hnn

lemma ChiVec3Feasible.mem_image_param {X : Matrix V V ℝ}
    (hX : ChiVec3Feasible G X) :
    X ∈ (fun p : (V → ℝ) × (V → ℝ) => vecMulVec p.1 p.1 + vecMulVec p.2 p.2) ''
      chiVec3Param G := by
  obtain ⟨u, v, rfl⟩ :=
    exists_add_vecMulVec_of_posSemidef_rank_le_two hX.1 hX.2.1
  exact ⟨(u, v), mem_chiVec3Param_of_add_vecMulVec rfl hX.2.2.1 hX.2.2.2, rfl⟩

lemma ChiVec3Feasible.of_mem_image_param {X : Matrix V V ℝ}
    (hX : X ∈ (fun p : (V → ℝ) × (V → ℝ) => vecMulVec p.1 p.1 + vecMulVec p.2 p.2) ''
      chiVec3Param G) :
    ChiVec3Feasible G X := by
  obtain ⟨⟨u, v⟩, hp, rfl⟩ := hX
  refine ⟨posSemidef_add_vecMulVec u v, rank_add_vecMulVec_le u v, hp.2.2.1, hp.2.2.2⟩

lemma chiVec3FeasibleSet_eq_image :
    {X : Matrix V V ℝ | ChiVec3Feasible G X} =
      (fun p : (V → ℝ) × (V → ℝ) => vecMulVec p.1 p.1 + vecMulVec p.2 p.2) ''
        chiVec3Param G := by
  ext X
  exact ⟨ChiVec3Feasible.mem_image_param, ChiVec3Feasible.of_mem_image_param⟩

/-- **CG07.** A standard-basis rank-one matrix is feasible after the
normalization (already equal to `1`). -/
lemma chiVec3Feasible_single [Nonempty V] :
    ChiVec3Feasible G
      (vecMulVec (Pi.single (Classical.arbitrary V) (1 : ℝ))
        (Pi.single (Classical.arbitrary V) 1)) := by
  set i0 : V := Classical.arbitrary V
  set u : V → ℝ := Pi.single i0 1
  set X := vecMulVec u u
  have hpsd : X.PosSemidef := by
    simpa [X] using posSemidef_vecMulVec_self_star (R := ℝ) u
  have hrank : X.rank ≤ 2 :=
    (rank_vecMulVec_le u u).trans (by norm_num)
  have hnorm : inner (offEdgeMatrix G) (X ⊙ X) = 1 := by
    rw [inner_offEdgeMatrix_hadamard_self]
    have hsq (i j : V) : X i j ^ 2 = if i = i0 ∧ j = i0 then (1 : ℝ) else 0 := by
      simp [X, u, vecMulVec_apply, Pi.single_apply]
      split_ifs <;> simp_all
    simp_rw [hsq]
    rw [Finset.sum_eq_single i0]
    · rw [Finset.sum_eq_single i0]
      · rw [ite_eq_right G.irrefl]
        norm_num
      · intro j _ hj
        simp [hj]
      · simp
    · intro i _ hi
      refine Finset.sum_eq_zero fun j _ => ?_
      simp [hi]
    · simp
  have hnn : ∀ i j, G.Adj i j → 0 ≤ X i j := by
    intro i j hij
    have hne : i ≠ j := G.ne_of_adj hij
    simp [X, u, vecMulVec_apply, Pi.single_apply]
    split_ifs <;> simp_all
  exact ⟨hpsd, hrank, hnorm, hnn⟩

lemma chiVec3FeasibleSet_nonempty [Nonempty V] :
    ({X : Matrix V V ℝ | ChiVec3Feasible G X}).Nonempty :=
  ⟨_, chiVec3Feasible_single (G := G)⟩

/-- **CG07.** The feasible set is compact. -/
lemma isCompact_chiVec3FeasibleSet : IsCompact {X : Matrix V V ℝ | ChiVec3Feasible G X} := by
  rw [chiVec3FeasibleSet_eq_image]
  exact isCompact_chiVec3Param.image continuous_add_vecMulVec

lemma bddAbove_image_inner_chiVec3 :
    BddAbove ((fun X : Matrix V V ℝ => inner X X) '' {X | ChiVec3Feasible G X}) :=
  isCompact_chiVec3FeasibleSet.image continuous_inner_self |>.bddAbove

/-- **CG07.** The Frobenius objective attains its maximum on the feasible set. -/
lemma exists_isMaxOn_inner_chiVec3 [Nonempty V] :
    ∃ X, ChiVec3Feasible G X ∧
      IsMaxOn (fun X : Matrix V V ℝ => inner X X) {X | ChiVec3Feasible G X} X := by
  obtain ⟨X, hX, hmax⟩ :=
    isCompact_chiVec3FeasibleSet.exists_isMaxOn (chiVec3FeasibleSet_nonempty (G := G))
      continuous_inner_self.continuousOn
  exact ⟨X, hX, hmax⟩

/-! ### CG09 — clique Gram matrix -/

/-- Indicator of a vertex set. -/
def cliqueIndicator (s : Finset V) : V → ℝ :=
  fun i => if i ∈ s then 1 else 0

/-- Normalized rank-one Gram matrix of a clique: `qqᵀ / √r`. -/
noncomputable def cliqueGram (s : Finset V) : Matrix V V ℝ :=
  (1 / Real.sqrt s.card) • vecMulVec (cliqueIndicator s) (cliqueIndicator s)

omit [Fintype V] in
lemma cliqueIndicator_apply (s : Finset V) (i : V) :
    cliqueIndicator s i = if i ∈ s then (1 : ℝ) else 0 :=
  rfl

omit [Fintype V] in
lemma cliqueGram_apply (s : Finset V) (i j : V) :
    cliqueGram s i j =
      if i ∈ s ∧ j ∈ s then 1 / Real.sqrt s.card else 0 := by
  simp only [cliqueGram, cliqueIndicator, vecMulVec_apply, Matrix.smul_apply, smul_eq_mul]
  split_ifs <;> simp_all

omit [Fintype V] in
lemma cliqueGram_sq_apply {s : Finset V} (hs : s.Nonempty) (i j : V) :
    cliqueGram s i j ^ 2 = if i ∈ s ∧ j ∈ s then (1 : ℝ) / s.card else 0 := by
  have hr : (0 : ℝ) < s.card := Nat.cast_pos.mpr (Finset.card_pos.mpr hs)
  have hsq : (1 / Real.sqrt s.card) ^ 2 = (1 : ℝ) / s.card := by
    rw [div_pow, one_pow, Real.sq_sqrt hr.le]
  simp only [cliqueGram_apply]
  split_ifs
  · exact hsq
  · simp

omit [DecidableEq V] in
lemma rank_smul_le (c : ℝ) (A : Matrix V V ℝ) : (c • A).rank ≤ A.rank := by
  classical
  rw [smul_eq_diagonal_mul]
  exact rank_mul_le_right _ _

/-- **CG09.** Off-edge mass of the clique Gram matrix is `1`. -/
lemma inner_offEdge_cliqueGram {s : Finset V} (hs : G.IsClique (s : Set V))
    (hne : s.Nonempty) :
    inner (offEdgeMatrix G) (cliqueGram s ⊙ cliqueGram s) = 1 := by
  have hr : (0 : ℝ) < s.card := Nat.cast_pos.mpr (Finset.card_pos.mpr hne)
  rw [inner_offEdgeMatrix_hadamard_self]
  have hterm (i j : V) :
      (if G.Adj i j then (0 : ℝ) else cliqueGram s i j ^ 2) =
        if i = j ∧ i ∈ s then (1 : ℝ) / s.card else 0 := by
    rw [cliqueGram_sq_apply hne]
    by_cases hij : G.Adj i j
    · have hneij : i ≠ j := G.ne_of_adj hij
      simp [hij, hneij]
    · by_cases hii : i = j
      · subst hii
        simp
      · have hnot : ¬ (i ∈ s ∧ j ∈ s) := by
          intro ⟨hi, hj⟩
          exact hij (hs hi hj hii)
        simp [hii, hnot]
  simp_rw [hterm]
  have hsum : ∑ i, (if i ∈ s then (1 : ℝ) / s.card else 0) = 1 := by
    rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, nsmul_eq_mul,
      mul_div_cancel₀ _ hr.ne']
  calc
    ∑ i, ∑ j, (if i = j ∧ i ∈ s then (1 : ℝ) / s.card else 0)
        = ∑ i, (if i ∈ s then (1 : ℝ) / s.card else 0) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [Finset.sum_eq_single i]
          · simp
          · intro j _ hji
            simp [hji.symm]
          · simp
    _ = 1 := hsum

/-- **CG09.** The clique Gram matrix is feasible. -/
lemma chiVec3Feasible_cliqueGram {s : Finset V} (hs : G.IsClique (s : Set V))
    (hne : s.Nonempty) :
    ChiVec3Feasible G (cliqueGram s) := by
  refine ⟨?_, ?_, inner_offEdge_cliqueGram hs hne, ?_⟩
  · exact (posSemidef_vecMulVec_self_star (R := ℝ) (cliqueIndicator s)).smul
      (div_nonneg zero_le_one (Real.sqrt_nonneg _))
  · exact (rank_smul_le _ _).trans ((rank_vecMulVec_le _ _).trans (by norm_num))
  · intro i j _hij
    simp only [cliqueGram_apply]
    split_ifs
    · exact div_nonneg zero_le_one (Real.sqrt_nonneg _)
    · exact le_rfl

/-- **CG09.** The clique Gram matrix has Frobenius mass `s.card`. -/
lemma inner_cliqueGram {s : Finset V} (hne : s.Nonempty) :
    inner (cliqueGram s) (cliqueGram s) = s.card := by
  have hr : (0 : ℝ) < s.card := Nat.cast_pos.mpr (Finset.card_pos.mpr hne)
  rw [inner_self]
  simp_rw [cliqueGram_sq_apply hne]
  have hinter (i : V) :
      ∑ j, (if i ∈ s ∧ j ∈ s then (1 : ℝ) / s.card else 0) =
        if i ∈ s then (1 : ℝ) else 0 := by
    by_cases hi : i ∈ s
    · simp only [hi, true_and]
      rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, nsmul_eq_mul]
      exact mul_div_cancel₀ _ hr.ne'
    · simp [hi]
  simp_rw [hinter]
  rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, nsmul_eq_mul, mul_one]

/-- A maximum clique witnesses `ω(G) ≤ χ''_{vec,3}(G)`. -/
lemma cliqueNum_le_chiVec3 [Nonempty V] :
    (G.cliqueNum : ℝ) ≤ chiVec3 G := by
  obtain ⟨s, hs⟩ := G.exists_isNClique_cliqueNum
  have hne : s.Nonempty := by
    have : 1 ≤ s.card := by
      rw [hs.card_eq]
      exact SimpleGraph.one_le_cliqueNum G
    exact Finset.one_le_card.mp this
  have hmem : inner (cliqueGram s) (cliqueGram s) ∈
      (fun X : Matrix V V ℝ => inner X X) '' {X | ChiVec3Feasible G X} :=
    ⟨cliqueGram s, chiVec3Feasible_cliqueGram hs.isClique hne, rfl⟩
  have hle : inner (cliqueGram s) (cliqueGram s) ≤ chiVec3 G :=
    le_csSup bddAbove_image_inner_chiVec3 hmem
  rwa [inner_cliqueGram hne, hs.card_eq] at hle

/-! ### CG08 — upper bound `chiVec3 ≤ cliqueNum` -/

omit [Fintype V] in
lemma onesMatrix_eq_adjMatrix_add_offEdgeMatrix :
    onesMatrix (V := V) = G.adjMatrix ℝ + offEdgeMatrix G := by
  ext i j
  simp [onesMatrix_apply, offEdgeMatrix_apply, SimpleGraph.adjMatrix_apply]
  split_ifs <;> simp

omit [DecidableEq V] in
lemma inner_adjMatrix_hadamard_self_eq_sum_posPart_sq {X : Matrix V V ℝ}
    (hnn : ∀ i j, G.Adj i j → 0 ≤ X i j) :
    inner (G.adjMatrix ℝ) (X ⊙ X) =
      ∑ i, ∑ j, G.adjMatrix ℝ i j * (posPart X i j) ^ 2 := by
  rw [inner_eq_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  simp only [hadamard_apply, SimpleGraph.adjMatrix_apply]
  by_cases hij : G.Adj i j
  · rw [ite_eq_left hij, posPart_eq_of_nonneg X (hnn i j hij), pow_two]
  · rw [ite_eq_right hij, zero_mul, zero_mul]

omit [DecidableEq V] in
lemma inner_adjMatrix_hadamard_self_nonneg (X : Matrix V V ℝ) :
    0 ≤ inner (G.adjMatrix ℝ) (X ⊙ X) := by
  rw [inner_eq_sum]
  refine Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => ?_
  simp only [hadamard_apply, SimpleGraph.adjMatrix_apply]
  split_ifs <;> simp [mul_self_nonneg]

lemma inner_adjMatrix_hadamard_le_turanFactor {X : Matrix V V ℝ}
    (hX : ChiVec3Feasible G X) :
    inner (G.adjMatrix ℝ) (X ⊙ X) ≤ turanFactor G * inner X X := by
  rw [inner_adjMatrix_hadamard_self_eq_sum_posPart_sq hX.2.2.2]
  exact gram_le (G := G) hX.1 hX.2.1

lemma inner_self_eq_inner_adjMatrix_hadamard_add_one {X : Matrix V V ℝ}
    (hX : ChiVec3Feasible G X) :
    inner X X = inner (G.adjMatrix ℝ) (X ⊙ X) + 1 := by
  rw [← inner_onesMatrix_hadamard_self, onesMatrix_eq_adjMatrix_add_offEdgeMatrix (G := G),
    inner_add_left, hX.2.2.1]

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
lemma one_sub_turanFactor :
    1 - turanFactor G = 1 / (G.cliqueNum : ℝ) := by
  simp [turanFactor]

/-- A feasible matrix has Frobenius mass at most `ω(G)`. -/
lemma inner_le_cliqueNum_of_chiVec3Feasible [Nonempty V] {X : Matrix V V ℝ}
    (hX : ChiVec3Feasible G X) :
    inner X X ≤ G.cliqueNum := by
  have hgram := inner_adjMatrix_hadamard_le_turanFactor hX
  have hdecomp := inner_self_eq_inner_adjMatrix_hadamard_add_one hX
  have hA := inner_adjMatrix_hadamard_self_nonneg (G := G) X
  have hω : (1 : ℝ) ≤ G.cliqueNum := by exact_mod_cast SimpleGraph.one_le_cliqueNum G
  by_cases hcl : G.cliqueNum = 1
  · have ht : turanFactor G = 0 := by
      rw [turanFactor, hcl]
      norm_num
    have hA0 : inner (G.adjMatrix ℝ) (X ⊙ X) = 0 :=
      le_antisymm (by simpa [ht] using hgram) hA
    have : inner X X = 1 := by linarith
    rw [this, hcl]
    norm_num
  · have hrearr : inner X X * (1 - turanFactor G) ≤ 1 := by
      rw [mul_sub, mul_one]
      linarith
    rw [one_sub_turanFactor (G := G), mul_one_div] at hrearr
    have hωpos : (0 : ℝ) < G.cliqueNum := lt_of_lt_of_le zero_lt_one hω
    exact (div_le_one hωpos).mp hrearr

/-- **CG08.** Every feasible objective is `≤ ω(G)`, so the supremum is too. -/
lemma chiVec3_le_cliqueNum [Nonempty V] :
    chiVec3 G ≤ G.cliqueNum := by
  refine csSup_le ?_ ?_
  · exact (chiVec3FeasibleSet_nonempty (G := G)).image _
  · rintro _ ⟨X, hX, rfl⟩
    exact inner_le_cliqueNum_of_chiVec3Feasible hX

/-! ### CG10 — `cor:parameter` -/

/-- **CG10.** Corollary `cor:parameter`. -/
theorem chiVec3_eq_cliqueNum [Nonempty V] :
    chiVec3 G = G.cliqueNum :=
  le_antisymm (chiVec3_le_cliqueNum (G := G)) (cliqueNum_le_chiVec3 (G := G))

end BollobasNikiforov
