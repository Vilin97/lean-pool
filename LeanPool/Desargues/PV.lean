/-
Copyright (c) 2026 Abdullah Uyu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Abdullah Uyu
-/

import Mathlib.LinearAlgebra.Projectivization.Basic
import Mathlib.LinearAlgebra.Projectivization.Independence
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.OrzechProperty
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import LeanPool.Desargues.Basic

/-!
# Projectivizations as projective geometries

Proves that Mathlib projectivizations satisfy the projective-geometry axioms
for the dependence-based collinearity relation.
-/

open Finset Set Submodule FiniteDimensional Projectivization
open scoped LinearAlgebra.Projectivization

open Basic

variable [DivisionRing K] [AddCommGroup V] [Module K V]

-- Lemmas for distribution of composition.
theorem rep_comp_3
  (X Y Z : ℙ K V) :
    Projectivization.rep ∘ ![X, Y, Z] = ![X.rep, Y.rep, Z.rep] := by
  exact List.ofFn_inj.mp rfl

theorem rep_comp_2
  (X Y : ℙ K V) :
    Projectivization.rep ∘ ![X, Y] = ![X.rep, Y.rep] := by
  exact List.ofFn_inj.mp rfl

theorem lin_dep_aab
  (a b : V) :
    ¬ LinearIndependent K ![a, a, b] := by
  intro aab_dep
  rw [linearIndependent_iff'] at aab_dep
  specialize aab_dep {0, 1, 2} ![1, -1, 0]
  aesop

theorem lin_dep_aba
  (a b : V) :
    ¬ LinearIndependent K ![a, b, a] := by
  intro aab_dep
  rw [linearIndependent_iff'] at aab_dep
  specialize aab_dep {0, 1, 2} ![1, 0, -1]
  aesop

theorem lin_dep_abb
  (a b : V) :
    ¬ LinearIndependent K ![a, b, b] := by
  intro abb_dep
  rw [linearIndependent_iff'] at abb_dep
  specialize abb_dep {0, 1, 2} ![0, 1, -1]
  aesop

theorem lin_dep_imp_span
  (a b c : V)
  (bc_indep : LinearIndependent K ![b, c])
  (abc_dep : ¬ LinearIndependent K ![a, b, c]) :
    a ∈ span K {b, c} := by
  rw [not_iff_not.mpr linearIndependent_finSucc] at abc_dep
  push Not at abc_dep
  simp only [Fin.isValue, Matrix.cons_val_zero] at abc_dep
  convert abc_dep bc_indep
  rw [show Fin.tail ![a, b, c] = ![b, c] from rfl, Matrix.range_cons_cons_empty]

-- A vector lying in the span of a pair is dependent with that pair.
theorem mem_span_pair_imp_dep
  (a b c : V)
  (a_mem : a ∈ span K {b, c}) :
    ¬ LinearIndependent K ![a, b, c] := by
  rw [Submodule.mem_span_pair] at a_mem
  obtain ⟨s, t, hst⟩ := a_mem
  rw [Fintype.not_linearIndependent_iff]
  refine ⟨![1, -s, -t], ?_, 0, by simp⟩
  simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons, one_smul, neg_smul]
  rw [← hst]
  abel

-- Version with representatives of the axiom L_2.
theorem l2_rep
  (a b p q : V)
  (apq_dep : ¬ LinearIndependent K ![a, p, q])
  (bpq_dep : ¬ LinearIndependent K ![b, p, q])
  (pq_indep : LinearIndependent K ![p, q]) :
    ¬ LinearIndependent K ![a, b, p] := by
  -- p and q are not the same points.
  have pq_neq : p ≠ q := by
    intro hpq
    have inj := pq_indep.injective
    have : (0 : Fin 2) = 1 := inj (by simp [hpq])
    simp at this
  -- a, b, p, q are in the span of p, q.
  have a_span_pq : a ∈ span K {p, q} := by
    apply lin_dep_imp_span a p q pq_indep apq_dep
  have b_span_pq : b ∈ span K {p, q} := by
    apply lin_dep_imp_span b p q pq_indep bpq_dep
  have ppq_dep : ¬ LinearIndependent K ![p, p, q] :=
    by apply (lin_dep_aab p q)
  have p_span_pq : p ∈ span K {p, q} :=
    by apply lin_dep_imp_span p p q pq_indep ppq_dep
  have qpq_dep : ¬ LinearIndependent K ![q, p, q] :=
    by apply (lin_dep_aba q p)
  have q_span_pq : q ∈ span K {p, q} :=
    by apply lin_dep_imp_span q p q pq_indep qpq_dep
  intro abp_dep
  -- The three vectors a, b, p all lie in the span of {p, q}, which has rank 2,
  -- so they cannot be linearly independent.
  have pq_range : ({p, q} : Set V) = Set.range ![p, q] := by
    rw [Matrix.range_cons_cons_empty]
  have span_le : span K (Set.range ![a, b, p]) ≤ span K (Set.range ![p, q]) := by
    rw [span_le, Set.range_subset_iff]
    intro i
    fin_cases i
    · rw [← pq_range]; exact a_span_pq
    · rw [← pq_range]; exact b_span_pq
    · rw [← pq_range]; exact p_span_pq
  have finite : Module.Finite K (span K (Set.range ![p, q])) :=
    Module.Finite.span_of_finite K (Set.finite_range _)
  have card_le := linearIndependent_iff_card_le_finrank_span.mp abp_dep
  have finrank_le : Module.finrank K (span K (Set.range ![a, b, p]))
      ≤ Module.finrank K (span K (Set.range ![p, q])) :=
    Submodule.finrank_mono span_le
  have pq_rank : Module.finrank K (span K (Set.range ![p, q])) = 2 := by
    rw [finrank_span_eq_card pq_indep, Fintype.card_fin]
  simp only [Fintype.card_fin, Set.finrank] at card_le
  omega

-- The span of a pair of vectors is finite-dimensional.
instance finiteDimensional_span_pair
    (x y : V) :
    FiniteDimensional K (span K ({x, y} : Set V)) :=
  Module.Finite.span_of_finite K (Set.toFinite _)

-- The span of a pair of vectors has rank at most two.
theorem finrank_span_pair_le
    (x y : V) :
    Module.finrank K (span K ({x, y} : Set V)) ≤ 2 := by
  have h := finrank_range_le_card (R := K) ![x, y]
  rw [Set.finrank, Matrix.range_cons_cons_empty, Fintype.card_fin] at h
  exact h

-- A linearly independent pair spans a rank-two subspace.
theorem finrank_span_pair_indep
    (x y : V)
    (xy_indep : LinearIndependent K ![x, y]) :
    Module.finrank K (span K ({x, y} : Set V)) = 2 := by
  rw [show ({x, y} : Set V) = Set.range ![x, y] from
        (Matrix.range_cons_cons_empty x y _).symm,
    finrank_span_eq_card xy_indep, Fintype.card_fin]

-- A linearly dependent pair spans a subspace of rank at most one.
theorem finrank_span_pair_dep
    (x y : V)
    (xy_dep : ¬ LinearIndependent K ![x, y]) :
    Module.finrank K (span K ({x, y} : Set V)) ≤ 1 := by
  rw [show ({x, y} : Set V) = Set.range ![x, y] from
        (Matrix.range_cons_cons_empty x y _).symm]
  by_contra h
  apply xy_dep
  rw [linearIndependent_iff_card_le_finrank_span, Fintype.card_fin, Set.finrank]
  omega

-- Under the L₃ hypotheses with `A ≠ C` and `B ≠ D`, lines `AC` and `BD` meet:
-- their spans have nontrivial intersection.
theorem l3_inter_ne_bot
    (a b c d p : V)
    (pab_dep : ¬ LinearIndependent K ![p, a, b])
    (pcd_dep : ¬ LinearIndependent K ![p, c, d])
    (p_ne : p ≠ 0)
    (ac_indep : LinearIndependent K ![a, c])
    (bd_indep : LinearIndependent K ![b, d]) :
    span K ({a, c} : Set V) ⊓ span K ({b, d} : Set V) ≠ ⊥ := by
  -- The span of the four points {a, b, c, d} has rank at most three, because
  -- the planes {a, b} and {c, d} share the common point p.
  have abcd_le : Module.finrank K ↥(span K ({a, b} : Set V) ⊔ span K ({c, d} : Set V)) ≤ 3 := by
    have grass := Submodule.finrank_sup_add_finrank_inf_eq
      (span K ({a, b} : Set V)) (span K ({c, d} : Set V))
    have hab := finrank_span_pair_le (K := K) a b
    have hcd := finrank_span_pair_le (K := K) c d
    by_cases hab_indep : LinearIndependent K ![a, b]
    · by_cases hcd_indep : LinearIndependent K ![c, d]
      · -- both planes are honest; p lies in their intersection.
        have p_in_ab : p ∈ span K ({a, b} : Set V) :=
          lin_dep_imp_span p a b hab_indep pab_dep
        have p_in_cd : p ∈ span K ({c, d} : Set V) :=
          lin_dep_imp_span p c d hcd_indep pcd_dep
        have inf_ne : span K ({a, b} : Set V) ⊓ span K ({c, d} : Set V) ≠ ⊥ := by
          intro h_bot
          have : p ∈ (⊥ : Submodule K V) := by
            rw [← h_bot]
            exact Submodule.mem_inf.mpr ⟨p_in_ab, p_in_cd⟩
          exact p_ne (Submodule.mem_bot K |>.mp this)
        have inf_pos : 1 ≤ Module.finrank K
            ↥(span K ({a, b} : Set V) ⊓ span K ({c, d} : Set V)) :=
          Submodule.one_le_finrank_iff.mpr inf_ne
        omega
      · -- the plane {c, d} degenerates to a line.
        have hcd1 := finrank_span_pair_dep (K := K) c d hcd_indep
        omega
    · -- the plane {a, b} degenerates to a line.
      have hab1 := finrank_span_pair_dep (K := K) a b hab_indep
      omega
  -- The lines AC and BD live inside that rank-≤3 space.
  have sup_le : span K ({a, c} : Set V) ⊔ span K ({b, d} : Set V)
      ≤ span K ({a, b} : Set V) ⊔ span K ({c, d} : Set V) := by
    apply sup_le
    · rw [span_le]
      intro x hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl
      · exact Submodule.mem_sup_left (subset_span (by simp))
      · exact Submodule.mem_sup_right (subset_span (by simp))
    · rw [span_le]
      intro x hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl
      · exact Submodule.mem_sup_left (subset_span (by simp))
      · exact Submodule.mem_sup_right (subset_span (by simp))
  have sup_le_three : Module.finrank K
      ↥(span K ({a, c} : Set V) ⊔ span K ({b, d} : Set V)) ≤ 3 :=
    le_trans (Submodule.finrank_mono sup_le) abcd_le
  have grass := Submodule.finrank_sup_add_finrank_inf_eq
    (span K ({a, c} : Set V)) (span K ({b, d} : Set V))
  have hac := finrank_span_pair_indep (K := K) a c ac_indep
  have hbd := finrank_span_pair_indep (K := K) b d bd_indep
  -- Grassmann's identity forces the intersection to have positive rank.
  intro h_bot
  rw [h_bot, finrank_bot] at grass
  omega

-- Every Projectivization is a ProjectiveGeometry
instance :
  ProjectiveGeometry (ℙ K V)
  (fun X Y Z => ¬ Independent ![X, Y, Z]) :=
⟨
by
intro A B
rw [independent_iff, rep_comp_3]
rw [not_linearIndependent_iff]
use {0, 1, 2}, ![1, 0, -1]
refine ⟨?_, ?_⟩
· simp
· simp,
by
intro A B P Q ABPcol BPQcol PQ_neq
rw [independent_iff, rep_comp_3] at ABPcol
rw [independent_iff, rep_comp_3] at BPQcol
rw [<- independent_pair_iff_ne] at PQ_neq
rw [independent_iff, rep_comp_2] at PQ_neq
rw [independent_iff, rep_comp_3]
apply l2_rep A.rep B.rep P.rep Q.rep
· exact ABPcol
· exact BPQcol
· exact PQ_neq,
by
intro A B C D P PABcol PCDcol
rw [independent_iff, rep_comp_3] at PABcol PCDcol
by_cases hAC : A = C
· -- A = C : the point B works, since both triples then repeat a point.
  refine ⟨B, ?_, ?_⟩
  · rw [hAC, independent_iff, rep_comp_3]
    exact lin_dep_abb B.rep C.rep
  · rw [independent_iff, rep_comp_3]
    exact lin_dep_aab B.rep D.rep
· by_cases hBD : B = D
  · -- B = D : the point A works, by the same repetition argument.
    refine ⟨A, ?_, ?_⟩
    · rw [independent_iff, rep_comp_3]
      exact lin_dep_aab A.rep C.rep
    · rw [hBD, independent_iff, rep_comp_3]
      exact lin_dep_abb A.rep D.rep
  · -- General position: lines AC and BD meet in a common point Q.
    have ac_indep : LinearIndependent K ![A.rep, C.rep] := by
      rw [← rep_comp_2, ← independent_iff, independent_pair_iff_ne]
      exact hAC
    have bd_indep : LinearIndependent K ![B.rep, D.rep] := by
      rw [← rep_comp_2, ← independent_iff, independent_pair_iff_ne]
      exact hBD
    have inter_ne :
        span K ({A.rep, C.rep} : Set V) ⊓ span K ({B.rep, D.rep} : Set V) ≠ ⊥ :=
      l3_inter_ne_bot A.rep B.rep C.rep D.rep P.rep PABcol PCDcol P.rep_nonzero
        ac_indep bd_indep
    obtain ⟨q, q_mem, q_ne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot inter_ne
    rw [Submodule.mem_inf] at q_mem
    obtain ⟨q_ac, q_bd⟩ := q_mem
    obtain ⟨u, hu⟩ := exists_smul_eq_mk_rep (K := K) q q_ne
    refine ⟨Projectivization.mk K q q_ne, ?_, ?_⟩
    · rw [independent_iff, rep_comp_3]
      apply mem_span_pair_imp_dep (Projectivization.mk K q q_ne).rep A.rep C.rep
      rw [← hu]
      exact Submodule.smul_mem _ _ q_ac
    · rw [independent_iff, rep_comp_3]
      apply mem_span_pair_imp_dep (Projectivization.mk K q q_ne).rep B.rep D.rep
      rw [← hu]
      exact Submodule.smul_mem _ _ q_bd
⟩
