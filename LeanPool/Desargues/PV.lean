/-
Copyright (c) 2026 Abdullah Uyu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Abdullah Uyu
-/

import Mathlib.LinearAlgebra.Projectivization.Basic
import Mathlib.LinearAlgebra.Projectivization.Independence
import LeanPool.Desargues.Basic

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

theorem lin_dep_imp_span
  (a b c : V)
  (bc_indep : LinearIndependent K ![b, c])
  (abc_dep : ¬ LinearIndependent K ![a, b, c]) :
    a ∈ span K {b, c} := by
  rw [not_iff_not.mpr linearIndependent_fin_succ] at abc_dep
  push_neg at abc_dep
  simp only [Fin.isValue, Matrix.cons_val_zero] at abc_dep
  convert abc_dep bc_indep
  ext x
  simp [show Fin.tail ![a, b, c] = ![b, c] from rfl]
  rw [or_comm]

-- Version with representatives of the axiom L_2.
theorem l2_rep
  (a b p q : V)
  (apq_dep : ¬ LinearIndependent K ![a, p, q])
  (bpq_dep : ¬ LinearIndependent K ![b, p, q])
  (pq_indep : LinearIndependent K ![p, q]) :
    ¬ LinearIndependent K ![a, b, p] := by
  -- p and q are not the same points.
  have pq_neq : p ≠ q := by sorry
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
  sorry

-- Every Projectivization is a ProjectiveGeometry
instance :
  ProjectiveGeometry (ℙ K V)
  (fun X Y Z => ¬ Independent ![X, Y, Z]) :=
⟨
-- fun X Y Z => ∃ k1 k2 k3 : K, ¬(k1 = 0 ∧ k2 = 0 ∧ k3 = 0) ∧ k1 • X.rep + k2 • Y.rep + k3 • Z.rep = 0,
-- fun X Y Z => ¬ LinearIndependent K ![X.rep, Y.rep, Z.rep],
-- fun X Y Z => Dependent (index X Y Z),
-- fun X Y Z => ¬ Independent ![X, Y, Z],

by
intro A B
rw [independent_iff, rep_comp_3]
rw [not_linearIndependent_iff]
use {0, 1, 2}, ![1, 0, -1]
constructor
simp
simp,

by
intro A B P Q
intro ABPcol BPQcol PQ_neq
rw [independent_iff, rep_comp_3] at ABPcol
rw [independent_iff, rep_comp_3] at BPQcol
rw [<- independent_pair_iff_neq] at PQ_neq
rw [independent_iff, rep_comp_2] at PQ_neq
rw [independent_iff, rep_comp_3]
apply l2_rep A.rep B.rep P.rep Q.rep
· exact ABPcol
· exact BPQcol
· exact PQ_neq,

sorry
⟩
