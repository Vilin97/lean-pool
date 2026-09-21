/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/

import LeanPool.BrillNoetherGraphs.Bananas.Jacobian.BananaJacobianProposition214
import LeanPool.BrillNoetherGraphs.Bananas.Classification.GenusOneKGeneral
import LeanPool.BrillNoetherGraphs.Bananas.Transmission.ChainTwoLoopsSameLeft
import Mathlib.Data.ZMod.Basic

/-!
# Example 1.11: the torsion order of a cycle

A cycle graph, marked at its two junction vertices, is exactly a genus-one
banana `B : Banana 1`, marked at `leftEndpoint B` and `rightEndpoint B`, with
the two strand lengths `B.length 0` and `B.length 1` playing the role of the
paper's `a` and `b`.

The proof identifies the marked difference `[rightEndpoint - leftEndpoint]`
with `(B.length 0) • w` in the graph Jacobian, where `w` is the first
normalized coordinate step on strand `0` (`bananaCoordinateStep B 0`).  Two
facts from the banana Jacobian presentation (Proposition 2.14) pin down the
order of `w` exactly:

* the diagonal relation (firing the shared left endpoint once) identifies
  `w` on strand `1` with `-w` on strand `0`, so combining the two
  strand-length relations gives `(B.length 0 + B.length 1) • w ~ 0`;
* conversely, the *exact* relation lattice of Proposition 2.14 (not just a
  containment) shows that no smaller multiple of `w` is principal, via a
  homomorphism to `ZMod (B.length 0 + B.length 1)` that kills exactly the
  displayed relations.

Combining the two pins down the torsion order at
`(B.length 0 + B.length 1) / gcd (B.length 0) (B.length 1)`, matching
`eg:cycle`.
-/

namespace Bananas

open Utilities

section Generic

/-- `linear_equiv G X 0` is literally membership of `X` in the principal
divisors, up to the sign convention baked into `linear_equiv`. -/
private theorem linear_equiv_zero_iff_mem {G : CFGraph} {X : CFDiv G} :
    linear_equiv G X 0 ↔ X ∈ principal_divisors G := by
  unfold linear_equiv
  rw [zero_sub, AddSubgroup.neg_mem_iff]

private theorem linear_equiv_neg {G : CFGraph} {X : CFDiv G}
    (h : linear_equiv G X 0) : linear_equiv G (-X) 0 :=
  linear_equiv_zero_iff_mem.mpr
    ((principal_divisors G).neg_mem (linear_equiv_zero_iff_mem.mp h))

private theorem linear_equiv_sub_to_zero {G : CFGraph} {X Y : CFDiv G}
    (h : linear_equiv G X Y) : linear_equiv G (X - Y) 0 := by
  unfold linear_equiv at h ⊢
  have heq : (0 : CFDiv G) - (X - Y) = Y - X := by abel
  rw [heq]
  exact h

private theorem linear_equiv_zsmul {G : CFGraph} {D E : CFDiv G}
    (h : linear_equiv G D E) (n : ℤ) :
    linear_equiv G (n • D) (n • E) := by
  unfold linear_equiv at h ⊢
  simpa [smul_sub] using (principal_divisors G).zsmul_mem h n

end Generic

/-- The homomorphism `(x0, x1) ↦ x0 - x1` from banana coordinates to
`ZMod n`.  For `n = a + b` this kills exactly the displayed relations of a
genus-one banana's Jacobian presentation. -/
def cycleTorsionHom (n : ℕ) : (Fin 2 → ℤ) →+ ZMod n where
  toFun x := (x 0 : ZMod n) - (x 1 : ZMod n)
  map_zero' := by simp
  map_add' x y := by
    simp only [Pi.add_apply]
    push_cast
    ring

@[simp] private theorem cycleTorsionHom_basis0 (n : ℕ) :
    cycleTorsionHom n (bananaCoordinateBasis (0 : Fin 2)) = 1 := by
  simp [cycleTorsionHom, bananaCoordinateBasis]

private theorem cycleTorsionHom_diagonalRelation (n : ℕ) :
    cycleTorsionHom n (bananaDiagonalRelation (g := 1)) = 0 := by
  simp [cycleTorsionHom, bananaDiagonalRelation]

private theorem cycleTorsionHom_strandLengthRelation
    (B : Banana 1) (beta : Fin 2) :
    cycleTorsionHom (B.length 0 + B.length 1)
      (bananaStrandLengthRelation B beta) = 0 := by
  fin_cases beta
  · simp [cycleTorsionHom, bananaStrandLengthRelation]
  · simp only [cycleTorsionHom, bananaStrandLengthRelation, bananaCoordinateBasis,
      AddMonoidHom.coe_mk, ZeroHom.coe_mk, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    norm_num
    push_cast
    have : ((B.length 0 + B.length 1 : ℕ) : ZMod (B.length 0 + B.length 1)) = 0 := by
      simp
    push_cast at this
    linear_combination this

private theorem bananaDisplayedRelations_le_cycleTorsionHom_ker (B : Banana 1) :
    bananaDisplayedRelations B ≤ (cycleTorsionHom (B.length 0 + B.length 1)).ker := by
  rw [bananaDisplayedRelations, AddSubgroup.closure_le]
  rintro x (hx | ⟨beta, rfl⟩)
  · rw [Set.mem_singleton_iff] at hx
    subst hx
    exact cycleTorsionHom_diagonalRelation _
  · exact cycleTorsionHom_strandLengthRelation B beta

/-- **Example 1.11** (`eg:cycle`), torsion order half: for a cycle graph
`B : Banana 1`, marked at its two junction vertices, the torsion order of
`(leftEndpoint, rightEndpoint)` is `(a + b) / gcd a b` with `a = B.length 0`,
`b = B.length 1`. -/
theorem cycle_isTorsionOrder (B : Banana 1) :
    IsTorsionOrder (mark B.graph (leftEndpoint B) (rightEndpoint B))
      ((B.length 0 + B.length 1) / Nat.gcd (B.length 0) (B.length 1)) := by
  set a := B.length 0 with ha
  set b := B.length 1 with hb
  set L := leftEndpoint B with hL
  set R := rightEndpoint B with hR
  set w0 := bananaCoordinateStep B (0 : Fin 2) with hw0
  set w1 := bananaCoordinateStep B (1 : Fin 2) with hw1
  have hapos : 0 < a := B.length_pos 0
  have hbpos : 0 < b := B.length_pos 1
  -- The two strand-length relations.
  have h0 : linear_equiv B.graph ((a : ℤ) • w0) (one_chip R - one_chip L) :=
    bananaCoordinateStep_length_linearEquiv_endpointDifference B 0
  have h1 : linear_equiv B.graph ((b : ℤ) • w1) (one_chip R - one_chip L) :=
    bananaCoordinateStep_length_linearEquiv_endpointDifference B 1
  -- The diagonal relation: firing the shared left endpoint.
  have hdiag : linear_equiv B.graph (w0 + w1) 0 := by
    have hmem := bananaDiagonalRelation_image_principal B
    rw [bananaCoordinateDivisorHom_diagonalRelation, Fin.sum_univ_two] at hmem
    exact linear_equiv_zero_iff_mem.mpr hmem
  have hw1neg : linear_equiv B.graph w1 (-w0) := by
    unfold linear_equiv at hdiag ⊢
    have heq : (-w0) - w1 = (0 : CFDiv B.graph) - (w0 + w1) := by abel
    rw [heq]
    exact hdiag
  have hb' : linear_equiv B.graph ((b : ℤ) • w1) (-((b : ℤ) • w0)) := by
    have := linear_equiv_zsmul hw1neg b
    simpa [smul_neg] using this
  -- Chase: a•w0 ~ (R - L) ~ b•w1 ~ -(b•w0), so (a+b)•w0 ~ 0.
  have hchain : linear_equiv B.graph ((a : ℤ) • w0) (-((b : ℤ) • w0)) :=
    h0.trans (h1.symm.trans hb')
  have hAB0 : linear_equiv B.graph
      (((a : ℤ) • w0) - (-((b : ℤ) • w0))) 0 := linear_equiv_sub_to_zero hchain
  have hAB : linear_equiv B.graph (((a + b : ℕ) : ℤ) • w0) 0 := by
    have heq : ((a : ℤ) • w0) - (-((b : ℤ) • w0)) = ((a + b : ℕ) : ℤ) • w0 := by
      push_cast
      module
    rwa [heq] at hAB0
  -- Arithmetic setup for `k = (a+b)/gcd a b`.
  set d := Nat.gcd a b with hdDef
  have hdpos : 0 < d := Nat.gcd_pos_of_pos_left b hapos
  have hda : d ∣ a := Nat.gcd_dvd_left a b
  have hdb : d ∣ b := Nat.gcd_dvd_right a b
  have hdab : d ∣ (a + b) := Nat.dvd_add hda hdb
  set k := (a + b) / d with hkDef
  have hkd : k * d = a + b := Nat.div_mul_cancel hdab
  set e := a / d with heDef
  have hed : e * d = a := Nat.div_mul_cancel hda
  set f := b / d with hfDef
  have hfd : f * d = b := Nat.div_mul_cancel hdb
  have hkpos : 0 < k := by
    rcases Nat.eq_zero_or_pos k with hk0 | hk0
    · exfalso; rw [hk0] at hkd; simp at hkd; omega
    · exact hk0
  have hka : k * a = (a + b) * e := by
    have haeq : a = e * d := hed.symm
    calc k * a = k * (e * d) := by rw [haeq]
      _ = (k * d) * e := by ring
      _ = (a + b) * e := by rw [hkd]
  -- Annihilation: k • (L - R) ~ 0.
  have hRL_k : linear_equiv B.graph ((k : ℤ) • ((a : ℤ) • w0))
      ((k : ℤ) • (one_chip R - one_chip L)) := linear_equiv_zsmul h0 k
  have hka0 : linear_equiv B.graph (((k * a : ℕ) : ℤ) • w0) 0 := by
    have heAB : linear_equiv B.graph
        ((e : ℤ) • (((a + b : ℕ) : ℤ) • w0)) ((e : ℤ) • (0 : CFDiv B.graph)) :=
      linear_equiv_zsmul hAB e
    have heAB' : linear_equiv B.graph (((k * a : ℕ) : ℤ) • w0) 0 := by
      have heq1 : ((k * a : ℕ) : ℤ) • w0
          = (e : ℤ) • (((a + b : ℕ) : ℤ) • w0) := by
        rw [hka]
        push_cast
        module
      rw [heq1]
      simpa using heAB
    exact heAB'
  have hRLk0 : linear_equiv B.graph ((k : ℤ) • (one_chip R - one_chip L)) 0 := by
    have heq : (k : ℤ) • ((a : ℤ) • w0) = ((k * a : ℕ) : ℤ) • w0 := by
      push_cast; module
    rw [heq] at hRL_k
    exact hRL_k.symm.trans hka0
  have hLRk0 : linear_equiv B.graph ((k : ℤ) • (one_chip L - one_chip R)) 0 := by
    have heq : (k : ℤ) • (one_chip L - one_chip R)
        = -((k : ℤ) • (one_chip R - one_chip L)) := by
      rw [← smul_neg]
      congr 1
      abel
    rw [heq]
    exact linear_equiv_neg hRLk0
  refine ⟨⟨hkpos, hLRk0⟩, ?_⟩
  -- Minimality.
  intro m hm
  obtain ⟨hmpos, hmw⟩ := hm
  have hmRL0 : linear_equiv B.graph ((m : ℤ) • (one_chip R - one_chip L)) 0 := by
    have heq : (m : ℤ) • (one_chip R - one_chip L)
        = -((m : ℤ) • (one_chip L - one_chip R)) := by
      rw [← smul_neg]
      congr 1
      abel
    rw [heq]
    exact linear_equiv_neg hmw
  have hRm : linear_equiv B.graph ((m : ℤ) • ((a : ℤ) • w0))
      ((m : ℤ) • (one_chip R - one_chip L)) := linear_equiv_zsmul h0 m
  have hmaw0 : linear_equiv B.graph (((m * a : ℕ) : ℤ) • w0) 0 := by
    have heq : (m : ℤ) • ((a : ℤ) • w0) = ((m * a : ℕ) : ℤ) • w0 := by
      push_cast; module
    rw [heq] at hRm
    exact hRm.trans hmRL0
  have hmem : (((m * a : ℕ) : ℤ) • w0) ∈ principal_divisors B.graph :=
    linear_equiv_zero_iff_mem.mp hmaw0
  have hcoordEq : bananaCoordinateDivisorHom B
      (((m * a : ℕ) : ℤ) • bananaCoordinateBasis (0 : Fin 2))
        = ((m * a : ℕ) : ℤ) • w0 := by
    rw [map_zsmul, bananaCoordinateDivisorHom_basis]
  have hmem' : bananaCoordinateDivisorHom B
      (((m * a : ℕ) : ℤ) • bananaCoordinateBasis (0 : Fin 2)) ∈
        principal_divisors B.graph := by
    rw [hcoordEq]; exact hmem
  have hrel : (((m * a : ℕ) : ℤ) • bananaCoordinateBasis (0 : Fin 2)) ∈
      bananaCoordinateRelations B := by
    rw [bananaCoordinateRelations, AddMonoidHom.mem_ker]
    exact (QuotientAddGroup.eq_zero_iff _).2 hmem'
  rw [bananaCoordinateRelations_eq_displayedRelations] at hrel
  have hker := bananaDisplayedRelations_le_cycleTorsionHom_ker B hrel
  rw [AddMonoidHom.mem_ker] at hker
  have hval : cycleTorsionHom (a + b)
      (((m * a : ℕ) : ℤ) • bananaCoordinateBasis (0 : Fin 2))
        = ((m * a : ℕ) : ℤ) := by
    rw [map_zsmul, cycleTorsionHom_basis0]
    simp
  rw [hval] at hker
  have hdvd : ((a + b : ℕ) : ℤ) ∣ ((m * a : ℕ) : ℤ) :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hker
  have hdvdNat : (a + b) ∣ (m * a) := by exact_mod_cast hdvd
  -- Reduce `(a+b) ∣ m*a` to `k ∣ m` using `gcd e f = 1`.
  have hkdvd : k ∣ (m * e) := by
    have hstep : k * d ∣ (m * e) * d := by
      have heq : (m * e) * d = m * a := by rw [mul_assoc, hed]
      rw [heq, hkd]
      exact hdvdNat
    exact (Nat.mul_dvd_mul_iff_right hdpos).mp hstep
  have hcopef : Nat.Coprime e f := Nat.coprime_div_gcd_div_gcd hdpos
  have hkef : k = e + f := by
    have : k * d = (e + f) * d := by rw [hkd, add_mul, hed, hfd]
    exact (Nat.mul_right_cancel hdpos this)
  have hcopke : Nat.Coprime k e := by
    rw [hkef, add_comm]
    exact Nat.coprime_add_self_left.mpr hcopef.symm
  have hkm : k ∣ m := hcopke.dvd_mul_right.mp hkdvd
  exact Nat.le_of_dvd hmpos hkm

/-- **Example 1.11** (`eg:cycle`), all-submodularity half: a cycle graph is
connected of genus one with distinct marks, so every divisor is
submodular. -/
theorem cycle_allSubmodular (B : Banana 1) :
    AllSubmodular (mark B.graph (leftEndpoint B) (rightEndpoint B)) :=
  allSubmodular_of_connected_genus_one_distinct_classes
    (banana_graph_connected B) B.genus_graph (leftEndpoint B) (rightEndpoint B)
    (marks_not_linearEquiv (le_refl 1) B (leftEndpoint_ne_rightEndpoint B))

/-- **Example 1.11** (`eg:cycle`): a cycle graph, marked at its two junction
vertices, has `k`-general transmission at `k = (a + b) / gcd a b`, where `a`
and `b` are the lengths of the two paths joining the marks. -/
theorem cycle_kGeneralTransmission (B : Banana 1) :
    KGeneralTransmission (mark B.graph (leftEndpoint B) (rightEndpoint B))
      ((B.length 0 + B.length 1) / Nat.gcd (B.length 0) (B.length 1)) :=
  kGeneralTransmission_genusOne_of_torsionOrder_and_allSubmodular
    (banana_graph_connected B) B.genus_graph (cycle_isTorsionOrder B)
    (cycle_allSubmodular B)

end Bananas
