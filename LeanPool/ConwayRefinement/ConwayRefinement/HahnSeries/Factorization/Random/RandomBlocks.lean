/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.Factorization.Random.NormalFormBlocks
public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.Factorization.Random.Random
public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.Factorization.Random.CoefficientRandom
public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.Factorization.Random.SupportRandom
public import LeanPool.ConwayRefinement.ConwayRefinement.LinearAlgebra.IndicatorFinsupp

import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.OrdinalValue.PrincipalComponentDegree
import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.Topology.Order.Monotone

/-!
# Randomness of a series passes to its blocks

Fornasiero, Lavi, L'Innocente and Mantova, *Irreducibility in generalized power series* (2024),
Theorem 1.8, apply Proposition 3.2 to the blocks `b₁, …, bₘ` of a random series
`b = ∑ᵢ bᵢ t^{γᵢ} + r`, which requires `Q(b₁, …, bₘ)`, hence the mutual randomness of the
blocks. The source does not write this step; it is carried out here.

Coefficient clause: every coefficient of a block is a coefficient of `b`, since the blocks
`bᵢ t^{γᵢ}` occupy disjoint parts of the support of `b`; the joint coefficient family of the
blocks is a subfamily of the coefficient family of `b`, indexed injectively.

Support clause: `cl(supp bᵢ) = cl(supp (bᵢ t^{γᵢ})) - γᵢ`, and `γᵢ ∈ cl(supp b)`. Two distinct
blocks cannot share a nonzero point `z` of their support closures, for `z + γᵢ`, `z + γⱼ`,
`γᵢ`, `γⱼ` would then satisfy a `ℚ`-relation in `cl(supp b) ∖ {0}` forcing `γᵢ = γⱼ`. A vanishing
`ℚ`-combination of elements `z` of `⋃ᵢ cl(supp bᵢ) ∖ {0}` lifts to the free module on
`cl(supp b) ∖ {0}` as a combination of `e(z + γ_{i(z)}) - e(γ_{i(z)})`; evaluated at the
smallest point `z₀ + γ_{i(z₀)}` occurring, only the coefficient of `z₀` survives, because
`γ_{i(z)} > z + γ_{i(z)}` for every `z`, and `z ↦ z + γ_{i(z)}` is injective.
-/

open scoped HahnSeries NatOrdinal

universe v

public noncomputable section

namespace FLLM24

open Berarducci HahnSeries HahnSeries.Nonpositive

variable {K : Type v} [Field K]

namespace BlockDecomposition

variable {b : Series K} {n m : ℕ} (d : BlockDecomposition b n m)

/-! ### Supports of the pieces -/

/-- The supports of two distinct pieces are disjoint. -/
theorem piece_disjoint {i j : Fin m} (hij : i ≠ j) {x : ℝ}
    (hx : x ∈ ((d.piece i : Series K) : K⟦ℝ⟧).support) :
    x ∉ ((d.piece j : Series K) : K⟦ℝ⟧).support := by
  intro hx'
  rcases lt_or_gt_of_ne hij with h | h
  · exact lt_irrefl x (d.piece_support_lt h hx hx')
  · exact lt_irrefl x (d.piece_support_lt h hx' hx)

/-- The coefficient of `b` at a support point of the `i`-th piece is the coefficient of that
piece. -/
theorem coeff_eq_coeff_piece (i : Fin m) {x : ℝ}
    (hx : x ∈ ((d.piece i : Series K) : K⟦ℝ⟧).support) :
    (b : K⟦ℝ⟧).coeff x = ((d.piece i : Series K) : K⟦ℝ⟧).coeff x := by
  classical
  have hsum := congrArg (fun c : Series K ↦ (c : K⟦ℝ⟧).coeff x) d.eq_sum_piece_add_rest
  simp only [Subring.coe_add, AddSubmonoidClass.coe_finsetSum, HahnSeries.coeff_add,
    HahnSeries.coeff_sum] at hsum
  rw [hsum, Finset.sum_eq_single i]
  · have hrest : ((d.rest : Series K) : K⟦ℝ⟧).coeff x = 0 := by
      by_contra hne
      exact lt_irrefl x (d.piece_support_lt_rest i hx hne)
    rw [hrest, add_zero]
  · intro j _ hji
    by_contra hne
    exact d.piece_disjoint hji.symm hx hne
  · intro h
    exact absurd (Finset.mem_univ i) h

/-- The support of each piece is contained in the support of `b`. -/
theorem support_piece_subset (i : Fin m) :
    ((d.piece i : Series K) : K⟦ℝ⟧).support ⊆ (b : K⟦ℝ⟧).support := by
  intro x hx
  rw [HahnSeries.mem_support, d.coeff_eq_coeff_piece i hx]
  exact hx

/-- The coefficient of a block is the coefficient of its piece at the translated exponent. -/
theorem coeff_block (i : Fin m) (y : ℝ) :
    ((d.block i : Series K) : K⟦ℝ⟧).coeff y =
      ((d.piece i : Series K) : K⟦ℝ⟧).coeff (d.exponent i + y) := by
  rw [d.coe_piece, coeff_translate, add_sub_cancel_left]

/-- The support of a piece is the translate of the support of its block. -/
theorem support_piece (i : Fin m) :
    ((d.piece i : Series K) : K⟦ℝ⟧).support = (d.exponent i + ·) '' ((d.block i : Series K) :
      K⟦ℝ⟧).support := by
  rw [d.coe_piece, support_translate]

/-- The closure of the support of a piece is the translate of the closure of the support of its
block. -/
theorem closure_support_piece (i : Fin m) :
    closure ((d.piece i : Series K) : K⟦ℝ⟧).support =
      (d.exponent i + ·) '' closure ((d.block i : Series K) : K⟦ℝ⟧).support := by
  rw [d.support_piece]
  exact ((Homeomorph.addLeft (d.exponent i)).image_closure _).symm

/-- The exponent of a block lies in the closure of the support of its piece. -/
theorem exponent_mem_closure (i : Fin m) :
    d.exponent i ∈ closure ((d.piece i : Series K) : K⟦ℝ⟧).support := by
  rw [d.closure_support_piece]
  refine ⟨0, ?_, add_zero _⟩
  have hsup := (d.block_isPrincipal i).supportSup_eq_zero
  rw [supportSup_of_ne (d.block_isPrincipal i).ne_zero] at hsup
  have h0 : sSup ((d.block i : Series K) : K⟦ℝ⟧).support = 0 := WithBot.coe_inj.mp hsup
  rw [← h0]
  exact csSup_mem_closure (support_nonempty_iff.mpr (by
    intro h; exact (d.block_isPrincipal i).ne_zero (Subtype.ext h))) (bddAbove_support _)

/-- Points of the closure of a later piece are at least the exponent of an earlier block. -/
theorem exponent_le_of_mem_closure_piece {i j : Fin m} (hij : i < j) {y : ℝ}
    (hy : y ∈ closure ((d.piece j : Series K) : K⟦ℝ⟧).support) : d.exponent i ≤ y := by
  have hsub : ((d.piece j : Series K) : K⟦ℝ⟧).support ⊆ Set.Ici (d.exponent i) := by
    intro y' hy'
    have hbound : ((d.piece i : Series K) : K⟦ℝ⟧).support ⊆ Set.Iic y' :=
      fun x hx ↦ (d.piece_support_lt hij hx hy').le
    exact closure_minimal hbound isClosed_Iic (d.exponent_mem_closure i)
  exact closure_minimal hsub isClosed_Ici hy

/-- Points of the closure of the support of a block are nonpositive. -/
theorem nonpos_of_mem_closure_block (i : Fin m) {z : ℝ}
    (hz : z ∈ closure ((d.block i : Series K) : K⟦ℝ⟧).support) : z ≤ 0 :=
  closure_minimal (support_subset (d.block i)) isClosed_Iic hz

/-- A point of the closure of the support of a block, translated by the exponent, lies in the
closure of the support of `b`. -/
theorem add_mem_closure_support (i : Fin m) {z : ℝ}
    (hz : z ∈ closure ((d.block i : Series K) : K⟦ℝ⟧).support) :
    d.exponent i + z ∈ closure (b : K⟦ℝ⟧).support := by
  apply closure_mono (d.support_piece_subset i)
  rw [d.closure_support_piece]
  exact ⟨z, hz, rfl⟩

/-- Two distinct blocks have no common nonzero point in their support closures translated into
position: `γᵢ + z = γⱼ + z'` with `z, z' ≠ 0` forces `i = j`. -/
theorem eq_of_exponent_add_eq {i j : Fin m} {z z' : ℝ}
    (hz : z ∈ closure ((d.block i : Series K) : K⟦ℝ⟧).support)
    (hz' : z' ∈ closure ((d.block j : Series K) : K⟦ℝ⟧).support) (hz0 : z ≠ 0) (hz0' : z' ≠ 0)
    (h : d.exponent i + z = d.exponent j + z') : i = j := by
  by_contra hij
  rcases lt_or_gt_of_ne hij with hlt | hlt
  · have hmem : d.exponent j + z' ∈ closure ((d.piece j : Series K) : K⟦ℝ⟧).support := by
      rw [d.closure_support_piece]; exact ⟨z', hz', rfl⟩
    have hge := d.exponent_le_of_mem_closure_piece hlt hmem
    have hzneg : z < 0 := lt_of_le_of_ne (d.nonpos_of_mem_closure_block i hz) hz0
    linarith
  · have hmem : d.exponent i + z ∈ closure ((d.piece i : Series K) : K⟦ℝ⟧).support := by
      rw [d.closure_support_piece]; exact ⟨z, hz, rfl⟩
    have hge := d.exponent_le_of_mem_closure_piece hlt hmem
    have hzneg : z' < 0 := lt_of_le_of_ne (d.nonpos_of_mem_closure_block j hz') hz0'
    linarith

/-! ### The coefficient clause -/

/-- The blocks of a series with algebraically independent coefficients have jointly
algebraically independent coefficients. -/
theorem isMutuallyCoefficientRandom_block [CharZero K] (hb : IsCoefficientRandom b) :
    IsMutuallyCoefficientRandom d.block := by
  apply IsMutuallyCoefficientRandom.of
  have hpiece : ∀ p : coefficientIndex d.block,
      d.exponent p.1.1 + p.1.2 ∈ ((d.piece p.1.1 : Series K) : K⟦ℝ⟧).support := by
    intro p
    rw [HahnSeries.mem_support, ← d.coeff_block]
    exact (mem_coefficientIndex_iff d.block p.1).mp p.2
  have hcoeff : ∀ p : coefficientIndex d.block,
      ((d.block p.1.1 : Series K) : K⟦ℝ⟧).coeff p.1.2 =
        (b : K⟦ℝ⟧).coeff (d.exponent p.1.1 + p.1.2) := fun p ↦ by
    rw [d.coeff_eq_coeff_piece _ (hpiece p), d.coeff_block]
  let f : coefficientIndex d.block → (b : K⟦ℝ⟧).support := fun p ↦
    ⟨d.exponent p.1.1 + p.1.2, by
      rw [HahnSeries.mem_support, ← hcoeff p]
      exact (mem_coefficientIndex_iff d.block p.1).mp p.2⟩
  have hf : Function.Injective f := by
    intro p q hpq
    have h : d.exponent p.1.1 + p.1.2 = d.exponent q.1.1 + q.1.2 := congrArg Subtype.val hpq
    have hij : p.1.1 = q.1.1 := by
      by_contra hne
      exact d.piece_disjoint hne (hpiece p) (h ▸ hpiece q)
    apply Subtype.ext
    apply Prod.ext hij
    rw [hij] at h
    exact add_left_cancel h
  have := hb.algebraicIndependent.comp f hf
  convert this using 1
  funext p
  exact hcoeff p

/-! ### The support clause -/

/-- The blocks of a series with `ℚ`-linearly independent support closure satisfy the support
clause of mutual randomness. -/
theorem isMutuallySupportRandom_block (hb : IsSupportRandom b) :
    IsMutuallySupportRandom d.block := by
  classical
  set L := supportClosure b with hL
  set T := Finsupp.linearCombination ℚ (fun z : L ↦ (z : ℝ)) with hT
  have hinjL : Function.Injective T :=
    linearIndependent_iff_injective_finsuppLinearCombination.mp hb.linearIndependent
  -- Translated closure points and exponents as elements of `L`.
  have hmemL : ∀ (i : Fin m) {z : ℝ}, z ∈ closure ((d.block i : Series K) : K⟦ℝ⟧).support →
      z ≠ 0 → d.exponent i + z ∈ L := by
    intro i z hz hz0
    refine (mem_supportClosure_iff b _).mpr ⟨d.add_mem_closure_support i hz, ?_⟩
    have hzneg : z < 0 := lt_of_le_of_ne (d.nonpos_of_mem_closure_block i hz) hz0
    linarith [d.exponent_nonpos i]
  have hγcomb : ∀ i : Fin m, T (L.indicatorFinsupp ℚ (d.exponent i)) = d.exponent i := by
    intro i
    rcases eq_or_ne (d.exponent i) 0 with h0 | h0
    · rw [h0]; exact L.linearCombination_indicatorFinsupp_zero ℚ
    · exact L.linearCombination_indicatorFinsupp_of_mem ℚ ((mem_supportClosure_iff b _).mpr
        ⟨closure_mono (d.support_piece_subset i) (d.exponent_mem_closure i), h0⟩)
  refine ⟨fun i j hij z hz ↦ ?_, ?_⟩
  · -- A common nonzero point of two support closures gives a relation in `L`.
    obtain ⟨hzi, hzj⟩ := hz
    by_contra hz0'
    have hz0 : z ≠ 0 := fun h ↦ hz0' (Set.mem_singleton_iff.mpr h)
    have hxL := hmemL i hzi hz0
    have hx'L := hmemL j hzj hz0
    have hrel : L.indicatorFinsupp ℚ (d.exponent i + z) + L.indicatorFinsupp ℚ (d.exponent j) =
        L.indicatorFinsupp ℚ (d.exponent j + z) + L.indicatorFinsupp ℚ (d.exponent i) := by
      apply hinjL
      rw [map_add, map_add, L.linearCombination_indicatorFinsupp_of_mem ℚ hxL,
        L.linearCombination_indicatorFinsupp_of_mem ℚ hx'L, hγcomb, hγcomb]
      ring
    have hpos : 0 < (L.indicatorFinsupp ℚ (d.exponent i + z) +
        L.indicatorFinsupp ℚ (d.exponent j)) ⟨_, hxL⟩ := by
      rw [Finsupp.add_apply, L.indicatorFinsupp_apply_self hxL]
      linarith [L.indicatorFinsupp_apply_nonneg (R := ℚ) (d.exponent j) ⟨_, hxL⟩]
    rw [hrel, Finsupp.add_apply] at hpos
    have hγi : L.indicatorFinsupp ℚ (d.exponent i) ⟨_, hxL⟩ = 0 := by
      apply L.indicatorFinsupp_apply_of_ne
      intro heq
      exact hz0 (by simp only at heq; linarith)
    rw [hγi, add_zero] at hpos
    have heq : d.exponent i + z = d.exponent j + z := by
      by_contra hne
      rw [L.indicatorFinsupp_apply_of_ne _ _ hne] at hpos
      exact lt_irrefl _ hpos
    exact hij (d.exponent_strictMono.injective (add_right_cancel heq))
  · -- A vanishing combination of the translated points, tested at the smallest point.
    rw [linearIndependent_iff']
    intro s g hsum z₀ hz₀
    by_contra hg₀
    set S := s.filter (fun z ↦ g z ≠ 0) with hS
    have hz₀S : z₀ ∈ S := Finset.mem_filter.mpr ⟨hz₀, hg₀⟩
    have hgS : ∀ z ∈ S, g z ≠ 0 := fun z hz ↦ (Finset.mem_filter.mp hz).2
    have hidx : ∀ z : supportClosureUnion d.block,
        ∃ i, (z : ℝ) ∈ closure ((d.block i : Series K) : K⟦ℝ⟧).support := fun z ↦
      ((mem_supportClosureUnion_iff d.block z).mp z.2).1
    choose idx hidx using hidx
    have hzne : ∀ z : supportClosureUnion d.block, (z : ℝ) ≠ 0 := fun z ↦
      ((mem_supportClosureUnion_iff d.block z).mp z.2).2
    have hzneg : ∀ z : supportClosureUnion d.block, (z : ℝ) < 0 := fun z ↦
      lt_of_le_of_ne (d.nonpos_of_mem_closure_block (idx z) (hidx z)) (hzne z)
    set ψ : supportClosureUnion d.block → ℝ := fun z ↦ d.exponent (idx z) + z with hψ
    have hψL : ∀ z, ψ z ∈ L := fun z ↦ hmemL (idx z) (hidx z) (hzne z)
    have hψinj : Function.Injective ψ := by
      intro z z' h
      have hij := d.eq_of_exponent_add_eq (hidx z) (hidx z') (hzne z) (hzne z') h
      apply Subtype.ext
      simp only [hψ] at h
      rw [hij] at h
      exact add_left_cancel h
    have hψlt : ∀ z, ψ z < d.exponent (idx z) := fun z ↦ by
      simp only [hψ]; linarith [hzneg z]
    obtain ⟨z₁, hz₁S, hmin⟩ := S.exists_min_image ψ ⟨z₀, hz₀S⟩
    have hz₁s : z₁ ∈ s := (Finset.mem_filter.mp hz₁S).1
    -- The lifted relation in the free module on `L`.
    set F : L →₀ ℚ := ∑ z ∈ s, g z •
      (L.indicatorFinsupp ℚ (ψ z) - L.indicatorFinsupp ℚ (d.exponent (idx z))) with hF
    have hTF : T F = 0 := by
      rw [hF, map_sum, ← hsum]
      refine Finset.sum_congr rfl fun z _ ↦ ?_
      rw [map_smul, map_sub, L.linearCombination_indicatorFinsupp_of_mem ℚ (hψL z), hγcomb]
      simp only [hψ, add_sub_cancel_left]
    have hF0 : F = 0 := hinjL (by rw [hTF, map_zero])
    have hval := congrArg (fun f : L →₀ ℚ ↦ f ⟨ψ z₁, hψL z₁⟩) hF0
    simp only [hF, Finsupp.finsetSum_apply, Finsupp.smul_apply, Finsupp.sub_apply,
      Finsupp.zero_apply, smul_eq_mul] at hval
    rw [Finset.sum_eq_single z₁] at hval
    · rw [L.indicatorFinsupp_apply_self (hψL z₁),
        L.indicatorFinsupp_apply_of_ne _ _ (hψlt z₁).ne, sub_zero, mul_one] at hval
      exact hgS z₁ hz₁S hval
    · intro z hz hne
      by_cases hgz : g z = 0
      · rw [hgz, zero_mul]
      · have hzS : z ∈ S := Finset.mem_filter.mpr ⟨hz, hgz⟩
        rw [L.indicatorFinsupp_apply_of_ne _ _ (fun h ↦ hne (hψinj h).symm),
          L.indicatorFinsupp_apply_of_ne _ _ ((hmin z hzS).trans_lt (hψlt z)).ne, sub_zero,
          mul_zero]
    · intro h
      exact absurd hz₁s h

/-! ### Hereditary `rv_J`-independence of the blocks -/

/-- The blocks of a random series of order type `ω^n · m + β` are hereditarily
`rv_J`-independent at degree `n ≥ 1`. -/
theorem hereditarilyRVIndependent_block [CharZero K] (hn : 1 ≤ n) (hb : IsRandom b) :
    HereditarilyRVIndependent n d.block := by
  have hval : ∀ i, ordinalValue (d.block i) = ω^ (n : NatOrdinal) := fun i ↦
    ordinalValue_eq_wpow_of_isPrincipal (d.block_isPrincipal i) (d.block_degree i)
  rcases (isRandom_iff b).mp hb with hsupp | hcoeff
  · exact (d.isMutuallySupportRandom_block hsupp).hereditarilyRVIndependent hn hval
  · exact (d.isMutuallyCoefficientRandom_block hcoeff).hereditarilyRVIndependent hn hval

end BlockDecomposition

end FLLM24

end
