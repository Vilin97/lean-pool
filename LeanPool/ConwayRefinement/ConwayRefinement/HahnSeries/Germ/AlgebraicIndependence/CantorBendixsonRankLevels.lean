/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import
  LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.Germ.AlgebraicIndependence.TranslatedTruncationInterpolationOnSets

import LeanPool.ConwayRefinement.ConwayRefinement.Blueprint

/-!
# Cantor–Bendixson rank levels of a closed support

The interpolation theorem over an arbitrary set of centers asks for five things. This file checks
them for the exact-rank level of a single series, so that the level version is recovered, and
records the two closure facts in the form a union of levels will use: the closure of a level is the
corresponding derivative stage, and near zero a point of that derivative whose truncations have
already dropped lies in the level itself.
-/

universe u v w

open scoped NatOrdinal Topology

open Filter Set TopologicalSpace HahnSeries

public noncomputable section

namespace HahnSeries.Nonpositive

variable {G : Type u} {R : Type v}
variable [AddCommGroup G] [LinearOrder G] [IsOrderedAddMonoid G]
  [UniformSpace G] [IsUniformAddGroup G] [OrderTopology G] [Nontrivial G] [CompleteSpace G]
  [CommRing R] [NoZeroDivisors R] [CharZero R]

local notation "ν" => (cantorBendixsonDegreeValuation (G := G) (R := R))

variable (p : Nonpositive G R) (α : NatOrdinal.{u})

/-- The exact-rank level of a series, as a subset of the exponents. -/
def rankLevelSet : Set G :=
  {x | x ∈ (p : HahnSeries G R).closedSupport ∧
    (p : HahnSeries G R).closedSupport.cantorBendixsonRank
      (p : HahnSeries G R).closedSupport_isPWO x = α.val}

omit [IsUniformAddGroup G] [Nontrivial G] [CompleteSpace G] [NoZeroDivisors R]
  [CharZero R] in
theorem mem_rankLevelSet_iff {x : G} :
    x ∈ rankLevelSet p α ↔ x ∈ (p : HahnSeries G R).closedSupport ∧
      (p : HahnSeries G R).closedSupport.cantorBendixsonRank
        (p : HahnSeries G R).closedSupport_isPWO x = α.val := Iff.rfl

omit [IsUniformAddGroup G] [Nontrivial G] [CompleteSpace G] [NoZeroDivisors R]
  [CharZero R] in
/-- A level sits at or below zero, since the support does. -/
theorem rankLevelSet_subset_Iic : rankLevelSet p α ⊆ Iic 0 := fun _ hx ↦
  closure_minimal p.property isClosed_Iic ((mem_closedSupport _ _).mp hx.1)

omit [IsUniformAddGroup G] [Nontrivial G] [CompleteSpace G] [NoZeroDivisors R]
  [CharZero R] in
/-- The closure of a level is the corresponding derivative stage. -/
theorem closure_rankLevelSet :
    closure (rankLevelSet p α) =
      ((p : HahnSeries G R).closedSupport.cantorBendixson α.val : Set G) :=
  (p : HahnSeries G R).closedSupport.closure_rank_level_eq
    (p : HahnSeries G R).closedSupport_isPWO α.val

/-- **Near zero the level is recovered from its closure.** Once the truncations of the series have
dropped to the level's degree, a point of the derivative stage has exactly that rank, so it lies in
the level. -/
theorem eventually_mem_rankLevelSet_of_mem_closure (hp : ν p ≤ (α + 1 : NatOrdinal)) :
    ∀ᶠ γ in 𝓝[<] (0 : G), γ ∈ closure (rankLevelSet p α) → γ ∈ rankLevelSet p α := by
  filter_upwards [eventually_degree_translatedTruncLE_le p α hp] with γ hpγ hγ
  rw [closure_rankLevelSet] at hγ
  have hmem := ((p : HahnSeries G R).mem_support_derivative_iff γ α.val).mp hγ
  refine ⟨(mem_closedSupport _ _).mpr hmem.1, ?_⟩
  rw [← cantorBendixsonRank_eq]
  exact cantorBendixsonRank_eq_of_mem_derivative_of_degree_translatedTruncLE_le α p γ
    ((mem_closedSupport _ _).mpr hmem.1) hmem.2 hpγ

/-- The origin has dropped out of the stage two above the level's. -/
theorem notMem_cantorBendixson_add_two (hp : ν p ≤ (α + 1 : NatOrdinal)) :
    (0 : G) ∉ ((p : HahnSeries G R).closedSupport.cantorBendixson ((α.val + 1) + 1) : Set G) := by
  have hpRank : (p : HahnSeries G R).cantorBendixsonRank 0 ≤ α.val + 1 := by
    by_cases hm : 0 ∈ (p : HahnSeries G R).closedSupport
    · rw [cantorBendixsonDegreeValuation_of_mem p hm, WithBot.coe_le_coe] at hp
      have h := NatOrdinal.of.symm.monotone hp
      change NatOrdinal.val (NatOrdinal.of ((p : HahnSeries G R).cantorBendixsonRank 0)) ≤
        NatOrdinal.val (α + 1) at h
      simpa only [NatOrdinal.val_of, NatOrdinal.val_add_one] using h
    · rw [cantorBendixsonRank_eq,
        (p : HahnSeries G R).closedSupport.cantorBendixsonRank_of_notMem
          (p : HahnSeries G R).closedSupport_isPWO hm]
      exact zero_le
  intro hm
  have hr := ((p : HahnSeries G R).mem_support_derivative_iff 0 _).mp hm |>.2
  exact (not_le_of_gt (hpRank.trans_lt (lt_add_one _))) hr

omit [IsUniformAddGroup G] [Nontrivial G] [CompleteSpace G] [NoZeroDivisors R]
  [CharZero R] in
/-- **A level is discrete.** -/
theorem isDiscrete_rankLevelSet : IsDiscrete (rankLevelSet p α) :=
  (p : HahnSeries G R).closedSupport.rankLevel_isDiscrete
    (p : HahnSeries G R).closedSupport_isPWO α.val

/-- **Near zero a level stays away from every point it does not contain.** Past the cutoff where
the truncations of the series have dropped to the level's degree, a point of the derivative stage
has exactly that rank, so the level agrees there with its own closure and its complement is a
neighbourhood of every other point. -/
theorem exists_compl_rankLevelSet_mem_nhds (hp : ν p ≤ (α + 1 : NatOrdinal)) :
    ∃ η < (0 : G), ∀ x, η < x → x < 0 → x ∉ rankLevelSet p α →
      (rankLevelSet p α)ᶜ ∈ 𝓝 x := by
  obtain ⟨η, hη, hcut⟩ :=
    eventually_nhdsLT_iff_exists.mp (eventually_mem_rankLevelSet_of_mem_closure p α hp)
  refine ⟨η, hη, fun x hηx hx0 hxL ↦ ?_⟩
  have hopen : IsOpen (Ioo η 0 ∩ (closure (rankLevelSet p α))ᶜ) :=
    isOpen_Ioo.inter isClosed_closure.isOpen_compl
  have hmem : x ∈ Ioo η 0 ∩ (closure (rankLevelSet p α))ᶜ :=
    ⟨⟨hηx, hx0⟩, fun hc ↦ hxL (hcut x hηx hx0 hc)⟩
  refine Filter.mem_of_superset (hopen.mem_nhds hmem) ?_
  exact fun y hy hyL ↦ hy.2 (subset_closure hyL)

variable {B : Type w} [Finite B]

/-- **A finite family of levels is discrete above a common cutoff.** Each level is discrete, and
past its own cutoff it stays away from the points it misses; taking the largest of finitely many
cutoffs makes all of them do so at once, so the union is discrete there. -/
@[blueprint "lem:discrete-finite-union-cantor-bendixson-rank-sets"
  (phase := "Algebraic independence in graded rings")
  (title := "Discrete finite unions of Cantor--Bendixson rank sets")
  (statement := /--
    Let $G$ be a nontrivial ordered abelian group with compatible additive
    uniformity and order topology, and let $R$ be a characteristic-zero
    domain.  Assume that $G$ is Cauchy complete.  Write $\nu$ for the
    Cantor--Bendixson degree on
    $R((G^{\leq 0}))$.  For a series $q$ and an ordinal $\rho$, let
    \[
      L_\rho(q)=\{\gamma\in\overline{\operatorname{supp}(q)}:
        \operatorname{rk}_{\overline{\operatorname{supp}(q)}}(\gamma)=\rho\}.
    \]
    If $B$ is finite and $\nu(q_b)\leq\rho_b+1$ for every $b\in B$, then
    there is $\eta<0$ such that
    \[
      \bigcup_{b\in B}\bigl(L_{\rho_b}(q_b)\cap(\eta,0)\bigr)
    \]
    is discrete.
  -/)
  (proof := /--
    By \ref{thm:cantor-bendixson-value-multiplicative}, the Cantor--Bendixson
    degree is the multiplicative degree denoted by $\nu$.  Each exact-rank set
    is discrete.  Moreover, once the translated
    truncations of $q_b$ have degree at most $\rho_b$, the exact-rank set
    agrees locally with its closure.  Choose such a negative cutoff for each
    $b$ and take their maximum.  Above this common cutoff, each set has a
    neighbourhood disjoint from every other set at any point it does not
    contain.  The finite union is therefore discrete.
  -/)]
theorem exists_isDiscrete_iUnion_rankLevelSet
    (q : B → Nonpositive G R) (ρ : B → NatOrdinal.{u})
    (hq : ∀ b, ν (q b) ≤ (ρ b + 1 : NatOrdinal)) :
    ∃ η < (0 : G), IsDiscrete (⋃ b : B, rankLevelSet (q b) (ρ b) ∩ Ioo η 0) := by
  classical
  cases nonempty_fintype B
  choose ηf hηf hcut using fun b ↦ exists_compl_rankLevelSet_mem_nhds (q b) (ρ b) (hq b)
  obtain ⟨η₀, hη₀⟩ := exists_lt (0 : G)
  rcases isEmpty_or_nonempty B with hB | hB
  · refine ⟨η₀, hη₀, ?_⟩
    simp only [Set.iUnion_of_empty]
    rw [isDiscrete_iff_nhdsNE]
    simp
  have hne : ((Finset.univ : Finset B).image ηf).Nonempty :=
    (Finset.univ_nonempty (α := B)).image ηf
  set ηmax : G := ((Finset.univ : Finset B).image ηf).max' hne with hηmaxdef
  have hηmax0 : ηmax < 0 := by
    obtain ⟨b, -, hb⟩ := Finset.mem_image.mp (Finset.max'_mem _ hne)
    rw [hηmaxdef, ← hb]
    exact hηf b
  have hle : ∀ b, ηf b ≤ ηmax := fun b ↦
    Finset.le_max' _ _ (Finset.mem_image_of_mem ηf (Finset.mem_univ b))
  refine ⟨ηmax, hηmax0, ?_⟩
  have hiUnion : (⋃ b : B, rankLevelSet (q b) (ρ b) ∩ Ioo ηmax 0) =
      ⋃ b ∈ (Finset.univ : Finset B), rankLevelSet (q b) (ρ b) ∩ Ioo ηmax 0 := by
    simp
  rw [hiUnion]
  refine TopologicalSpace.Closeds.isDiscrete_biUnion _ _ (fun b _ ↦ ?_) (fun i _ j _ x hx hxi ↦ ?_)
  · exact (isDiscrete_rankLevelSet (q b) (ρ b)).mono Set.inter_subset_left
  · by_cases hxL : x ∈ rankLevelSet (q i) (ρ i)
    · have hxIoo : x ∈ Ioo ηmax 0 := hx.2
      exact absurd ⟨hxL, hxIoo⟩ hxi
    · refine Filter.mem_of_superset
        (hcut i x (lt_of_le_of_lt (hle i) hx.2.1) hx.2.2 hxL) ?_
      exact fun y hy hyi ↦ hy hyi.1

end HahnSeries.Nonpositive

end
