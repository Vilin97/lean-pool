/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import LeanPool.ConwayRefinement.ConwayRefinement.Topology.CantorBendixsonProduct
public import LeanPool.ConwayRefinement.ConwayRefinement.Topology.CantorBendixsonRank

import LeanPool.ConwayRefinement.ConwayRefinement.Blueprint

/-!
# Cantor–Bendixson bounds for addition of supports

Addition on two closed well-ordered supports is a closed map with finite fibers in an ordered
uniform group that is Cauchy complete. A point in any derivative of their sum therefore comes
from a pair whose natural sum of point ranks bounds that stage. This applies at arbitrary
ordinals and does not require addition on the supports to be injective.
-/

public noncomputable section

open Set Filter Topology TopologicalSpace
open scoped Pointwise

universe u

namespace TopologicalSpace.Closeds

variable {G : Type u} [AddCommGroup G] [LinearOrder G] [IsOrderedAddMonoid G]
  [UniformSpace G] [IsUniformAddGroup G] [OrderTopology G] [Nontrivial G] [CompleteSpace G]

/-- A point in a derivative of a sum lifts to summands with a sufficient natural sum of ranks. -/
@[blueprint "lem:cantor-bendixson-derivative-of-sum"
  (phase := "Cantor–Bendixson ranks of supports")
  (title := "Cantor--Bendixson derivatives of sums of well-ordered sets")
  (statement := /--
    Let $S,T$ be closed well-ordered subsets of a nontrivial ordered abelian
    group $G$, equipped with a compatible additive uniformity and its order
    topology, and assume that $G$ is Cauchy complete.  For every ordinal $\alpha$,
    \[
      (S+T)^{(\alpha)}\subseteq
      \left\{z:\begin{array}{l}
        z=x+y\text{ for some }x\in S, y\in T,\\
        \alpha\le
        \operatorname{rk}_S(x)\oplus\operatorname{rk}_T(y)
      \end{array}\right\}.
    \]
  -/)
  (proof := /--
    On $S\times T$, the natural sum of the two point ranks strictly decreases
    in a punctured neighbourhood of each point.  Transfinite
    Cantor--Bendixson induction therefore bounds the derivative rank on the
    product.  Addition $S\times T\to S+T$ is closed and has finite fibers;
    lifting derivatives through this map gives the stated summands and rank
    bound.
  -/)]
theorem cantorBendixson_add_subset (s t : Closeds G)
    (hs : (s : Set G).IsPWO) (ht : (t : Set G).IsPWO) (o : Ordinal.{u}) :
    ((⟨(s : Set G) + (t : Set G),
      hs.isClosed_add ht s.isClosed t.isClosed⟩ : Closeds G).cantorBendixson o : Set G) ⊆
      {z | ∃ x ∈ s, ∃ y ∈ t, x + y = z ∧
        o ≤ (NatOrdinal.of (s.cantorBendixsonRank hs x) +
          NatOrdinal.of (t.cantorBendixsonRank ht y)).val} := by
  let f : (s : Set G) ×ˢ t → G := fun p ↦ p.1.1 + p.1.2
  have hf : IsClosedMap f := hs.isClosedMap_add ht s.isClosed t.isClosed
  have himage : f '' (univ : Set ((s : Set G) ×ˢ t)) = (s : Set G) + (t : Set G) := by
    ext z
    constructor
    · rintro ⟨p, _, rfl⟩
      exact add_mem_add p.2.1 p.2.2
    · rintro ⟨x, hx, y, hy, rfl⟩
      exact ⟨⟨(x, y), hx, hy⟩, mem_univ _, rfl⟩
  have he : (⟨f '' (univ : Set ((s : Set G) ×ˢ t)), hf _ isClosed_univ⟩ : Closeds G) =
      ⟨(s : Set G) + (t : Set G), hs.isClosed_add ht s.isClosed t.isClosed⟩ :=
    Closeds.ext himage
  let r (p : (s : Set G) ×ˢ t) : NatOrdinal :=
    NatOrdinal.of (s.cantorBendixsonRank hs p.1.1) +
      NatOrdinal.of (t.cantorBendixsonRank ht p.1.2)
  have hr (p : (s : Set G) ×ˢ t) (_hp : p ∈ (⊤ : Closeds ((s : Set G) ×ˢ t))) :
      ∀ᶠ q in 𝓝 p, q ∈ (⊤ : Closeds ((s : Set G) ×ˢ t)) → q ≠ p → r q < r p := by
    have hfst : Continuous (fun q : (s : Set G) ×ˢ t ↦ q.1.1) := by fun_prop
    have hsnd : Continuous (fun q : (s : Set G) ×ˢ t ↦ q.1.2) := by fun_prop
    filter_upwards
      [hfst.continuousAt.tendsto.eventually (s.cantorBendixsonRank_locally_lt hs p.1.1),
       hsnd.continuousAt.tendsto.eventually (t.cantorBendixsonRank_locally_lt ht p.1.2)]
      with q hq1 hq2 _ hne
    change NatOrdinal.of _ + NatOrdinal.of _ < NatOrdinal.of _ + NatOrdinal.of _
    by_cases h1 : q.1.1 = p.1.1
    · have h2 : q.1.2 ≠ p.1.2 := fun h2 ↦ hne (Subtype.ext (Prod.ext h1 h2))
      rw [h1]
      apply add_lt_add_right
      exact hq2 q.2.2 h2
    · have h2 : NatOrdinal.of (t.cantorBendixsonRank ht q.1.2) ≤
          NatOrdinal.of (t.cantorBendixsonRank ht p.1.2) := by
        by_cases he2 : q.1.2 = p.1.2
        · rw [he2]
        · exact (hq2 q.2.2 he2).le
      exact add_lt_add_of_lt_of_le (hq1 q.2.1 h1) h2
  have hb := (⊤ : Closeds ((s : Set G) ×ˢ t)).cantorBendixson_subset_of_locally_lt
    (fun p ↦ (r p).val) (fun p hp ↦ (hr p hp).mono fun q hq hqt hne ↦ hq hqt hne) o
  have hlift := hf.cantorBendixson_image_subset (hs.finite_subtype_add_fiber ht) ⊤ o
  rw [show (⊤ : Closeds ((s : Set G) ×ˢ t)) =
    ⟨univ, isClosed_univ⟩ from rfl] at hlift
  change ((⟨f '' univ, hf _ isClosed_univ⟩ : Closeds G).cantorBendixson o : Set G) ⊆ _
    at hlift
  rw [he] at hlift
  intro z hz
  obtain ⟨p, hp, hpz⟩ := hlift hz
  exact ⟨p.1.1, p.2.1, p.1.2, p.2.2, hpz, hb hp⟩

end TopologicalSpace.Closeds
