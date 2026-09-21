/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import Mathlib.Topology.Algebra.IsUniformGroup.Defs
public import Mathlib.Topology.Order.Basic
public import Mathlib.Topology.UniformSpace.Cauchy

import LeanPool.ConwayRefinement.ConwayRefinement.Blueprint

/-!
# Completeness from a coinitial family and fillable cuts

An ordered abelian group need not be Cauchy complete, and the group of exponents of a Conway
normal form is a case in point: the partial sums of `∑_a ω^(-a)` over all ordinals `a` form a
Cauchy family with no limit, because a limit would need a support that is not a set. What rescues
the situation is passing to a quotient by a convex subgroup, where the positive elements acquire a
*set-indexed* coinitial family. This file records what that buys.

Suppose the positive elements of `G` admit a family `ε : ι → G` that is coinitial with room to
spare — below every positive element sits some `ε i` together with a second copy of itself — and
suppose every cut cut out by two `ι`-indexed families can be filled. Then `G` is Cauchy complete
(`completeSpace_of_coinitial_of_forall_exists_mem_cut`).

The proof is the usual centre-and-radius argument, carried out at the fixed index type `ι` so that
only cuts between two `ι`-indexed families are ever needed. Pick for each `i` a set `A i` in the
Cauchy filter of diameter below `ε i` and a point `a i` of it. Any two of these sets meet, so
`a i - ε i < a j + ε j` for all `i` and `j`; filling that cut gives a point `z` within `ε i` of
every `a i`, and then `A i` sits inside any interval around `z` of radius at least `ε i + ε i`.

For the intended application `ι` indexes a coinitial family of the quotient, the cuts are filled by
choosing representatives and taking a single surreal cut between the two resulting sets, and the
second copy of `ε i` is available because the quotient is divisible.
-/

universe u w

open Filter Set Topology Uniformity

public section

/-- Filling cuts between two `ι`-indexed families. Stated as a predicate so that the hypothesis
can be transported along a quotient before being fed to the completeness criterion. -/
def FillsCuts (ι : Type w) (G : Type u) [Preorder G] : Prop :=
  ∀ L R : ι → G, (∀ i j, L i < R j) → ∃ z, (∀ i, L i ≤ z) ∧ ∀ j, z ≤ R j

theorem fillsCuts_iff (ι : Type w) (G : Type u) [Preorder G] :
    FillsCuts ι G ↔
      ∀ L R : ι → G, (∀ i j, L i < R j) → ∃ z, (∀ i, L i ≤ z) ∧ ∀ j, z ≤ R j :=
  Iff.rfl

/-- A conditionally complete order fills every cut between nonempty families: the supremum of the
lower family is bounded above by the upper one, and lies below all of it. -/
theorem fillsCuts_of_conditionallyCompleteLinearOrder {ι : Type w} [Nonempty ι]
    {G : Type u} [ConditionallyCompleteLinearOrder G] : FillsCuts ι G := by
  intro L R hLR
  have hbdd : BddAbove (Set.range L) :=
    ⟨R (Classical.arbitrary ι), by rintro _ ⟨i, rfl⟩; exact (hLR i _).le⟩
  refine ⟨sSup (Set.range L), fun i ↦ le_csSup hbdd ⟨i, rfl⟩, fun j ↦ ?_⟩
  exact csSup_le (Set.range_nonempty L) (by rintro _ ⟨i, rfl⟩; exact (hLR i j).le)

/-- **Cut filling passes to a quotient.** A surjection that preserves `≤` and reflects `<` carries
the property of filling `ι`-indexed cuts along with it: lift the two families to representatives,
which the reflected order still separates, fill the cut upstairs, and push the filler down.

For a quotient of an ordered group by a convex subgroup the hypotheses hold, so the quotient fills
cuts as soon as the group does — which for the surreals is the simplicity theorem at sets. -/
@[blueprint "lem:cut-filling-order-reflecting-surjection"
  (phase := "A cut criterion for Cauchy completeness")
  (title := "Cut filling under monotone order-reflecting surjections")
  (statement := /--
    Let $f\colon G\twoheadrightarrow C$ be a monotone surjection of preordered
    sets that reflects strict inequalities.  If every cut between two
    $I$-indexed families in $G$ can be filled, then the same is true in $C$.
  -/)
  (proof := /--
    Choose preimages in $G$ of the two families in $C$.  Reflection of strict
    inequalities keeps the lifted families separated.  Fill their cut in
    $G$, then apply $f$; monotonicity places the image between the two original
    families.
  -/)]
theorem FillsCuts.of_surjective {ι : Type w} {G : Type u} {C : Type*} [Preorder G] [Preorder C]
    {f : G → C} (hsurj : Function.Surjective f) (hmono : Monotone f)
    (hreflect : ∀ a b : G, f a < f b → a < b) (hG : FillsCuts ι G) : FillsCuts ι C := by
  intro L R hLR
  choose l hl using fun i ↦ hsurj (L i)
  choose r hr using fun j ↦ hsurj (R j)
  obtain ⟨z, hzl, hzr⟩ := hG l r fun i j ↦ hreflect _ _ (by rw [hl, hr]; exact hLR i j)
  exact ⟨f z, fun i ↦ hl i ▸ hmono (hzl i), fun j ↦ hr j ▸ hmono (hzr j)⟩

variable {G : Type u} [AddCommGroup G] [LinearOrder G] [IsOrderedAddMonoid G]
  [UniformSpace G] [IsUniformAddGroup G] [OrderTopology G]

/-- The symmetric interval of a positive radius is an entourage. -/
theorem mem_uniformity_Ioo_of_pos {c : G} (hc : 0 < c) :
    {p : G × G | p.2 - p.1 ∈ Ioo (-c) c} ∈ 𝓤 G := by
  rw [uniformity_eq_comap_nhds_zero G]
  exact ⟨Ioo (-c) c, Ioo_mem_nhds (neg_neg_iff_pos.mpr hc) hc, subset_rfl⟩

/-- Conversely every entourage contains a symmetric interval of positive radius. -/
theorem exists_pos_Ioo_subset_of_mem_uniformity [Nontrivial G] {s : Set (G × G)}
    (hs : s ∈ 𝓤 G) : ∃ c : G, 0 < c ∧ {p : G × G | p.2 - p.1 ∈ Ioo (-c) c} ⊆ s := by
  rw [uniformity_eq_comap_nhds_zero G] at hs
  obtain ⟨W, hW, hWs⟩ := hs
  obtain ⟨x, hx⟩ := exists_ne (0 : G)
  have hpos : (0 : G) < |x| := abs_pos.mpr hx
  obtain ⟨l, u, hlu, hsub⟩ :=
    (mem_nhds_iff_exists_Ioo_subset' ⟨-|x|, neg_neg_iff_pos.mpr hpos⟩ ⟨|x|, hpos⟩).mp hW
  refine ⟨min (-l) u, lt_min (neg_pos.mpr hlu.1) hlu.2, fun p hp ↦ hWs ?_⟩
  refine hsub ⟨?_, ?_⟩
  · refine lt_of_le_of_lt ?_ hp.1
    rw [le_neg]
    exact min_le_left (-l) u
  · exact hp.2.trans_le (min_le_right (-l) u)

/-- **Completeness from a coinitial family and fillable cuts.** If the positive elements of `G`
admit a coinitial family `ε : ι → G` whose members each fit twice below any prescribed positive
element, and every cut between two `ι`-indexed families of `G` is filled, then `G` is Cauchy
complete.

Only cuts indexed by the same `ι` as the coinitial family are used, so for a quotient of the
surreals by a convex subgroup this asks for the simplicity theorem at sets, not at classes. -/
@[blueprint "lem:complete-of-coinitial-scales-and-cut-filling"
  (phase := "A cut criterion for Cauchy completeness")
  (title := "A cut criterion for Cauchy completeness")
  (statement := /--
    Let $G$ be an ordered abelian group whose order topology is induced by a
    compatible additive uniformity, and let $I$ be nonempty.  Suppose there
    are elements $\varepsilon_i>0$ such that, for every $c>0$, some $i\in I$
    satisfies
    \[
      \varepsilon_i+\varepsilon_i\le c.
    \]
    Suppose also that whenever $L_i<R_j$ for all $i,j\in I$, there is
    $z\in G$ with $L_i\le z\le R_j$ for all $i,j$.  Then $G$ is Cauchy
    complete.
  -/)
  (proof := /--
    For a Cauchy filter and each $i$, choose a set of diameter less than
    $\varepsilon_i$ and a point $a_i$ in it.  Any two chosen sets meet, so
    \[
      a_i-\varepsilon_i<a_j+\varepsilon_j
    \]
    for all $i,j$.  Fill this cut by $z$.  Every point of the $i$-th chosen
    set then lies within $\varepsilon_i+\varepsilon_i$ of $z$.  Coinitiality
    of these doubled scales shows that the filter converges to $z$.
  -/)]
theorem completeSpace_of_coinitial_of_forall_exists_mem_cut {ι : Type w} [Nonempty ι] (ε : ι → G)
    (hε : ∀ i, 0 < ε i) (hcoinitial : ∀ c : G, 0 < c → ∃ i, ε i + ε i ≤ c)
    (hcut : FillsCuts ι G) :
    CompleteSpace G := by
  refine ⟨fun {F} hF ↦ ?_⟩
  haveI : F.NeBot := hF.1
  -- a set of small diameter in `F` for each index, together with a point of it
  have hsmall : ∀ i, ∃ A ∈ F, ∃ a ∈ A, ∀ x ∈ A, x - a ∈ Ioo (-ε i) (ε i) := by
    intro i
    obtain ⟨A, hA, hAsub⟩ := (cauchy_iff.mp hF).2 _ (mem_uniformity_Ioo_of_pos (hε i))
    obtain ⟨a, ha⟩ := Filter.nonempty_of_mem hA
    exact ⟨A, hA, a, ha, fun x hx ↦ hAsub (Set.mk_mem_prod ha hx)⟩
  choose A hA a haA hdiam using hsmall
  -- the centres, offset by their radii, cut `G`: any two of the small sets meet
  have hlt : ∀ i j, a i - ε i < a j + ε j := by
    intro i j
    obtain ⟨w, hwi, hwj⟩ := Filter.nonempty_of_mem (inter_mem (hA i) (hA j))
    have h₁ : a i - ε i < w := by
      have h := (hdiam i w hwi).1
      rw [neg_lt_sub_iff_lt_add, add_comm] at h
      exact sub_lt_iff_lt_add.mpr h
    have h₂ : w < a j + ε j := by
      have h := (hdiam j w hwj).2
      rw [sub_lt_iff_lt_add, add_comm] at h
      exact h
    exact h₁.trans h₂
  obtain ⟨z, hzl, hzr⟩ := hcut _ _ hlt
  -- every point of a small set is within twice its radius of the filled point
  have hclose : ∀ i, ∀ x ∈ A i, z - (ε i + ε i) < x ∧ x < z + (ε i + ε i) := by
    intro i x hx
    have hxl := (hdiam i x hx).1
    have hxr := (hdiam i x hx).2
    constructor
    · have hstep : z - (ε i + ε i) ≤ (a i + ε i) - (ε i + ε i) :=
        sub_le_sub_right (hzr i) _
      refine hstep.trans_lt ?_
      have : a i - ε i < x := by
        rw [neg_lt_sub_iff_lt_add, add_comm] at hxl
        exact sub_lt_iff_lt_add.mpr hxl
      simpa [sub_add_eq_sub_sub, add_sub_cancel_right] using this
    · have hstep : (a i - ε i) + (ε i + ε i) ≤ z + (ε i + ε i) :=
        add_le_add (hzl i) le_rfl
      refine lt_of_lt_of_le ?_ hstep
      have : x < a i + ε i := by
        rw [sub_lt_iff_lt_add, add_comm] at hxr
        exact hxr
      simpa [sub_add_eq_add_sub, add_sub_cancel_left, ← add_assoc, sub_add_cancel] using this
  -- so the filter converges to the filled point
  refine ⟨z, fun s hs ↦ ?_⟩
  obtain ⟨i₀⟩ := ‹Nonempty ι›
  obtain ⟨l, u, hzlu, hsub⟩ :=
    (mem_nhds_iff_exists_Ioo_subset' ⟨z - ε i₀, sub_lt_self z (hε i₀)⟩
      ⟨z + ε i₀, lt_add_of_pos_right z (hε i₀)⟩).mp hs
  obtain ⟨i, hi⟩ :=
    hcoinitial (min (z - l) (u - z))
      (lt_min (sub_pos.mpr hzlu.1) (sub_pos.mpr hzlu.2))
  refine mem_of_superset (hA i) fun x hx ↦ hsub ⟨?_, ?_⟩
  · refine lt_of_le_of_lt ?_ (hclose i x hx).1
    have := hi.trans (min_le_left (z - l) (u - z))
    exact le_sub_comm.mp this
  · refine (hclose i x hx).2.trans_le ?_
    have := hi.trans (min_le_right (z - l) (u - z))
    exact add_le_of_le_sub_left this

/-- **Completeness from coinitiality, divisibility, and fillable cuts.** The form in which the
criterion is met in practice: the coinitial family is only asked to reach below every positive
element, and the second copy of each `ε i` comes from halving, which a divisible group supplies. -/
theorem completeSpace_of_coinitial_of_exists_half {ι : Type w} [Nonempty ι] (ε : ι → G)
    (hε : ∀ i, 0 < ε i) (hcoinitial : ∀ c : G, 0 < c → ∃ i, ε i ≤ c)
    (hhalf : ∀ c : G, 0 < c → ∃ d : G, 0 < d ∧ d + d ≤ c) (hcut : FillsCuts ι G) :
    CompleteSpace G := by
  refine completeSpace_of_coinitial_of_forall_exists_mem_cut ε hε (fun c hc ↦ ?_) hcut
  obtain ⟨d, hd, hdc⟩ := hhalf c hc
  obtain ⟨i, hi⟩ := hcoinitial d hd
  exact ⟨i, (add_le_add hi hi).trans hdc⟩

/-- **Completeness of a group that fills its own cuts.** Taking the positive elements themselves as
the coinitial family removes that hypothesis entirely, leaving cut filling as the sole burden.

This is the form to aim at inside a set-sized group, where a coinitial family is free but filling
cuts is not, rather than in an ambient group where the reverse holds. -/
theorem completeSpace_of_fillsCuts_pos (hpos : ∃ c : G, 0 < c)
    (hhalf : ∀ c : G, 0 < c → ∃ d : G, 0 < d ∧ d + d ≤ c)
    (hcut : FillsCuts {x : G // 0 < x} G) : CompleteSpace G := by
  obtain ⟨c₀, hc₀⟩ := hpos
  haveI : Nonempty {x : G // 0 < x} := ⟨⟨c₀, hc₀⟩⟩
  exact completeSpace_of_coinitial_of_exists_half Subtype.val (fun i ↦ i.2)
    (fun c hc ↦ ⟨⟨c, hc⟩, le_rfl⟩) hhalf hcut
