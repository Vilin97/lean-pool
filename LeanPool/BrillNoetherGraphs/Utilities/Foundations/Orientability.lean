/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/
module


public import LeanPool.BrillNoetherGraphs.Utilities.Foundations.AcyclicOrientation

/-!
# Orientability of degree `g - 1` divisor classes

An–Baker–Kuperberg–Shokrieh, *Canonical representatives for divisor classes on tropical
curves and the matrix–tree theorem*, calls a divisor `D` **orientable** when
`D(p) = indeg_𝒪(p) - 1` for some orientation `𝒪`, and proves in
[Theorem 4.10 of arXiv:1304.4259v2](https://arxiv.org/pdf/1304.4259v2) that **every divisor
of degree `g - 1` on a finite graph is linearly equivalent to an orientable one**.
This file proves
the finite-multigraph form in `orientable_of_deg_eq` and
`orientable_iff_deg_eq`.

## Parallel edges

`CFOrientation` is a `count_preserving` flow-count vector representing an
arbitrary edge-level orientation. Parallel edges may therefore be oriented
independently, and no simplicity hypothesis is required.

## The two halves, and how each is proved

The classes split by winnability, and the two halves are proved by unrelated arguments:

* **Unwinnable classes are orientable** — by an *acyclic* orientation. This is
  `orientable_of_not_winnable` below, a corollary of `unwinnable_iff_exists_acyclic_ordiv`
  (`Foundations/AcyclicOrientation.lean`). It was the one statement here that never needed
  simplicity even under the old model, because two parallel edges pointing opposite ways are
  themselves a directed `2`-cycle, so `no_bidirectional` discarded no acyclic orientation.
* **Winnable classes need a cyclic orientation**, and are reached by the ABKS route of §3.
  `orientable_of_forall_winnable` records the reduction to them, but it is no longer needed
  for the main theorem: §3 proves all degree-`(g−1)` classes at once.

## The ABKS route, as formalized in §3

The source's argument has two steps, and both are proved here.

1. **Hakimi's criterion** (`\label{thm:orient}`, line 744): a divisor of degree `g − 1` with
   `χ(S, D) ≥ 0` for every nonempty `S` *is* an orientation divisor, where
   `χ(S,D) = deg(D|_S) + |S| − e(S)`. Here `exists_ordiv_eq_of_chi_nonneg`.

   ABKS obtain this from max-flow/min-cut.  Section 3c takes an elementary route instead:
   with `d v = D v + 1` the target in-degree, orient the edges one
   at a time (`exists_isOrientationOf`, induction on the edge multiset), decrementing `d` at
   the head. Some direction of the chosen edge always keeps Hakimi's inequality
   `e(S) ≤ ∑_{v ∈ S} d v` alive, because a tight set separating `b` from `a` and a tight set
   separating `a` from `b` would make the cross term `e(S∖T, T∖S)` of the submodularity
   refinement both zero and at least one — the edge `ab` sits inside it. No flow theory, and
   no simplicity: `CFOrientation` is now the edge-level orientation type, so an orientation
   built edge by edge packages directly.

2. **The submodularity descent** (`\label{thm:eqiv_orient}`, line 758): every degree-`(g−1)`
   divisor is linearly equivalent to one satisfying (1). Here `exists_linear_equiv_chi_nonneg`.

   `χ(·, D)` is submodular, with the quantitative refinement
   `χ(S,D) + χ(T,D) = χ(S∪T,D) + χ(S∩T,D) + e(S∖T, T∖S)` (`eulerChi_add_eulerChi`), so its
   minimizers are closed under `∩` and `∪` (`eulerChi_inter_union_eq_chiMin`) and there is a
   minimal one, `chiMinimizer G D` (`chiMinimizer_subset`). Firing its complement raises
   every `χ(S, ·)` above `χ_D`, with equality only for `S ⊋ S₀`
   (`chiMin_le_eulerChi_set_firing`).

   ABKS then argue that the loop terminates. The formalization replaces the loop by its fixed
   point: `chiPotential = χ_D · (|V| + 1) + |S₀|` is bounded above by `|V|` and strictly
   increases at each step, so the divisor of greatest potential in the class — which exists by
   `Int.exists_greatest_of_bdd` — must already have `χ_D ≥ 0`. No well-founded recursion is
   needed.

Everything in §3a–§3b (`edgesWithinOf`, `edgesBetweenOf`, `numEdgesOf`, `edgesBetween` and
their identities) is stated for an *arbitrary* edge multiset, because step (1) removes edges;
`G.edges` is substituted only at the end.

-/

@[expose] public section

namespace Utilities

variable {G : CFGraph}

/-! ## 1. `Orientable`, and the trivial facts -/

/-- **A divisor class is orientable** when it contains the divisor of some orientation.

This is An–Baker–Kuperberg–Shokrieh's "linearly equivalent to an orientable divisor"; the
linear equivalence is built into the predicate because that is the form every consumer wants.
Since `CFOrientation` lost its `no_bidirectional` field it is the set of edge-level
orientations of `G`, multigraphs included, so this predicate now agrees with ABKS's
everywhere and not merely on simple graphs. -/
def Orientable (G : CFGraph) (D : CFDiv G) : Prop :=
  ∃ O : CFOrientation G, linearEquiv G D (ordiv G O)

/-- The acyclic refinement: the class contains the divisor of an *acyclic* orientation. By
`unwinnable_iff_exists_acyclic_ordiv` this is exactly unwinnability at degree `genus G - 1`
(`acyclicallyOrientable_iff_not_winnable`). -/
def AcyclicallyOrientable (G : CFGraph) (D : CFDiv G) : Prop :=
  ∃ O : CFOrientation G, isAcyclic G O ∧ linearEquiv G D (ordiv G O)

/-- An orientation divisor is orientable, tautologically. -/
theorem orientable_ordiv (O : CFOrientation G) : Orientable G (ordiv G O) :=
  ⟨O, linearEquiv.refl G (ordiv G O)⟩

/-- **Orientability is a property of the linear equivalence class.** -/
theorem Orientable.of_linear_equiv {D D' : CFDiv G} (h : linearEquiv G D D')
    (hD' : Orientable G D') : Orientable G D := by
  obtain ⟨O, hO⟩ := hD'
  exact ⟨O, h.trans hO⟩

/-- Orientability transported the other way, so that `Orientable` is genuinely
class-invariant. -/
theorem Orientable.congr {D D' : CFDiv G} (h : linearEquiv G D D') :
    Orientable G D ↔ Orientable G D' :=
  ⟨fun hD => Orientable.of_linear_equiv h.symm hD, fun hD' => Orientable.of_linear_equiv h hD'⟩

/-- **An orientable divisor has degree `genus G - 1`.** This is the converse half of the main
theorem, and unlike the forward half it is unconditional: it needs neither connectivity nor
simplicity, only `degree_ordiv`. -/
theorem Orientable.deg_eq {D : CFDiv G} (h : Orientable G D) : deg D = genus G - 1 := by
  obtain ⟨O, hO⟩ := h
  rw [linear_equiv_preserves_deg G D (ordiv G O) hO]
  exact degree_ordiv O

/-- An acyclically orientable divisor is orientable. -/
theorem AcyclicallyOrientable.orientable {D : CFDiv G} (h : AcyclicallyOrientable G D) :
    Orientable G D :=
  let ⟨O, _, hO⟩ := h; ⟨O, hO⟩

/-- An acyclically orientable divisor has degree `genus G - 1`. -/
theorem AcyclicallyOrientable.deg_eq {D : CFDiv G} (h : AcyclicallyOrientable G D) :
    deg D = genus G - 1 :=
  h.orientable.deg_eq

/-! ## 2. The unwinnable half, which is already done

This section never needed a simplicity hypothesis, even under the old restricted model:
`no_bidirectional` discarded no *acyclic* orientation, because two parallel edges pointing
opposite ways form a directed `2`-cycle. -/

/-- **Acyclic orientability is unwinnability**, at degree `genus G - 1`. A restatement of
`unwinnable_iff_exists_acyclic_ordiv` (`Foundations/AcyclicOrientation.lean`, `sorry`-free)
in the vocabulary of this file. -/
theorem acyclicallyOrientable_iff_not_winnable (h_conn : graphConnected G) (D : CFDiv G)
    (hDeg : deg D = genus G - 1) : AcyclicallyOrientable G D ↔ ¬ winnable G D :=
  (unwinnable_iff_exists_acyclic_ordiv h_conn D hDeg).symm

/-- **Every unwinnable class of degree `genus G - 1` is orientable, by an acyclic
orientation.**

This is the unwinnable case of ABKS Theorem 4.10, for which a *cyclic* orientation is
never needed. It predates the ABKS route of §3, which now proves every degree-`(g−1)` class.
It is kept
because it says more than `orientable_of_deg_eq` does on unwinnable classes: the witnessing
orientation is acyclic. -/
theorem orientable_of_not_winnable (h_conn : graphConnected G) (D : CFDiv G)
    (hDeg : deg D = genus G - 1) (hUnwin : ¬ winnable G D) : Orientable G D :=
  ((acyclicallyOrientable_iff_not_winnable h_conn D hDeg).mpr hUnwin).orientable

/-- **The decomposition, made explicit.** To orient every degree-`(g−1)` class it suffices to
orient the *winnable* ones; the unwinnable ones are already done by
`orientable_of_not_winnable`.

This was the reduction §2c was attacked through while the winnable case was open; §3 has
since closed that case, so the lemma is no longer on the path to `orientable_of_deg_eq`. It
still records why the winnable case was the hard one: such a class is by
`isAcyclic_iff_not_winnable_ordiv` (`Foundations/OrientationReversal.lean`) never the divisor
of an acyclic orientation, so any witness for it must be cyclic, and cyclic orientations were
precisely what `CFOrientation.no_bidirectional` failed to represent on a multigraph. -/
theorem orientable_of_forall_winnable (h_conn : graphConnected G)
    (hwin : ∀ D : CFDiv G, deg D = genus G - 1 → winnable G D → Orientable G D)
    (D : CFDiv G) (hDeg : deg D = genus G - 1) : Orientable G D := by
  by_cases hw : winnable G D
  · exact hwin D hDeg hw
  · exact orientable_of_not_winnable h_conn D hDeg hw

/-! ## 3. The ABKS route: the Euler characteristic of an induced subgraph -/

/-- `e(S)`: the number of edges of `G` with both endpoints in `S`, parallel edges counted with
multiplicity. -/
def edgesWithin (G : CFGraph) (S : Finset G.V) : ℕ :=
  Multiset.card (G.edges.filter (fun e => e.1 ∈ S ∧ e.2 ∈ S))

/-- `χ(S, D) = deg(D|_S) + |S| - e(S)` — the Euler characteristic of the induced subgraph
`G[S]` shifted by the degree of `D` restricted to `S`.

This is An–Baker–Kuperberg–Shokrieh's `χ(S,D)`
(An--Baker--Kuperberg--Shokrieh, arXiv:1304.4259), the function whose
submodularity drives the whole proof of §2c. -/
def eulerChi (G : CFGraph) (S : Finset G.V) (D : CFDiv G) : ℤ :=
  (∑ v ∈ S, D v) + (S.card : ℤ) - (edgesWithin G S : ℤ)

/-- Sanity check on the definitions, and the reason `χ(V,D) = 0 ↔ deg D = g - 1`: on the full
vertex set, `χ` measures the deviation of `deg D` from `genus G - 1`. -/
theorem eulerChi_univ (D : CFDiv G) :
    eulerChi G Finset.univ D = deg D - (genus G - 1) := by
  have hEdges : edgesWithin G Finset.univ = Multiset.card G.edges := by
    unfold edgesWithin
    congr 1
    exact Multiset.filter_eq_self.mpr (by intro e _; exact ⟨Finset.mem_univ _, Finset.mem_univ _⟩)
  have hDeg : (∑ v ∈ Finset.univ, D v) = deg D := rfl
  rw [eulerChi, hEdges, hDeg, Finset.card_univ, genus]
  ring

/-! ## 3a. Edge counts, on an arbitrary edge multiset

Hakimi's criterion is proved below by induction on the edge multiset, so both counting
functions are introduced for an arbitrary `M : Multiset (G.V × G.V)` and specialised to
`G.edges` afterwards (`edgesWithin_eq`, `numEdgesOf_edges`). `Multiset.countP` rather than
`Multiset.card ∘ Multiset.filter` is the working form: `countP_cons` is exactly the induction
step, and the whole layer is then arithmetic. -/

/-- `e_M(S)`: the number of edges of the multiset `M` with both endpoints in `S`. -/
def edgesWithinOf (M : Multiset (G.V × G.V)) (S : Finset G.V) : ℕ :=
  Multiset.countP (fun e => e.1 ∈ S ∧ e.2 ∈ S) M

/-- `e_M(S, T)`: the number of edges of `M` with one endpoint in `S` and the other in `T`. -/
def edgesBetweenOf (M : Multiset (G.V × G.V)) (S T : Finset G.V) : ℕ :=
  Multiset.countP (fun e => (e.1 ∈ S ∧ e.2 ∈ T) ∨ (e.1 ∈ T ∧ e.2 ∈ S)) M

/-- `numEdges` on an arbitrary edge multiset. -/
def numEdgesOf (M : Multiset (G.V × G.V)) (v w : G.V) : ℕ :=
  Multiset.countP (fun e => e = (v, w) ∨ e = (w, v)) M

/-- `e(S)` is `e_{E(G)}(S)`. -/
lemma edgesWithin_eq (S : Finset G.V) : edgesWithin G S = edgesWithinOf G.edges S := by
  simp only [edgesWithin, edgesWithinOf, Multiset.countP_eq_card_filter]

/-- `numEdges G v w` is `numEdgesOf G.edges v w`. -/
lemma numEdgesOf_edges (v w : G.V) : numEdgesOf G.edges v w = numEdges G v w := by
  simp only [numEdgesOf, numEdges, Multiset.countP_eq_card_filter]

/-- **The quantitative refinement of the submodularity of `e(·)`**
(`Picg_revised.tex:706`): `e(S) + e(T) + e(S∖T, T∖S) = e(S∩T) + e(S∪T)`. Proved by induction
on the edge multiset; the induction step is a sixteen-case check on which of `S`, `T` each
endpoint lies in. -/
lemma edgesWithinOf_add_edgesWithinOf (M : Multiset (G.V × G.V)) (S T : Finset G.V) :
    edgesWithinOf M S + edgesWithinOf M T + edgesBetweenOf M (S \ T) (T \ S)
      = edgesWithinOf M (S ∩ T) + edgesWithinOf M (S ∪ T) := by
  induction M using Multiset.induction_on with
  | empty => simp only [edgesWithinOf, edgesBetweenOf, Multiset.countP_zero]
  | cons e M ih =>
    obtain ⟨a, b⟩ := e
    have key : ((if a ∈ S ∧ b ∈ S then 1 else 0) + (if a ∈ T ∧ b ∈ T then 1 else 0)
        + (if (a ∈ S \ T ∧ b ∈ T \ S) ∨ (a ∈ T \ S ∧ b ∈ S \ T) then 1 else 0) : ℕ)
        = (if a ∈ S ∩ T ∧ b ∈ S ∩ T then 1 else 0)
          + (if a ∈ S ∪ T ∧ b ∈ S ∪ T then 1 else 0) := by
      simp only [Finset.mem_inter, Finset.mem_union, Finset.mem_sdiff]
      by_cases haS : a ∈ S <;> by_cases haT : a ∈ T <;> by_cases hbS : b ∈ S <;>
        by_cases hbT : b ∈ T <;> simp [haS, haT, hbS, hbT]
    simp only [edgesWithinOf, edgesBetweenOf, Multiset.countP_cons] at ih ⊢
    omega

/-- **Submodularity of `e_M(·)`**, the inequality form. -/
lemma edgesWithinOf_submodular (M : Multiset (G.V × G.V)) (S T : Finset G.V) :
    edgesWithinOf M S + edgesWithinOf M T ≤ edgesWithinOf M (S ∩ T) + edgesWithinOf M (S ∪ T) := by
  have := edgesWithinOf_add_edgesWithinOf M S T
  omega

/-- `e_M(S, T)` counts pairs, so it is symmetric. -/
lemma edgesBetweenOf_comm (M : Multiset (G.V × G.V)) (S T : Finset G.V) :
    edgesBetweenOf M S T = edgesBetweenOf M T S := by
  simp only [edgesBetweenOf]
  exact Multiset.countP_congr rfl (by intro e _; simp only [eq_iff_iff]; tauto)

/-- An indicator identity: a disjunction of two mutually exclusive conditions counts as the
sum of the two indicators. -/
private lemma ite_or_add {P Q : Prop} [Decidable P] [Decidable Q] (h : ¬ (P ∧ Q)) :
    (if P ∨ Q then (1 : ℕ) else 0) = (if P then 1 else 0) + (if Q then 1 else 0) := by
  by_cases hP : P <;> by_cases hQ : Q <;> simp_all

/-- **`e_M(S,T)` as a double sum of edge multiplicities**, for disjoint `S` and `T`. This is
the bridge between the `countP` form, in which submodularity is proved, and the
`numEdges` form, in which the effect of a set firing is computed. -/
lemma edgesBetweenOf_eq_sum (M : Multiset (G.V × G.V)) {S T : Finset G.V}
    (hST : Disjoint S T) :
    edgesBetweenOf M S T = ∑ v ∈ S, ∑ w ∈ T, numEdgesOf M v w := by
  induction M using Multiset.induction_on with
  | empty => simp only [edgesBetweenOf, numEdgesOf, Multiset.countP_zero, Finset.sum_const_zero]
  | cons e M ih =>
    obtain ⟨a, b⟩ := e
    have hne : ∀ v ∈ S, ∀ w ∈ T, v ≠ w := by
      intro v hv w hw h
      exact (Finset.disjoint_left.mp hST hv) (h ▸ hw)
    have hsplit : ∀ v ∈ S, ∀ w ∈ T,
        numEdgesOf ((a, b) ::ₘ M) v w
          = numEdgesOf M v w + ((if a = v ∧ b = w then 1 else 0)
              + (if a = w ∧ b = v then 1 else 0)) := by
      intro v hv w hw
      have hvw := hne v hv w hw
      have hex : ¬ ((a = v ∧ b = w) ∧ (a = w ∧ b = v)) := by
        rintro ⟨⟨rfl, rfl⟩, h, -⟩
        exact hvw h
      simp only [numEdgesOf, Multiset.countP_cons, Prod.mk.injEq]
      rw [ite_or_add hex]
    rw [Finset.sum_congr rfl fun v hv => Finset.sum_congr rfl fun w hw => hsplit v hv w hw]
    simp only [Finset.sum_add_distrib]
    rw [← ih]
    have h₁ : (∑ v ∈ S, ∑ w ∈ T, if a = v ∧ b = w then (1 : ℕ) else 0)
        = if a ∈ S ∧ b ∈ T then 1 else 0 := by
      by_cases haS : a ∈ S
      · rw [Finset.sum_eq_single a (fun v _ hv => Finset.sum_eq_zero fun w _ =>
          ite_eq_right (by tauto)) (fun h => absurd haS h)]
        by_cases hbT : b ∈ T
        · rw [Finset.sum_eq_single b (fun w _ hw => ite_eq_right (by tauto))
            (fun h => absurd hbT h), ite_eq_left ⟨rfl, rfl⟩, ite_eq_left ⟨haS, hbT⟩]
        · rw [Finset.sum_eq_zero fun w hw => ite_eq_right (by rintro ⟨-, rfl⟩; exact hbT hw),
            ite_eq_right (by tauto)]
      · rw [Finset.sum_eq_zero fun v hv => Finset.sum_eq_zero fun w _ =>
          ite_eq_right (by rintro ⟨rfl, -⟩; exact haS hv), ite_eq_right (by tauto)]
    have h₂ : (∑ v ∈ S, ∑ w ∈ T, if a = w ∧ b = v then (1 : ℕ) else 0)
        = if a ∈ T ∧ b ∈ S then 1 else 0 := by
      by_cases hbS : b ∈ S
      · rw [Finset.sum_eq_single b (fun v _ hv => Finset.sum_eq_zero fun w _ =>
          ite_eq_right (by tauto)) (fun h => absurd hbS h)]
        by_cases haT : a ∈ T
        · rw [Finset.sum_eq_single a (fun w _ hw => ite_eq_right (by tauto))
            (fun h => absurd haT h), ite_eq_left ⟨rfl, rfl⟩, ite_eq_left ⟨haT, hbS⟩]
        · rw [Finset.sum_eq_zero fun w hw => ite_eq_right (by rintro ⟨rfl, -⟩; exact haT hw),
            ite_eq_right (by tauto)]
      · rw [Finset.sum_eq_zero fun v hv => Finset.sum_eq_zero fun w _ =>
          ite_eq_right (by rintro ⟨-, rfl⟩; exact hbS hv), ite_eq_right (by tauto)]
    have hdisj : ¬ ((a ∈ S ∧ b ∈ T) ∧ (a ∈ T ∧ b ∈ S)) := by
      rintro ⟨⟨haS, -⟩, haT, -⟩
      exact (Finset.disjoint_left.mp hST haS) haT
    rw [h₁, h₂]
    simp only [edgesBetweenOf, Multiset.countP_cons]
    rw [ite_or_add hdisj]

/-- `e(S, T)`, as the double sum of edge multiplicities over `S × T`. For disjoint `S` and
`T` this is the number of edges with one end in each (`edgesBetweenOf_eq_sum`), which is what
makes it the right bookkeeping device for a set firing. -/
def edgesBetween (G : CFGraph) (S T : Finset G.V) : ℕ :=
  ∑ v ∈ S, ∑ w ∈ T, numEdges G v w

/-- `edgesBetween` is symmetric. -/
lemma edgesBetween_comm (S T : Finset G.V) : edgesBetween G S T = edgesBetween G T S := by
  simp only [edgesBetween]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun v _ => Finset.sum_congr rfl fun w _ => num_edges_symmetric G w v

/-- `edgesBetween` is monotone in its second argument. -/
lemma edgesBetween_mono_right {S T T' : Finset G.V} (h : T ⊆ T') :
    edgesBetween G S T ≤ edgesBetween G S T' :=
  Finset.sum_le_sum fun _ _ => Finset.sum_le_sum_of_subset h

/-- The two forms of `e(S,T)` agree on disjoint sets. -/
lemma edgesBetweenOf_edges (S T : Finset G.V) (hST : Disjoint S T) :
    edgesBetweenOf G.edges S T = edgesBetween G S T := by
  rw [edgesBetweenOf_eq_sum G.edges hST, edgesBetween]
  exact Finset.sum_congr rfl fun v _ => Finset.sum_congr rfl fun w _ => numEdgesOf_edges v w

/-! ## 3b. `eulerChi` is submodular

`χ(S,D) = deg(D|_S) + |S| - e(S)` with the first two terms modular and `-e(·)` submodular:
ABKS's Lemmas `lem:SubmodularLem` and `lem:EulerLem` (`Picg_revised.tex:694,704`). Everything
here is `edgesWithinOf_add_edgesWithinOf` plus `Finset.sum_union_inter` and
`Finset.card_union_add_card_inter`. -/

/-- `χ(∅, D) = 0`. -/
@[simp] lemma eulerChi_empty (D : CFDiv G) : eulerChi G (∅ : Finset G.V) D = 0 := by
  simp only [eulerChi, edgesWithin_eq, edgesWithinOf, Finset.sum_empty, Finset.card_empty]
  simp

/-- **The quantitative refinement of submodularity** (`Picg_revised.tex:706`,
`\label{lem:EulerLem}`): `χ(S,D) + χ(T,D) = χ(S∪T,D) + χ(S∩T,D) + e(S∖T, T∖S)`. -/
theorem eulerChi_add_eulerChi (D : CFDiv G) (S T : Finset G.V) :
    eulerChi G S D + eulerChi G T D
      = eulerChi G (S ∪ T) D + eulerChi G (S ∩ T) D
        + (edgesBetweenOf G.edges (S \ T) (T \ S) : ℤ) := by
  have hsum : (∑ v ∈ S ∪ T, D v) + (∑ v ∈ S ∩ T, D v) = (∑ v ∈ S, D v) + (∑ v ∈ T, D v) :=
    Finset.sum_union_inter
  have hcard : (S ∪ T).card + (S ∩ T).card = S.card + T.card :=
    Finset.card_union_add_card_inter S T
  have hedge := edgesWithinOf_add_edgesWithinOf G.edges S T
  simp only [eulerChi, edgesWithin_eq]
  omega

/-- **Submodularity of `χ(·, D)`** (`Picg_revised.tex:694`, `\label{lem:SubmodularLem}`). -/
theorem eulerChi_submodular (D : CFDiv G) (S T : Finset G.V) :
    eulerChi G (S ∪ T) D + eulerChi G (S ∩ T) D ≤ eulerChi G S D + eulerChi G T D := by
  have h := eulerChi_add_eulerChi D S T
  have : (0 : ℤ) ≤ (edgesBetweenOf G.edges (S \ T) (T \ S) : ℤ) := Int.natCast_nonneg _
  omega

/-- **`χ` on a disjoint union** (`Picg_revised.tex:710`, `\eqref{eq:EulerUnion}`):
`χ(S ∪ T, D) = χ(S,D) + χ(T,D) - e(S,T)`. -/
theorem eulerChi_union_of_disjoint (D : CFDiv G) {S T : Finset G.V} (h : Disjoint S T) :
    eulerChi G (S ∪ T) D = eulerChi G S D + eulerChi G T D - (edgesBetween G S T : ℤ) := by
  have hST : S \ T = S := Finset.sdiff_eq_self_of_disjoint h
  have hTS : T \ S = T := Finset.sdiff_eq_self_of_disjoint h.symm
  have hinter : S ∩ T = (∅ : Finset G.V) := Finset.disjoint_iff_inter_eq_empty.mp h
  have hmain := eulerChi_add_eulerChi D S T
  rw [hST, hTS, hinter, eulerChi_empty, edgesBetweenOf_edges S T h] at hmain
  omega

/-! ## 3c. Hakimi's criterion, by induction on the edge multiset

The classical proof of `\label{thm:orient}` goes through max-flow/min-cut. The
route taken here is elementary: orient the edges one at
a time, maintaining Hakimi's inequality for the remaining multiset. The only thing that has to
be checked is that *some* direction of the chosen edge keeps the inequality, and that is
exactly `edgesWithinOf_add_edgesWithinOf`: if a tight set separated `b` from `a` **and**
another tight set separated `a` from `b`, the cross term `e(S∖T, T∖S)` would be both `0` and
`≥ 1`, the edge `ab` itself sitting inside it.

Because the induction removes edges, everything is stated for an arbitrary edge multiset;
`G.edges` is substituted only at the very end. -/

/-- `N` **orients** the edge multiset `M` with in-degree function `d`: every parallel class of
`M` is split between the two directions, and `d v` edges of `N` point at `v`. Unfolded, this
is exactly `CFOrientation.count_preserving` together with `indeg = d`. -/
def IsOrientationOf (M N : Multiset (G.V × G.V)) (d : G.V → ℕ) : Prop :=
  (∀ v w : G.V, Multiset.count (v, w) N + Multiset.count (w, v) N = numEdgesOf M v w) ∧
    (∀ v : G.V, Multiset.countP (fun e => e.2 = v) N = d v)

/-- A loopless multiset has no edge inside a singleton. -/
lemma edgesWithinOf_singleton {M : Multiset (G.V × G.V)} (hloop : ∀ v : G.V, (v, v) ∉ M)
    (v : G.V) : edgesWithinOf M ({v} : Finset G.V) = 0 := by
  simp only [edgesWithinOf, Multiset.countP_eq_zero]
  rintro ⟨x, y⟩ he ⟨hx, hy⟩
  simp only [Finset.mem_singleton] at hx hy
  subst hx
  subst hy
  exact absurd he (hloop _)

/-- **One step of the Hakimi induction.** Given that no tight set separates `b` from `a`,
the edge `p` (which joins `a` and `b`) may be oriented `a → b`: decrementing the target
in-degree at `b` preserves Hakimi's inequality for the remaining multiset, so the inductive
hypothesis `ih` applies and the oriented edge is put back on top. -/
private lemma hakimi_step {n : ℕ}
    (ih : ∀ M : Multiset (G.V × G.V), Multiset.card M = n → (∀ v : G.V, (v, v) ∉ M) →
      ∀ d : G.V → ℕ, (∑ v : G.V, d v) = Multiset.card M →
        (∀ S : Finset G.V, edgesWithinOf M S ≤ ∑ v ∈ S, d v) → ∃ N, IsOrientationOf M N d)
    {M₀ : Multiset (G.V × G.V)} {p : G.V × G.V} {a b : G.V}
    (hp : p = (a, b) ∨ p = (b, a)) (hcard : Multiset.card M₀ = n)
    (hloop : ∀ v : G.V, (v, v) ∉ p ::ₘ M₀) (d : G.V → ℕ)
    (hsum : (∑ v : G.V, d v) = Multiset.card (p ::ₘ M₀))
    (hS : ∀ S : Finset G.V, edgesWithinOf (p ::ₘ M₀) S ≤ ∑ v ∈ S, d v)
    (hstrict : ∀ S : Finset G.V, b ∈ S → a ∉ S → edgesWithinOf (p ::ₘ M₀) S < ∑ v ∈ S, d v) :
    ∃ N, IsOrientationOf (p ::ₘ M₀) N d := by
  classical
  have hab : a ≠ b := by
    rintro rfl
    exact hloop a (by rcases hp with rfl | rfl <;> exact Multiset.mem_cons_self _ _)
  -- the two counting functions on `p ::ₘ M₀`, in terms of `M₀`
  have hcons : ∀ S : Finset G.V, edgesWithinOf (p ::ₘ M₀) S
      = edgesWithinOf M₀ S + (if a ∈ S ∧ b ∈ S then 1 else 0) := by
    intro S
    simp only [edgesWithinOf, Multiset.countP_cons]
    rcases hp with rfl | rfl
    · rfl
    · by_cases h₁ : a ∈ S <;> by_cases h₂ : b ∈ S <;> simp [h₁, h₂]
  have hconsNum : ∀ v w : G.V, numEdgesOf (p ::ₘ M₀) v w
      = numEdgesOf M₀ v w + (if (a, b) = (v, w) ∨ (a, b) = (w, v) then 1 else 0) := by
    intro v w
    simp only [numEdgesOf, Multiset.countP_cons]
    rcases hp with rfl | rfl
    · rfl
    · congr 1
      by_cases h₁ : (a, b) = (v, w) <;> by_cases h₂ : (a, b) = (w, v) <;>
        · simp only [Prod.mk.injEq] at h₁ h₂ ⊢
          simp only [h₁, and_self, or_true, ↓reduceIte, true_or, h₂, or_self, ite_eq_right_iff,
            one_ne_zero, imp_false, not_or, not_and]
          all_goals tauto
  -- the target in-degree at `b` is positive, since `{b}` is not tight
  have hdb : 1 ≤ d b := by
    have h := hstrict {b} (Finset.mem_singleton_self b) (by simpa using hab)
    have hz : edgesWithinOf (p ::ₘ M₀) ({b} : Finset G.V) = 0 :=
      edgesWithinOf_singleton hloop b
    rw [Finset.sum_singleton, hz] at h
    omega
  -- the decremented target
  set d' : G.V → ℕ := Function.update d b (d b - 1) with hd'
  have hd'S : ∀ S : Finset G.V, b ∈ S → (∑ v ∈ S, d' v) + 1 = ∑ v ∈ S, d v := by
    intro S hb
    have h₁ := Finset.add_sum_erase S d hb
    have h₂ : (∑ v ∈ S, d' v) = (d b - 1) + ∑ v ∈ S.erase b, d v := by
      rw [hd', Finset.sum_update_of_mem hb, Finset.sdiff_singleton_eq_erase]
    omega
  have hd'notMem : ∀ S : Finset G.V, b ∉ S → (∑ v ∈ S, d' v) = ∑ v ∈ S, d v := by
    intro S hb
    refine Finset.sum_congr rfl fun v hv => ?_
    rw [hd', Function.update_of_ne (by rintro rfl; exact hb hv)]
  obtain ⟨N₀, hcount₀, hindeg₀⟩ :=
    ih M₀ hcard (fun v hv => hloop v (Multiset.mem_cons_of_mem hv)) d'
      (by
        have h := hd'S Finset.univ (Finset.mem_univ b)
        rw [Multiset.card_cons] at hsum
        omega)
      (by
        intro S
        have hmain := hS S
        have hcs := hcons S
        by_cases hb : b ∈ S
        · have hsplit := hd'S S hb
          by_cases ha : a ∈ S
          · rw [ite_eq_left ⟨ha, hb⟩] at hcs
            omega
          · have := hstrict S hb ha
            rw [ite_eq_right (by tauto)] at hcs
            omega
        · rw [hd'notMem S hb]
          rw [ite_eq_right (by tauto)] at hcs
          omega)
  refine ⟨(a, b) ::ₘ N₀, fun v w => ?_, fun v => ?_⟩
  · have hex : ¬ ((a, b) = (v, w) ∧ (a, b) = (w, v)) := by
      rintro ⟨h₁, h₂⟩
      simp only [Prod.mk.injEq] at h₁ h₂
      exact hab (h₁.1.trans h₂.2.symm)
    rw [hconsNum v w, ← hcount₀ v w, ite_or_add hex, Multiset.count_cons, Multiset.count_cons]
    have e₁ : (if (v, w) = (a, b) then 1 else 0) = (if (a, b) = (v, w) then (1 : ℕ) else 0) := by
      by_cases h : (a, b) = (v, w) <;> simp [h, eq_comm]
    have e₂ : (if (w, v) = (a, b) then 1 else 0) = (if (a, b) = (w, v) then (1 : ℕ) else 0) := by
      by_cases h : (a, b) = (w, v) <;> simp [h, eq_comm]
    rw [e₁, e₂]
    omega
  · rw [Multiset.countP_cons, hindeg₀ v]
    by_cases hv : v = b
    · subst hv
      rw [hd', Function.update_self, ite_eq_left rfl]
      omega
    · rw [hd', Function.update_of_ne hv, ite_eq_right (by simpa using fun h => hv h.symm)]
      omega

/-- **Hakimi's criterion for an arbitrary edge multiset.** If `d` sums to the number of edges
and dominates `e_M(S)` on every vertex set, then `M` has an orientation with in-degree
function `d`. The induction is on the number of edges. -/
theorem exists_isOrientationOf (n : ℕ) : ∀ M : Multiset (G.V × G.V), Multiset.card M = n →
    (∀ v : G.V, (v, v) ∉ M) → ∀ d : G.V → ℕ, (∑ v : G.V, d v) = Multiset.card M →
      (∀ S : Finset G.V, edgesWithinOf M S ≤ ∑ v ∈ S, d v) → ∃ N, IsOrientationOf M N d := by
  classical
  induction n with
  | zero =>
    intro M hM _ d hsum _
    rw [Multiset.card_eq_zero] at hM
    subst hM
    have hall : ∀ v : G.V, d v = 0 := by
      have hz : (∑ v : G.V, d v) = 0 := by simpa using hsum
      exact fun v => (Finset.sum_eq_zero_iff.mp hz) v (Finset.mem_univ v)
    exact ⟨0, fun v w => by simp [numEdgesOf], fun v => by simp [hall v]⟩
  | succ n ih =>
    intro M hM hloop d hsum hS
    have hne : M ≠ 0 := by
      rintro rfl
      simp at hM
    obtain ⟨p, hpM⟩ := Multiset.exists_mem_of_ne_zero hne
    obtain ⟨M₀, rfl⟩ := Multiset.exists_cons_of_mem hpM
    obtain ⟨a, b⟩ := p
    have hcard₀ : Multiset.card M₀ = n := by
      rw [Multiset.card_cons] at hM
      omega
    by_cases hcase : ∀ S : Finset G.V, b ∈ S → a ∉ S →
        edgesWithinOf ((a, b) ::ₘ M₀) S < ∑ v ∈ S, d v
    · -- no tight set separates `b` from `a`: orient the edge `a → b`.
      exact hakimi_step ih (Or.inl rfl) hcard₀ hloop d hsum hS hcase
    · -- a tight set separates `b` from `a`, so no tight set separates `a` from `b`:
      -- orient the edge `b → a`.
      obtain ⟨S, hbS, haS, htight⟩ :
          ∃ S : Finset G.V, b ∈ S ∧ a ∉ S ∧ (∑ v ∈ S, d v) ≤ edgesWithinOf ((a, b) ::ₘ M₀) S := by
        by_contra hc
        exact hcase fun S hb ha => by
          by_contra hlt
          exact hc ⟨S, hb, ha, by omega⟩
      refine hakimi_step (a := b) (b := a) ih (Or.inr rfl) hcard₀ hloop d hsum hS ?_
      intro T haT hbT
      rcases lt_or_ge (edgesWithinOf ((a, b) ::ₘ M₀) T) (∑ v ∈ T, d v) with hlt | hge
      · exact hlt
      · exfalso
        have hmaster := edgesWithinOf_add_edgesWithinOf ((a, b) ::ₘ M₀) S T
        have hSint := hS (S ∩ T)
        have hSuni := hS (S ∪ T)
        have hSS := hS S
        have hST := hS T
        have hmod : (∑ v ∈ S ∪ T, d v) + (∑ v ∈ S ∩ T, d v) = (∑ v ∈ S, d v) + (∑ v ∈ T, d v) :=
          Finset.sum_union_inter
        have hcross : 0 < edgesBetweenOf ((a, b) ::ₘ M₀) (S \ T) (T \ S) := by
          simp only [edgesBetweenOf]
          exact Multiset.countP_pos.mpr ⟨(a, b), Multiset.mem_cons_self _ _,
            Or.inr ⟨Finset.mem_sdiff.mpr ⟨haT, haS⟩, Finset.mem_sdiff.mpr ⟨hbS, hbT⟩⟩⟩
        omega

/-- **Hakimi's criterion** (`Picg_revised.tex:744`, `\label{thm:orient}`): a divisor of degree
`genus G - 1` all of whose `χ(S, ·)` are nonnegative *is* an orientation divisor — on the
nose, not merely up to linear equivalence.

**No simplicity hypothesis, since 2026-08-20.** This is where the old model defect lived and
where the hypothesis was consumed: the classical statement produces an edge-level orientation,
and packaging one as a `CFOrientation` used to require that no parallel class be split — on
the 5-banana the divisor `(1, 2)` satisfies the criterion and was not `ordiv` of any
`CFOrientation`. With `no_bidirectional` removed, `CFOrientation` *is* the edge-level
orientation type, `(1, 2)` is realised, and the classical statement transcribes verbatim.

ABKS cite Hakimi, Schrijver Thm 61.1 and Backman Thm 7.3, and note that the statement is
equivalent to max-flow/min-cut; no flow theory is used here. The proof is
`exists_isOrientationOf`, the edge-by-edge greedy orientation, applied to `G.edges` with
target in-degree `d v = D v + 1`. The hypothesis enters twice: at `S = {v}` it says
`D v + 1 ≥ 0`, so `d` is a well-defined natural number, and at general `S` it is exactly
Hakimi's inequality `e(S) ≤ ∑_{v ∈ S} d v`. `deg D = genus G - 1` is what makes `∑ d` the
number of edges. -/
theorem exists_ordiv_eq_of_chi_nonneg (D : CFDiv G) (hDeg : deg D = genus G - 1)
    (hchi : ∀ S : Finset G.V, S.Nonempty → 0 ≤ eulerChi G S D) :
    ∃ O : CFOrientation G, D = ordiv G O := by
  classical
  -- the target in-degree, `d v = D v + 1`, is a natural number by `χ({v}, D) ≥ 0`
  have hpos : ∀ v : G.V, 0 ≤ D v + 1 := by
    intro v
    have h := hchi {v} ⟨v, Finset.mem_singleton_self v⟩
    have hz : edgesWithin G ({v} : Finset G.V) = 0 := by
      rw [edgesWithin_eq]
      exact edgesWithinOf_singleton G.loopless v
    simp only [eulerChi, Finset.sum_singleton, Finset.card_singleton, hz, Nat.cast_zero,
      Nat.cast_one, sub_zero] at h
    omega
  set d : G.V → ℕ := fun v => (D v + 1).toNat with hd
  have hdv : ∀ v : G.V, (d v : ℤ) = D v + 1 := fun v => Int.toNat_of_nonneg (hpos v)
  -- `∑ d = |E|`, since `deg D = g - 1`
  have hsum : (∑ v : G.V, d v) = Multiset.card G.edges := by
    have hZ : (∑ v : G.V, (d v : ℤ)) = (Multiset.card G.edges : ℤ) := by
      rw [Finset.sum_congr rfl fun v _ => hdv v, Finset.sum_add_distrib]
      have hdegD : (∑ v : G.V, D v) = deg D := rfl
      rw [hdegD, hDeg, genus]
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one, Finset.card_univ]
      ring
    exact_mod_cast hZ
  -- Hakimi's inequality, which for nonempty `S` is the hypothesis `χ(S, D) ≥ 0`
  have hineq : ∀ S : Finset G.V, edgesWithinOf G.edges S ≤ ∑ v ∈ S, d v := by
    intro S
    rcases S.eq_empty_or_nonempty with rfl | hne
    · simp only [edgesWithinOf, Finset.sum_empty, Nat.le_zero, Multiset.countP_eq_zero]
      rintro ⟨x, y⟩ _ ⟨hx, -⟩
      exact absurd hx (Finset.notMem_empty x)
    · have h := hchi S hne
      have hZ : (∑ v ∈ S, (d v : ℤ)) = (∑ v ∈ S, D v) + (S.card : ℤ) := by
        rw [Finset.sum_congr rfl fun v _ => hdv v, Finset.sum_add_distrib]
        simp
      simp only [eulerChi, edgesWithin_eq] at h
      have : ((edgesWithinOf G.edges S : ℕ) : ℤ) ≤ ∑ v ∈ S, (d v : ℤ) := by omega
      exact_mod_cast (by push_cast at this ⊢; exact this :
        ((edgesWithinOf G.edges S : ℕ) : ℤ) ≤ ((∑ v ∈ S, d v : ℕ) : ℤ))
  obtain ⟨N, hcount, hindeg⟩ :=
    exists_isOrientationOf (Multiset.card G.edges) G.edges rfl G.loopless d hsum hineq
  refine ⟨⟨N, fun v w => ?_⟩, ?_⟩
  · rw [← numEdgesOf_edges v w, ← hcount v w]
  · funext v
    have : indeg G ⟨N, fun v w => by rw [← numEdgesOf_edges v w, ← hcount v w]⟩ v = d v := by
      rw [indeg, ← Multiset.countP_eq_card_filter]
      exact hindeg v
    simp only [ordiv, this]
    have hv := hdv v
    omega

/-! ## 3d. Firing a set of vertices, seen by `eulerChi`

Two formulas, both instances of "chips cross the boundary of the fired set once per edge":
firing `A` **adds** `e(A, T)` to `χ(T, ·)` when `T` misses `A`, and **subtracts**
`e(Aᶜ, T)` when `T` sits inside `A`. Everything below uses only these two. -/

/-- Firing a set is a linear equivalence: `setFiring G D A - D` is the sum of the firing
vectors of the members of `A`, hence principal. -/
lemma linear_equiv_set_firing (D : CFDiv G) (A : Finset G.V) :
    linearEquiv G D (setFiring G D A) := by
  rw [set_firing_eq_add_prin_indicator_script]
  unfold linearEquiv
  rw [principal_iff_eq_prin]
  exact ⟨indicatorScript G A, by abel⟩

/-- **Firing `A` seen from outside `A`**: every edge from `A` to `T` sends one chip. -/
lemma sum_set_firing_of_disjoint (D : CFDiv G) {A T : Finset G.V} (h : Disjoint T A) :
    (∑ w ∈ T, setFiring G D A w) = (∑ w ∈ T, D w) + (edgesBetween G A T : ℤ) := by
  have hpt : ∀ w ∈ T, setFiring G D A w = D w + ∑ v ∈ A, (numEdges G v w : ℤ) := by
    intro w hw
    rw [set_firing_apply_of_not_mem G D (by
      intro hwA
      exact (Finset.disjoint_left.mp h hw) hwA)]
    congr 1
    unfold outdegreeSet
    refine Finset.sum_congr ?_ fun v _ => ?_
    · ext v
      simp
    · exact_mod_cast num_edges_symmetric G w v
  rw [Finset.sum_congr rfl hpt, Finset.sum_add_distrib, edgesBetween]
  push_cast
  rw [Finset.sum_comm]

/-- **Firing `A` seen from inside `A`**: every edge from `T` to the outside of `A` loses one
chip. -/
lemma sum_set_firing_of_subset (D : CFDiv G) {A T : Finset G.V} (h : T ⊆ A) :
    (∑ w ∈ T, setFiring G D A w) = (∑ w ∈ T, D w) - (edgesBetween G Aᶜ T : ℤ) := by
  have hpt : ∀ w ∈ T, setFiring G D A w = D w - ∑ v ∈ Aᶜ, (numEdges G v w : ℤ) := by
    intro w hw
    have hwA : w ∈ A := h hw
    rw [set_firing_apply_of_mem G D hwA]
    congr 1
    unfold outdegreeSet
    exact Finset.sum_congr rfl fun v _ => by
      exact_mod_cast num_edges_symmetric G w v
  rw [Finset.sum_congr rfl hpt, Finset.sum_sub_distrib, edgesBetween]
  push_cast
  rw [Finset.sum_comm]

/-- `χ(T, ·)` after firing `A`, for `T` disjoint from `A`. -/
lemma eulerChi_set_firing_of_disjoint (D : CFDiv G) {A T : Finset G.V} (h : Disjoint T A) :
    eulerChi G T (setFiring G D A) = eulerChi G T D + (edgesBetween G A T : ℤ) := by
  simp only [eulerChi, sum_set_firing_of_disjoint D h]
  ring

/-- `χ(T, ·)` after firing `A`, for `T` inside `A`. -/
lemma eulerChi_set_firing_of_subset (D : CFDiv G) {A T : Finset G.V} (h : T ⊆ A) :
    eulerChi G T (setFiring G D A) = eulerChi G T D - (edgesBetween G Aᶜ T : ℤ) := by
  simp only [eulerChi, sum_set_firing_of_subset D h]
  ring

/-! ## 3e. The minimum of `χ(·, D)` and its minimal minimizer -/

/-- `χ_D`, the minimum of `χ(S, D)` over *all* vertex sets. Including `∅` (where `χ = 0`) and
`V` costs nothing and removes a side condition: `χ_D ≤ 0` always, and at degree `genus G - 1`
both of those sets have `χ = 0`, so a negative minimum is automatically attained at a proper
nonempty set. -/
noncomputable def chiMin (G : CFGraph) (D : CFDiv G) : ℤ :=
  (Finset.univ : Finset (Finset G.V)).inf' ⟨(∅ : Finset G.V), Finset.mem_univ _⟩
    (fun S => eulerChi G S D)

/-- `χ_D` is a lower bound. -/
lemma chiMin_le (D : CFDiv G) (S : Finset G.V) : chiMin G D ≤ eulerChi G S D :=
  Finset.inf'_le _ (Finset.mem_univ S)

/-- `χ_D` is attained. -/
lemma exists_eulerChi_eq_chiMin (D : CFDiv G) : ∃ S : Finset G.V, eulerChi G S D = chiMin G D := by
  obtain ⟨S, -, hS⟩ :=
    Finset.exists_mem_eq_inf' (⟨(∅ : Finset G.V), Finset.mem_univ _⟩ :
      (Finset.univ : Finset (Finset G.V)).Nonempty) (fun S => eulerChi G S D)
  exact ⟨S, hS.symm⟩

/-- `χ_D ≤ 0`, because `χ(∅, D) = 0`. -/
lemma chiMin_nonpos (D : CFDiv G) : chiMin G D ≤ 0 := by
  have h := chiMin_le D (∅ : Finset G.V)
  rwa [eulerChi_empty] at h

/-- **The minimizers of `χ(·, D)` are closed under `∩` and `∪`** (`Picg_revised.tex:696`,
`\label{lem:intersection}`), by the quantitative refinement: the cross term is a nonnegative
integer and both new values are `≥ χ_D`, so all three inequalities are equalities. -/
lemma eulerChi_inter_union_eq_chiMin (D : CFDiv G) {S T : Finset G.V}
    (hS : eulerChi G S D = chiMin G D) (hT : eulerChi G T D = chiMin G D) :
    eulerChi G (S ∩ T) D = chiMin G D ∧ eulerChi G (S ∪ T) D = chiMin G D := by
  have hmaster := eulerChi_add_eulerChi D S T
  have hcross : (0 : ℤ) ≤ (edgesBetweenOf G.edges (S \ T) (T \ S) : ℤ) := Int.natCast_nonneg _
  have h₁ := chiMin_le D (S ∩ T)
  have h₂ := chiMin_le D (S ∪ T)
  constructor <;> omega

/-- The minimizer of least cardinality exists. -/
private lemma exists_min_card_minimizer (G : CFGraph) (D : CFDiv G) :
    ∃ S : Finset G.V, eulerChi G S D = chiMin G D ∧
      ∀ T : Finset G.V, eulerChi G T D = chiMin G D → S.card ≤ T.card := by
  classical
  have hne : (Finset.univ.filter (fun S : Finset G.V => eulerChi G S D = chiMin G D)).Nonempty := by
    obtain ⟨S, hS⟩ := exists_eulerChi_eq_chiMin D
    exact ⟨S, Finset.mem_filter.mpr ⟨Finset.mem_univ S, hS⟩⟩
  obtain ⟨S, hSmem, hmin⟩ := Finset.exists_min_image _ Finset.card hne
  exact ⟨S, (Finset.mem_filter.mp hSmem).2,
    fun T hT => hmin T (Finset.mem_filter.mpr ⟨Finset.mem_univ T, hT⟩)⟩

/-- **`S₀(D)`, the minimal minimizer of `χ(·, D)`** (`Picg_revised.tex:730`,
`\label{cor:minimal1}`). Defined as a minimizer of least cardinality; `chiMinimizer_subset`
shows it is contained in every other minimizer, which is what makes it *the* minimal one. -/
noncomputable def chiMinimizer (G : CFGraph) (D : CFDiv G) : Finset G.V :=
  Classical.choose (show ∃ S : Finset G.V, eulerChi G S D = chiMin G D ∧
      ∀ T : Finset G.V, eulerChi G T D = chiMin G D → S.card ≤ T.card from by
    exact exists_min_card_minimizer G D)

/-- `S₀(D)` is a minimizer. -/
lemma chiMinimizer_eq (D : CFDiv G) : eulerChi G (chiMinimizer G D) D = chiMin G D :=
  (exists_min_card_minimizer G D).choose_spec.1

/-- **`S₀(D)` is contained in every minimizer.** -/
lemma chiMinimizer_subset (D : CFDiv G) {T : Finset G.V} (hT : eulerChi G T D = chiMin G D) :
    chiMinimizer G D ⊆ T := by
  have hmin := (exists_min_card_minimizer G D).choose_spec.2
  have hinter := (eulerChi_inter_union_eq_chiMin D (chiMinimizer_eq D) hT).1
  have hcard := hmin _ hinter
  have : chiMinimizer G D ∩ T = chiMinimizer G D :=
    Finset.eq_of_subset_of_card_le Finset.inter_subset_left hcard
  exact Finset.inter_eq_left.mp this

/-! ## 3f. One descent step

`ABKS`'s Claim (`Picg_revised.tex:772`): firing the complement of `S₀(D)` produces a divisor
whose `χ` is everywhere `≥ χ_D`, with equality only on sets strictly containing `S₀(D)`. The
proof below merges their four cases into two — `S ⊆ S₀` and `S ⊄ S₀` — which is legitimate
because the empty intersection is not a special case once `χ(∅, ·) = 0 ≥ χ_D` is available. -/

/-- **ABKS's Claim.** With `S₀ = S₀(D)` and `D₁` obtained from `D` by firing `S₀ᶜ`, every
`χ(S, D₁)` is at least `χ_D`, and equals it only when `S ⊋ S₀`.

Connectivity is used exactly once, in the case `S = S₀`: it makes `e(S₀ᶜ, S₀) > 0`, which is
what turns that case's inequality into a strict one. -/
private lemma chiMin_le_eulerChi_set_firing (h_conn : graphConnected G) (D : CFDiv G)
    (hdeg : deg D = genus G - 1) (hneg : chiMin G D < 0) (S : Finset G.V) :
    chiMin G D ≤ eulerChi G S (setFiring G D (chiMinimizer G D)ᶜ) ∧
      (eulerChi G S (setFiring G D (chiMinimizer G D)ᶜ) = chiMin G D →
        chiMinimizer G D ⊂ S) := by
  classical
  set S₀ := chiMinimizer G D with hS₀def
  set D₁ := setFiring G D S₀ᶜ with hD₁def
  have hmin₀ : eulerChi G S₀ D = chiMin G D := chiMinimizer_eq D
  -- `S₀` is neither empty nor everything, so connectivity gives an edge across it
  have hS₀ne : S₀.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    rintro h
    rw [h, eulerChi_empty] at hmin₀
    omega
  have hS₀univ : S₀ ≠ Finset.univ := by
    rintro h
    rw [h, eulerChi_univ, hdeg] at hmin₀
    omega
  have hcross : 0 < edgesBetween G S₀ᶜ S₀ := by
    obtain ⟨v, hv⟩ := hS₀ne
    obtain ⟨w, hw⟩ : ∃ w : G.V, w ∉ S₀ := by
      by_contra hc
      exact hS₀univ (Finset.eq_univ_iff_forall.mpr (by simpa using hc))
    obtain ⟨x, hx, y, hy, hpos⟩ := h_conn S₀ ⟨v, w, hv, hw⟩
    calc 0 < numEdges G y x := by rw [num_edges_symmetric]; exact hpos
      _ ≤ ∑ u ∈ S₀, numEdges G y u :=
          Finset.single_le_sum (fun u _ => Nat.zero_le _) hx
      _ ≤ edgesBetween G S₀ᶜ S₀ :=
          Finset.single_le_sum (f := fun z => ∑ u ∈ S₀, numEdges G z u)
            (fun z _ => Nat.zero_le _) (Finset.mem_compl.mpr hy)
  by_cases hsub : S ⊆ S₀
  · -- **Case A**: `S ⊆ S₀`. Firing `S₀ᶜ` can only add chips to `S`, and `S₀` is minimal.
    have hdisj : Disjoint S S₀ᶜ :=
      Finset.disjoint_left.mpr fun x hx hx' => (Finset.mem_compl.mp hx') (hsub hx)
    have hchi : eulerChi G S D₁ = eulerChi G S D + (edgesBetween G S₀ᶜ S : ℤ) :=
      eulerChi_set_firing_of_disjoint D hdisj
    have hstrict : chiMin G D < eulerChi G S D₁ := by
      by_cases hSeq : S = S₀
      · subst hSeq
        rw [hchi, hmin₀]
        have : (0 : ℤ) < (edgesBetween G S₀ᶜ S₀ : ℤ) := by exact_mod_cast hcross
        omega
      · have hgt : chiMin G D < eulerChi G S D := by
          rcases eq_or_lt_of_le (chiMin_le D S) with heq | hlt
          · exact absurd (Finset.Subset.antisymm hsub (chiMinimizer_subset D heq.symm)) hSeq
          · exact hlt
        have : (0 : ℤ) ≤ (edgesBetween G S₀ᶜ S : ℤ) := Int.natCast_nonneg _
        omega
    exact ⟨le_of_lt hstrict, fun heq => absurd heq (by omega)⟩
  · -- **Case B**: `S ⊄ S₀`. Split `S` into `A = S ∩ S₀` and the nonempty `B = S ∖ S₀`.
    set A := S ∩ S₀ with hAdef
    set B := S \ S₀ with hBdef
    have hAB : A ∪ B = S := by
      ext x
      simp only [hAdef, hBdef, Finset.mem_union, Finset.mem_inter, Finset.mem_sdiff]
      tauto
    have hABdisj : Disjoint A B :=
      Finset.disjoint_left.mpr fun x hx hx' => (Finset.mem_sdiff.mp hx').2 (Finset.mem_inter.mp hx).2
    have hAsub : A ⊆ S₀ := Finset.inter_subset_right
    have hBsub : B ⊆ S₀ᶜ := fun x hx => Finset.mem_compl.mpr (Finset.mem_sdiff.mp hx).2
    have hBS₀ : Disjoint B S₀ :=
      Finset.disjoint_left.mpr fun x hx hx' => (Finset.mem_sdiff.mp hx).2 hx'
    -- `χ(B, D₁) = χ(B ∪ S₀, D) - χ_D ≥ 0`
    have hB₁ : eulerChi G B D₁ = eulerChi G (B ∪ S₀) D - chiMin G D := by
      have h₁ : eulerChi G B D₁ = eulerChi G B D - (edgesBetween G (S₀ᶜ)ᶜ B : ℤ) :=
        eulerChi_set_firing_of_subset D hBsub
      have h₂ := eulerChi_union_of_disjoint D hBS₀
      rw [compl_compl] at h₁
      rw [edgesBetween_comm] at h₁
      omega
    have hB₁nonneg : 0 ≤ eulerChi G B D₁ := by
      have := chiMin_le D (B ∪ S₀)
      omega
    -- `χ(A, D₁) = χ(A, D) + e(S₀ᶜ, A)`, and `e(A, B) ≤ e(S₀ᶜ, A)`
    have hA₁ : eulerChi G A D₁ = eulerChi G A D + (edgesBetween G S₀ᶜ A : ℤ) :=
      eulerChi_set_firing_of_disjoint D
        (Finset.disjoint_left.mpr fun x hx hx' => (Finset.mem_compl.mp hx') (hAsub hx))
    have hABle : edgesBetween G A B ≤ edgesBetween G S₀ᶜ A :=
      le_trans (edgesBetween_mono_right hBsub) (le_of_eq (edgesBetween_comm A S₀ᶜ))
    have hABleZ : ((edgesBetween G A B : ℕ) : ℤ) ≤ ((edgesBetween G S₀ᶜ A : ℕ) : ℤ) := by
      exact_mod_cast hABle
    have hunion : eulerChi G S D₁
        = eulerChi G A D₁ + eulerChi G B D₁ - (edgesBetween G A B : ℤ) := by
      rw [← hAB]
      exact eulerChi_union_of_disjoint D₁ hABdisj
    have hkey : eulerChi G A D ≤ eulerChi G S D₁ := by omega
    refine ⟨le_trans (chiMin_le D A) hkey, fun heq => ?_⟩
    have hAmin : eulerChi G A D = chiMin G D :=
      le_antisymm (by omega) (chiMin_le D A)
    have hS₀A : S₀ ⊆ A := chiMinimizer_subset D hAmin
    exact Finset.ssubset_def.mpr ⟨le_trans hS₀A Finset.inter_subset_left, hsub⟩

/-- The termination measure: `χ_D` weighted so that a unit gain in the minimum beats any
change in `|S₀(D)|`, plus `|S₀(D)|` itself. It is bounded above by `|V|` (as `χ_D ≤ 0` and
`|S₀| ≤ |V|`) and strictly increases at every descent step, which is why the descent stops. -/
noncomputable def chiPotential (G : CFGraph) (D : CFDiv G) : ℤ :=
  chiMin G D * (Fintype.card G.V + 1) + (chiMinimizer G D).card

/-- The potential is bounded above by `|V|`. -/
lemma chiPotential_le (D : CFDiv G) : chiPotential G D ≤ Fintype.card G.V := by
  have h1 : chiMin G D ≤ 0 := chiMin_nonpos D
  have h2 : ((chiMinimizer G D).card : ℤ) ≤ (Fintype.card G.V : ℤ) := by
    exact_mod_cast (chiMinimizer G D).card_le_univ.trans_eq Finset.card_univ
  have h3 : (0 : ℤ) ≤ (Fintype.card G.V : ℤ) + 1 := by positivity
  have h4 : chiMin G D * ((Fintype.card G.V : ℤ) + 1) ≤ 0 * ((Fintype.card G.V : ℤ) + 1) :=
    mul_le_mul_of_nonneg_right h1 h3
  rw [zero_mul] at h4
  simp only [chiPotential]
  linarith

/-- **The descent step strictly increases the potential.** Either the minimum goes up (worth
`|V| + 1`, more than any possible loss in `|S₀|`), or it stays put and `S₀` strictly grows. -/
private lemma chiPotential_lt (h_conn : graphConnected G) (D : CFDiv G)
    (hdeg : deg D = genus G - 1) (hneg : chiMin G D < 0) :
    chiPotential G D < chiPotential G (setFiring G D (chiMinimizer G D)ᶜ) := by
  classical
  set D₁ := setFiring G D (chiMinimizer G D)ᶜ with hD₁def
  have hclaim := chiMin_le_eulerChi_set_firing h_conn D hdeg hneg
  have hmin₁ : chiMin G D ≤ chiMin G D₁ := by
    rw [← chiMinimizer_eq D₁]
    exact (hclaim (chiMinimizer G D₁)).1
  have hcard₀ : ((chiMinimizer G D).card : ℤ) ≤ (Fintype.card G.V : ℤ) := by
    exact_mod_cast (chiMinimizer G D).card_le_univ.trans_eq Finset.card_univ
  have hcard₁ : (0 : ℤ) ≤ ((chiMinimizer G D₁).card : ℤ) := Int.natCast_nonneg _
  rcases eq_or_lt_of_le hmin₁ with heq | hlt
  · -- the minimum is unchanged: `S₀(D) ⊊ S₀(D₁)`
    have hss : chiMinimizer G D ⊂ chiMinimizer G D₁ :=
      (hclaim (chiMinimizer G D₁)).2 (by rw [chiMinimizer_eq D₁, heq])
    have : ((chiMinimizer G D).card : ℤ) < ((chiMinimizer G D₁).card : ℤ) := by
      exact_mod_cast Finset.card_lt_card hss
    simp only [chiPotential, heq]
    linarith
  · -- the minimum strictly increases
    have hstep : (chiMin G D + 1) * ((Fintype.card G.V : ℤ) + 1)
        ≤ chiMin G D₁ * ((Fintype.card G.V : ℤ) + 1) :=
      mul_le_mul_of_nonneg_right hlt (by positivity)
    rw [add_mul, one_mul] at hstep
    simp only [chiPotential]
    linarith

/-- **The submodularity descent** (`Picg_revised.tex:758`, `\label{thm:eqiv_orient}`): every
divisor of degree `genus G - 1` is linearly equivalent to one satisfying Hakimi's criterion.

No simplicity hypothesis: this step never mentions orientations, only `eulerChi` and set
firing.

ABKS run the descent as a loop and argue that it terminates. Here the loop is replaced by its
fixed point: `chiPotential` is bounded above by `|V|`, so among all divisors in the class
there is one of greatest potential (`Int.exists_greatest_of_bdd`), and `chiPotential_lt` says
that a divisor with `χ_D < 0` is never of greatest potential. Hence the maximiser has
`χ_D ≥ 0`, which is Hakimi's criterion. -/
theorem exists_linear_equiv_chi_nonneg (h_conn : graphConnected G) (D : CFDiv G)
    (hDeg : deg D = genus G - 1) :
    ∃ D' : CFDiv G, linearEquiv G D D' ∧ ∀ S : Finset G.V, S.Nonempty → 0 ≤ eulerChi G S D' := by
  classical
  have hbdd : ∃ b : ℤ, ∀ z : ℤ,
      (∃ D' : CFDiv G, linearEquiv G D D' ∧ chiPotential G D' = z) → z ≤ b := by
    refine ⟨(Fintype.card G.V : ℤ), ?_⟩
    rintro z ⟨D', -, rfl⟩
    exact chiPotential_le D'
  obtain ⟨z, ⟨D', hequiv, hz⟩, hmax⟩ :=
    Int.exists_greatest_of_bdd hbdd ⟨chiPotential G D, D, linearEquiv.refl G D, rfl⟩
  have hdeg' : deg D' = genus G - 1 := by
    rw [← linear_equiv_preserves_deg G D D' hequiv]
    exact hDeg
  rcases lt_or_ge (chiMin G D') 0 with hneg | hpos
  · exfalso
    have hlt := chiPotential_lt h_conn D' hdeg' hneg
    have hle : chiPotential G (setFiring G D' (chiMinimizer G D')ᶜ) ≤ z :=
      hmax _ ⟨setFiring G D' (chiMinimizer G D')ᶜ,
        hequiv.trans (linear_equiv_set_firing D' _), rfl⟩
    omega
  · exact ⟨D', hequiv, fun S _ => le_trans hpos (chiMin_le D' S)⟩

/-! ## 4. The main statement -/

/-- **ABKS Theorem 4.10** ([arXiv:1304.4259v2](https://arxiv.org/pdf/1304.4259v2)).
On a connected graph, simple or not, every divisor
of degree `genus G - 1` is linearly equivalent to `ordiv G O` for some orientation `O`.

The simplicity hypothesis this theorem used to carry (it was called
`orientable_of_deg_eq_of_simple`) was an artefact of `CFOrientation.no_bidirectional` and has
been deleted with it; see the module docstring.

Proved by composing the two halves of the ABKS route: `exists_linear_equiv_chi_nonneg` (the
submodularity descent) moves the class to a representative satisfying Hakimi's criterion, and
`exists_ordiv_eq_of_chi_nonneg` (Hakimi) turns that representative into an orientation on the
nose. The unwinnable case also has an independent proof with an *acyclic* witness — see
`orientable_of_not_winnable`. -/
theorem orientable_of_deg_eq (h_conn : graphConnected G) (D : CFDiv G)
    (hDeg : deg D = genus G - 1) : Orientable G D := by
  obtain ⟨D', hEquiv, hchi⟩ := exists_linear_equiv_chi_nonneg h_conn D hDeg
  have hDeg' : deg D' = genus G - 1 := by
    rw [← linear_equiv_preserves_deg G D D' hEquiv]; exact hDeg
  obtain ⟨O, hO⟩ := exists_ordiv_eq_of_chi_nonneg D' hDeg' hchi
  exact ⟨O, by rw [← hO]; exact hEquiv⟩

/-- **§2c as a biconditional.** On a connected graph the orientable divisors are exactly the
divisors of degree `genus G - 1`. The `→` direction is unconditional (`Orientable.deg_eq`);
only `←` needs connectivity. -/
theorem orientable_iff_deg_eq (h_conn : graphConnected G) (D : CFDiv G) :
    Orientable G D ↔ deg D = genus G - 1 :=
  ⟨Orientable.deg_eq, orientable_of_deg_eq h_conn D⟩

end Utilities
