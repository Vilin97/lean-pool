/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Stirling
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Combinatorics.Pigeonhole
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.Coloring.EdgeLabeling
import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Superexponential lower bounds for multicolor triangle Ramsey numbers

Source: url:https://github.com/openai/ten-proofs
Authors: OpenAI
Status: verified
Main declarations: `ErdosProblems.MulticolourTriangleRamsey.erdos_problem_183_explicit`
Tags: extremal-combinatorics, ramsey-theory, graph-coloring, erdos-problems
MSC: 05D10, 05C55
-/

namespace ErdosProblems.MulticolourTriangleRamsey

open Filter Finset SimpleGraph
open scoped Topology

/-- An edge coloring in which every color class is triangle-free. -/
def TriangleFree {n k : ℕ}
    (C : SimpleGraph.TopEdgeLabeling (Fin n) (Fin k)) : Prop :=
  ∀ colour : Fin k, (C.labelGraph colour).CliqueFree 3

theorem labelGraph_pullback_embedding {U V K : Type*}
    (C : SimpleGraph.TopEdgeLabeling V K)
    (f : U ↪ V) (colour : K) :
    (C.pullback f).labelGraph colour = (C.labelGraph colour).comap f := by
  ext x y
  change
    ((C.pullback f).labelGraph colour).Adj x y ↔
      (C.labelGraph colour).Adj (f x) (f y)
  constructor
  · intro hadj
    obtain ⟨hxy, hcolour⟩ :=
      (SimpleGraph.TopEdgeLabeling.labelGraph_adj x y).mp hadj
    apply (SimpleGraph.TopEdgeLabeling.labelGraph_adj (f x) (f y)).mpr
    refine ⟨f.injective.ne hxy, ?_⟩
    simpa [SimpleGraph.EdgeLabeling.get,
      SimpleGraph.EdgeLabeling.pullback, SimpleGraph.Hom.mapEdgeSet] using hcolour
  · intro hadj
    obtain ⟨hxy, hcolour⟩ :=
      (SimpleGraph.TopEdgeLabeling.labelGraph_adj (f x) (f y)).mp hadj
    apply (SimpleGraph.TopEdgeLabeling.labelGraph_adj x y).mpr
    refine ⟨fun heq => hxy (congrArg f heq), ?_⟩
    simpa [SimpleGraph.EdgeLabeling.get,
      SimpleGraph.EdgeLabeling.pullback, SimpleGraph.Hom.mapEdgeSet] using hcolour

theorem cliqueFree_pullback_embedding {U V K : Type*}
    (C : SimpleGraph.TopEdgeLabeling V K)
    (f : U ↪ V)
    (hC : ∀ colour : K, (C.labelGraph colour).CliqueFree 3) :
    ∀ colour : K, ((C.pullback f).labelGraph colour).CliqueFree 3 := by
  intro colour T hT
  have hmap :
      ((C.pullback f).labelGraph colour).map f ≤ C.labelGraph colour := by
    rw [labelGraph_pullback_embedding]
    exact SimpleGraph.map_comap_le f (C.labelGraph colour)
  exact hC colour (T.map f) (hT.map.mono hmap)

theorem colorable_pullback_embedding {U V K : Type*} {j : ℕ}
    (C : SimpleGraph.TopEdgeLabeling V K)
    (f : U ↪ V) (colour : K)
    (hC : (C.labelGraph colour).Colorable j) :
    ((C.pullback f).labelGraph colour).Colorable j := by
  obtain ⟨label⟩ := hC
  refine ⟨SimpleGraph.Coloring.mk (fun u => label (f u)) ?_⟩
  intro u v hadj
  apply label.valid
  rw [labelGraph_pullback_embedding] at hadj
  exact hadj

theorem cliqueFree_compRight_embedding {V K K' : Type*}
    (C : SimpleGraph.TopEdgeLabeling V K)
    (e : K ↪ K')
    (hC : ∀ colour : K, (C.labelGraph colour).CliqueFree 3) :
    ∀ colour : K', ((C.compRight e).labelGraph colour).CliqueFree 3 := by
  classical
  intro colour T hT
  obtain ⟨x, y, z, hxy, hxz, hyz, _⟩ :=
    (SimpleGraph.is3Clique_iff).mp hT
  obtain ⟨hxyne, hxycolour⟩ :=
    (SimpleGraph.TopEdgeLabeling.labelGraph_adj x y).mp hxy
  change e (C.get x y hxyne) = colour at hxycolour
  let old : K := C.get x y hxyne
  have reflect {u v : V}
      (hadj : ((C.compRight e).labelGraph colour).Adj u v) :
      (C.labelGraph old).Adj u v := by
    obtain ⟨hne, hcolour⟩ :=
      (SimpleGraph.TopEdgeLabeling.labelGraph_adj u v).mp hadj
    change e (C.get u v hne) = colour at hcolour
    apply (SimpleGraph.TopEdgeLabeling.labelGraph_adj u v).mpr
    refine ⟨hne, ?_⟩
    exact e.injective (hcolour.trans hxycolour.symm)
  exact hC old {x, y, z}
    ((SimpleGraph.is3Clique_triple_iff).mpr
      ⟨reflect hxy, reflect hxz, reflect hyz⟩)

/-- Identifies all colors except one distinguished color with `Fin k`. -/
noncomputable def omittedColourEquiv (k : ℕ) (omitted : Fin (k + 1)) :
    {colour : Fin (k + 1) // colour ≠ omitted} ≃ Fin k := by
  classical
  apply Fintype.equivFinOfCardEq
  rw [Fintype.card_subtype_compl (fun colour : Fin (k + 1) =>
    colour = omitted)]
  simp

/-- Identifies the colors outside a palette of size `t` with `Fin (N - t)`. -/
noncomputable def activeColourEquiv (N t : ℕ) (P : Finset (Fin N))
    (hP : P.card = t) :
    Fin (N - t) ≃ {colour : Fin N // colour ∉ P} := by
  classical
  refine (Fintype.equivFinOfCardEq ?_).symm
  rw [Fintype.card_subtype_compl (fun colour : Fin N => colour ∈ P)]
  simp [Fintype.card_subtype, hP]

/-- The reduced-palette index of an active color. -/
noncomputable def activeColourPreimage (N t : ℕ) (P : Finset (Fin N))
    (hP : P.card = t) (colour : Fin N) (hactive : colour ∉ P) :
    Fin (N - t) :=
  (activeColourEquiv N t P hP).symm ⟨colour, hactive⟩

/-- Relabels a coloring on the active colors into the full palette. -/
noncomputable def paletteRelabel {V : Type*} {N t : ℕ}
    (C : SimpleGraph.TopEdgeLabeling V (Fin (N - t)))
    (P : Finset (Fin N)) (hP : P.card = t) :
    SimpleGraph.TopEdgeLabeling V (Fin N) :=
  C.compRight (fun colour => (activeColourEquiv N t P hP colour).val)

theorem paletteRelabel_adj_iff {V : Type*} {N t : ℕ}
    (C : SimpleGraph.TopEdgeLabeling V (Fin (N - t)))
    (P : Finset (Fin N)) (hP : P.card = t)
    (colour : Fin N) (hactive : colour ∉ P) (u v : V) :
    ((paletteRelabel C P hP).labelGraph colour).Adj u v ↔
      (C.labelGraph (activeColourPreimage N t P hP colour hactive)).Adj u v := by
  constructor
  · intro hadj
    obtain ⟨hne, hcolour⟩ :=
      (SimpleGraph.TopEdgeLabeling.labelGraph_adj u v).mp hadj
    apply (SimpleGraph.TopEdgeLabeling.labelGraph_adj u v).mpr
    refine ⟨hne, ?_⟩
    apply (activeColourEquiv N t P hP).injective
    apply Subtype.ext
    simpa [paletteRelabel, activeColourPreimage] using hcolour
  · intro hadj
    obtain ⟨hne, hcolour⟩ :=
      (SimpleGraph.TopEdgeLabeling.labelGraph_adj u v).mp hadj
    apply (SimpleGraph.TopEdgeLabeling.labelGraph_adj u v).mpr
    refine ⟨hne, ?_⟩
    change (activeColourEquiv N t P hP (C.get u v hne)).val = colour
    have heq := congrArg
      (fun old => (activeColourEquiv N t P hP old).val) hcolour
    simpa [activeColourPreimage] using heq

theorem paletteRelabel_missing_no_adj {V : Type*} {N t : ℕ}
    (C : SimpleGraph.TopEdgeLabeling V (Fin (N - t)))
    (P : Finset (Fin N)) (hP : P.card = t)
    (colour : Fin N) (hmissing : colour ∈ P) (u v : V) :
    ¬ ((paletteRelabel C P hP).labelGraph colour).Adj u v := by
  intro hadj
  obtain ⟨hne, hcolour⟩ :=
    (SimpleGraph.TopEdgeLabeling.labelGraph_adj u v).mp hadj
  have hnot : (paletteRelabel C P hP).get u v hne ∉ P :=
    (activeColourEquiv N t P hP (C.get u v hne)).property
  rw [hcolour] at hnot
  exact hnot hmissing

/-- A proper vertex label inside one active-color block. -/
noncomputable def paletteBlockLabel {V : Type*} {N t j : ℕ}
    (C : SimpleGraph.TopEdgeLabeling V (Fin (N - t)))
    (hC : ∀ colour : Fin (N - t), (C.labelGraph colour).Colorable j)
    (P : Finset (Fin N)) (hP : P.card = t)
    (colour : Fin N) (hactive : colour ∉ P) : V → Fin j :=
  fun v =>
    (Classical.choice
      (hC (activeColourPreimage N t P hP colour hactive))) v

theorem paletteBlockLabel_valid {V : Type*} {N t j : ℕ}
    (C : SimpleGraph.TopEdgeLabeling V (Fin (N - t)))
    (hC : ∀ colour : Fin (N - t), (C.labelGraph colour).Colorable j)
    (P : Finset (Fin N)) (hP : P.card = t)
    (colour : Fin N) (hactive : colour ∉ P) (u v : V)
    (hadj : ((paletteRelabel C P hP).labelGraph colour).Adj u v) :
    paletteBlockLabel C hC P hP colour hactive u ≠
      paletteBlockLabel C hC P hP colour hactive v := by
  have hold := (paletteRelabel_adj_iff C P hP colour hactive u v).mp hadj
  exact (Classical.choice
    (hC (activeColourPreimage N t P hP colour hactive))).valid hold

theorem paletteRelabel_cliqueFree {V : Type*} {N t : ℕ}
    (C : SimpleGraph.TopEdgeLabeling V (Fin (N - t)))
    (hC : ∀ colour : Fin (N - t), (C.labelGraph colour).CliqueFree 3)
    (P : Finset (Fin N)) (hP : P.card = t) (colour : Fin N) :
    ((paletteRelabel C P hP).labelGraph colour).CliqueFree 3 := by
  classical
  by_cases hactive : colour ∈ P
  · intro T hT
    obtain ⟨u, v, _, huv, _, _, _⟩ :=
      (SimpleGraph.is3Clique_iff).mp hT
    exact paletteRelabel_missing_no_adj C P hP colour hactive u v huv
  · have hgraph :
        (paletteRelabel C P hP).labelGraph colour =
          C.labelGraph (activeColourPreimage N t P hP colour hactive) := by
      ext u v
      exact paletteRelabel_adj_iff C P hP colour hactive u v
    rw [hgraph]
    exact hC _

/-- Deletes a color that is unused by an edge coloring. -/
noncomputable def deleteUnusedColour {V : Type*} {k : ℕ}
    (C : SimpleGraph.TopEdgeLabeling V (Fin (k + 1)))
    (omitted : Fin (k + 1))
    (hunused : ∀ edge : (⊤ : SimpleGraph V).edgeSet, C edge ≠ omitted) :
    SimpleGraph.TopEdgeLabeling V (Fin k) :=
  fun edge => omittedColourEquiv k omitted ⟨C edge, hunused edge⟩

theorem triangleFree_deleteUnusedColour {n k : ℕ}
    (C : SimpleGraph.TopEdgeLabeling (Fin n) (Fin (k + 1)))
    (omitted : Fin (k + 1))
    (hunused : ∀ edge : (⊤ : SimpleGraph (Fin n)).edgeSet,
      C edge ≠ omitted)
    (hC : TriangleFree C) :
    TriangleFree (deleteUnusedColour C omitted hunused) := by
  classical
  intro colour t ht
  let lifted : Fin (k + 1) :=
    ((omittedColourEquiv k omitted).symm colour).val
  have hmono :
      (deleteUnusedColour C omitted hunused).labelGraph colour ≤
        C.labelGraph lifted := by
    intro x y hadj
    obtain ⟨hxy, hcolour⟩ :=
      (SimpleGraph.TopEdgeLabeling.labelGraph_adj x y).mp hadj
    apply (SimpleGraph.TopEdgeLabeling.labelGraph_adj x y).mpr
    refine ⟨hxy, ?_⟩
    change
      omittedColourEquiv k omitted
        ⟨C.get x y hxy, hunused ⟨s(x, y), hxy⟩⟩ = colour at hcolour
    have hvalue := congrArg
      (fun c : Fin k => ((omittedColourEquiv k omitted).symm c).val)
      hcolour
    simpa [lifted] using hvalue
  exact hC lifted t (ht.mono hmono)

/-- Every `k`-coloring of the complete graph on `n` vertices has a monochromatic triangle. -/
def ForcesMonochromaticTriangle (n k : ℕ) : Prop :=
  ∀ C : SimpleGraph.TopEdgeLabeling (Fin n) (Fin k), ¬ TriangleFree C

theorem forcesMonochromaticTriangle_mono {m n k : ℕ}
    (hmn : m ≤ n) (hm : ForcesMonochromaticTriangle m k) :
    ForcesMonochromaticTriangle n k := by
  intro C hC
  exact hm (C.pullback (Fin.castLEEmb hmn))
    (cliqueFree_pullback_embedding C (Fin.castLEEmb hmn) hC)

theorem forcesMonochromaticTriangle_zero :
    ForcesMonochromaticTriangle 2 0 := by
  intro C _
  exact Fin.elim0 (C.get (0 : Fin 2) (1 : Fin 2) (by decide))

theorem forcesMonochromaticTriangle_succ {n k : ℕ}
    (hn : ForcesMonochromaticTriangle n k) :
    ForcesMonochromaticTriangle (1 + (k + 1) * n) (k + 1) := by
  classical
  intro C hC
  let root : Fin (1 + (k + 1) * n) := ⟨0, by omega⟩
  let others : Finset (Fin (1 + (k + 1) * n)) :=
    Finset.univ.erase root
  let edgeColour : Fin (1 + (k + 1) * n) → Fin (k + 1) :=
    fun v => if h : root ≠ v then C.get root v h else 0
  have hothers : others.card = (k + 1) * n := by
    simp [others]
  have hpigeon :
      (Finset.univ : Finset (Fin (k + 1))).card * n ≤ others.card := by
    simp [hothers]
  obtain ⟨omitted, _, hfiber⟩ :=
    Finset.exists_le_card_fiber_of_mul_le_card_of_maps_to
      (f := edgeColour) (s := others)
      (t := (Finset.univ : Finset (Fin (k + 1))))
      (fun _ _ => Finset.mem_univ _)
      (Finset.univ_nonempty) hpigeon
  let fiber := others.filter (fun v => edgeColour v = omitted)
  have hlarge : n ≤ fiber.card := by
    simpa [fiber] using hfiber
  let embedding : Fin n ↪ Fin (1 + (k + 1) * n) :=
    ((Fin.castLEEmb hlarge).trans
      (Finset.equivFin fiber).symm.toEmbedding).trans
        (Function.Embedding.subtype (fun v => v ∈ fiber))
  have hmember (v : Fin n) : embedding v ∈ fiber := by
    exact ((Finset.equivFin fiber).symm (Fin.castLE hlarge v)).property
  have hrootedge (v : Fin n) :
      (C.labelGraph omitted).Adj root (embedding v) := by
    have hfilter := Finset.mem_filter.mp (hmember v)
    have herase : embedding v ∈ Finset.univ.erase root := by
      simpa only [others] using hfilter.1
    have hrootne : root ≠ embedding v :=
      Ne.symm (Finset.mem_erase.mp herase).1
    apply (SimpleGraph.TopEdgeLabeling.labelGraph_adj
      root (embedding v)).mpr
    refine ⟨hrootne, ?_⟩
    simpa [edgeColour, hrootne] using hfilter.2
  let restricted : SimpleGraph.TopEdgeLabeling (Fin n) (Fin (k + 1)) :=
    C.pullback embedding
  have hrestricted : TriangleFree restricted :=
    cliqueFree_pullback_embedding C embedding hC
  have hnoedge (u v : Fin n) :
      ¬ (restricted.labelGraph omitted).Adj u v := by
    intro hadj
    have horiginal : (C.labelGraph omitted).Adj (embedding u) (embedding v) := by
      have hcomap :
          restricted.labelGraph omitted =
            (C.labelGraph omitted).comap embedding :=
        labelGraph_pullback_embedding C embedding omitted
      rw [hcomap] at hadj
      exact hadj
    exact hC omitted {root, embedding u, embedding v}
      ((SimpleGraph.is3Clique_triple_iff).mpr
        ⟨hrootedge u, hrootedge v, horiginal⟩)
  have hunused :
      ∀ edge : (⊤ : SimpleGraph (Fin n)).edgeSet,
        restricted edge ≠ omitted := by
    intro edge hcolour
    rcases edge with ⟨edge, hedge⟩
    induction edge using Sym2.inductionOn with
    | _ u v =>
      exact hnoedge u v
        ((SimpleGraph.TopEdgeLabeling.labelGraph_adj u v).mpr
          ⟨hedge, hcolour⟩)
  exact hn (deleteUnusedColour restricted omitted hunused)
    (triangleFree_deleteUnusedColour restricted omitted hunused hrestricted)

theorem exists_forcesMonochromaticTriangle (k : ℕ) :
    ∃ n : ℕ, ForcesMonochromaticTriangle n k := by
  induction k with
  | zero =>
      exact ⟨2, forcesMonochromaticTriangle_zero⟩
  | succ k ih =>
      obtain ⟨n, hn⟩ := ih
      exact ⟨1 + (k + 1) * n, forcesMonochromaticTriangle_succ hn⟩

/-- The least order forcing a monochromatic triangle in every `k`-edge-coloring. -/
noncomputable def triangleRamseyNumber (k : ℕ) : ℕ :=
  sInf {n : ℕ | ForcesMonochromaticTriangle n k}

theorem triangleRamseyNumber_forces (k : ℕ) :
    ForcesMonochromaticTriangle (triangleRamseyNumber k) k := by
  exact Nat.sInf_mem (exists_forcesMonochromaticTriangle k)

theorem triangleRamseyNumber_succ_le (k : ℕ) :
    triangleRamseyNumber (k + 1) ≤
      1 + (k + 1) * triangleRamseyNumber k := by
  apply Nat.sInf_le
  exact forcesMonochromaticTriangle_succ (triangleRamseyNumber_forces k)

theorem triangleRamseyNumber_factorial_upper (k : ℕ) :
    triangleRamseyNumber k ≤ 4 * k.factorial := by
  have hzero : triangleRamseyNumber 0 ≤ 2 := by
    apply Nat.sInf_le
    exact forcesMonochromaticTriangle_zero
  have hone : triangleRamseyNumber 1 + 1 ≤ 4 := by
    have hrec := triangleRamseyNumber_succ_le 0
    norm_num at hrec ⊢
    omega
  have hstrict : ∀ k : ℕ, 1 ≤ k →
      triangleRamseyNumber k + 1 ≤ 4 * k.factorial := by
    intro j hj
    induction j with
    | zero => omega
    | succ j ih =>
        by_cases hzeroj : j = 0
        · subst j
          exact hone
        · have hjpos : 1 ≤ j := by omega
          have hprev := ih hjpos
          have hrec := triangleRamseyNumber_succ_le j
          rw [Nat.factorial_succ]
          nlinarith
  by_cases hk : k = 0
  · subst k
    norm_num
    omega
  · have hbound := hstrict k (by omega)
    omega

theorem triangleFree_lt_triangleRamseyNumber {n k : ℕ}
    (C : SimpleGraph.TopEdgeLabeling (Fin n) (Fin k))
    (hC : TriangleFree C) :
    n < triangleRamseyNumber k := by
  by_contra hnot
  have hle : triangleRamseyNumber k ≤ n := by omega
  have hforcing : ForcesMonochromaticTriangle n k :=
    forcesMonochromaticTriangle_mono hle
      (triangleRamseyNumber_forces k)
  exact hforcing C hC

theorem triangleRamseyNumber_mono {k l : ℕ} (hkl : k ≤ l) :
    triangleRamseyNumber k ≤ triangleRamseyNumber l := by
  apply Nat.sInf_le
  intro C hC
  have hlarge :
      TriangleFree (C.compRight (Fin.castLEEmb hkl)) :=
    cliqueFree_compRight_embedding C (Fin.castLEEmb hkl) hC
  exact triangleRamseyNumber_forces l
    (C.compRight (Fin.castLEEmb hkl)) hlarge

theorem no_three_pairwise_palette_disagreements {α : Type*}
    (P Q R : Finset α) (colour : α)
    (hPQ : (colour ∈ P) ≠ (colour ∈ Q))
    (hQR : (colour ∈ Q) ≠ (colour ∈ R))
    (hRP : (colour ∈ R) ≠ (colour ∈ P)) : False := by
  classical
  by_cases hP : colour ∈ P <;>
    by_cases hQ : colour ∈ Q <;>
      by_cases hR : colour ∈ R <;>
        simp_all

/-- Embeds a finite index set into the colors present in one palette but not another. -/
noncomputable def differenceColourEmbedding {α : Type*} [DecidableEq α]
    (P Q : Finset α) {s : ℕ} (hcard : s ≤ (Q \ P).card) :
    Fin s ↪ α := by
  classical
  let selection : Fin s ↪ ↥(Q \ P) :=
    (Fin.castLEEmb hcard).trans (Finset.equivFin (Q \ P)).symm.toEmbedding
  exact ⟨fun i => (selection i).val,
    fun i j h => selection.injective (Subtype.ext h)⟩

theorem differenceColourEmbedding_mem {α : Type*} [DecidableEq α]
    (P Q : Finset α) {s : ℕ} (hcard : s ≤ (Q \ P).card)
    (i : Fin s) :
    differenceColourEmbedding P Q hcard i ∈ Q \ P := by
  classical
  exact ((Fin.castLEEmb hcard).trans
    (Finset.equivFin (Q \ P)).symm.toEmbedding i).property

/-- A palette family whose ordered differences all contain at least `s` colors. -/
def IsPaletteSeparated {α : Type*} [DecidableEq α]
    (s : ℕ) (family : Finset (Finset α)) : Prop :=
  ∀ P ∈ family, ∀ Q ∈ family, P ≠ Q → s ≤ (P \ Q).card

theorem paletteSeparated_insert {α : Type*} [DecidableEq α]
    {s : ℕ} {family : Finset (Finset α)} {P : Finset α}
    (hseparated : IsPaletteSeparated s family)
    (hequal : ∀ Q ∈ family, Q.card = P.card)
    (hfar : ∀ Q ∈ family, s ≤ (P \ Q).card) :
    IsPaletteSeparated s (insert P family) := by
  classical
  intro X hX Y hY hXY
  by_cases hXP : X = P
  · subst X
    by_cases hYP : Y = P
    · exact (hXY hYP.symm).elim
    · have hYfamily : Y ∈ family :=
        (Finset.mem_insert.mp hY).resolve_left hYP
      exact hfar Y hYfamily
  · have hXfamily : X ∈ family :=
      (Finset.mem_insert.mp hX).resolve_left hXP
    by_cases hYP : Y = P
    · subst Y
      rw [Finset.card_sdiff_comm (hequal X hXfamily)]
      exact hfar X hXfamily
    · have hYfamily : Y ∈ family :=
        (Finset.mem_insert.mp hY).resolve_left hYP
      exact hseparated X hXfamily Y hYfamily hXY

theorem exists_maximal_separated_palette_cover {α : Type*} [DecidableEq α]
    (ambient : Finset (Finset α)) (s : ℕ) (hs : 0 < s)
    (hequal : ∀ P ∈ ambient, ∀ Q ∈ ambient, P.card = Q.card) :
    ∃ family : Finset (Finset α),
      family ⊆ ambient ∧ IsPaletteSeparated s family ∧
        ∀ P ∈ ambient, ∃ Q ∈ family, (P \ Q).card < s := by
  classical
  let candidates := ambient.powerset.filter (IsPaletteSeparated s)
  have hcandidates : candidates.Nonempty := by
    refine ⟨∅, ?_⟩
    simp [candidates, IsPaletteSeparated]
  obtain ⟨family, hfamily, hmax⟩ :=
    Finset.exists_max_image candidates Finset.card hcandidates
  have hfamily' : family ⊆ ambient ∧ IsPaletteSeparated s family := by
    simpa [candidates] using hfamily
  refine ⟨family, hfamily'.1, hfamily'.2, ?_⟩
  intro P hP
  by_contra hnot
  have hfar : ∀ Q ∈ family, s ≤ (P \ Q).card := by
    intro Q hQ
    exact Nat.le_of_not_gt (fun hclose => hnot ⟨Q, hQ, hclose⟩)
  have hPnot : P ∉ family := by
    intro hPF
    apply hnot
    refine ⟨P, hPF, ?_⟩
    simpa using hs
  have hcards : ∀ Q ∈ family, Q.card = P.card := by
    intro Q hQ
    exact hequal Q (hfamily'.1 hQ) P hP
  have hinsert_separated : IsPaletteSeparated s (insert P family) :=
    paletteSeparated_insert hfamily'.2 hcards hfar
  have hinsert : insert P family ∈ candidates := by
    simp only [candidates, Finset.mem_filter, Finset.mem_powerset]
    exact ⟨Finset.insert_subset hP hfamily'.1, hinsert_separated⟩
  have hmaxcard := hmax (insert P family) hinsert
  rw [Finset.card_insert_of_notMem hPnot] at hmaxcard
  omega

/-- Palettes of fixed size whose one-sided distance from a center is below `s`. -/
noncomputable def paletteBall {α : Type*} [DecidableEq α]
    (ambient : Finset (Finset α)) (Q : Finset α) (s : ℕ) :
    Finset (Finset α) := by
  classical
  exact ambient.filter (fun P => (P \ Q).card < s)

/-- The shell of `t`-element palettes at one-sided distance `d` from `Q`. -/
noncomputable def paletteShell (N t : ℕ) (Q : Finset (Fin N)) (d : ℕ) :
    Finset (Finset (Fin N)) := by
  classical
  exact ((Finset.univ : Finset (Fin N)).powersetCard t).filter
    (fun P => (P \ Q).card = d)

/-- Encodes a palette shell by the elements removed from and added to its center. -/
noncomputable def paletteShellEmbedding (N t d : ℕ)
    (Q : Finset (Fin N)) (hQ : Q.card = t) :
    ↥(paletteShell N t Q d) ↪
      (↥(Q.powersetCard d) ×
        ↥(((Finset.univ : Finset (Fin N)) \ Q).powersetCard d)) := by
  classical
  refine
    { toFun := fun P =>
        (⟨Q \ P.val, ?_⟩, ⟨P.val \ Q, ?_⟩)
      inj' := ?_ }
  · apply Finset.mem_powersetCard.mpr
    refine ⟨Finset.sdiff_subset, ?_⟩
    have hP := (Finset.mem_filter.mp P.property)
    have hPcard := (Finset.mem_powersetCard.mp hP.1).2
    rw [Finset.card_sdiff_comm (hQ.trans hPcard.symm)]
    exact hP.2
  · apply Finset.mem_powersetCard.mpr
    constructor
    · intro x hx
      exact Finset.mem_sdiff.mpr
        ⟨Finset.mem_univ x, (Finset.mem_sdiff.mp hx).2⟩
    · exact (Finset.mem_filter.mp P.property).2
  · intro P P' heq
    have hleft := congrArg (fun z => z.1.val) heq
    have hright := congrArg (fun z => z.2.val) heq
    apply Subtype.ext
    ext x
    by_cases hx : x ∈ Q
    · have hmem := Finset.ext_iff.mp hleft x
      have hnegative : x ∉ P.val ↔ x ∉ P'.val := by
        simpa [hx] using hmem
      constructor
      · intro hP
        by_contra hP'
        exact (hnegative.mpr hP') hP
      · intro hP'
        by_contra hP
        exact (hnegative.mp hP) hP'
    · have hmem := Finset.ext_iff.mp hright x
      simpa [hx] using hmem

theorem paletteShell_card_le (N t d : ℕ)
    (Q : Finset (Fin N)) (hQ : Q.card = t) :
    (paletteShell N t Q d).card ≤
      t.choose d * (N - t).choose d := by
  classical
  have hcard := Fintype.card_le_of_injective
    (paletteShellEmbedding N t d Q hQ)
    (paletteShellEmbedding N t d Q hQ).injective
  calc
    (paletteShell N t Q d).card = Fintype.card ↥(paletteShell N t Q d) :=
      (Fintype.card_coe _).symm
    _ ≤ Fintype.card
      (↥(Q.powersetCard d) ×
        ↥(((Finset.univ : Finset (Fin N)) \ Q).powersetCard d)) := hcard
    _ = t.choose d * (N - t).choose d := by
      rw [Fintype.card_prod, Fintype.card_coe, Fintype.card_coe,
        Finset.card_powersetCard, Finset.card_powersetCard,
        Finset.card_sdiff_of_subset (Finset.subset_univ Q)]
      simp [hQ]

theorem palette_packing_card_le {α : Type*} [DecidableEq α]
    (ambient family : Finset (Finset α)) (s ballBound : ℕ)
    (hcover : ∀ P ∈ ambient, ∃ Q ∈ family, (P \ Q).card < s)
    (hball : ∀ Q ∈ family, (paletteBall ambient Q s).card ≤ ballBound) :
    ambient.card ≤ family.card * ballBound := by
  classical
  have hsubset : ambient ⊆ family.biUnion (fun Q => paletteBall ambient Q s) := by
    intro P hP
    obtain ⟨Q, hQ, hclose⟩ := hcover P hP
    exact Finset.mem_biUnion.mpr ⟨Q, hQ, by simp [paletteBall, hP, hclose]⟩
  calc
    ambient.card ≤ (family.biUnion (fun Q => paletteBall ambient Q s)).card :=
      Finset.card_le_card hsubset
    _ ≤ ∑ Q ∈ family, (paletteBall ambient Q s).card :=
      Finset.card_biUnion_le
    _ ≤ ∑ _Q ∈ family, ballBound :=
      Finset.sum_le_sum fun Q hQ => hball Q hQ
    _ = family.card * ballBound := by simp

theorem paletteBall_card_le_binomial_sum (N t s : ℕ)
    (Q : Finset (Fin N)) (hQ : Q.card = t) :
    (paletteBall ((Finset.univ : Finset (Fin N)).powersetCard t) Q s).card ≤
      ∑ d ∈ Finset.range s, t.choose d * (N - t).choose d := by
  classical
  let ambient : Finset (Finset (Fin N)) :=
    (Finset.univ : Finset (Fin N)).powersetCard t
  have hsubset :
      paletteBall ambient Q s ⊆
        (Finset.range s).biUnion (fun d => paletteShell N t Q d) := by
    intro P hP
    have hP' : P ∈ ambient ∧ (P \ Q).card < s := by
      simpa [paletteBall] using hP
    apply Finset.mem_biUnion.mpr
    refine ⟨(P \ Q).card, Finset.mem_range.mpr hP'.2, ?_⟩
    simpa [paletteShell, ambient] using hP'.1
  calc
    (paletteBall ambient Q s).card ≤
        ((Finset.range s).biUnion (fun d => paletteShell N t Q d)).card :=
      Finset.card_le_card hsubset
    _ ≤ ∑ d ∈ Finset.range s, (paletteShell N t Q d).card :=
      Finset.card_biUnion_le
    _ ≤ ∑ d ∈ Finset.range s, t.choose d * (N - t).choose d := by
      exact Finset.sum_le_sum fun d _ => paletteShell_card_le N t d Q hQ

theorem exists_separated_palette_packing (N t s : ℕ) (hs : 0 < s) :
    ∃ family : Finset (Finset (Fin N)),
      family ⊆ (Finset.univ : Finset (Fin N)).powersetCard t ∧
      IsPaletteSeparated s family ∧
      N.choose t ≤ family.card *
        (∑ d ∈ Finset.range s, t.choose d * (N - t).choose d) := by
  classical
  obtain ⟨family, hfamily, hseparated, hcover⟩ :=
    exists_maximal_separated_palette_cover
      ((Finset.univ : Finset (Fin N)).powersetCard t) s hs
      (fun P hP Q hQ => (Finset.mem_powersetCard.mp hP).2.trans
        (Finset.mem_powersetCard.mp hQ).2.symm)
  refine ⟨family, hfamily, hseparated, ?_⟩
  have hpacking := palette_packing_card_le
    ((Finset.univ : Finset (Fin N)).powersetCard t) family s
    (∑ d ∈ Finset.range s, t.choose d * (N - t).choose d)
    hcover (fun Q hQ => paletteBall_card_le_binomial_sum N t s Q
      (Finset.mem_powersetCard.mp (hfamily hQ)).2)
  simpa using hpacking

/-- Embeds one selected coordinate from each of `t` blocks of width `j`. -/
def transversalCoordinateEmbedding (j t : ℕ) (choice : Fin t → Fin j) :
    Fin t ↪ Fin (j * t) where
  toFun coordinate :=
    ((finProdFinEquiv : Fin t × Fin j ≃ Fin (t * j)).trans
      (finCongr (Nat.mul_comm t j))) (coordinate, choice coordinate)
  inj' := by
    intro x y heq
    have hpairs :=
      (((finProdFinEquiv : Fin t × Fin j ≃ Fin (t * j)).trans
        (finCongr (Nat.mul_comm t j)))).injective heq
    exact congrArg Prod.fst hpairs

/-- The palette consisting of the selected coordinate in every block. -/
noncomputable def transversalPalette (j t : ℕ) (choice : Fin t → Fin j) :
    Finset (Fin (j * t)) :=
  Finset.univ.map (transversalCoordinateEmbedding j t choice)

/-- Embeds blockwise choices into their transversal palettes. -/
noncomputable def transversalPaletteEmbedding (j t : ℕ) :
    (Fin t → Fin j) ↪
      ↥((Finset.univ : Finset (Fin (j * t))).powersetCard t) := by
  classical
  refine
    { toFun := fun choice => ⟨transversalPalette j t choice, ?_⟩
      inj' := ?_ }
  · apply Finset.mem_powersetCard.mpr
    exact ⟨Finset.subset_univ _, by simp [transversalPalette]⟩
  · intro choice₁ choice₂ heq
    have hpalettes :
        transversalPalette j t choice₁ =
          transversalPalette j t choice₂ :=
      congrArg Subtype.val heq
    funext coordinate
    have hmember :
        transversalCoordinateEmbedding j t choice₁ coordinate ∈
          transversalPalette j t choice₂ := by
      rw [← hpalettes]
      exact Finset.mem_map.mpr
        ⟨coordinate, Finset.mem_univ coordinate, rfl⟩
    obtain ⟨coordinate', _, hcoordinate⟩ :=
      Finset.mem_map.mp (show
        transversalCoordinateEmbedding j t choice₁ coordinate ∈
          Finset.univ.map
            (transversalCoordinateEmbedding j t choice₂) from hmember)
    have hpairs :
        (coordinate', choice₂ coordinate') =
          (coordinate, choice₁ coordinate) := by
      exact
        (((finProdFinEquiv : Fin t × Fin j ≃ Fin (t * j)).trans
          (finCongr (Nat.mul_comm t j)))).injective hcoordinate
    have hindex : coordinate' = coordinate := congrArg Prod.fst hpairs
    subst coordinate'
    exact (congrArg Prod.snd hpairs).symm

theorem stage_palette_numerator_bound (j t : ℕ) :
    j ^ t ≤ (j * t).choose t := by
  have hcard := Fintype.card_le_of_injective
    (transversalPaletteEmbedding j t)
    (transversalPaletteEmbedding j t).injective
  calc
    j ^ t = Fintype.card (Fin t → Fin j) := by simp
    _ ≤ Fintype.card
      ↥((Finset.univ : Finset (Fin (j * t))).powersetCard t) := hcard
    _ = (j * t).choose t := by
      rw [Fintype.card_coe, Finset.card_powersetCard]
      simp

theorem choose_le_choose_of_le_half {N d s : ℕ}
    (hds : d ≤ s) (hhalf : 2 * s ≤ N) :
    N.choose d ≤ N.choose s := by
  induction hds with
  | refl => exact le_rfl
  | @step d hds ih =>
      have hprevious : 2 * d ≤ N := by omega
      exact (ih hprevious).trans
        (Nat.choose_le_succ_of_lt_half_left (by omega))

theorem factorial_exp_lower (s : ℕ) (hs : 0 < s) :
    ((s : ℝ) / Real.exp 1) ^ s ≤ (s.factorial : ℝ) := by
  have hsreal : (1 : ℝ) ≤ s := by
    exact_mod_cast hs
  have hradicand : (1 : ℝ) ≤ 2 * Real.pi * (s : ℝ) := by
    nlinarith [Real.pi_gt_three]
  have hsqrt : (1 : ℝ) ≤ Real.sqrt (2 * Real.pi * (s : ℝ)) := by
    nlinarith [Real.sq_sqrt (show 0 ≤ 2 * Real.pi * (s : ℝ) by positivity),
      Real.sqrt_nonneg (2 * Real.pi * (s : ℝ))]
  have hpower : 0 ≤ ((s : ℝ) / Real.exp 1) ^ s := by positivity
  calc
    ((s : ℝ) / Real.exp 1) ^ s ≤
        Real.sqrt (2 * Real.pi * (s : ℝ)) *
          ((s : ℝ) / Real.exp 1) ^ s := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hsqrt) hpower]
    _ ≤ (s.factorial : ℝ) := Stirling.le_factorial_stirling s

theorem choose_le_exp_mul_div_pow (N s : ℕ) (hs : 0 < s) :
    (N.choose s : ℝ) ≤
      (Real.exp 1 * (N : ℝ) / (s : ℝ)) ^ s := by
  have hsreal : 0 < (s : ℝ) := by exact_mod_cast hs
  have hsmall : 0 < ((s : ℝ) / Real.exp 1) ^ s := by positivity
  calc
    (N.choose s : ℝ) ≤ (N : ℝ) ^ s / (s.factorial : ℝ) :=
      Nat.choose_le_pow_div s N
    _ ≤ (N : ℝ) ^ s / (((s : ℝ) / Real.exp 1) ^ s) :=
      div_le_div_of_nonneg_left (by positivity) hsmall
        (factorial_exp_lower s hs)
    _ = (Real.exp 1 * (N : ℝ) / (s : ℝ)) ^ s := by
      rw [← div_pow]
      congr 1
      field_simp

theorem palette_binomial_sum_le (N t s : ℕ)
    (hhalf : 2 * s ≤ t) (htN : t ≤ N) :
    (∑ d ∈ Finset.range s,
      t.choose d * (N - t).choose d) ≤
        s * t.choose s * N.choose s := by
  have hNhalf : 2 * s ≤ N := hhalf.trans htN
  calc
    (∑ d ∈ Finset.range s,
      t.choose d * (N - t).choose d) ≤
        ∑ _d ∈ Finset.range s, t.choose s * N.choose s := by
      apply Finset.sum_le_sum
      intro d hd
      have hds : d ≤ s := by
        have := Finset.mem_range.mp hd
        omega
      apply Nat.mul_le_mul
      · exact choose_le_choose_of_le_half hds hhalf
      · exact (Nat.choose_le_choose d (Nat.sub_le N t)).trans
          (choose_le_choose_of_le_half hds hNhalf)
    _ = s * t.choose s * N.choose s := by simp [mul_assoc]

theorem exists_stage_palette_packing_binomial (j t s : ℕ)
    (hs : 0 < s) (hj : 0 < j) (hhalf : 2 * s ≤ t) :
    ∃ family : Finset (Finset (Fin (j * t))),
      family ⊆ (Finset.univ : Finset (Fin (j * t))).powersetCard t ∧
      IsPaletteSeparated s family ∧
      j ^ t ≤ family.card *
        (s * t.choose s * (j * t).choose s) := by
  obtain ⟨family, hfamily, hseparated, hpacking⟩ :=
    exists_separated_palette_packing (j * t) t s hs
  refine ⟨family, hfamily, hseparated,
    (stage_palette_numerator_bound j t).trans (hpacking.trans ?_)⟩
  exact Nat.mul_le_mul_left _
    (palette_binomial_sum_le (j * t) t s hhalf
      (Nat.le_mul_of_pos_left t hj))

theorem exists_stage_palette_packing_exp (j a s : ℕ)
    (hj : 0 < j) (ha : 2 ≤ a) (hs : 0 < s) :
    ∃ family : Finset (Finset (Fin (j * (a * s)))),
      family ⊆
        (Finset.univ : Finset (Fin (j * (a * s)))).powersetCard (a * s) ∧
      IsPaletteSeparated s family ∧
      (j : ℝ) ^ (a * s) ≤
        (family.card : ℝ) * (s : ℝ) *
          (Real.exp 1 ^ 2 * (a : ℝ) ^ 2 * (j : ℝ)) ^ s := by
  have hhalf : 2 * s ≤ a * s := Nat.mul_le_mul_right s ha
  obtain ⟨family, hfamily, hseparated, hpacking⟩ :=
    exists_stage_palette_packing_binomial j (a * s) s hs hj hhalf
  refine ⟨family, hfamily, hseparated, ?_⟩
  have hreal :
      (j : ℝ) ^ (a * s) ≤
        (family.card : ℝ) *
          ((s * (a * s).choose s * (j * (a * s)).choose s : ℕ) : ℝ) := by
    exact_mod_cast hpacking
  have hfirst := choose_le_exp_mul_div_pow (a * s) s hs
  have hsecond := choose_le_exp_mul_div_pow (j * (a * s)) s hs
  have hbase :
      (Real.exp 1 * ((a * s : ℕ) : ℝ) / (s : ℝ)) *
        (Real.exp 1 * ((j * (a * s) : ℕ) : ℝ) / (s : ℝ)) =
          Real.exp 1 ^ 2 * (a : ℝ) ^ 2 * (j : ℝ) := by
    push_cast
    field_simp
  have hpowers :
      (Real.exp 1 * ((a * s : ℕ) : ℝ) / (s : ℝ)) ^ s *
        (Real.exp 1 * ((j * (a * s) : ℕ) : ℝ) / (s : ℝ)) ^ s =
          (Real.exp 1 ^ 2 * (a : ℝ) ^ 2 * (j : ℝ)) ^ s := by
    rw [← mul_pow, hbase]
  calc
    (j : ℝ) ^ (a * s) ≤
        (family.card : ℝ) *
          ((s * (a * s).choose s * (j * (a * s)).choose s : ℕ) : ℝ) :=
      hreal
    _ = (family.card : ℝ) * (s : ℝ) *
          ((a * s).choose s : ℝ) *
          ((j * (a * s)).choose s : ℝ) := by
      push_cast
      ring
    _ ≤ (family.card : ℝ) * (s : ℝ) *
          (Real.exp 1 * ((a * s : ℕ) : ℝ) / (s : ℝ)) ^ s *
          (Real.exp 1 * ((j * (a * s) : ℕ) : ℝ) / (s : ℝ)) ^ s := by
      gcongr
    _ = (family.card : ℝ) * (s : ℝ) *
          (Real.exp 1 ^ 2 * (a : ℝ) ^ 2 * (j : ℝ)) ^ s := by
      calc
        (family.card : ℝ) * (s : ℝ) *
            (Real.exp 1 * ((a * s : ℕ) : ℝ) / (s : ℝ)) ^ s *
            (Real.exp 1 * ((j * (a * s) : ℕ) : ℝ) / (s : ℝ)) ^ s =
          (family.card : ℝ) * (s : ℝ) *
            ((Real.exp 1 * ((a * s : ℕ) : ℝ) / (s : ℝ)) ^ s *
              (Real.exp 1 * ((j * (a * s) : ℕ) : ℝ) / (s : ℝ)) ^ s) := by
                ring
        _ = (family.card : ℝ) * (s : ℝ) *
            (Real.exp 1 ^ 2 * (a : ℝ) ^ 2 * (j : ℝ)) ^ s := by
              rw [hpowers]

/-- Two transformations cover every input vector in at least one coordinate. -/
def IsCoordinateCovering {H s : ℕ}
    (f g : (Fin s → Fin H) → (Fin s → Fin H)) : Prop :=
  ∀ x y : Fin s → Fin H,
    (∃ d : Fin s, x d = f y d) ∨
      (∃ d : Fin s, y d = g x d)

/-- Selects a cross-block color from a coordinate-covering pair of transformations. -/
noncomputable def recursiveCrossColour {K : Type*} {H s : ℕ}
    (a b : Fin s ↪ K)
    (f g : (Fin s → Fin H) → (Fin s → Fin H))
    (hcover : IsCoordinateCovering f g)
    (x y : Fin s → Fin H) : K := by
  classical
  exact
    if hforward : ∃ d : Fin s, x d = f y d then
      a (Fin.find (fun d => x d = f y d) hforward)
    else
      b (Fin.find (fun d => y d = g x d)
        ((hcover x y).resolve_left hforward))

theorem recursiveCrossColour_spec {K : Type*} {H s : ℕ}
    (a b : Fin s ↪ K)
    (f g : (Fin s → Fin H) → (Fin s → Fin H))
    (hcover : IsCoordinateCovering f g)
    (x y : Fin s → Fin H) :
    (∃ d : Fin s,
      recursiveCrossColour a b f g hcover x y = a d ∧ x d = f y d) ∨
    (∃ d : Fin s,
      recursiveCrossColour a b f g hcover x y = b d ∧ y d = g x d) := by
  classical
  by_cases hforward : ∃ d : Fin s, x d = f y d
  · let d := Fin.find (fun d => x d = f y d) hforward
    left
    refine ⟨d, ?_, Fin.find_spec hforward⟩
    simp [recursiveCrossColour, hforward, d]
  · have hbackward : ∃ d : Fin s, y d = g x d :=
      (hcover x y).resolve_left hforward
    let d := Fin.find (fun d => y d = g x d) hbackward
    right
    refine ⟨d, ?_, Fin.find_spec hbackward⟩
    simp [recursiveCrossColour, hforward, d]

theorem recursiveCrossColour_changes_membership {K : Type*} [DecidableEq K]
    {H s : ℕ} (P Q : Finset K)
    (a b : Fin s ↪ K)
    (ha : ∀ d, a d ∈ Q \ P)
    (hb : ∀ d, b d ∈ P \ Q)
    (f g : (Fin s → Fin H) → (Fin s → Fin H))
    (hcover : IsCoordinateCovering f g)
    (x y : Fin s → Fin H) :
    (recursiveCrossColour a b f g hcover x y ∈ P) ≠
      (recursiveCrossColour a b f g hcover x y ∈ Q) := by
  rcases recursiveCrossColour_spec a b f g hcover x y with
    ⟨d, hcolour, _⟩ | ⟨d, hcolour, _⟩
  · rw [hcolour]
    have hmem := Finset.mem_sdiff.mp (ha d)
    simp [hmem.1, hmem.2]
  · rw [hcolour]
    have hmem := Finset.mem_sdiff.mp (hb d)
    simp [hmem.1, hmem.2]

theorem recursiveCrossColour_same_left_coordinate
    {K : Type*} [DecidableEq K] {H s : ℕ}
    (P Q : Finset K) (a b : Fin s ↪ K)
    (_ha : ∀ d, a d ∈ Q \ P)
    (hb : ∀ d, b d ∈ P \ Q)
    (f g : (Fin s → Fin H) → (Fin s → Fin H))
    (hcover : IsCoordinateCovering f g)
    (x x' y : Fin s → Fin H) (colour : K)
    (hactive : colour ∉ P)
    (hxy : recursiveCrossColour a b f g hcover x y = colour)
    (hx'y : recursiveCrossColour a b f g hcover x' y = colour) :
    ∃ d : Fin s, colour = a d ∧ x d = x' d := by
  have select (z : Fin s → Fin H)
      (hz : recursiveCrossColour a b f g hcover z y = colour) :
      ∃ d : Fin s, colour = a d ∧ z d = f y d := by
    have hforward :=
      (recursiveCrossColour_spec a b f g hcover z y).resolve_right (by
        rintro ⟨d, hd, _⟩
        apply hactive
        rw [← hz, hd]
        exact (Finset.mem_sdiff.mp (hb d)).1)
    obtain ⟨d, hd, hforced⟩ := hforward
    exact ⟨d, hz.symm.trans hd, hforced⟩
  obtain ⟨d, hd, hforced⟩ := select x hxy
  obtain ⟨d', hd', hforced'⟩ := select x' hx'y
  have hindex : d = d' := a.injective (hd.symm.trans hd')
  exact ⟨d, hd, hforced.trans (by simpa [hindex] using hforced'.symm)⟩

theorem recursiveCrossColour_same_right_coordinate
    {K : Type*} [DecidableEq K] {H s : ℕ}
    (P Q : Finset K) (a b : Fin s ↪ K)
    (ha : ∀ d, a d ∈ Q \ P)
    (_hb : ∀ d, b d ∈ P \ Q)
    (f g : (Fin s → Fin H) → (Fin s → Fin H))
    (hcover : IsCoordinateCovering f g)
    (x y y' : Fin s → Fin H) (colour : K)
    (hactive : colour ∉ Q)
    (hxy : recursiveCrossColour a b f g hcover x y = colour)
    (hxy' : recursiveCrossColour a b f g hcover x y' = colour) :
    ∃ d : Fin s, colour = b d ∧ y d = y' d := by
  have select (z : Fin s → Fin H)
      (hz : recursiveCrossColour a b f g hcover x z = colour) :
      ∃ d : Fin s, colour = b d ∧ z d = g x d := by
    have hbackward :=
      (recursiveCrossColour_spec a b f g hcover x z).resolve_left (by
        rintro ⟨d, hd, _⟩
        apply hactive
        rw [← hz, hd]
        exact (Finset.mem_sdiff.mp (ha d)).1)
    obtain ⟨d, hd, hforced⟩ := hbackward
    exact ⟨d, hz.symm.trans hd, hforced⟩
  obtain ⟨d, hd, hforced⟩ := select y hxy
  obtain ⟨d', hd', hforced'⟩ := select y' hxy'
  have hindex : d = d' := b.injective (hd.symm.trans hd')
  exact ⟨d, hd, hforced.trans (by simpa [hindex] using hforced'.symm)⟩

/-- The vector of internal proper-coloring labels attached to a palette block vertex. -/
noncomputable def paletteBlockVector {V : Type*} {N t j H s : ℕ}
    (C : SimpleGraph.TopEdgeLabeling V (Fin (N - t)))
    (hC : ∀ colour : Fin (N - t), (C.labelGraph colour).Colorable j)
    (hj : j ≤ H) (P : Finset (Fin N)) (hP : P.card = t)
    (colours : Fin s ↪ Fin N)
    (hcolours : ∀ d : Fin s, colours d ∉ P)
    (u : V) : Fin s → Fin H :=
  fun d =>
    Fin.castLE hj
      (paletteBlockLabel C hC P hP (colours d) (hcolours d) u)

/-- The color assigned to an edge crossing two palette blocks. -/
noncomputable def paletteCrossColour {V : Type*} {N t j H s : ℕ}
    (C : SimpleGraph.TopEdgeLabeling V (Fin (N - t)))
    (hC : ∀ colour : Fin (N - t), (C.labelGraph colour).Colorable j)
    (hj : j ≤ H)
    (P Q : Finset (Fin N)) (hP : P.card = t) (hQ : Q.card = t)
    (a b : Fin s ↪ Fin N)
    (ha : ∀ d, a d ∈ Q \ P)
    (hb : ∀ d, b d ∈ P \ Q)
    (f g : (Fin s → Fin H) → (Fin s → Fin H))
    (hcover : IsCoordinateCovering f g)
    (u v : V) : Fin N :=
  recursiveCrossColour a b f g hcover
    (paletteBlockVector C hC hj P hP a
      (fun d => (Finset.mem_sdiff.mp (ha d)).2) u)
    (paletteBlockVector C hC hj Q hQ b
      (fun d => (Finset.mem_sdiff.mp (hb d)).2) v)

theorem paletteCrossColour_changes_membership
    {V : Type*} {N t j H s : ℕ}
    (C : SimpleGraph.TopEdgeLabeling V (Fin (N - t)))
    (hC : ∀ colour : Fin (N - t), (C.labelGraph colour).Colorable j)
    (hj : j ≤ H)
    (P Q : Finset (Fin N)) (hP : P.card = t) (hQ : Q.card = t)
    (a b : Fin s ↪ Fin N)
    (ha : ∀ d, a d ∈ Q \ P)
    (hb : ∀ d, b d ∈ P \ Q)
    (f g : (Fin s → Fin H) → (Fin s → Fin H))
    (hcover : IsCoordinateCovering f g)
    (u v : V) :
    (paletteCrossColour C hC hj P Q hP hQ a b ha hb f g hcover u v ∈ P) ≠
      (paletteCrossColour C hC hj P Q hP hQ a b ha hb f g hcover u v ∈ Q) := by
  exact recursiveCrossColour_changes_membership P Q a b ha hb f g hcover
    (paletteBlockVector C hC hj P hP a
      (fun d => (Finset.mem_sdiff.mp (ha d)).2) u)
    (paletteBlockVector C hC hj Q hQ b
      (fun d => (Finset.mem_sdiff.mp (hb d)).2) v)

theorem paletteCrossColour_same_left_label
    {V : Type*} {N t j H s : ℕ}
    (C : SimpleGraph.TopEdgeLabeling V (Fin (N - t)))
    (hC : ∀ colour : Fin (N - t), (C.labelGraph colour).Colorable j)
    (hj : j ≤ H)
    (P Q : Finset (Fin N)) (hP : P.card = t) (hQ : Q.card = t)
    (a b : Fin s ↪ Fin N)
    (ha : ∀ d, a d ∈ Q \ P)
    (hb : ∀ d, b d ∈ P \ Q)
    (f g : (Fin s → Fin H) → (Fin s → Fin H))
    (hcover : IsCoordinateCovering f g)
    (u u' v : V) (colour : Fin N) (hactive : colour ∉ P)
    (hu : paletteCrossColour C hC hj P Q hP hQ a b ha hb f g hcover u v =
      colour)
    (hu' : paletteCrossColour C hC hj P Q hP hQ a b ha hb f g hcover u' v =
      colour) :
    paletteBlockLabel C hC P hP colour hactive u =
      paletteBlockLabel C hC P hP colour hactive u' := by
  obtain ⟨d, hd, hequal⟩ :=
    recursiveCrossColour_same_left_coordinate P Q a b ha hb f g hcover
      (paletteBlockVector C hC hj P hP a
        (fun d => (Finset.mem_sdiff.mp (ha d)).2) u)
      (paletteBlockVector C hC hj P hP a
        (fun d => (Finset.mem_sdiff.mp (ha d)).2) u')
      (paletteBlockVector C hC hj Q hQ b
        (fun d => (Finset.mem_sdiff.mp (hb d)).2) v)
      colour hactive hu hu'
  change
    Fin.castLE hj
        (paletteBlockLabel C hC P hP (a d)
          ((Finset.mem_sdiff.mp (ha d)).2) u) =
      Fin.castLE hj
        (paletteBlockLabel C hC P hP (a d)
          ((Finset.mem_sdiff.mp (ha d)).2) u') at hequal
  have hlabels := Fin.castLE_injective hj hequal
  simpa [hd] using hlabels

theorem paletteCrossColour_same_right_label
    {V : Type*} {N t j H s : ℕ}
    (C : SimpleGraph.TopEdgeLabeling V (Fin (N - t)))
    (hC : ∀ colour : Fin (N - t), (C.labelGraph colour).Colorable j)
    (hj : j ≤ H)
    (P Q : Finset (Fin N)) (hP : P.card = t) (hQ : Q.card = t)
    (a b : Fin s ↪ Fin N)
    (ha : ∀ d, a d ∈ Q \ P)
    (hb : ∀ d, b d ∈ P \ Q)
    (f g : (Fin s → Fin H) → (Fin s → Fin H))
    (hcover : IsCoordinateCovering f g)
    (u v v' : V) (colour : Fin N) (hactive : colour ∉ Q)
    (hv : paletteCrossColour C hC hj P Q hP hQ a b ha hb f g hcover u v =
      colour)
    (hv' : paletteCrossColour C hC hj P Q hP hQ a b ha hb f g hcover u v' =
      colour) :
    paletteBlockLabel C hC Q hQ colour hactive v =
      paletteBlockLabel C hC Q hQ colour hactive v' := by
  obtain ⟨d, hd, hequal⟩ :=
    recursiveCrossColour_same_right_coordinate P Q a b ha hb f g hcover
      (paletteBlockVector C hC hj P hP a
        (fun d => (Finset.mem_sdiff.mp (ha d)).2) u)
      (paletteBlockVector C hC hj Q hQ b
        (fun d => (Finset.mem_sdiff.mp (hb d)).2) v)
      (paletteBlockVector C hC hj Q hQ b
        (fun d => (Finset.mem_sdiff.mp (hb d)).2) v')
      colour hactive hv hv'
  change
    Fin.castLE hj
        (paletteBlockLabel C hC Q hQ (b d)
          ((Finset.mem_sdiff.mp (hb d)).2) v) =
      Fin.castLE hj
        (paletteBlockLabel C hC Q hQ (b d)
          ((Finset.mem_sdiff.mp (hb d)).2) v') at hequal
  have hlabels := Fin.castLE_injective hj hequal
  simpa [hd] using hlabels

/-- Data certifying that a blockwise edge coloring contains no monochromatic triangle. -/
structure PaletteBlockCertificate {I V K : Type*} [DecidableEq K]
    (C : SimpleGraph.TopEdgeLabeling (I × V) K) (j : ℕ) where
  /-- The colors omitted from internal edges of each block. -/
  palette : I → Finset K
  /-- A proper internal vertex coloring for every active color in a block. -/
  label : ∀ (i : I) (colour : K), colour ∉ palette i → V → Fin j
  internal_no_triangle :
    ∀ (i : I) (colour : K) (u v w : V),
      ¬ ((C.labelGraph colour).Adj (i, u) (i, v) ∧
         (C.labelGraph colour).Adj (i, u) (i, w) ∧
         (C.labelGraph colour).Adj (i, v) (i, w))
  missing_has_no_internal_edge :
    ∀ (i : I) (colour : K), colour ∈ palette i →
      ∀ u v : V, ¬ (C.labelGraph colour).Adj (i, u) (i, v)
  internal_labels_proper :
    ∀ (i : I) (colour : K) (hactive : colour ∉ palette i)
      (u v : V),
      (C.labelGraph colour).Adj (i, u) (i, v) →
        label i colour hactive u ≠ label i colour hactive v
  cross_edge_changes_membership :
    ∀ (i i' : I) (colour : K) (u v : V), i ≠ i' →
      (C.labelGraph colour).Adj (i, u) (i', v) →
        (colour ∈ palette i) ≠ (colour ∈ palette i')
  cross_edges_force_equal_active_labels :
    ∀ (i i' : I) (colour : K) (u u' v : V)
      (_hne : i ≠ i') (hactive : colour ∉ palette i),
      (C.labelGraph colour).Adj (i, u) (i', v) →
      (C.labelGraph colour).Adj (i, u') (i', v) →
        label i colour hactive u = label i colour hactive u'

namespace PaletteBlockCertificate

theorem noMonochromaticTriangle {I V K : Type*} [DecidableEq K]
    {C : SimpleGraph.TopEdgeLabeling (I × V) K} {j : ℕ}
    (certificate : PaletteBlockCertificate C j) :
    ∀ colour : K, (C.labelGraph colour).CliqueFree 3 := by
  classical
  intro colour t ht
  obtain ⟨x, y, z, hxy, hxz, hyz, _⟩ :=
    (SimpleGraph.is3Clique_iff).mp ht
  rcases x with ⟨i, u⟩
  rcases y with ⟨i', v⟩
  rcases z with ⟨i'', w⟩
  by_cases hii' : i = i'
  · subst i'
    by_cases hii'' : i = i''
    · subst i''
      exact certificate.internal_no_triangle i colour u v w ⟨hxy, hxz, hyz⟩
    · by_cases hmissing : colour ∈ certificate.palette i
      · exact certificate.missing_has_no_internal_edge i colour hmissing u v hxy
      · have hequal := certificate.cross_edges_force_equal_active_labels
          i i'' colour u v w hii'' hmissing hxz hyz
        exact certificate.internal_labels_proper
          i colour hmissing u v hxy hequal
  · by_cases hii'' : i = i''
    · subst i''
      by_cases hmissing : colour ∈ certificate.palette i
      · exact certificate.missing_has_no_internal_edge i colour hmissing u w hxz
      · have hequal := certificate.cross_edges_force_equal_active_labels
          i i' colour u w v hii' hmissing hxy hyz.symm
        exact certificate.internal_labels_proper
          i colour hmissing u w hxz hequal
    · by_cases hi'i'' : i' = i''
      · subst i''
        by_cases hmissing : colour ∈ certificate.palette i'
        · exact certificate.missing_has_no_internal_edge
            i' colour hmissing v w hyz
        · have hequal := certificate.cross_edges_force_equal_active_labels
            i' i colour v w u (Ne.symm hii') hmissing hxy.symm hxz.symm
          exact certificate.internal_labels_proper
            i' colour hmissing v w hyz hequal
      · exact no_three_pairwise_palette_disagreements
          (certificate.palette i) (certificate.palette i')
          (certificate.palette i'') colour
          (certificate.cross_edge_changes_membership
            i i' colour u v hii' hxy)
          (certificate.cross_edge_changes_membership
            i' i'' colour v w hi'i'' hyz)
          (certificate.cross_edge_changes_membership
            i'' i colour w u (Ne.symm hii'') hxz.symm)

/-- Extends the internal labels by a final label for omitted colors. -/
noncomputable def globalLabel {I V K : Type*} [DecidableEq K]
    {C : SimpleGraph.TopEdgeLabeling (I × V) K} {j : ℕ}
    (certificate : PaletteBlockCertificate C j) (colour : K)
    (x : I × V) : Fin (j + 1) := by
  classical
  exact
    if h : colour ∈ certificate.palette x.1 then
      Fin.last j
    else
      (certificate.label x.1 colour h x.2).castSucc

theorem colourGraph_colorable {I V K : Type*} [DecidableEq K]
    {C : SimpleGraph.TopEdgeLabeling (I × V) K} {j : ℕ}
    (certificate : PaletteBlockCertificate C j) (colour : K) :
    (C.labelGraph colour).Colorable (j + 1) := by
  classical
  refine ⟨SimpleGraph.Coloring.mk (globalLabel certificate colour) ?_⟩
  intro x y hadj
  rcases x with ⟨i, u⟩
  rcases y with ⟨i', v⟩
  by_cases hs : i = i'
  · subst i'
    by_cases hmissing : colour ∈ certificate.palette i
    · exact False.elim
        (certificate.missing_has_no_internal_edge i colour hmissing u v hadj)
    · have hproper := certificate.internal_labels_proper
        i colour hmissing u v hadj
      simp only [globalLabel, dite_eq_right hmissing]
      exact fun heq => hproper (Fin.castSucc_inj.mp heq)
  · have hchange := certificate.cross_edge_changes_membership
      i i' colour u v hs hadj
    by_cases hi : colour ∈ certificate.palette i
    · have hi' : colour ∉ certificate.palette i' := by
        intro h
        exact hchange (propext ⟨fun _ => h, fun _ => hi⟩)
      simp only [globalLabel, dite_eq_left hi, dite_eq_right hi']
      exact Ne.symm (Fin.castSucc_ne_last _)
    · have hi' : colour ∈ certificate.palette i' := by
        by_contra h
        exact hchange (propext ⟨fun h' => (hi h').elim, fun h' => (h h').elim⟩)
      simp only [globalLabel, dite_eq_right hi, dite_eq_left hi']
      exact Fin.castSucc_ne_last _

end PaletteBlockCertificate

/-- Lists `s` colors witnessing an ordered difference between two palettes. -/
noncomputable def paletteFamilyForwardList {N s : ℕ}
    (family : Finset (Finset (Fin N)))
    (hseparated : IsPaletteSeparated s family)
    (i i' : ↥family) (hne : i ≠ i') : Fin s ↪ Fin N :=
  differenceColourEmbedding i.val i'.val
    (hseparated i'.val i'.property i.val i.property
      (fun heq => hne (Subtype.ext heq.symm)))

theorem paletteFamilyForwardList_mem {N s : ℕ}
    (family : Finset (Finset (Fin N)))
    (hseparated : IsPaletteSeparated s family)
    (i i' : ↥family) (hne : i ≠ i') (d : Fin s) :
    paletteFamilyForwardList family hseparated i i' hne d ∈
      i'.val \ i.val := by
  unfold paletteFamilyForwardList
  exact differenceColourEmbedding_mem _ _ _ _

/-- Chooses a cross-block color from two separated palettes and coordinate vectors. -/
noncomputable def paletteFamilyCrossColour
    {V : Type*} {N t j H s : ℕ}
    (C : SimpleGraph.TopEdgeLabeling V (Fin (N - t)))
    (hC : ∀ colour : Fin (N - t), (C.labelGraph colour).Colorable j)
    (hj : j ≤ H)
    (family : Finset (Finset (Fin N)))
    (hcard : ∀ P ∈ family, P.card = t)
    (hseparated : IsPaletteSeparated s family)
    (f g : (Fin s → Fin H) → (Fin s → Fin H))
    (hcover : IsCoordinateCovering f g)
    (i i' : ↥family) (hne : i ≠ i') (u v : V) : Fin N :=
  paletteCrossColour C hC hj i.val i'.val
    (hcard i.val i.property) (hcard i'.val i'.property)
    (paletteFamilyForwardList family hseparated i i' hne)
    (paletteFamilyForwardList family hseparated i' i hne.symm)
    (paletteFamilyForwardList_mem family hseparated i i' hne)
    (paletteFamilyForwardList_mem family hseparated i' i hne.symm)
    f g hcover u v

theorem paletteFamilyCrossColour_changes_membership
    {V : Type*} {N t j H s : ℕ}
    (C : SimpleGraph.TopEdgeLabeling V (Fin (N - t)))
    (hC : ∀ colour : Fin (N - t), (C.labelGraph colour).Colorable j)
    (hj : j ≤ H)
    (family : Finset (Finset (Fin N)))
    (hcard : ∀ P ∈ family, P.card = t)
    (hseparated : IsPaletteSeparated s family)
    (f g : (Fin s → Fin H) → (Fin s → Fin H))
    (hcover : IsCoordinateCovering f g)
    (i i' : ↥family) (hne : i ≠ i') (u v : V) :
    (paletteFamilyCrossColour C hC hj family hcard hseparated
        f g hcover i i' hne u v ∈ i.val) ≠
      (paletteFamilyCrossColour C hC hj family hcard hseparated
        f g hcover i i' hne u v ∈ i'.val) := by
  exact paletteCrossColour_changes_membership C hC hj i.val i'.val
    (hcard i.val i.property) (hcard i'.val i'.property)
    (paletteFamilyForwardList family hseparated i i' hne)
    (paletteFamilyForwardList family hseparated i' i hne.symm)
    (paletteFamilyForwardList_mem family hseparated i i' hne)
    (paletteFamilyForwardList_mem family hseparated i' i hne.symm)
    f g hcover u v

theorem paletteFamilyCrossColour_same_left_label
    {V : Type*} {N t j H s : ℕ}
    (C : SimpleGraph.TopEdgeLabeling V (Fin (N - t)))
    (hC : ∀ colour : Fin (N - t), (C.labelGraph colour).Colorable j)
    (hj : j ≤ H)
    (family : Finset (Finset (Fin N)))
    (hcard : ∀ P ∈ family, P.card = t)
    (hseparated : IsPaletteSeparated s family)
    (f g : (Fin s → Fin H) → (Fin s → Fin H))
    (hcover : IsCoordinateCovering f g)
    (i i' : ↥family) (hne : i ≠ i')
    (u u' v : V) (colour : Fin N) (hactive : colour ∉ i.val)
    (hu : paletteFamilyCrossColour C hC hj family hcard hseparated
      f g hcover i i' hne u v = colour)
    (hu' : paletteFamilyCrossColour C hC hj family hcard hseparated
      f g hcover i i' hne u' v = colour) :
    paletteBlockLabel C hC i.val (hcard i.val i.property)
        colour hactive u =
      paletteBlockLabel C hC i.val (hcard i.val i.property)
        colour hactive u' := by
  exact paletteCrossColour_same_left_label C hC hj i.val i'.val
    (hcard i.val i.property) (hcard i'.val i'.property)
    (paletteFamilyForwardList family hseparated i i' hne)
    (paletteFamilyForwardList family hseparated i' i hne.symm)
    (paletteFamilyForwardList_mem family hseparated i i' hne)
    (paletteFamilyForwardList_mem family hseparated i' i hne.symm)
    f g hcover u u' v colour hactive hu hu'

theorem paletteFamilyCrossColour_same_right_label
    {V : Type*} {N t j H s : ℕ}
    (C : SimpleGraph.TopEdgeLabeling V (Fin (N - t)))
    (hC : ∀ colour : Fin (N - t), (C.labelGraph colour).Colorable j)
    (hj : j ≤ H)
    (family : Finset (Finset (Fin N)))
    (hcard : ∀ P ∈ family, P.card = t)
    (hseparated : IsPaletteSeparated s family)
    (f g : (Fin s → Fin H) → (Fin s → Fin H))
    (hcover : IsCoordinateCovering f g)
    (i i' : ↥family) (hne : i ≠ i')
    (u v v' : V) (colour : Fin N) (hactive : colour ∉ i'.val)
    (hv : paletteFamilyCrossColour C hC hj family hcard hseparated
      f g hcover i i' hne u v = colour)
    (hv' : paletteFamilyCrossColour C hC hj family hcard hseparated
      f g hcover i i' hne u v' = colour) :
    paletteBlockLabel C hC i'.val (hcard i'.val i'.property)
        colour hactive v =
      paletteBlockLabel C hC i'.val (hcard i'.val i'.property)
        colour hactive v' := by
  exact paletteCrossColour_same_right_label C hC hj i.val i'.val
    (hcard i.val i.property) (hcard i'.val i'.property)
    (paletteFamilyForwardList family hseparated i i' hne)
    (paletteFamilyForwardList family hseparated i' i hne.symm)
    (paletteFamilyForwardList_mem family hseparated i i' hne)
    (paletteFamilyForwardList_mem family hseparated i' i hne.symm)
    f g hcover u v v' colour hactive hv hv'

/-- Assigns colors recursively to edges between members of a palette family. -/
noncomputable def recursivePaletteEdgeColour
    {V : Type*} {N t j H s : ℕ}
    (C : SimpleGraph.TopEdgeLabeling V (Fin (N - t)))
    (hC : ∀ colour : Fin (N - t), (C.labelGraph colour).Colorable j)
    (hj : j ≤ H)
    (family : Finset (Finset (Fin N)))
    (hcard : ∀ P ∈ family, P.card = t)
    (hseparated : IsPaletteSeparated s family)
    (f g : (Fin s → Fin H) → (Fin s → Fin H))
    (hcover : IsCoordinateCovering f g)
    (x y : ↥family × V) (hne : x ≠ y) : Fin N := by
  classical
  exact
    if hsame : x.1 = y.1 then
      (paletteRelabel C x.1.val (hcard x.1.val x.1.property)).get
        x.2 y.2 (fun heq => hne (Prod.ext hsame heq))
    else if horder :
        (Finset.equivFin family) x.1 < (Finset.equivFin family) y.1 then
      paletteFamilyCrossColour C hC hj family hcard hseparated
        f g hcover x.1 y.1 hsame x.2 y.2
    else
      paletteFamilyCrossColour C hC hj family hcard hseparated
        f g hcover y.1 x.1 (Ne.symm hsame) y.2 x.2

theorem recursivePaletteEdgeColour_symm
    {V : Type*} {N t j H s : ℕ}
    (C : SimpleGraph.TopEdgeLabeling V (Fin (N - t)))
    (hC : ∀ colour : Fin (N - t), (C.labelGraph colour).Colorable j)
    (hj : j ≤ H)
    (family : Finset (Finset (Fin N)))
    (hcard : ∀ P ∈ family, P.card = t)
    (hseparated : IsPaletteSeparated s family)
    (f g : (Fin s → Fin H) → (Fin s → Fin H))
    (hcover : IsCoordinateCovering f g)
    (x y : ↥family × V) (hne : x ≠ y) :
    recursivePaletteEdgeColour C hC hj family hcard hseparated
        f g hcover y x hne.symm =
      recursivePaletteEdgeColour C hC hj family hcard hseparated
        f g hcover x y hne := by
  classical
  rcases x with ⟨i, u⟩
  rcases y with ⟨i', v⟩
  by_cases hsame : i = i'
  · subst i'
    have huv : u ≠ v := fun heq => hne (Prod.ext rfl heq)
    simpa [recursivePaletteEdgeColour] using
      (SimpleGraph.EdgeLabeling.get_comm
        (C := paletteRelabel C i.val (hcard i.val i.property))
        u v (Ne.symm huv))
  · have hrank :
        (Finset.equivFin family) i ≠ (Finset.equivFin family) i' :=
      fun heq => hsame ((Finset.equivFin family).injective heq)
    rcases lt_or_gt_of_ne hrank with horder | horder
    · simp [recursivePaletteEdgeColour, hsame, Ne.symm hsame,
        horder, not_lt_of_gt horder]
    · simp [recursivePaletteEdgeColour, hsame, Ne.symm hsame,
        horder, not_lt_of_gt horder]

/-- The complete edge coloring assembled recursively from a palette family. -/
noncomputable def recursivePaletteColouring
    {V : Type*} {N t j H s : ℕ}
    (C : SimpleGraph.TopEdgeLabeling V (Fin (N - t)))
    (hC : ∀ colour : Fin (N - t), (C.labelGraph colour).Colorable j)
    (hj : j ≤ H)
    (family : Finset (Finset (Fin N)))
    (hcard : ∀ P ∈ family, P.card = t)
    (hseparated : IsPaletteSeparated s family)
    (f g : (Fin s → Fin H) → (Fin s → Fin H))
    (hcover : IsCoordinateCovering f g) :
    SimpleGraph.TopEdgeLabeling (↥family × V) (Fin N) :=
  SimpleGraph.EdgeLabeling.mk
    (fun x y hne => recursivePaletteEdgeColour C hC hj family hcard
      hseparated f g hcover x y hne)
    (fun x y hne => recursivePaletteEdgeColour_symm C hC hj family hcard
      hseparated f g hcover x y hne)

theorem recursivePaletteColouring_get
    {V : Type*} {N t j H s : ℕ}
    (C : SimpleGraph.TopEdgeLabeling V (Fin (N - t)))
    (hC : ∀ colour : Fin (N - t), (C.labelGraph colour).Colorable j)
    (hj : j ≤ H)
    (family : Finset (Finset (Fin N)))
    (hcard : ∀ P ∈ family, P.card = t)
    (hseparated : IsPaletteSeparated s family)
    (f g : (Fin s → Fin H) → (Fin s → Fin H))
    (hcover : IsCoordinateCovering f g)
    (x y : ↥family × V) (hne : x ≠ y) :
    (recursivePaletteColouring C hC hj family hcard hseparated
      f g hcover).get x y hne =
        recursivePaletteEdgeColour C hC hj family hcard hseparated
          f g hcover x y hne := by
  rfl

theorem recursivePaletteColouring_internal_adj_iff
    {V : Type*} {N t j H s : ℕ}
    (C : SimpleGraph.TopEdgeLabeling V (Fin (N - t)))
    (hC : ∀ colour : Fin (N - t), (C.labelGraph colour).Colorable j)
    (hj : j ≤ H)
    (family : Finset (Finset (Fin N)))
    (hcard : ∀ P ∈ family, P.card = t)
    (hseparated : IsPaletteSeparated s family)
    (f g : (Fin s → Fin H) → (Fin s → Fin H))
    (hcover : IsCoordinateCovering f g)
    (i : ↥family) (colour : Fin N) (u v : V) :
    ((recursivePaletteColouring C hC hj family hcard hseparated
        f g hcover).labelGraph colour).Adj (i, u) (i, v) ↔
      ((paletteRelabel C i.val (hcard i.val i.property)).labelGraph
        colour).Adj u v := by
  constructor
  · intro hadj
    obtain ⟨hne, hcolour⟩ :=
      (SimpleGraph.TopEdgeLabeling.labelGraph_adj (i, u) (i, v)).mp hadj
    have huv : u ≠ v := by
      intro heq
      exact hne (Prod.ext rfl heq)
    apply (SimpleGraph.TopEdgeLabeling.labelGraph_adj u v).mpr
    refine ⟨huv, ?_⟩
    rw [recursivePaletteColouring_get] at hcolour
    simpa [recursivePaletteEdgeColour] using hcolour
  · intro hadj
    obtain ⟨huv, hcolour⟩ :=
      (SimpleGraph.TopEdgeLabeling.labelGraph_adj u v).mp hadj
    have hne : (i, u) ≠ (i, v) := by
      intro heq
      exact huv (congrArg Prod.snd heq)
    apply (SimpleGraph.TopEdgeLabeling.labelGraph_adj (i, u) (i, v)).mpr
    refine ⟨hne, ?_⟩
    rw [recursivePaletteColouring_get]
    simpa [recursivePaletteEdgeColour] using hcolour

theorem recursivePaletteColouring_cross_adj_iff_of_lt
    {V : Type*} {N t j H s : ℕ}
    (C : SimpleGraph.TopEdgeLabeling V (Fin (N - t)))
    (hC : ∀ colour : Fin (N - t), (C.labelGraph colour).Colorable j)
    (hj : j ≤ H)
    (family : Finset (Finset (Fin N)))
    (hcard : ∀ P ∈ family, P.card = t)
    (hseparated : IsPaletteSeparated s family)
    (f g : (Fin s → Fin H) → (Fin s → Fin H))
    (hcover : IsCoordinateCovering f g)
    (i i' : ↥family) (hne : i ≠ i')
    (horder : (Finset.equivFin family) i < (Finset.equivFin family) i')
    (colour : Fin N) (u v : V) :
    ((recursivePaletteColouring C hC hj family hcard hseparated
        f g hcover).labelGraph colour).Adj (i, u) (i', v) ↔
      paletteFamilyCrossColour C hC hj family hcard hseparated
        f g hcover i i' hne u v = colour := by
  constructor
  · intro hadj
    obtain ⟨hpair, hcolour⟩ :=
      (SimpleGraph.TopEdgeLabeling.labelGraph_adj (i, u) (i', v)).mp hadj
    rw [recursivePaletteColouring_get] at hcolour
    simpa [recursivePaletteEdgeColour, hne, horder] using hcolour
  · intro hcolour
    have hpair : (i, u) ≠ (i', v) := by
      intro heq
      exact hne (congrArg Prod.fst heq)
    apply (SimpleGraph.TopEdgeLabeling.labelGraph_adj (i, u) (i', v)).mpr
    refine ⟨hpair, ?_⟩
    rw [recursivePaletteColouring_get]
    simpa [recursivePaletteEdgeColour, hne, horder] using hcolour

theorem paletteFamily_reverse_rank_lt {N : ℕ}
    (family : Finset (Finset (Fin N)))
    (i i' : ↥family) (hne : i ≠ i')
    (hnot : ¬ (Finset.equivFin family) i <
      (Finset.equivFin family) i') :
    (Finset.equivFin family) i' < (Finset.equivFin family) i := by
  have hrank : (Finset.equivFin family) i ≠ (Finset.equivFin family) i' := by
    intro heq
    exact hne ((Finset.equivFin family).injective heq)
  exact lt_of_le_of_ne (le_of_not_gt hnot) hrank.symm

/-- The triangle-free certificate for the recursive palette coloring. -/
noncomputable def recursivePaletteCertificate
    {V : Type*} {N t j H s : ℕ}
    (C : SimpleGraph.TopEdgeLabeling V (Fin (N - t)))
    (htriangle : ∀ colour : Fin (N - t),
      (C.labelGraph colour).CliqueFree 3)
    (hC : ∀ colour : Fin (N - t), (C.labelGraph colour).Colorable j)
    (hj : j ≤ H)
    (family : Finset (Finset (Fin N)))
    (hcard : ∀ P ∈ family, P.card = t)
    (hseparated : IsPaletteSeparated s family)
    (f g : (Fin s → Fin H) → (Fin s → Fin H))
    (hcover : IsCoordinateCovering f g) :
    PaletteBlockCertificate
      (recursivePaletteColouring C hC hj family hcard hseparated
        f g hcover) j := by
  classical
  refine
    { palette := fun i => i.val
      label := fun i colour hactive =>
        paletteBlockLabel C hC i.val (hcard i.val i.property)
          colour hactive
      internal_no_triangle := ?_
      missing_has_no_internal_edge := ?_
      internal_labels_proper := ?_
      cross_edge_changes_membership := ?_
      cross_edges_force_equal_active_labels := ?_ }
  · intro i colour u v w htriangle'
    obtain ⟨huv, huw, hvw⟩ := htriangle'
    have huv' :=
      (recursivePaletteColouring_internal_adj_iff C hC hj family
        hcard hseparated f g hcover i colour u v).mp huv
    have huw' :=
      (recursivePaletteColouring_internal_adj_iff C hC hj family
        hcard hseparated f g hcover i colour u w).mp huw
    have hvw' :=
      (recursivePaletteColouring_internal_adj_iff C hC hj family
        hcard hseparated f g hcover i colour v w).mp hvw
    exact (paletteRelabel_cliqueFree C htriangle i.val
      (hcard i.val i.property) colour) {u, v, w}
        ((SimpleGraph.is3Clique_triple_iff).mpr ⟨huv', huw', hvw'⟩)
  · intro i colour hmissing u v hadj
    exact paletteRelabel_missing_no_adj C i.val
      (hcard i.val i.property) colour hmissing u v
        ((recursivePaletteColouring_internal_adj_iff C hC hj family
          hcard hseparated f g hcover i colour u v).mp hadj)
  · intro i colour hactive u v hadj
    exact paletteBlockLabel_valid C hC i.val
      (hcard i.val i.property) colour hactive u v
        ((recursivePaletteColouring_internal_adj_iff C hC hj family
          hcard hseparated f g hcover i colour u v).mp hadj)
  · intro i i' colour u v hne hadj
    by_cases horder :
        (Finset.equivFin family) i < (Finset.equivFin family) i'
    · have hcolour :=
        (recursivePaletteColouring_cross_adj_iff_of_lt C hC hj family
          hcard hseparated f g hcover i i' hne horder colour u v).mp hadj
      have hchange := paletteFamilyCrossColour_changes_membership
        C hC hj family hcard hseparated f g hcover i i' hne u v
      rw [hcolour] at hchange
      exact hchange
    · have hreverse := paletteFamily_reverse_rank_lt family i i' hne horder
      have hcolour :=
        (recursivePaletteColouring_cross_adj_iff_of_lt C hC hj family
          hcard hseparated f g hcover i' i (Ne.symm hne)
            hreverse colour v u).mp hadj.symm
      have hchange := paletteFamilyCrossColour_changes_membership
        C hC hj family hcard hseparated f g hcover i' i (Ne.symm hne) v u
      rw [hcolour] at hchange
      exact Ne.symm hchange
  · intro i i' colour u u' v hne hactive hadj hadj'
    by_cases horder :
        (Finset.equivFin family) i < (Finset.equivFin family) i'
    · have hu :=
        (recursivePaletteColouring_cross_adj_iff_of_lt C hC hj family
          hcard hseparated f g hcover i i' hne horder colour u v).mp hadj
      have hu' :=
        (recursivePaletteColouring_cross_adj_iff_of_lt C hC hj family
          hcard hseparated f g hcover i i' hne horder colour u' v).mp hadj'
      exact paletteFamilyCrossColour_same_left_label C hC hj family
        hcard hseparated f g hcover i i' hne u u' v colour hactive hu hu'
    · have hreverse := paletteFamily_reverse_rank_lt family i i' hne horder
      have hu :=
        (recursivePaletteColouring_cross_adj_iff_of_lt C hC hj family
          hcard hseparated f g hcover i' i (Ne.symm hne)
            hreverse colour v u).mp hadj.symm
      have hu' :=
        (recursivePaletteColouring_cross_adj_iff_of_lt C hC hj family
          hcard hseparated f g hcover i' i (Ne.symm hne)
            hreverse colour v u').mp hadj'.symm
      exact paletteFamilyCrossColour_same_right_label C hC hj family
        hcard hseparated f g hcover i' i (Ne.symm hne)
          v u u' colour hactive hu hu'

/-- Every word is matched in some coordinate by at least `s` rows of a matrix. -/
def IsSaturated {H m s : ℕ}
    (A : Fin s → (Fin m → Fin H) → Fin H) : Prop :=
  ∀ T : Finset (Fin m → Fin H), T.card = m + 1 →
    ∃ row : Fin s, ∀ symbol : Fin H,
      ∃ column ∈ T, A row column = symbol

/-- A matrix row agrees with a word in at least one coordinate. -/
def RowCovers {H m : ℕ}
    (T : Finset (Fin m → Fin H))
    (row : (Fin m → Fin H) → Fin H) : Prop :=
  ∀ symbol : Fin H, ∃ column ∈ T, row column = symbol

/-- Rows that fail to cover a fixed word. -/
noncomputable def badSaturationRows (H m : ℕ)
    (T : Finset (Fin m → Fin H)) :
    Finset ((Fin m → Fin H) → Fin H) := by
  classical
  exact Finset.univ.filter (fun row => ¬ RowCovers T row)

/-- Rows omitting a chosen symbol from all coordinates. -/
noncomputable def missingSymbolRows (H m : ℕ)
    (T : Finset (Fin m → Fin H)) (symbol : Fin H) :
    Finset ((Fin m → Fin H) → Fin H) := by
  classical
  exact Fintype.piFinset fun column =>
    if column ∈ T then (Finset.univ : Finset (Fin H)).erase symbol
    else Finset.univ

theorem mem_missingSymbolRows (H m : ℕ)
    (T : Finset (Fin m → Fin H)) (symbol : Fin H)
    (row : (Fin m → Fin H) → Fin H) :
    row ∈ missingSymbolRows H m T symbol ↔
      ∀ column ∈ T, row column ≠ symbol := by
  classical
  rw [missingSymbolRows, Fintype.mem_piFinset]
  constructor
  · intro hrow column hcolumn
    simpa [hcolumn] using hrow column
  · intro hrow column
    by_cases hcolumn : column ∈ T
    · simpa [hcolumn] using hrow column hcolumn
    · simp [hcolumn]

theorem card_missingSymbolRows (H m : ℕ)
    (T : Finset (Fin m → Fin H)) (symbol : Fin H) :
    (missingSymbolRows H m T symbol).card =
      (H - 1) ^ T.card * H ^ (H ^ m - T.card) := by
  classical
  calc
    (missingSymbolRows H m T symbol).card =
        ∏ column : Fin m → Fin H,
          if column ∈ T then H - 1 else H := by
      rw [missingSymbolRows, Fintype.card_piFinset]
      apply Finset.prod_congr rfl
      intro column _
      split_ifs <;> simp
    _ = (H - 1) ^ T.card * H ^ (H ^ m - T.card) := by
      rw [Finset.prod_ite]
      simp [Finset.filter_notMem_eq_sdiff, Finset.card_sdiff_of_subset]

theorem card_badSaturationRows_le (H m : ℕ)
    (T : Finset (Fin m → Fin H)) :
    (badSaturationRows H m T).card ≤
      H * ((H - 1) ^ T.card * H ^ (H ^ m - T.card)) := by
  classical
  have hsubset : badSaturationRows H m T ⊆
      (Finset.univ : Finset (Fin H)).biUnion
        (fun symbol => missingSymbolRows H m T symbol) := by
    intro row hrow
    have hbad : ¬ RowCovers T row := by
      simpa [badSaturationRows] using hrow
    unfold RowCovers at hbad
    push Not at hbad
    obtain ⟨symbol, hsymbol⟩ := hbad
    exact Finset.mem_biUnion.mpr
      ⟨symbol, Finset.mem_univ symbol,
        (mem_missingSymbolRows H m T symbol row).mpr hsymbol⟩
  calc
    (badSaturationRows H m T).card ≤
        ((Finset.univ : Finset (Fin H)).biUnion
          (fun symbol => missingSymbolRows H m T symbol)).card :=
      Finset.card_le_card hsubset
    _ ≤ ∑ symbol : Fin H, (missingSymbolRows H m T symbol).card :=
      Finset.card_biUnion_le
    _ = H * ((H - 1) ^ T.card * H ^ (H ^ m - T.card)) := by
      simp [card_missingSymbolRows]

theorem missing_symbol_power_bound (H m : ℕ) (hH : 2 ≤ H)
    (hm : 2 * (H : ℝ) * Real.log (H : ℝ) ≤ (m : ℝ)) :
    (H : ℝ) ^ 2 * ((H : ℝ) - 1) ^ (m + 1) <
      (H : ℝ) ^ (m + 1) := by
  have hHpos : 0 < (H : ℝ) := by
    exact_mod_cast (show 0 < H by omega)
  have hfrac_nonneg : 0 ≤ 1 - 1 / (H : ℝ) := by
    apply sub_nonneg.mpr
    apply (div_le_iff₀ hHpos).mpr
    norm_num
    exact_mod_cast (show 1 ≤ H by omega)
  have hfrac_exp : 1 - 1 / (H : ℝ) ≤
      Real.exp (-(1 / (H : ℝ))) := by
    linarith [Real.add_one_le_exp (-(1 / (H : ℝ)))]
  have hfrac_strict :
      (1 - 1 / (H : ℝ)) ^ (m + 1) < ((H : ℝ) ^ 2)⁻¹ := by
    calc
      (1 - 1 / (H : ℝ)) ^ (m + 1) ≤
          Real.exp (-(1 / (H : ℝ))) ^ (m + 1) :=
        pow_le_pow_left₀ hfrac_nonneg hfrac_exp _
      _ = Real.exp (-((m + 1 : ℕ) : ℝ) / (H : ℝ)) := by
        rw [← Real.exp_nat_mul]
        congr 1
        push_cast
        ring
      _ < Real.exp (-2 * Real.log (H : ℝ)) := by
        apply Real.exp_strictMono
        apply (div_lt_iff₀ hHpos).mpr
        push_cast
        nlinarith
      _ = ((H : ℝ) ^ 2)⁻¹ := by
        rw [show -2 * Real.log (H : ℝ) =
          -(Real.log (H : ℝ) + Real.log (H : ℝ)) by ring]
        rw [Real.exp_neg, Real.exp_add, Real.exp_log hHpos, ← pow_two]
  have hidentity : 1 - 1 / (H : ℝ) = ((H : ℝ) - 1) / H := by
    field_simp
  rw [hidentity, div_pow] at hfrac_strict
  have hcross := (div_lt_div_iff₀
    (pow_pos hHpos (m + 1)) (pow_pos hHpos 2)).mp
      (show ((H : ℝ) - 1) ^ (m + 1) / (H : ℝ) ^ (m + 1) <
        1 / (H : ℝ) ^ 2 by simpa [one_div] using hfrac_strict)
  simpa [mul_comm] using hcross

theorem missing_symbol_power_bound_nat (H m : ℕ) (hH : 2 ≤ H)
    (hm : 2 * (H : ℝ) * Real.log (H : ℝ) ≤ (m : ℝ)) :
    H ^ 2 * (H - 1) ^ (m + 1) < H ^ (m + 1) := by
  have hreal := missing_symbol_power_bound H m hH hm
  have hcast :
      ((H ^ 2 * (H - 1) ^ (m + 1) : ℕ) : ℝ) <
        ((H ^ (m + 1) : ℕ) : ℝ) := by
    simpa [Nat.cast_sub (show 1 ≤ H by omega)] using hreal
  exact_mod_cast hcast

theorem card_badSaturationRows_mul_lt (H m : ℕ) (hH : 2 ≤ H)
    (hm : 2 * (H : ℝ) * Real.log (H : ℝ) ≤ (m : ℝ))
    (T : Finset (Fin m → Fin H)) (hT : T.card = m + 1) :
    (badSaturationRows H m T).card * H < H ^ (H ^ m) := by
  have hcolumns : m + 1 ≤ H ^ m := by
    calc
      m + 1 = T.card := hT.symm
      _ ≤ Fintype.card (Fin m → Fin H) := Finset.card_le_univ T
      _ = H ^ m := by simp
  have hremaining : 0 < H ^ (H ^ m - (m + 1)) := by
    exact pow_pos (show 0 < H by omega) _
  calc
    (badSaturationRows H m T).card * H ≤
        (H * ((H - 1) ^ T.card * H ^ (H ^ m - T.card))) * H :=
      Nat.mul_le_mul_right H (card_badSaturationRows_le H m T)
    _ = (H ^ 2 * (H - 1) ^ (m + 1)) *
          H ^ (H ^ m - (m + 1)) := by rw [hT]; ring
    _ < H ^ (m + 1) * H ^ (H ^ m - (m + 1)) :=
      Nat.mul_lt_mul_of_pos_right
        (missing_symbol_power_bound_nat H m hH hm) hremaining
    _ = H ^ (H ^ m) := by
      rw [← pow_add]
      congr 1
      omega

theorem card_badSaturationRows_lt_pow (H m : ℕ) (hH : 2 ≤ H)
    (hm : 2 * (H : ℝ) * Real.log (H : ℝ) ≤ (m : ℝ))
    (T : Finset (Fin m → Fin H)) (hT : T.card = m + 1) :
    (badSaturationRows H m T).card < H ^ (H ^ m - 1) := by
  have hpositive : 0 < H ^ m := pow_pos (show 0 < H by omega) _
  have hpower : H ^ (H ^ m) = H ^ (H ^ m - 1) * H := by
    rw [← pow_succ]
    congr 1
    omega
  have hrows := card_badSaturationRows_mul_lt H m hH hm T hT
  rw [hpower] at hrows
  exact (Nat.mul_lt_mul_right (show 0 < H by omega)).mp hrows

/-- Matrices for which some word is covered by fewer than `s` rows. -/
noncomputable def badSaturationMatrices (H m s : ℕ)
    (T : Finset (Fin m → Fin H)) :
    Finset (Fin s → (Fin m → Fin H) → Fin H) :=
  Fintype.piFinset fun _ : Fin s => badSaturationRows H m T

theorem card_badSaturationMatrices (H m s : ℕ)
    (T : Finset (Fin m → Fin H)) :
    (badSaturationMatrices H m s T).card =
      (badSaturationRows H m T).card ^ s := by
  classical
  simp [badSaturationMatrices, Fintype.card_piFinset]

theorem exists_saturated_of_bad_row_union_bound (H m s : ℕ)
    (hbound :
      (∑ T ∈
          (Finset.univ : Finset (Fin m → Fin H)).powersetCard (m + 1),
        (badSaturationRows H m T).card ^ s) <
          Fintype.card (Fin s → (Fin m → Fin H) → Fin H)) :
    ∃ A : Fin s → (Fin m → Fin H) → Fin H, IsSaturated A := by
  classical
  by_contra hno
  push Not at hno
  let columnSets : Finset (Finset (Fin m → Fin H)) :=
    (Finset.univ : Finset (Fin m → Fin H)).powersetCard (m + 1)
  have hcover :
      (Finset.univ : Finset (Fin s → (Fin m → Fin H) → Fin H)) ⊆
        columnSets.biUnion (fun T => badSaturationMatrices H m s T) := by
    intro A _
    have hA := hno A
    unfold IsSaturated at hA
    push Not at hA
    obtain ⟨T, hTcard, hrows⟩ := hA
    apply Finset.mem_biUnion.mpr
    refine ⟨T, ?_, ?_⟩
    · simp [columnSets, hTcard]
    · simp only [badSaturationMatrices, Fintype.mem_piFinset,
        badSaturationRows, Finset.mem_filter, Finset.mem_univ, true_and]
      intro row
      unfold RowCovers
      intro hcover_row
      obtain ⟨symbol, hmissing⟩ := hrows row
      obtain ⟨column, hcolumn, heq⟩ := hcover_row symbol
      exact hmissing column hcolumn heq
  have hcard :
      Fintype.card (Fin s → (Fin m → Fin H) → Fin H) ≤
        ∑ T ∈ columnSets, (badSaturationMatrices H m s T).card := by
    calc
      Fintype.card (Fin s → (Fin m → Fin H) → Fin H) =
          (Finset.univ : Finset (Fin s → (Fin m → Fin H) → Fin H)).card := by
            simp
      _ ≤ (columnSets.biUnion
        (fun T => badSaturationMatrices H m s T)).card :=
        Finset.card_le_card hcover
      _ ≤ ∑ T ∈ columnSets, (badSaturationMatrices H m s T).card :=
        Finset.card_biUnion_le
  simp_rw [card_badSaturationMatrices] at hcard
  change
    Fintype.card (Fin s → (Fin m → Fin H) → Fin H) ≤
      ∑ T ∈
        (Finset.univ : Finset (Fin m → Fin H)).powersetCard (m + 1),
          (badSaturationRows H m T).card ^ s at hcard
  exact (Nat.not_lt_of_ge hcard) hbound

theorem exists_saturated_matrix (H m : ℕ) (hH : 2 ≤ H)
    (hm : 2 * (H : ℝ) * Real.log (H : ℝ) ≤ (m : ℝ)) :
    ∃ A : Fin (m * (m + 1) + 1) → (Fin m → Fin H) → Fin H,
      IsSaturated A := by
  classical
  let s := m * (m + 1) + 1
  let columnSets : Finset (Finset (Fin m → Fin H)) :=
    (Finset.univ : Finset (Fin m → Fin H)).powersetCard (m + 1)
  apply exists_saturated_of_bad_row_union_bound H m s
  have hterms : ∀ T ∈ columnSets,
      (badSaturationRows H m T).card ^ s ≤
        (H ^ (H ^ m - 1)) ^ s := by
    intro T hT
    have hcard : T.card = m + 1 :=
      (Finset.mem_powersetCard.mp hT).2
    exact Nat.pow_le_pow_left
      (card_badSaturationRows_lt_pow H m hH hm T hcard).le s
  have hnumber : columnSets.card ≤ (H ^ m) ^ (m + 1) := by
    dsimp [columnSets]
    simpa using Nat.choose_le_pow (H ^ m) (m + 1)
  have hpositive : 0 < H ^ m := pow_pos (show 0 < H by omega) _
  change
    (∑ T ∈ columnSets, (badSaturationRows H m T).card ^ s) <
      Fintype.card (Fin s → (Fin m → Fin H) → Fin H)
  calc
    (∑ T ∈ columnSets, (badSaturationRows H m T).card ^ s) ≤
        columnSets.card * (H ^ (H ^ m - 1)) ^ s := by
      calc
        (∑ T ∈ columnSets, (badSaturationRows H m T).card ^ s) ≤
            ∑ _T ∈ columnSets, (H ^ (H ^ m - 1)) ^ s := by
          exact Finset.sum_le_sum fun T hT => hterms T hT
        _ = columnSets.card * (H ^ (H ^ m - 1)) ^ s := by simp
    _ ≤ (H ^ m) ^ (m + 1) * (H ^ (H ^ m - 1)) ^ s :=
      Nat.mul_le_mul_right _ hnumber
    _ = H ^ (m * (m + 1) + (H ^ m - 1) * s) := by
      rw [← pow_mul, ← pow_mul, ← pow_add]
    _ < H ^ (H ^ m * s) := by
      apply Nat.pow_lt_pow_right (show 1 < H by omega)
      calc
        m * (m + 1) + (H ^ m - 1) * s <
            s + (H ^ m - 1) * s := by
          apply Nat.add_lt_add_right
          dsimp [s]
          omega
        _ = 1 * s + (H ^ m - 1) * s := by simp
        _ = (1 + (H ^ m - 1)) * s := by rw [Nat.add_mul]
        _ = H ^ m * s := by
          congr 1
          omega
    _ = Fintype.card (Fin s → (Fin m → Fin H) → Fin H) := by
      simp [← pow_mul]

/-- The width parameter used for the saturated-matrix construction. -/
noncomputable def saturatedMatrixWidth (H : ℕ) : ℕ :=
  ⌈2 * (H : ℝ) * Real.log (H : ℝ)⌉₊

/-- The row-count parameter used for the saturated-matrix construction. -/
noncomputable def saturatedMatrixRows (H : ℕ) : ℕ :=
  saturatedMatrixWidth H * (saturatedMatrixWidth H + 1) + 1

theorem exists_saturated_matrix_ceil (H : ℕ) (hH : 2 ≤ H) :
    ∃ A : Fin (saturatedMatrixRows H) →
        (Fin (saturatedMatrixWidth H) → Fin H) → Fin H,
      IsSaturated A := by
  have hwidth :
      2 * (H : ℝ) * Real.log (H : ℝ) ≤
        (saturatedMatrixWidth H : ℝ) := by
    exact Nat.le_ceil _
  simpa [saturatedMatrixRows] using
    exists_saturated_matrix H (saturatedMatrixWidth H) hH hwidth

/-- Columns on which a matrix row differs from a prescribed word. -/
noncomputable def exceptionalColumns {H m s : ℕ}
    (A : Fin s → (Fin m → Fin H) → Fin H)
    (y : Fin s → Fin H) : Finset (Fin m → Fin H) := by
  classical
  exact Finset.univ.filter (fun z => ∀ row : Fin s, A row z ≠ y row)

theorem mem_exceptionalColumns {H m s : ℕ}
    (A : Fin s → (Fin m → Fin H) → Fin H)
    (y : Fin s → Fin H) (z : Fin m → Fin H) :
    z ∈ exceptionalColumns A y ↔
      ∀ row : Fin s, A row z ≠ y row := by
  classical
  simp [exceptionalColumns]

theorem card_exceptionalColumns_le {H m s : ℕ}
    (A : Fin s → (Fin m → Fin H) → Fin H)
    (hA : IsSaturated A) (y : Fin s → Fin H) :
    (exceptionalColumns A y).card ≤ m := by
  classical
  by_contra hnot
  have hcard : m + 1 ≤ (exceptionalColumns A y).card := by
    omega
  obtain ⟨T, hTsub, hTcard⟩ := Finset.exists_subset_card_eq hcard
  obtain ⟨row, hrow⟩ := hA T hTcard
  obtain ⟨z, hzT, hz⟩ := hrow (y row)
  have hzexception : z ∈ exceptionalColumns A y := hTsub hzT
  exact (mem_exceptionalColumns A y z).mp hzexception row hz

/-- An enumeration of the exceptional columns for one row. -/
noncomputable def exceptionalColumnIndex {H m s : ℕ}
    (A : Fin s → (Fin m → Fin H) → Fin H)
    (hA : IsSaturated A) (y : Fin s → Fin H) :
    (exceptionalColumns A y) ↪ Fin m :=
  (Finset.equivFin (exceptionalColumns A y)).toEmbedding.trans
    (Fin.castLEEmb (card_exceptionalColumns_le A hA y))

/-- A word obtained by reading one selected matrix row. -/
def backwardGuess {H m s : ℕ}
    (A : Fin s → (Fin m → Fin H) → Fin H)
    (hms : m ≤ s) (x : Fin s → Fin H) : Fin s → Fin H :=
  fun row => A row (fun coordinate => x (Fin.castLE hms coordinate))

/-- A word chosen to disagree with a target on its exceptional columns. -/
noncomputable def forwardGuess {H m s : ℕ}
    (A : Fin s → (Fin m → Fin H) → Fin H)
    (hA : IsSaturated A) (hH : 0 < H) (hms : m ≤ s)
    (y : Fin s → Fin H) (row : Fin s) : Fin H := by
  classical
  let index := exceptionalColumnIndex A hA y
  exact
    if h : ∃ z : exceptionalColumns A y,
        Fin.castLE hms (index z) = row then
      (Classical.choose h).val (index (Classical.choose h))
    else
      ⟨0, hH⟩

theorem saturated_coordinate_covering {H m s : ℕ}
    (A : Fin s → (Fin m → Fin H) → Fin H)
    (hA : IsSaturated A) (hH : 0 < H) (hms : m ≤ s) :
    ∃ f g : (Fin s → Fin H) → (Fin s → Fin H),
      ∀ x y : Fin s → Fin H,
        (∃ row : Fin s, x row = f y row) ∨
        (∃ row : Fin s, y row = g x row) := by
  classical
  refine ⟨forwardGuess A hA hH hms, backwardGuess A hms, ?_⟩
  intro x y
  by_cases hback : ∃ row : Fin s, y row = backwardGuess A hms x row
  · exact Or.inr hback
  · left
    let z : Fin m → Fin H := fun coordinate => x (Fin.castLE hms coordinate)
    have hz : z ∈ exceptionalColumns A y := by
      apply (mem_exceptionalColumns A y z).mpr
      intro row heq
      apply hback
      refine ⟨row, ?_⟩
      simpa [backwardGuess, z] using heq.symm
    let ez : exceptionalColumns A y := ⟨z, hz⟩
    let index := exceptionalColumnIndex A hA y
    let row : Fin s := Fin.castLE hms (index ez)
    refine ⟨row, ?_⟩
    have hexists : ∃ w : exceptionalColumns A y,
        Fin.castLE hms (index w) = row := ⟨ez, rfl⟩
    have hindex : index (Classical.choose hexists) = index ez :=
      Fin.castLE_injective hms (Classical.choose_spec hexists)
    have hchosen : Classical.choose hexists = ez := index.injective hindex
    change x row =
      if h : ∃ w : exceptionalColumns A y,
          Fin.castLE hms (index w) = row then
        (Classical.choose h).val (index (Classical.choose h))
      else
        ⟨0, hH⟩
    rw [dite_eq_left hexists, hchosen]

theorem exists_coordinate_covering (H : ℕ) (hH : 2 ≤ H) :
    ∃ f g : (Fin (saturatedMatrixRows H) → Fin H) →
        (Fin (saturatedMatrixRows H) → Fin H),
      IsCoordinateCovering f g := by
  obtain ⟨A, hA⟩ := exists_saturated_matrix_ceil H hH
  have hwidth : saturatedMatrixWidth H ≤ saturatedMatrixRows H := by
    dsimp [saturatedMatrixRows]
    nlinarith [sq_nonneg (saturatedMatrixWidth H : ℤ)]
  exact saturated_coordinate_covering A hA (by omega) hwidth

theorem exists_recursivePaletteColouring_fin
    {n N t j H : ℕ}
    (C : SimpleGraph.TopEdgeLabeling (Fin n) (Fin (N - t)))
    (htriangle : ∀ colour : Fin (N - t),
      (C.labelGraph colour).CliqueFree 3)
    (hC : ∀ colour : Fin (N - t), (C.labelGraph colour).Colorable j)
    (hH : 2 ≤ H) (hj : j ≤ H)
    (family : Finset (Finset (Fin N)))
    (hcard : ∀ P ∈ family, P.card = t)
    (hseparated : IsPaletteSeparated (saturatedMatrixRows H) family) :
    ∃ C' : SimpleGraph.TopEdgeLabeling
        (Fin (family.card * n)) (Fin N),
      TriangleFree C' ∧
        (∀ colour : Fin N, (C'.labelGraph colour).Colorable (j + 1)) := by
  classical
  obtain ⟨f, g, hcover⟩ := exists_coordinate_covering H hH
  let C' := recursivePaletteColouring C hC hj family hcard hseparated
    f g hcover
  let certificate := recursivePaletteCertificate C htriangle hC hj family
    hcard hseparated f g hcover
  have hproduct : Fintype.card (↥family × Fin n) = family.card * n := by
    simp
  let embedding : Fin (family.card * n) ↪ (↥family × Fin n) :=
    (Fintype.equivFinOfCardEq hproduct).symm.toEmbedding
  refine ⟨C'.pullback embedding, ?_, ?_⟩
  · exact cliqueFree_pullback_embedding C' embedding
      certificate.noMonochromaticTriangle
  · intro colour
    exact colorable_pullback_embedding C' embedding colour
      (certificate.colourGraph_colorable colour)

/-- The unique edge coloring of a singleton vertex set with color zero. -/
def singletonZeroColouring :
    SimpleGraph.TopEdgeLabeling (Fin 1) (Fin 0) := by
  intro edge
  exfalso
  obtain ⟨edge, hedge⟩ := edge
  induction edge using Sym2.inductionOn with
  | _ u v =>
      exact hedge (Subsingleton.elim u v)

/-- A stagewise lower bound on the size of a recursively constructed coloring. -/
def PaletteGrowthBound (a s j n : ℕ) : Prop :=
  (j.factorial : ℝ) ^ (a * s) ≤
    (n : ℝ) * (s : ℝ) ^ j *
      (Real.exp 1 ^ 2 * (a : ℝ) ^ 2) ^ (s * j) *
      (j.factorial : ℝ) ^ s

theorem paletteGrowthBound_succ {a s j n B : ℕ}
    (hstage : ((j + 1 : ℕ) : ℝ) ^ (a * s) ≤
      (B : ℝ) * (s : ℝ) *
        (Real.exp 1 ^ 2 * (a : ℝ) ^ 2 * ((j + 1 : ℕ) : ℝ)) ^ s)
    (hprevious : PaletteGrowthBound a s j n) :
    PaletteGrowthBound a s (j + 1) (B * n) := by
  unfold PaletteGrowthBound at hprevious ⊢
  calc
    (((j + 1).factorial : ℕ) : ℝ) ^ (a * s) =
        ((j + 1 : ℕ) : ℝ) ^ (a * s) *
          (j.factorial : ℝ) ^ (a * s) := by
      simp [Nat.factorial_succ, mul_pow]
    _ ≤
        ((B : ℝ) * (s : ℝ) *
          (Real.exp 1 ^ 2 * (a : ℝ) ^ 2 *
            ((j + 1 : ℕ) : ℝ)) ^ s) *
        ((n : ℝ) * (s : ℝ) ^ j *
          (Real.exp 1 ^ 2 * (a : ℝ) ^ 2) ^ (s * j) *
          (j.factorial : ℝ) ^ s) := by
      exact mul_le_mul hstage hprevious (by positivity) (by positivity)
    _ =
        ((B * n : ℕ) : ℝ) * (s : ℝ) ^ (j + 1) *
          (Real.exp 1 ^ 2 * (a : ℝ) ^ 2) ^ (s * (j + 1)) *
          (((j + 1).factorial : ℕ) : ℝ) ^ s := by
      push_cast
      simp only [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one,
        Nat.mul_succ, pow_add, pow_succ, mul_pow]
      ring

theorem exists_recursivePaletteStage (H a j : ℕ)
    (hH : 2 ≤ H) (ha : 2 ≤ a) (hj : j ≤ H) :
    ∃ (n : ℕ)
      (C : SimpleGraph.TopEdgeLabeling (Fin n)
        (Fin (j * (a * saturatedMatrixRows H)))),
      TriangleFree C ∧
        (∀ colour : Fin (j * (a * saturatedMatrixRows H)),
          (C.labelGraph colour).Colorable (j + 1)) ∧
        PaletteGrowthBound a (saturatedMatrixRows H) j n := by
  classical
  have hs : 0 < saturatedMatrixRows H := by
    simp [saturatedMatrixRows]
  induction j with
  | zero =>
      refine ⟨1, (by simpa using singletonZeroColouring), ?_, ?_, ?_⟩
      · intro colour
        exact Fin.elim0 (by simpa using colour)
      · intro colour
        exact Fin.elim0 (by simpa using colour)
      · simp [PaletteGrowthBound]
  | succ j ih =>
      obtain ⟨n, C, htriangle, hcolour, hgrowth⟩ := ih (by omega)
      obtain ⟨family, hfamily, hseparated, hstage⟩ :=
        exists_stage_palette_packing_exp (j + 1) a
          (saturatedMatrixRows H) (by omega) ha hs
      have hcard :
          ∀ P ∈ family, P.card = a * saturatedMatrixRows H := by
        intro P hP
        exact (Finset.mem_powersetCard.mp (hfamily hP)).2
      have hsubtract :
          (j + 1) * (a * saturatedMatrixRows H) -
            a * saturatedMatrixRows H =
              j * (a * saturatedMatrixRows H) := by
        simp [Nat.succ_mul]
      have hstep := @exists_recursivePaletteColouring_fin
        n ((j + 1) * (a * saturatedMatrixRows H))
        (a * saturatedMatrixRows H) (j + 1) H
      rw [hsubtract] at hstep
      obtain ⟨C', htriangle', hcolour'⟩ :=
        hstep C htriangle hcolour hH hj family hcard hseparated
      exact ⟨family.card * n, C', htriangle', hcolour',
        paletteGrowthBound_succ hstage hgrowth⟩

theorem palette_exp_loss_bound (H a s : ℕ)
    (hH : 2 ≤ H) (ha : 2 ≤ a) (hs : 0 < s)
    (hlogH : Real.log (H : ℝ) ≤ (a : ℝ)) :
    ((H : ℝ) / Real.exp 4) ^ (H * (a * s)) ≤
      ((H : ℝ) / Real.exp 1) ^ (H * ((a - 1) * s)) /
        ((s : ℝ) ^ H *
          (Real.exp 1 ^ 2 * (a : ℝ) ^ 2) ^ (s * H)) := by
  have hHpos : (0 : ℝ) < H := by exact_mod_cast (by omega : 0 < H)
  have hapos : (0 : ℝ) < a := by exact_mod_cast (by omega : 0 < a)
  have hspos : (0 : ℝ) < s := by exact_mod_cast hs
  have hepos : 0 < Real.exp 1 ^ 2 * (a : ℝ) ^ 2 := by positivity
  have hbasepos : 0 < (H : ℝ) / Real.exp 1 := by positivity
  have htargetpos :
      0 < ((H : ℝ) / Real.exp 4) ^ (H * (a * s)) := by positivity
  have hsourcepos :
      0 < ((H : ℝ) / Real.exp 1) ^ (H * ((a - 1) * s)) /
        ((s : ℝ) ^ H *
          (Real.exp 1 ^ 2 * (a : ℝ) ^ 2) ^ (s * H)) := by
    positivity
  have hloga : Real.log (a : ℝ) ≤ (a : ℝ) - 1 :=
    Real.log_le_sub_one_of_pos hapos
  have hlogs : Real.log (s : ℝ) ≤ (s : ℝ) - 1 :=
    Real.log_le_sub_one_of_pos hspos
  have hweightedH :
      (s : ℝ) * Real.log (H : ℝ) ≤ (s : ℝ) * (a : ℝ) :=
    mul_le_mul_of_nonneg_left hlogH hspos.le
  have hweightedA :
      2 * (s : ℝ) * Real.log (a : ℝ) ≤
        2 * (s : ℝ) * ((a : ℝ) - 1) := by
    gcongr
  have hcore :
      (a : ℝ) * (s : ℝ) * (Real.log (H : ℝ) - 4) +
          Real.log (s : ℝ) +
          (s : ℝ) * (2 + 2 * Real.log (a : ℝ)) ≤
        ((a : ℝ) - 1) * (s : ℝ) *
          (Real.log (H : ℝ) - 1) := by
    nlinarith
  have hscaled := mul_le_mul_of_nonneg_left hcore hHpos.le
  have htargetlog :
      Real.log (((H : ℝ) / Real.exp 4) ^ (H * (a * s))) =
        (H : ℝ) * (a : ℝ) * (s : ℝ) *
          (Real.log (H : ℝ) - 4) := by
    rw [Real.log_pow,
      Real.log_div hHpos.ne' (Real.exp_ne_zero 4), Real.log_exp]
    push_cast
    ring
  have hsourcelog :
      Real.log
          (((H : ℝ) / Real.exp 1) ^ (H * ((a - 1) * s)) /
            ((s : ℝ) ^ H *
              (Real.exp 1 ^ 2 * (a : ℝ) ^ 2) ^ (s * H))) =
        (H : ℝ) * ((a : ℝ) - 1) * (s : ℝ) *
            (Real.log (H : ℝ) - 1) -
          ((H : ℝ) * Real.log (s : ℝ) +
            (s : ℝ) * (H : ℝ) *
              (2 + 2 * Real.log (a : ℝ))) := by
    rw [Real.log_div
      (pow_ne_zero _ hbasepos.ne')
      (mul_ne_zero (pow_ne_zero _ hspos.ne') (pow_ne_zero _ hepos.ne'))]
    rw [Real.log_pow,
      Real.log_div hHpos.ne' (Real.exp_ne_zero 1), Real.log_exp]
    rw [Real.log_mul (pow_ne_zero _ hspos.ne') (pow_ne_zero _ hepos.ne'),
      Real.log_pow, Real.log_pow]
    rw [Real.log_mul (pow_ne_zero _ (Real.exp_ne_zero 1))
      (pow_ne_zero _ hapos.ne'), Real.log_pow, Real.log_exp, Real.log_pow]
    push_cast
    rw [Nat.cast_sub (by omega : 1 ≤ a)]
    ring
  apply (Real.log_le_log_iff htargetpos hsourcepos).mp
  rw [htargetlog, hsourcelog]
  nlinarith

theorem recursivePaletteRamsey_exponential_bound (H a : ℕ)
    (hH : 2 ≤ H) (ha : 2 ≤ a)
    (hloga : Real.log (H : ℝ) ≤ (a : ℝ)) :
    ((H : ℝ) / Real.exp 4) ^
        (H * (a * saturatedMatrixRows H)) ≤
      (triangleRamseyNumber
        (H * (a * saturatedMatrixRows H)) : ℝ) := by
  obtain ⟨n, C, htriangle, _, hgrowth⟩ :=
    exists_recursivePaletteStage H a H hH ha le_rfl
  have hramsey := triangleFree_lt_triangleRamseyNumber C htriangle
  have hs : 0 < saturatedMatrixRows H := by
    simp [saturatedMatrixRows]
  have hden :
      0 < (saturatedMatrixRows H : ℝ) ^ H *
        (Real.exp 1 ^ 2 * (a : ℝ) ^ 2) ^
          (saturatedMatrixRows H * H) := by
    positivity
  have hsplit :
      a * saturatedMatrixRows H =
        (a - 1) * saturatedMatrixRows H + saturatedMatrixRows H := by
    calc
      a * saturatedMatrixRows H =
          ((a - 1) + 1) * saturatedMatrixRows H := by
        rw [Nat.sub_add_cancel (by omega)]
      _ = (a - 1) * saturatedMatrixRows H + saturatedMatrixRows H := by
        simp [Nat.add_mul]
  unfold PaletteGrowthBound at hgrowth
  nth_rewrite 1 [hsplit] at hgrowth
  rw [pow_add] at hgrowth
  have hfactor : 0 < (H.factorial : ℝ) ^ saturatedMatrixRows H := by
    positivity
  have hcancel :
      (H.factorial : ℝ) ^ ((a - 1) * saturatedMatrixRows H) ≤
        (triangleRamseyNumber (H * (a * saturatedMatrixRows H)) : ℝ) *
          (saturatedMatrixRows H : ℝ) ^ H *
          (Real.exp 1 ^ 2 * (a : ℝ) ^ 2) ^
            (saturatedMatrixRows H * H) := by
    apply le_of_mul_le_mul_right ?_ hfactor
    calc
      (H.factorial : ℝ) ^ ((a - 1) * saturatedMatrixRows H) *
          (H.factorial : ℝ) ^ saturatedMatrixRows H ≤
        (n : ℝ) * (saturatedMatrixRows H : ℝ) ^ H *
          (Real.exp 1 ^ 2 * (a : ℝ) ^ 2) ^
            (saturatedMatrixRows H * H) *
          (H.factorial : ℝ) ^ saturatedMatrixRows H := hgrowth
      _ ≤ (triangleRamseyNumber
            (H * (a * saturatedMatrixRows H)) : ℝ) *
          (saturatedMatrixRows H : ℝ) ^ H *
          (Real.exp 1 ^ 2 * (a : ℝ) ^ 2) ^
            (saturatedMatrixRows H * H) *
          (H.factorial : ℝ) ^ saturatedMatrixRows H := by
        gcongr
  calc
    ((H : ℝ) / Real.exp 4) ^
        (H * (a * saturatedMatrixRows H)) ≤
      ((H : ℝ) / Real.exp 1) ^
          (H * ((a - 1) * saturatedMatrixRows H)) /
        ((saturatedMatrixRows H : ℝ) ^ H *
          (Real.exp 1 ^ 2 * (a : ℝ) ^ 2) ^
            (saturatedMatrixRows H * H)) :=
      palette_exp_loss_bound H a (saturatedMatrixRows H)
        hH ha hs hloga
    _ ≤ (triangleRamseyNumber
        (H * (a * saturatedMatrixRows H)) : ℝ) := by
      apply (div_le_iff₀ hden).mpr
      calc
        ((H : ℝ) / Real.exp 1) ^
            (H * ((a - 1) * saturatedMatrixRows H)) =
          (((H : ℝ) / Real.exp 1) ^ H) ^
            ((a - 1) * saturatedMatrixRows H) := by
          rw [pow_mul]
        _ ≤ (H.factorial : ℝ) ^
            ((a - 1) * saturatedMatrixRows H) := by
          gcongr
          exact factorial_exp_lower H (by omega)
        _ ≤ (triangleRamseyNumber
              (H * (a * saturatedMatrixRows H)) : ℝ) *
            ((saturatedMatrixRows H : ℝ) ^ H *
              (Real.exp 1 ^ 2 * (a : ℝ) ^ 2) ^
                (saturatedMatrixRows H * H)) := by
          simpa [mul_assoc] using hcancel

/-- The logarithmic block width at stage `H`. -/
noncomputable def paletteLogWidth (H : ℕ) : ℕ :=
  max 2 ⌈Real.log (H : ℝ)⌉₊

/-- The cumulative number of colors available through stage `H`. -/
noncomputable def paletteColourCount (H : ℕ) : ℕ :=
  H * (paletteLogWidth H * saturatedMatrixRows H)

theorem paletteLogWidth_two_le (H : ℕ) : 2 ≤ paletteLogWidth H := by
  exact Nat.le_max_left _ _

theorem log_le_paletteLogWidth (H : ℕ) :
    Real.log (H : ℝ) ≤ (paletteLogWidth H : ℝ) := by
  calc
    Real.log (H : ℝ) ≤ (⌈Real.log (H : ℝ)⌉₊ : ℝ) :=
      Nat.le_ceil _
    _ ≤ (paletteLogWidth H : ℝ) := by
      exact_mod_cast (Nat.le_max_right 2 ⌈Real.log (H : ℝ)⌉₊)

theorem stageWidths_succ_le (H : ℕ) (hH : 1 ≤ H) :
    paletteLogWidth (H + 1) ≤ paletteLogWidth H + 1 ∧
      saturatedMatrixWidth (H + 1) ≤
        saturatedMatrixWidth H + 2 * paletteLogWidth H + 4 := by
  have hpos : (0 : ℝ) < H := by
    exact_mod_cast (by omega : 0 < H)
  have hHreal : (1 : ℝ) ≤ H := by
    exact_mod_cast hH
  have hinv : 1 / (H : ℝ) ≤ 1 := by
    apply (div_le_iff₀ hpos).mpr
    simpa using hHreal
  have hlogsucc :
      Real.log ((H + 1 : ℕ) : ℝ) ≤
        Real.log (H : ℝ) + 1 / (H : ℝ) := by
    have hsucc : (0 : ℝ) < ((H + 1 : ℕ) : ℝ) := by positivity
    have hbound := Real.log_le_sub_one_of_pos (div_pos hsucc hpos)
    rw [Real.log_div hsucc.ne' hpos.ne'] at hbound
    have hratio :
        ((H + 1 : ℕ) : ℝ) / (H : ℝ) - 1 = 1 / (H : ℝ) := by
      push_cast
      field_simp
      ring
    rw [hratio] at hbound
    linarith
  constructor
  · have hceil :
        ⌈Real.log ((H + 1 : ℕ) : ℝ)⌉₊ ≤
          ⌈Real.log (H : ℝ)⌉₊ + 1 := by
      apply Nat.ceil_le.mpr
      push_cast
      have hlogsucc_real :
          Real.log ((H : ℝ) + 1) ≤
            Real.log (H : ℝ) + 1 / (H : ℝ) := by
        simpa using hlogsucc
      linarith [Nat.le_ceil (Real.log (H : ℝ))]
    change
      max 2 ⌈Real.log ((H + 1 : ℕ) : ℝ)⌉₊ ≤
        max 2 ⌈Real.log (H : ℝ)⌉₊ + 1
    exact max_le (by omega)
      (hceil.trans (Nat.add_le_add_right
        (Nat.le_max_right 2 ⌈Real.log (H : ℝ)⌉₊) 1))
  · have htwoinv : 2 / (H : ℝ) ≤ 2 := by
      calc
        2 / (H : ℝ) = 2 * (1 / (H : ℝ)) := by ring
        _ ≤ 2 * 1 := by gcongr
        _ = 2 := by norm_num
    have hprevious :
        2 * (H : ℝ) * Real.log (H : ℝ) ≤
          (saturatedMatrixWidth H : ℝ) := Nat.le_ceil _
    change
      ⌈2 * (((H + 1 : ℕ) : ℝ)) *
        Real.log ((H + 1 : ℕ) : ℝ)⌉₊ ≤
          saturatedMatrixWidth H + 2 * paletteLogWidth H + 4
    apply Nat.ceil_le.mpr
    push_cast
    calc
      2 * ((H : ℝ) + 1) * Real.log ((H : ℝ) + 1) ≤
        2 * ((H : ℝ) + 1) *
          (Real.log (H : ℝ) + 1 / (H : ℝ)) := by
            gcongr
            simpa using hlogsucc
      _ = 2 * (H : ℝ) * Real.log (H : ℝ) +
          2 * Real.log (H : ℝ) + 2 + 2 / (H : ℝ) := by
            field_simp
            ring
      _ ≤ (saturatedMatrixWidth H : ℝ) +
          2 * (paletteLogWidth H : ℝ) + 4 := by
            linarith [log_le_paletteLogWidth H]

theorem one_le_log_nat_of_three_le (H : ℕ) (hH : 3 ≤ H) :
    1 ≤ Real.log (H : ℝ) := by
  have hpos : (0 : ℝ) < H := by exact_mod_cast (by omega : 0 < H)
  apply (Real.le_log_iff_exp_le hpos).mpr
  calc
    Real.exp 1 ≤ (3 : ℝ) := Real.exp_one_lt_three.le
    _ ≤ (H : ℝ) := by exact_mod_cast hH

theorem paletteLogWidth_le_two_log (H : ℕ) (hH : 3 ≤ H) :
    (paletteLogWidth H : ℝ) ≤ 2 * Real.log (H : ℝ) := by
  have hlog : 1 ≤ Real.log (H : ℝ) :=
    one_le_log_nat_of_three_le H hH
  have hceil :
      (⌈Real.log (H : ℝ)⌉₊ : ℝ) ≤ Real.log (H : ℝ) + 1 :=
    (Nat.ceil_lt_add_one (by linarith : 0 ≤ Real.log (H : ℝ))).le
  unfold paletteLogWidth
  by_cases htwo : 2 ≤ ⌈Real.log (H : ℝ)⌉₊
  · rw [max_eq_right htwo]
    linarith
  · rw [max_eq_left (by omega)]
    norm_num
    linarith

theorem paletteLogWidth_le_stage (H : ℕ) (hH : 2 ≤ H) :
    paletteLogWidth H ≤ H := by
  unfold paletteLogWidth
  apply max_le
  · exact hH
  · apply Nat.ceil_le.mpr
    have hpos : (0 : ℝ) < H := by exact_mod_cast (by omega : 0 < H)
    have hlog := Real.log_le_sub_one_of_pos hpos
    exact hlog.trans (by linarith)

theorem paletteColourCount_mono {H H' : ℕ}
    (hH : 1 ≤ H) (hHH' : H ≤ H') :
    paletteColourCount H ≤ paletteColourCount H' := by
  have hpos : (0 : ℝ) < H := by
    exact_mod_cast (by omega : 0 < H)
  have hreal : (H : ℝ) ≤ H' := by
    exact_mod_cast hHH'
  have hlog : Real.log (H : ℝ) ≤ Real.log (H' : ℝ) :=
    Real.log_le_log hpos hreal
  have hlognonneg : 0 ≤ Real.log (H : ℝ) :=
    Real.log_nonneg (by exact_mod_cast hH)
  have hwidth : saturatedMatrixWidth H ≤ saturatedMatrixWidth H' := by
    unfold saturatedMatrixWidth
    apply Nat.ceil_le_ceil
    gcongr
  unfold paletteColourCount
  apply Nat.mul_le_mul hHH'
  apply Nat.mul_le_mul
  · exact max_le_max_left 2 (Nat.ceil_le_ceil hlog)
  · unfold saturatedMatrixRows
    gcongr

theorem two_mul_stage_le_paletteColourCount (H : ℕ) :
    2 * H ≤ paletteColourCount H := by
  have hrows : 1 ≤ saturatedMatrixRows H := by
    simp [saturatedMatrixRows]
  have hfactor : 2 ≤ paletteLogWidth H * saturatedMatrixRows H := by
    calc
      2 = 2 * 1 := by simp
      _ ≤ paletteLogWidth H * saturatedMatrixRows H :=
        Nat.mul_le_mul (paletteLogWidth_two_le H) hrows
  unfold paletteColourCount
  calc
    2 * H = H * 2 := by omega
    _ ≤ H * (paletteLogWidth H * saturatedMatrixRows H) :=
      Nat.mul_le_mul_left H hfactor

theorem exists_paletteStage_bracket (k : ℕ)
    (hk : paletteColourCount 2 ≤ k) :
    ∃ H : ℕ, 2 ≤ H ∧
      paletteColourCount H ≤ k ∧ k < paletteColourCount (H + 1) := by
  have hexists : ∃ H : ℕ, k < paletteColourCount H := by
    refine ⟨k + 1, ?_⟩
    have hcount := two_mul_stage_le_paletteColourCount (k + 1)
    omega
  let M : ℕ := Nat.find hexists
  have hM : k < paletteColourCount M := Nat.find_spec hexists
  have hMpos : 1 ≤ M := by
    by_contra hnot
    have hzero : M = 0 := by omega
    simp [hzero, paletteColourCount] at hM
  have hMlarge : 2 < M := by
    by_contra hnot
    have hMtwo : M ≤ 2 := by omega
    have hmono := paletteColourCount_mono hMpos hMtwo
    omega
  refine ⟨M - 1, by omega, ?_, ?_⟩
  · have hminimal :=
      Nat.find_min hexists (show M - 1 < M by omega)
    change ¬ k < paletteColourCount (M - 1) at hminimal
    omega
  · have hsucc : M - 1 + 1 = M := by omega
    simpa [hsucc] using hM

theorem stage_mul_paletteWidth_le_matrixWidth_sharp (H : ℕ) (hH : 3 ≤ H) :
    H * paletteLogWidth H ≤ saturatedMatrixWidth H := by
  have hpalette := paletteLogWidth_le_two_log H hH
  have hmatrix :
      2 * (H : ℝ) * Real.log (H : ℝ) ≤
        (saturatedMatrixWidth H : ℝ) := by
    exact Nat.le_ceil _
  have hscaled :=
    mul_le_mul_of_nonneg_left hpalette (show (0 : ℝ) ≤ H by positivity)
  have hreal :
      ((H * paletteLogWidth H : ℕ) : ℝ) ≤
        (saturatedMatrixWidth H : ℝ) := by
    push_cast
    calc
      (H : ℝ) * (paletteLogWidth H : ℝ) ≤
          (H : ℝ) * (2 * Real.log (H : ℝ)) := hscaled
      _ = 2 * (H : ℝ) * Real.log (H : ℝ) := by ring
      _ ≤ (saturatedMatrixWidth H : ℝ) := hmatrix
  exact_mod_cast hreal

theorem saturatedMatrixRows_adjacent_scaled_sharp (H : ℕ) (hH : 3 ≤ H) :
    H * saturatedMatrixRows (H + 1) ≤
      (H + 14) * saturatedMatrixRows H := by
  let w := saturatedMatrixWidth H
  let a := paletteLogWidth H
  have ha : 2 ≤ a := by
    simpa [a] using paletteLogWidth_two_le H
  have hwa : H * a ≤ w := by
    simpa [a, w] using stage_mul_paletteWidth_le_matrixWidth_sharp H hH
  have hthreea : 3 * a ≤ w :=
    (Nat.mul_le_mul_right a hH).trans hwa
  have hnext : saturatedMatrixWidth (H + 1) ≤ w + 4 * a := by
    have hwidth := (stageWidths_succ_le H (by omega)).2
    change saturatedMatrixWidth (H + 1) ≤ w + 2 * a + 4 at hwidth
    exact hwidth.trans (by omega)
  have hrows : saturatedMatrixRows (H + 1) ≤
      (w + 4 * a) * (w + 4 * a + 1) + 1 := by
    unfold saturatedMatrixRows
    gcongr
  calc
    H * saturatedMatrixRows (H + 1) ≤
        H * ((w + 4 * a) * (w + 4 * a + 1) + 1) :=
      Nat.mul_le_mul_left H hrows
    _ = H * (w * (w + 1) + 1) +
        H * a * (8 * w + 16 * a + 4) := by ring
    _ ≤ H * (w * (w + 1) + 1) +
        14 * (w * (w + 1) + 1) :=
      Nat.add_le_add_left (by
        calc
          H * a * (8 * w + 16 * a + 4) ≤
              w * (8 * w + 16 * a + 4) :=
            Nat.mul_le_mul_right _ hwa
          _ ≤ w * (14 * w + 4) :=
            Nat.mul_le_mul_left w (by omega)
          _ ≤ 14 * (w * (w + 1) + 1) := by nlinarith) _
    _ = (H + 14) * saturatedMatrixRows H := by
      simp [w, saturatedMatrixRows]
      ring

theorem paletteColourCount_adjacent_scaled_sharp (H : ℕ) (hH : 3 ≤ H) :
    paletteLogWidth H * paletteColourCount (H + 1) ≤
      (paletteLogWidth H + 34) * paletteColourCount H := by
  let a := paletteLogWidth H
  let s := saturatedMatrixRows H
  let s' := saturatedMatrixRows (H + 1)
  have haH : a ≤ H := by
    simpa [a] using paletteLogWidth_le_stage H (by omega)
  have ha' : paletteLogWidth (H + 1) ≤ a + 1 := by
    simpa [a] using (stageWidths_succ_le H (by omega)).1
  have hrows : H * s' ≤ (H + 14) * s := by
    simpa [s, s'] using saturatedMatrixRows_adjacent_scaled_sharp H hH
  have hHreal : (3 : ℝ) ≤ H := by exact_mod_cast hH
  have hareal : (a : ℝ) ≤ H := by exact_mod_cast haH
  have hpolyreal :
      ((H : ℝ) + 1) * ((a : ℝ) + 1) * ((H : ℝ) + 14) ≤
        ((a : ℝ) + 34) * (H : ℝ) ^ 2 := by
    nlinarith [
      mul_nonneg (show 0 ≤ 15 * (H : ℝ) + 14 by positivity)
        (sub_nonneg.mpr hareal),
      mul_nonneg (show 0 ≤ (H : ℝ) - 3 by linarith)
        (show 0 ≤ 18 * (H : ℝ) + 25 by positivity)]
  have hpoly :
      (H + 1) * (a + 1) * (H + 14) ≤ (a + 34) * H ^ 2 := by
    exact_mod_cast hpolyreal
  have hstep : (H + 1) * (a + 1) * s' ≤ (a + 34) * H * s := by
    apply Nat.le_of_mul_le_mul_left (c := H) ?_ (by omega)
    calc
      H * ((H + 1) * (a + 1) * s') =
          ((H + 1) * (a + 1)) * (H * s') := by ring
      _ ≤ ((H + 1) * (a + 1)) * ((H + 14) * s) :=
        Nat.mul_le_mul_left _ hrows
      _ = ((H + 1) * (a + 1) * (H + 14)) * s := by ring
      _ ≤ ((a + 34) * H ^ 2) * s :=
        Nat.mul_le_mul_right s hpoly
      _ = H * ((a + 34) * H * s) := by ring
  calc
    paletteLogWidth H * paletteColourCount (H + 1) =
        a * ((H + 1) * paletteLogWidth (H + 1) * s') := by
      simp only [a, s', paletteColourCount]
      ring
    _ ≤ a * ((H + 1) * (a + 1) * s') := by
      gcongr
    _ ≤ a * ((a + 34) * H * s) := Nat.mul_le_mul_left a hstep
    _ = (paletteLogWidth H + 34) * paletteColourCount H := by
      simp only [a, s, paletteColourCount]
      ring

theorem palette_exponential_adjacent_transfer_sharp
    (H a k₀ k : ℕ)
    (hH : 3 ≤ H)
    (hlog : Real.log (H : ℝ) ≤ (a : ℝ))
    (hk₀ : k₀ ≤ k)
    (hratio : a * k ≤ (a + 34) * k₀) :
    ((H : ℝ) / Real.exp 38) ^ k ≤
      ((H : ℝ) / Real.exp 4) ^ k₀ := by
  have hHpos : (0 : ℝ) < H := by exact_mod_cast (by omega : 0 < H)
  have htarget : 0 < ((H : ℝ) / Real.exp 38) ^ k := by positivity
  have hsource : 0 < ((H : ℝ) / Real.exp 4) ^ k₀ := by positivity
  have hratioReal :
      (a : ℝ) * (k : ℝ) ≤
        ((a : ℝ) + 34) * (k₀ : ℝ) := by
    exact_mod_cast hratio
  have hdelta : 0 ≤ (k : ℝ) - (k₀ : ℝ) := by
    exact sub_nonneg.mpr (by exact_mod_cast hk₀)
  have hweighted := mul_le_mul_of_nonneg_left hlog hdelta
  apply (Real.log_le_log_iff htarget hsource).mp
  rw [Real.log_pow, Real.log_pow,
    Real.log_div hHpos.ne' (Real.exp_ne_zero 38),
    Real.log_div hHpos.ne' (Real.exp_ne_zero 4),
    Real.log_exp, Real.log_exp]
  nlinarith

theorem allColourPaletteRamsey_exponential_bound_sharp (k : ℕ)
    (hk : paletteColourCount 3 ≤ k) :
    ∃ H : ℕ,
      3 ≤ H ∧
      paletteColourCount H ≤ k ∧
      k < paletteColourCount (H + 1) ∧
      ((H : ℝ) / Real.exp 38) ^ k ≤
        (triangleRamseyNumber k : ℝ) := by
  have htwo : paletteColourCount 2 ≤ paletteColourCount 3 :=
    paletteColourCount_mono (by omega) (by omega)
  obtain ⟨H, hH, hlower, hupper⟩ :=
    exists_paletteStage_bracket k (htwo.trans hk)
  have hthree : 3 ≤ H := by
    by_contra hnot
    have htwoeq : H = 2 := by omega
    subst H
    exact (Nat.not_lt_of_ge hk) (by simpa using hupper)
  have hratio :
      paletteLogWidth H * k ≤
        (paletteLogWidth H + 34) * paletteColourCount H := by
    exact (Nat.mul_le_mul_left (paletteLogWidth H)
      (Nat.le_of_lt hupper)).trans
        (paletteColourCount_adjacent_scaled_sharp H hthree)
  refine ⟨H, hthree, hlower, hupper, ?_⟩
  calc
    ((H : ℝ) / Real.exp 38) ^ k ≤
        ((H : ℝ) / Real.exp 4) ^ paletteColourCount H :=
      palette_exponential_adjacent_transfer_sharp H (paletteLogWidth H)
        (paletteColourCount H) k hthree
        (log_le_paletteLogWidth H) hlower hratio
    _ ≤ (triangleRamseyNumber (paletteColourCount H) : ℝ) :=
      by
        simpa [paletteColourCount] using
          recursivePaletteRamsey_exponential_bound H (paletteLogWidth H)
            (by omega) (paletteLogWidth_two_le H) (log_le_paletteLogWidth H)
    _ ≤ (triangleRamseyNumber k : ℝ) := by
      exact_mod_cast triangleRamseyNumber_mono hlower

theorem paletteColourCount_le_twenty_six_sharp (H : ℕ) (hH : 3 ≤ H) :
    (paletteColourCount H : ℝ) ≤
      26 * (H : ℝ) ^ 3 * Real.log (H : ℝ) ^ 3 := by
  let y : ℝ := (H : ℝ) * Real.log (H : ℝ)
  have hlog : 1 ≤ Real.log (H : ℝ) :=
    one_le_log_nat_of_three_le H hH
  have hHreal : (1 : ℝ) ≤ (H : ℝ) := by
    exact_mod_cast (show 1 ≤ H by omega)
  have hy : 1 ≤ y := by
    dsimp [y]
    calc
      (1 : ℝ) = 1 * 1 := by norm_num
      _ ≤ (H : ℝ) * Real.log (H : ℝ) := by gcongr
  have harg : 0 ≤ 2 * (H : ℝ) * Real.log (H : ℝ) := by
    positivity
  have hceil :
      (⌈2 * (H : ℝ) * Real.log (H : ℝ)⌉₊ : ℝ) ≤
        2 * (H : ℝ) * Real.log (H : ℝ) + 1 :=
    (Nat.ceil_lt_add_one harg).le
  have hm : (saturatedMatrixWidth H : ℝ) ≤ 3 * y := by
    unfold saturatedMatrixWidth
    dsimp [y]
    nlinarith
  have hmsucc : (saturatedMatrixWidth H : ℝ) + 1 ≤ 4 * y := by
    linarith
  have hone : (1 : ℝ) ≤ y ^ 2 := by
    nlinarith [sq_nonneg (y - 1)]
  have hrows : (saturatedMatrixRows H : ℝ) ≤ 13 * y ^ 2 := by
    unfold saturatedMatrixRows
    push_cast
    calc
      (saturatedMatrixWidth H : ℝ) *
          ((saturatedMatrixWidth H : ℝ) + 1) + 1 ≤
        (3 * y) * (4 * y) + y ^ 2 := by
          gcongr
      _ = 13 * y ^ 2 := by ring
  have hwidth := paletteLogWidth_le_two_log H hH
  unfold paletteColourCount
  push_cast
  calc
    (H : ℝ) *
        ((paletteLogWidth H : ℝ) * (saturatedMatrixRows H : ℝ)) ≤
      (H : ℝ) *
        ((2 * Real.log (H : ℝ)) * (13 * y ^ 2)) := by
          gcongr
    _ = 26 * (H : ℝ) ^ 3 * Real.log (H : ℝ) ^ 3 := by
      dsimp [y]
      ring

theorem paletteStage_cube_root_control_six_sharp (H k : ℕ)
    (hH : 3 ≤ H)
    (hlower : paletteColourCount H ≤ k)
    (hupper : k < paletteColourCount (H + 1)) :
    (k : ℝ) ^ ((1 : ℝ) / 3) ≤
      6 * (H : ℝ) * Real.log (k : ℝ) := by
  have hkstage : 2 * H ≤ k :=
    (two_mul_stage_le_paletteColourCount H).trans hlower
  have hHk : H + 1 ≤ k := by omega
  have hkthree : 3 ≤ k := by omega
  have hlogk : 1 ≤ Real.log (k : ℝ) :=
    one_le_log_nat_of_three_le k hkthree
  have hlognext :
      Real.log ((H + 1 : ℕ) : ℝ) ≤ Real.log (k : ℝ) := by
    apply Real.log_le_log (by positivity)
    exact_mod_cast hHk
  have hHnext : ((H + 1 : ℕ) : ℝ) ≤ 2 * (H : ℝ) := by
    exact_mod_cast (show H + 1 ≤ 2 * H by omega)
  have hkbound :
      (k : ℝ) ≤
        26 * (((H + 1 : ℕ) : ℝ)) ^ 3 *
          Real.log ((H + 1 : ℕ) : ℝ) ^ 3 := by
    calc
      (k : ℝ) ≤ (paletteColourCount (H + 1) : ℝ) := by
        exact_mod_cast (Nat.le_of_lt hupper)
      _ ≤ 26 * (((H + 1 : ℕ) : ℝ)) ^ 3 *
          Real.log ((H + 1 : ℕ) : ℝ) ^ 3 :=
        paletteColourCount_le_twenty_six_sharp (H + 1) (by omega)
  have hcube :
      (k : ℝ) ≤ (6 * (H : ℝ) * Real.log (k : ℝ)) ^ 3 := by
    calc
      (k : ℝ) ≤
          26 * (((H + 1 : ℕ) : ℝ)) ^ 3 *
            Real.log ((H + 1 : ℕ) : ℝ) ^ 3 := hkbound
      _ ≤ 26 * (2 * (H : ℝ)) ^ 3 * Real.log (k : ℝ) ^ 3 := by
        gcongr
      _ = 208 * (H : ℝ) ^ 3 * Real.log (k : ℝ) ^ 3 := by
        ring
      _ ≤ 216 * (H : ℝ) ^ 3 * Real.log (k : ℝ) ^ 3 := by
        gcongr
        norm_num
      _ = (6 * (H : ℝ) * Real.log (k : ℝ)) ^ 3 := by
        ring
  have hrootcube :
      ((k : ℝ) ^ ((1 : ℝ) / 3)) ^ (3 : ℕ) = (k : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
    norm_num
  apply (pow_le_pow_iff_left₀
    (Real.rpow_nonneg (by positivity) _)
    (by positivity)
    (by norm_num : (3 : ℕ) ≠ 0)).mp
  rw [hrootcube]
  exact hcube

theorem paletteColourCount_three : paletteColourCount 3 = 342 := by
  have hlo : (1 : ℝ) < Real.log 3 := by
    nlinarith [Real.log_three_gt_d9]
  have hhi : Real.log (3 : ℝ) < 7 / 6 := by
    nlinarith [Real.log_three_lt_d9]
  have ha : ⌈Real.log (3 : ℝ)⌉₊ = 2 := by
    apply (Nat.ceil_eq_iff (by norm_num : (2 : ℕ) ≠ 0)).mpr
    constructor <;> norm_num <;> linarith
  have hm : ⌈(6 : ℝ) * Real.log (3 : ℝ)⌉₊ = 7 := by
    apply (Nat.ceil_eq_iff (by norm_num : (7 : ℕ) ≠ 0)).mpr
    constructor <;> norm_num <;> nlinarith
  norm_num [paletteColourCount, paletteLogWidth,
    saturatedMatrixRows, saturatedMatrixWidth, ha, hm]

theorem quantitativeLowerBound_explicit_small (k : ℕ)
    (hk : 2 ≤ k) (hsmall : k < 342) :
    (((1 : ℝ) / (6 * Real.exp 38)) *
      (k : ℝ) ^ ((1 : ℝ) / 3) / Real.log (k : ℝ)) ^ k ≤
        (triangleRamseyNumber k : ℝ) := by
  have hlog : (1 / 2 : ℝ) ≤ Real.log (k : ℝ) := by
    calc
      (1 / 2 : ℝ) ≤ Real.log 2 := by
        nlinarith [Real.log_two_gt_d9]
      _ ≤ Real.log (k : ℝ) := by
        apply Real.log_le_log (by norm_num)
        exact_mod_cast hk
  have hroot : (k : ℝ) ^ ((1 : ℝ) / 3) ≤ (7 : ℝ) := by
    apply (pow_le_pow_iff_left₀
      (Real.rpow_nonneg (by positivity) _) (by positivity)
      (by norm_num : (3 : ℕ) ≠ 0)).mp
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
    norm_num
    exact_mod_cast (show k ≤ 343 by omega)
  have hexp : (39 : ℝ) ≤ Real.exp 38 := by
    nlinarith [Real.add_one_le_exp (38 : ℝ)]
  have hbase :
      ((1 : ℝ) / (6 * Real.exp 38)) *
        (k : ℝ) ^ ((1 : ℝ) / 3) / Real.log (k : ℝ) ≤ 1 := by
    apply (div_le_one (by linarith : 0 < Real.log (k : ℝ))).mpr
    calc
      ((1 : ℝ) / (6 * Real.exp 38)) *
          (k : ℝ) ^ ((1 : ℝ) / 3) ≤
          (1 / (6 * (39 : ℝ))) * 7 := by gcongr
      _ ≤ Real.log (k : ℝ) := by norm_num; linarith
  calc
    (((1 : ℝ) / (6 * Real.exp 38)) *
        (k : ℝ) ^ ((1 : ℝ) / 3) / Real.log (k : ℝ)) ^ k ≤
        (1 : ℝ) ^ k := by gcongr
    _ = 1 := one_pow _
    _ ≤ (triangleRamseyNumber k : ℝ) := by
      let C : SimpleGraph.TopEdgeLabeling (Fin 0) (Fin k) :=
        fun _ => ⟨0, by omega⟩
      exact_mod_cast triangleFree_lt_triangleRamseyNumber C
        (fun _ => SimpleGraph.cliqueFree_of_card_lt (by simp))

theorem quantitativeLowerBound_explicit_all :
    ∀ k : ℕ, 2 ≤ k →
      (((1 : ℝ) / (6 * Real.exp 38)) *
        (k : ℝ) ^ ((1 : ℝ) / 3) / Real.log (k : ℝ)) ^ k ≤
          (triangleRamseyNumber k : ℝ) := by
  intro k hk
  by_cases hlarge : paletteColourCount 3 ≤ k
  · obtain ⟨H, hH, hlower, hupper, hramsey⟩ :=
      allColourPaletteRamsey_exponential_bound_sharp k hlarge
    have hkthree : 3 ≤ k := by
      have hstage := (two_mul_stage_le_paletteColourCount H).trans hlower
      omega
    have hlog : 0 < Real.log (k : ℝ) := by
      have hone := one_le_log_nat_of_three_le k hkthree
      linarith
    have hroot :=
      paletteStage_cube_root_control_six_sharp H k hH hlower hupper
    have hbase :
        ((1 : ℝ) / (6 * Real.exp 38)) *
            (k : ℝ) ^ ((1 : ℝ) / 3) / Real.log (k : ℝ) ≤
          (H : ℝ) / Real.exp 38 := by
      calc
        ((1 : ℝ) / (6 * Real.exp 38)) *
            (k : ℝ) ^ ((1 : ℝ) / 3) / Real.log (k : ℝ) =
          (k : ℝ) ^ ((1 : ℝ) / 3) /
            (6 * Real.log (k : ℝ) * Real.exp 38) := by
          field_simp
        _ ≤ (H : ℝ) / Real.exp 38 := by
          apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
          nlinarith [mul_le_mul_of_nonneg_right hroot
            (Real.exp_pos 38).le]
    calc
      (((1 : ℝ) / (6 * Real.exp 38)) *
          (k : ℝ) ^ ((1 : ℝ) / 3) / Real.log (k : ℝ)) ^ k ≤
        ((H : ℝ) / Real.exp 38) ^ k := by gcongr
      _ ≤ (triangleRamseyNumber k : ℝ) := hramsey
  · apply quantitativeLowerBound_explicit_small k hk
    rw [paletteColourCount_three] at hlarge
    omega

theorem triangleRamseyNumber_log_sharp_coefficients :
    ∀ ε : ℝ, 0 < ε →
      ∀ᶠ k : ℕ in atTop,
        ((1 / 3 : ℝ) - ε) * (k : ℝ) * Real.log (k : ℝ) ≤
            Real.log (triangleRamseyNumber k : ℝ) ∧
          Real.log (triangleRamseyNumber k : ℝ) ≤
            (1 + ε) * (k : ℝ) * Real.log (k : ℝ) := by
  intro ε hε
  let c : ℝ := 1 / (6 * Real.exp 38)
  have hc : 0 < c := by dsimp [c]; positivity
  have hsmall :
      ∀ᶠ k : ℕ in atTop,
        ‖Real.log (k : ℝ)‖ ≤ c * ‖(k : ℝ) ^ ε‖ := by
    simpa [Function.comp_def] using
      ((isLittleO_log_rpow_atTop hε).comp_tendsto
        (tendsto_natCast_atTop_atTop (R := ℝ))).bound hc
  have hfour :
      ∀ᶠ k : ℕ in atTop,
        ‖Real.log (4 : ℝ)‖ ≤ ε * ‖Real.log (k : ℝ)‖ := by
    simpa [Function.comp_def] using
      ((Real.isLittleO_const_log_atTop (c := Real.log (4 : ℝ))).comp_tendsto
        (tendsto_natCast_atTop_atTop (R := ℝ))).bound hε
  filter_upwards [hsmall, hfour, eventually_ge_atTop 2] with k hk hfour' hk2
  have hx : 0 < (k : ℝ) := by exact_mod_cast (by omega : 0 < k)
  have hlog : 0 < Real.log (k : ℝ) :=
    Real.log_pos (by exact_mod_cast (by omega : 1 < k))
  have hrpow : 0 < (k : ℝ) ^ ε := Real.rpow_pos_of_pos hx _
  have hsmall' : Real.log (k : ℝ) ≤ c * (k : ℝ) ^ ε := by
    rw [Real.norm_eq_abs, abs_of_pos hlog,
      Real.norm_eq_abs, abs_of_pos hrpow] at hk
    exact hk
  have hfourlog : Real.log (4 : ℝ) ≤ ε * Real.log (k : ℝ) := by
    rw [Real.norm_eq_abs, abs_of_pos (Real.log_pos (by norm_num)),
      Real.norm_eq_abs, abs_of_pos hlog] at hfour'
    exact hfour'
  have hroot : 0 < (k : ℝ) ^ ((1 / 3 : ℝ) - ε) :=
    Real.rpow_pos_of_pos hx _
  have hbase :
      (k : ℝ) ^ ((1 / 3 : ℝ) - ε) ≤
        c * (k : ℝ) ^ ((1 : ℝ) / 3) / Real.log (k : ℝ) := by
    apply (le_div_iff₀ hlog).mpr
    calc
      (k : ℝ) ^ ((1 / 3 : ℝ) - ε) * Real.log (k : ℝ) ≤
          (k : ℝ) ^ ((1 / 3 : ℝ) - ε) *
            (c * (k : ℝ) ^ ε) := by gcongr
      _ = c * ((k : ℝ) ^ ((1 / 3 : ℝ) - ε) *
          (k : ℝ) ^ ε) := by ring
      _ = c * (k : ℝ) ^ ((1 : ℝ) / 3) := by
        rw [← Real.rpow_add hx]
        congr 1
        ring_nf
  have hRamseyLower :
      ((k : ℝ) ^ ((1 / 3 : ℝ) - ε)) ^ k ≤
        (triangleRamseyNumber k : ℝ) := by
    calc
      ((k : ℝ) ^ ((1 / 3 : ℝ) - ε)) ^ k ≤
          (c * (k : ℝ) ^ ((1 : ℝ) / 3) / Real.log (k : ℝ)) ^ k := by
            gcongr
      _ ≤ (triangleRamseyNumber k : ℝ) := by
        simpa [c] using quantitativeLowerBound_explicit_all k hk2
  have hRamseyPositive : 0 < (triangleRamseyNumber k : ℝ) :=
    lt_of_lt_of_le (pow_pos hroot k) hRamseyLower
  have hRamseyUpper :
      (triangleRamseyNumber k : ℝ) ≤ 4 * (k : ℝ) ^ k := by
    have hnat : triangleRamseyNumber k ≤ 4 * k ^ k :=
      (triangleRamseyNumber_factorial_upper k).trans
        (Nat.mul_le_mul_left 4 (Nat.factorial_le_pow k))
    exact_mod_cast hnat
  constructor
  · calc
      ((1 / 3 : ℝ) - ε) * (k : ℝ) * Real.log (k : ℝ) =
          Real.log (((k : ℝ) ^ ((1 / 3 : ℝ) - ε)) ^ k) := by
            rw [Real.log_pow, Real.log_rpow hx]
            ring
      _ ≤ Real.log (triangleRamseyNumber k : ℝ) :=
        Real.log_le_log (pow_pos hroot k) hRamseyLower
  · calc
      Real.log (triangleRamseyNumber k : ℝ) ≤
          Real.log (4 * (k : ℝ) ^ k) :=
        Real.log_le_log hRamseyPositive hRamseyUpper
      _ = Real.log 4 + (k : ℝ) * Real.log (k : ℝ) := by
        rw [Real.log_mul (by norm_num) (pow_ne_zero _ hx.ne'), Real.log_pow]
      _ ≤ (1 + ε) * (k : ℝ) * Real.log (k : ℝ) := by
        have hkreal : (1 : ℝ) ≤ k := by exact_mod_cast (by omega : 1 ≤ k)
        nlinarith [mul_nonneg (sub_nonneg.mpr hkreal)
          (mul_nonneg hε.le hlog.le)]

theorem triangleRamseyNumber_log_eventually_bounds :
    ∀ᶠ k : ℕ in atTop,
      (1 / 6 : ℝ) * (k : ℝ) * Real.log (k : ℝ) ≤
          Real.log (triangleRamseyNumber k : ℝ) ∧
        Real.log (triangleRamseyNumber k : ℝ) ≤
          2 * (k : ℝ) * Real.log (k : ℝ) := by
  have hconstant : 0 < (1 / (6 * Real.exp 38) : ℝ) := by positivity
  have hlogsmall :
      ∀ᶠ k : ℕ in atTop,
        ‖Real.log (k : ℝ)‖ ≤
          (1 / (6 * Real.exp 38) : ℝ) *
            ‖(k : ℝ) ^ ((1 : ℝ) / 6)‖ := by
    simpa [Function.comp_def] using
      ((isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 6)).comp_tendsto
        (tendsto_natCast_atTop_atTop (R := ℝ))).bound hconstant
  filter_upwards [hlogsmall, eventually_ge_atTop 4] with k hsmall hk
  have hkpositive : 0 < (k : ℝ) := by exact_mod_cast (by omega : 0 < k)
  have hlogpositive : 0 < Real.log (k : ℝ) :=
    Real.log_pos (by exact_mod_cast (by omega : 1 < k))
  have hrootpositive : 0 < (k : ℝ) ^ ((1 : ℝ) / 6) :=
    Real.rpow_pos_of_pos hkpositive _
  have hsmall' :
      Real.log (k : ℝ) ≤
        (1 / (6 * Real.exp 38) : ℝ) * (k : ℝ) ^ ((1 : ℝ) / 6) := by
    rw [Real.norm_eq_abs, abs_of_pos hlogpositive,
      Real.norm_eq_abs, abs_of_pos hrootpositive] at hsmall
    exact hsmall
  have hrootsquare :
      (k : ℝ) ^ ((1 : ℝ) / 6) * (k : ℝ) ^ ((1 : ℝ) / 6) =
        (k : ℝ) ^ ((1 : ℝ) / 3) := by
    rw [← Real.rpow_add hkpositive]
    norm_num
  have hbase :
      (k : ℝ) ^ ((1 : ℝ) / 6) ≤
        ((1 : ℝ) / (6 * Real.exp 38)) *
          (k : ℝ) ^ ((1 : ℝ) / 3) / Real.log (k : ℝ) := by
    apply (le_div_iff₀ hlogpositive).mpr
    calc
      (k : ℝ) ^ ((1 : ℝ) / 6) * Real.log (k : ℝ) ≤
          (k : ℝ) ^ ((1 : ℝ) / 6) *
            ((1 / (6 * Real.exp 38) : ℝ) *
              (k : ℝ) ^ ((1 : ℝ) / 6)) := by gcongr
      _ = (1 / (6 * Real.exp 38) : ℝ) *
            ((k : ℝ) ^ ((1 : ℝ) / 6) *
              (k : ℝ) ^ ((1 : ℝ) / 6)) := by ring
      _ = (1 / (6 * Real.exp 38) : ℝ) *
            (k : ℝ) ^ ((1 : ℝ) / 3) := by rw [hrootsquare]
  have hramsey :
      ((k : ℝ) ^ ((1 : ℝ) / 6)) ^ k ≤
        (triangleRamseyNumber k : ℝ) := by
    calc
      ((k : ℝ) ^ ((1 : ℝ) / 6)) ^ k ≤
          (((1 : ℝ) / (6 * Real.exp 38)) *
            (k : ℝ) ^ ((1 : ℝ) / 3) / Real.log (k : ℝ)) ^ k := by gcongr
      _ ≤ (triangleRamseyNumber k : ℝ) :=
        quantitativeLowerBound_explicit_all k (by omega)
  have hramseypositive : 0 < (triangleRamseyNumber k : ℝ) :=
    lt_of_lt_of_le (pow_pos hrootpositive k) hramsey
  have hkpow : k ≤ k ^ k :=
    le_self_pow (by omega : 1 ≤ k) (by omega : k ≠ 0)
  have hfour : 4 ≤ k ^ k := by omega
  have huppernat : triangleRamseyNumber k ≤ (k ^ k) ^ 2 := by
    calc
      triangleRamseyNumber k ≤ 4 * k.factorial :=
        triangleRamseyNumber_factorial_upper k
      _ ≤ 4 * k ^ k := Nat.mul_le_mul_left 4 (Nat.factorial_le_pow k)
      _ ≤ (k ^ k) * (k ^ k) := Nat.mul_le_mul_right (k ^ k) hfour
      _ = (k ^ k) ^ 2 := by ring
  have hupperreal :
      (triangleRamseyNumber k : ℝ) ≤ (((k : ℝ) ^ k) ^ 2) := by
    exact_mod_cast huppernat
  constructor
  · calc
      (1 / 6 : ℝ) * (k : ℝ) * Real.log (k : ℝ) =
          Real.log (((k : ℝ) ^ ((1 : ℝ) / 6)) ^ k) := by
            rw [Real.log_pow, Real.log_rpow hkpositive]
            ring
      _ ≤ Real.log (triangleRamseyNumber k : ℝ) :=
        Real.log_le_log (pow_pos hrootpositive k) hramsey
  · calc
      Real.log (triangleRamseyNumber k : ℝ) ≤
          Real.log (((k : ℝ) ^ k) ^ 2) :=
        Real.log_le_log hramseypositive hupperreal
      _ = 2 * (k : ℝ) * Real.log (k : ℝ) := by
        rw [Real.log_pow, Real.log_pow]
        ring

theorem triangleRamseyNumber_log_isTheta :
    (fun k : ℕ => Real.log (triangleRamseyNumber k : ℝ))
      =Θ[atTop] (fun k : ℕ => (k : ℝ) * Real.log (k : ℝ)) := by
  constructor
  · apply Asymptotics.isBigO_iff.mpr
    refine ⟨2, ?_⟩
    filter_upwards [triangleRamseyNumber_log_eventually_bounds,
      eventually_ge_atTop 4] with k hbounds hk
    have hscale : 0 ≤ (k : ℝ) * Real.log (k : ℝ) :=
      mul_nonneg (Nat.cast_nonneg _) (Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ k)))
    have hlog : 0 ≤ Real.log (triangleRamseyNumber k : ℝ) := by
      nlinarith [hbounds.1]
    change |Real.log (triangleRamseyNumber k : ℝ)| ≤
      (2 : ℝ) * |(k : ℝ) * Real.log (k : ℝ)|
    rw [abs_of_nonneg hlog, abs_of_nonneg hscale]
    simpa [mul_assoc] using hbounds.2
  · apply Asymptotics.isBigO_iff.mpr
    refine ⟨6, ?_⟩
    filter_upwards [triangleRamseyNumber_log_eventually_bounds,
      eventually_ge_atTop 4] with k hbounds hk
    have hscale : 0 ≤ (k : ℝ) * Real.log (k : ℝ) :=
      mul_nonneg (Nat.cast_nonneg _) (Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ k)))
    have hlog : 0 ≤ Real.log (triangleRamseyNumber k : ℝ) := by
      nlinarith [hbounds.1]
    have hreverse :
        (k : ℝ) * Real.log (k : ℝ) ≤
          6 * Real.log (triangleRamseyNumber k : ℝ) := by
      nlinarith [hbounds.1]
    change |(k : ℝ) * Real.log (k : ℝ)| ≤
      (6 : ℝ) * |Real.log (triangleRamseyNumber k : ℝ)|
    rw [abs_of_nonneg hscale, abs_of_nonneg hlog]
    exact hreverse

theorem divergentRamseyRoot :
    Filter.Tendsto
      (fun k : ℕ =>
        (triangleRamseyNumber k : ℝ) ^ ((1 : ℝ) / (k : ℝ)))
      atTop atTop := by
  apply Filter.tendsto_atTop.mpr
  intro bound
  let minimum : ℕ := max 3 ⌈bound * Real.exp 38⌉₊
  have hminimum : 3 ≤ minimum := Nat.le_max_left _ _
  filter_upwards [Filter.eventually_ge_atTop (paletteColourCount minimum)]
    with k hk
  have hklarge : paletteColourCount 3 ≤ k :=
    (paletteColourCount_mono (by norm_num) hminimum).trans hk
  obtain ⟨H, _, _, hupper, hramsey⟩ :=
    allColourPaletteRamsey_exponential_bound_sharp k hklarge
  have hstage : minimum ≤ H := by
    by_contra h
    have hcolour := paletteColourCount_mono
      (by omega : 1 ≤ H + 1) (by omega : H + 1 ≤ minimum)
    omega
  have hkreal : (0 : ℝ) < (k : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le
      (by norm_num [paletteColourCount_three] : 0 < paletteColourCount 3)
      hklarge)
  calc
    bound ≤ (H : ℝ) / Real.exp 38 := by
      apply (le_div_iff₀ (Real.exp_pos 38)).mpr
      exact (Nat.le_ceil _).trans (by
        exact_mod_cast
          (Nat.le_max_right 3 ⌈bound * Real.exp 38⌉₊).trans hstage)
    _ ≤ (triangleRamseyNumber k : ℝ) ^ ((1 : ℝ) / (k : ℝ)) := by
      simpa only [one_div] using
        (Real.le_rpow_inv_iff_of_pos
          (by positivity) (by positivity) hkreal).mpr
            (by simpa [Real.rpow_natCast] using hramsey)

theorem erdos_183 :
    Filter.Tendsto
      (fun k : ℕ =>
        (triangleRamseyNumber k : ℝ) ^ ((1 : ℝ) / (k : ℝ)))
      atTop atTop := by
  exact divergentRamseyRoot

theorem erdos_problem_183_explicit :
    (∀ k : ℕ, 2 ≤ k →
      (((1 : ℝ) / (6 * Real.exp 38)) *
        (k : ℝ) ^ ((1 : ℝ) / 3) / Real.log (k : ℝ)) ^ k ≤
          (triangleRamseyNumber k : ℝ)) ∧
      Filter.Tendsto
        (fun k : ℕ =>
          (triangleRamseyNumber k : ℝ) ^ ((1 : ℝ) / (k : ℝ)))
        atTop atTop := by
  exact ⟨quantitativeLowerBound_explicit_all, divergentRamseyRoot⟩

end ErdosProblems.MulticolourTriangleRamsey
