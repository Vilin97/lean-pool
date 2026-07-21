/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/

import Mathlib.Combinatorics.Compactness
import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex

/-!
# The de Bruijn--Erdős compactness theorem for graph coloring

De Bruijn and Erdős proved that a graph is colorable with a fixed finite
number of colors if every finite subgraph is. We derive the theorem from
Mathlib's formalization of Rado's selection principle. We also prove stronger
finite-target homomorphism and finite-list-coloring versions, the finite
obstruction equivalence, and finite attainment of every positive finite
chromatic number.

## Source

N. G. de Bruijn and P. Erdős, *A colour problem for infinite graphs and a
problem in the theory of relations*, Indagationes Mathematicae 13 (1951),
369--373.

Publisher PDF:
https://pure.tue.nl/ws/files/4237754/597497.pdf
-/

universe u v

variable {α : Type u} {β : α → Type v} [∀ a, Finite (β a)]

/-- Binary-constraint form of Rado compactness. If every finite set of
variables has a simultaneous assignment satisfying all pairwise constraints,
then all variables have such an assignment. -/
theorem Finset.rado_selection_constraints
    (compatible : ∀ a b, β a → β b → Prop)
    (hfinite : ∀ s : Finset α,
      ∃ choice : (a : s) → β a,
        ∀ a b : s, compatible a b (choice a) (choice b)) :
    ∃ choice : (a : α) → β a,
      ∀ a b, compatible a b (choice a) (choice b) := by
  classical
  let localChoice (s : Finset α) : (a : s) → β a :=
    (hfinite s).choose
  have localCompatible (s : Finset α) :
      ∀ a b : s,
        compatible a b (localChoice s a) (localChoice s b) :=
    (hfinite s).choose_spec
  obtain ⟨choice, hagree⟩ :=
    Finset.rado_selection_subtype localChoice
  refine ⟨choice, ?_⟩
  intro a b
  obtain ⟨t, hsubset, hchoice⟩ := hagree {a, b}
  let aSmall : ({a, b} : Finset α) := ⟨a, by simp⟩
  let bSmall : ({a, b} : Finset α) := ⟨b, by simp⟩
  let aLarge : t := Set.inclusion hsubset aSmall
  let bLarge : t := Set.inclusion hsubset bSmall
  have ha : choice a = localChoice t aLarge := by
    simpa [aSmall, aLarge] using hchoice aSmall
  have hb : choice b = localChoice t bLarge := by
    simpa [bSmall, bLarge] using hchoice bSmall
  have hlocal := localCompatible t aLarge bLarge
  rw [← ha, ← hb] at hlocal
  simpa [aLarge, bLarge] using hlocal

namespace SimpleGraph

variable {V : Type u} {W C : Type v} {n : ℕ}
    (G : SimpleGraph V) (H : SimpleGraph W)

/-- Finite-target graph-homomorphism compactness. If every finite induced
subgraph of `G` admits a homomorphism to a finite graph `H`, then `G` itself
admits a homomorphism to `H`. -/
theorem nonempty_hom_of_finite_induced [Finite W]
    (hfinite : ∀ s : Finset V,
      Nonempty (G.induce (↑s : Set V) →g H)) :
    Nonempty (G →g H) := by
  classical
  let localHom (s : Finset V) : G.induce (↑s : Set V) →g H :=
    (hfinite s).some
  obtain ⟨vertexMap, hvertexMap⟩ :=
    Finset.rado_selection_constraints
      (β := fun _ : V => W)
      (fun a b imageA imageB => G.Adj a b → H.Adj imageA imageB)
      (fun s => ⟨fun vertex => localHom s vertex, fun a b hadj =>
        (localHom s).map_adj ((induce_adj (G := G)).2 hadj)⟩)
  exact ⟨⟨vertexMap, fun {a b} hadj => hvertexMap a b hadj⟩⟩

/-- A homomorphism to a finite target exists exactly when one exists from
every finite induced subgraph. -/
theorem nonempty_hom_iff_finite_induced [Finite W] :
    Nonempty (G →g H) ↔
      ∀ s : Finset V,
        Nonempty (G.induce (↑s : Set V) →g H) := by
  constructor
  · rintro ⟨hom⟩ s
    exact ⟨hom.comp (Embedding.induce (G := G) (↑s : Set V)).toHom⟩
  · exact G.nonempty_hom_of_finite_induced H

/-- Failure of a homomorphism to a finite target is witnessed on a finite
induced subgraph. -/
theorem not_nonempty_hom_iff_exists_finite_induced [Finite W] :
    ¬Nonempty (G →g H) ↔
      ∃ s : Finset V,
        ¬Nonempty (G.induce (↑s : Set V) →g H) := by
  classical
  rw [G.nonempty_hom_iff_finite_induced H]
  simp only [not_forall]

/-- Coloring compactness for an arbitrary finite palette. If every finite
induced subgraph has a coloring by `C`, then the whole graph does. -/
theorem nonempty_coloring_of_finite_induced [Finite C]
    (hfinite : ∀ s : Finset V,
      Nonempty ((G.induce (↑s : Set V)).Coloring C)) :
    Nonempty (G.Coloring C) := by
  exact G.nonempty_hom_of_finite_induced (completeGraph C) hfinite

/-- A coloring by a finite palette exists exactly when every finite induced
subgraph has one. -/
theorem nonempty_coloring_iff_finite_induced [Finite C] :
    Nonempty (G.Coloring C) ↔
      ∀ s : Finset V,
        Nonempty ((G.induce (↑s : Set V)).Coloring C) := by
  constructor
  · rintro ⟨coloring⟩ s
    exact ⟨coloring.comp
      (Embedding.induce (G := G) (↑s : Set V)).toHom⟩
  · exact G.nonempty_coloring_of_finite_induced

/-- Failure of coloring by a finite palette is witnessed on a finite induced
subgraph. -/
theorem not_nonempty_coloring_iff_exists_finite_induced [Finite C] :
    ¬Nonempty (G.Coloring C) ↔
      ∃ s : Finset V,
        ¬Nonempty ((G.induce (↑s : Set V)).Coloring C) := by
  classical
  rw [G.nonempty_coloring_iff_finite_induced]
  simp only [not_forall]

/-- **De Bruijn--Erdős compactness theorem.** If every finite induced subgraph
of `G` is colorable with `n` colors, then `G` is colorable with `n` colors. -/
theorem colorable_of_finite_induced_colorable
    (hfinite : ∀ s : Finset V, (G.induce (↑s : Set V)).Colorable n) :
    G.Colorable n := by
  exact G.nonempty_hom_of_finite_induced (completeGraph (Fin n)) hfinite

/-- A global coloring restricts to every finite induced subgraph. -/
theorem finite_induced_colorable_of_colorable (hcolorable : G.Colorable n)
    (s : Finset V) : (G.induce (↑s : Set V)).Colorable n :=
  hcolorable.of_hom (Embedding.induce (G := G) (↑s : Set V)).toHom

/-- A graph is `n`-colorable exactly when all its finite induced subgraphs are
`n`-colorable. -/
theorem colorable_iff_finite_induced_colorable :
    G.Colorable n ↔
      ∀ s : Finset V, (G.induce (↑s : Set V)).Colorable n := by
  constructor
  · exact fun hcolorable s =>
      G.finite_induced_colorable_of_colorable hcolorable s
  · exact G.colorable_of_finite_induced_colorable

/-- Contrapositive finite-obstruction form of the de Bruijn--Erdős theorem. -/
theorem not_colorable_iff_exists_finite_induced_not_colorable :
    ¬G.Colorable n ↔
      ∃ s : Finset V, ¬(G.induce (↑s : Set V)).Colorable n := by
  classical
  rw [G.colorable_iff_finite_induced_colorable]
  simp only [not_forall]

section ListColoring

variable (available : V → Set C)

/-- A proper coloring in which every vertex receives a color from its
prescribed finite list. -/
structure ListColoring where
  /-- The underlying proper coloring. -/
  coloring : G.Coloring C
  /-- Every chosen color belongs to the corresponding vertex list. -/
  mem_available : ∀ vertex, coloring vertex ∈ available vertex

namespace ListColoring

/-- Restrict a list coloring to an induced subgraph. -/
def induce {G : SimpleGraph V} {available : V → Set C}
    (coloring : G.ListColoring available) (s : Finset V) :
    (G.induce (↑s : Set V)).ListColoring
      (fun vertex : s => available vertex) where
  coloring := coloring.coloring.comp
    (Embedding.induce (G := G) (↑s : Set V)).toHom
  mem_available vertex := coloring.mem_available vertex

end ListColoring

/-- Compactness for finite-list coloring. If every finite induced subgraph
has a proper coloring from the prescribed finite lists, then the whole graph
has one. -/
theorem nonempty_listColoring_of_finite_induced
    [∀ vertex, Finite (available vertex)]
    (hfinite : ∀ s : Finset V,
      Nonempty ((G.induce (↑s : Set V)).ListColoring
        (fun vertex : s => available vertex))) :
    Nonempty (G.ListColoring available) := by
  classical
  let localColoring (s : Finset V) :
      (G.induce (↑s : Set V)).ListColoring
        (fun vertex : s => available vertex) :=
    (hfinite s).some
  obtain ⟨choice, hchoice⟩ :=
    Finset.rado_selection_constraints
      (β := fun vertex => {color // color ∈ available vertex})
      (fun a b colorA colorB => G.Adj a b → colorA.1 ≠ colorB.1)
      (fun s => ⟨fun vertex =>
        ⟨(localColoring s).coloring vertex,
          (localColoring s).mem_available vertex⟩,
        fun a b hadj => (localColoring s).coloring.valid
          ((induce_adj (G := G)).2 hadj)⟩)
  refine ⟨⟨Coloring.mk (fun vertex => (choice vertex).1) ?_,
    fun vertex => (choice vertex).2⟩⟩
  intro a b hadj
  exact hchoice a b hadj

/-- A graph has a coloring from prescribed finite lists exactly when all its
finite induced subgraphs do. -/
theorem nonempty_listColoring_iff_finite_induced
    [∀ vertex, Finite (available vertex)] :
    Nonempty (G.ListColoring available) ↔
      ∀ s : Finset V,
        Nonempty ((G.induce (↑s : Set V)).ListColoring
          (fun vertex : s => available vertex)) := by
  constructor
  · rintro ⟨coloring⟩ s
    exact ⟨coloring.induce s⟩
  · exact G.nonempty_listColoring_of_finite_induced available

/-- Failure of coloring from finite lists is witnessed on a finite induced
subgraph. -/
theorem not_nonempty_listColoring_iff_exists_finite_induced
    [∀ vertex, Finite (available vertex)] :
    ¬Nonempty (G.ListColoring available) ↔
      ∃ s : Finset V,
        ¬Nonempty ((G.induce (↑s : Set V)).ListColoring
          (fun vertex : s => available vertex)) := by
  classical
  rw [G.nonempty_listColoring_iff_finite_induced available]
  simp only [not_forall]

end ListColoring

/-- Requiring at least `n + 1` colors is equivalent to failure of
`n`-colorability. -/
theorem succ_le_chromaticNumber_iff_not_colorable :
    ((n + 1 : ℕ) : ℕ∞) ≤ G.chromaticNumber ↔ ¬G.Colorable n := by
  constructor
  · intro hlower hcolorable
    have himpossible : ((n + 1 : ℕ) : ℕ∞) ≤ (n : ℕ∞) :=
      hlower.trans hcolorable.chromaticNumber_le
    norm_cast at himpossible
    omega
  · intro hnot
    apply le_chromaticNumber_iff_colorable.2
    intro colors hcolorable
    by_contra hbound
    have hle : colors ≤ n := by omega
    exact hnot (hcolorable.mono hle)

/-- Every positive finite lower bound on the chromatic number is already
detected by a finite induced subgraph. -/
theorem succ_le_chromaticNumber_iff_exists_finite_induced :
    ((n + 1 : ℕ) : ℕ∞) ≤ G.chromaticNumber ↔
      ∃ s : Finset V,
        ((n + 1 : ℕ) : ℕ∞) ≤
          (G.induce (↑s : Set V)).chromaticNumber := by
  calc
    ((n + 1 : ℕ) : ℕ∞) ≤ G.chromaticNumber ↔ ¬G.Colorable n :=
      G.succ_le_chromaticNumber_iff_not_colorable
    _ ↔ ∃ s : Finset V,
        ¬(G.induce (↑s : Set V)).Colorable n :=
      G.not_colorable_iff_exists_finite_induced_not_colorable
    _ ↔ ∃ s : Finset V,
        ((n + 1 : ℕ) : ℕ∞) ≤
          (G.induce (↑s : Set V)).chromaticNumber := by
      apply exists_congr
      intro s
      exact (G.induce (↑s : Set V)).succ_le_chromaticNumber_iff_not_colorable.symm

/-- If a graph has positive finite chromatic number, some finite induced
subgraph has exactly the same chromatic number. -/
theorem exists_finite_induced_chromaticNumber_eq
    (hchromatic : G.chromaticNumber = ((n + 1 : ℕ) : ℕ∞)) :
    ∃ s : Finset V,
      (G.induce (↑s : Set V)).chromaticNumber =
        ((n + 1 : ℕ) : ℕ∞) := by
  obtain ⟨s, hlower⟩ :=
    G.succ_le_chromaticNumber_iff_exists_finite_induced.mp hchromatic.ge
  refine ⟨s, le_antisymm ?_ hlower⟩
  have hupper := chromaticNumber_mono_of_hom
    (Embedding.induce (G := G) (↑s : Set V)).toHom
  simpa [hchromatic] using hupper

/-- A graph has finite chromatic number exactly when one finite number of
colors works uniformly for all finite induced subgraphs. -/
theorem chromaticNumber_ne_top_iff_exists_uniform_finite_induced_colorable :
    G.chromaticNumber ≠ ⊤ ↔
      ∃ n, ∀ s : Finset V,
        (G.induce (↑s : Set V)).Colorable n := by
  rw [chromaticNumber_ne_top_iff_exists]
  constructor
  · rintro ⟨n, hcolorable⟩
    exact ⟨n, fun s =>
      G.finite_induced_colorable_of_colorable hcolorable s⟩
  · rintro ⟨n, hfinite⟩
    exact ⟨n, G.colorable_of_finite_induced_colorable hfinite⟩

/-- An infinite chromatic number is equivalent to finite obstructions to
`n`-colorability for every finite `n`. -/
theorem chromaticNumber_eq_top_iff_forall_exists_finite_induced_not_colorable :
    G.chromaticNumber = ⊤ ↔
      ∀ n, ∃ s : Finset V,
        ¬(G.induce (↑s : Set V)).Colorable n := by
  constructor
  · intro htop n
    rw [← G.not_colorable_iff_exists_finite_induced_not_colorable]
    intro hcolorable
    have hne : G.chromaticNumber ≠ ⊤ :=
      chromaticNumber_ne_top_iff_exists.mpr ⟨n, hcolorable⟩
    exact hne htop
  · intro hfinite
    by_contra hne
    obtain ⟨n, hcolorable⟩ :=
      chromaticNumber_ne_top_iff_exists.mp hne
    obtain ⟨s, hnotColorable⟩ := hfinite n
    exact hnotColorable
      (G.finite_induced_colorable_of_colorable hcolorable s)

/-- Equivalently, finite induced chromatic numbers are unbounded precisely
when the whole graph has infinite chromatic number. -/
theorem chromaticNumber_eq_top_iff_forall_exists_finite_induced_succ_le :
    G.chromaticNumber = ⊤ ↔
      ∀ n, ∃ s : Finset V,
        ((n + 1 : ℕ) : ℕ∞) ≤
          (G.induce (↑s : Set V)).chromaticNumber := by
  constructor
  · intro htop n
    obtain ⟨s, hnotColorable⟩ :=
      G.chromaticNumber_eq_top_iff_forall_exists_finite_induced_not_colorable.mp
        htop n
    exact ⟨s,
      (G.induce (↑s : Set V)).succ_le_chromaticNumber_iff_not_colorable.mpr
        hnotColorable⟩
  · intro hunbounded
    apply G.chromaticNumber_eq_top_iff_forall_exists_finite_induced_not_colorable.mpr
    intro n
    obtain ⟨s, hlower⟩ := hunbounded n
    exact ⟨s,
      (G.induce (↑s : Set V)).succ_le_chromaticNumber_iff_not_colorable.mp
        hlower⟩

end SimpleGraph
