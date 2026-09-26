/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/
module


public import LeanPool.BrillNoetherGraphs.Utilities.Foundations.RankOne
public import LeanPool.BrillNoetherGraphs.Utilities.Transmission.TransmissionSpecial

/-!
# Rank-one witnesses from indexed harmonic maps

This file isolates the *small* mathematical interface behind the familiar
``harmonic morphism to a tree gives a `g^1_d`'' argument.

`IndexedHarmonicCertificate` is passive finite data: a vertex map, positive
local degrees, and the total positive indices over each pair of source
vertices.  Its Boolean checker verifies the local harmonicity equations.  For
unit indices, `pullback_prin_of_unitIndexed` proves the required Laplacian
identity and no pullback hypothesis remains.  General metric dilation indices
would require a weighted source Laplacian, so that genuinely broader case is
still exposed separately as `PullbackPrincipalCompatible` rather than being
silently accepted by the ordinary `CFGraph` checker.

Once that compatibility is available, the soundness proof is deliberately
tiny: a fibre is effective, has degree `d`, and contains a chip above every
source vertex.  Equivalence of one-chip divisors on the target transports the
corresponding fibres, so the fibre has rank at least one.
-/

@[expose] public section

namespace MarkedGraphs

open Utilities

open Finset

/-- Passive finite data emitted by a search program for an indexed harmonic
map.  `Valid` below, rather than this structure, records its correctness. -/
structure IndexedHarmonicCertificate (G H : CFGraph) where
  /-- The proposed map of source vertices to target vertices; harmonicity and adjacency
  conditions are imposed by `Valid`. -/
  vertexMap : G.V → H.V
  /-- The proposed local degree at each source vertex, used in the harmonicity equations checked
  by `Valid`. -/
  localDegree : G.V → ℕ
  /-- The total index assigned to each parallel bundle between source vertices; positivity and
  compatibility are required separately by `Valid`. -/
  edgeIndex : G.V → G.V → ℕ

namespace IndexedHarmonicCertificate

variable {G H : CFGraph}

/-- Propositional validity of the finite edge-index data.

`edgeIndex x y` is the *total* index of the parallel bundle between `x` and
`y`.  The lower bound by `numEdges G x y` says that each source edge has a
positive integral index; the target-adjacency condition says that no edge is
contracted.  The local equation is harmonicity, expressed after aggregating
parallel edges. -/
def Valid (c : IndexedHarmonicCertificate G H) : Prop :=
  (∀ x, 0 < c.localDegree x) ∧
  (∀ p : G.V × G.V, c.edgeIndex p.1 p.2 = c.edgeIndex p.2 p.1) ∧
  (∀ p : G.V × G.V, numEdges G p.1 p.2 = 0 → c.edgeIndex p.1 p.2 = 0) ∧
  (∀ p : G.V × G.V, numEdges G p.1 p.2 ≤ c.edgeIndex p.1 p.2) ∧
  (∀ p : G.V × G.V, numEdges G p.1 p.2 > 0 →
    c.vertexMap p.1 ≠ c.vertexMap p.2 ∧
      numEdges H (c.vertexMap p.1) (c.vertexMap p.2) > 0) ∧
  (∀ p : G.V × H.V,
    (∑ y : G.V, if c.vertexMap y = p.2 then c.edgeIndex p.1 y else 0) =
      c.localDegree p.1 * numEdges H (c.vertexMap p.1) p.2)

end IndexedHarmonicCertificate

/-- Validated finite data for a nondegenerate indexed harmonic map. -/
structure IndexedHarmonicData (G H : CFGraph) extends IndexedHarmonicCertificate G H where
  localDegree_pos : ∀ x, 0 < localDegree x
  edgeIndex_symmetric : ∀ x y, edgeIndex x y = edgeIndex y x
  edgeIndex_zero_of_no_source_edge : ∀ x y,
    numEdges G x y = 0 → edgeIndex x y = 0
  sourceMultiplicity_le_edgeIndex : ∀ x y,
    numEdges G x y ≤ edgeIndex x y
  maps_source_edges_to_target_edges : ∀ x y,
    numEdges G x y > 0 →
      vertexMap x ≠ vertexMap y ∧ numEdges H (vertexMap x) (vertexMap y) > 0
  harmonic : ∀ x z,
    (∑ y : G.V, if vertexMap y = z then edgeIndex x y else 0) =
      localDegree x * numEdges H (vertexMap x) z

namespace IndexedHarmonicCertificate

/-- Compatibility with ordinary (unweighted) `CFGraph` chip-firing: the total
index of a parallel source bundle is its ordinary edge multiplicity.  General
metric dilation indices require a weighted Laplacian and are intentionally not
silently accepted by this predicate. -/
def UnitIndexed (c : IndexedHarmonicCertificate G H) : Prop :=
  ∀ p : G.V × G.V, c.edgeIndex p.1 p.2 = numEdges G p.1 p.2

/-- Degree of one raw fibre, computed without constructing a divisor. -/
def fibreDegree (c : IndexedHarmonicCertificate G H) (z : H.V) : ℤ :=
  ∑ x : G.V, if c.vertexMap x = z then (c.localDegree x : ℤ) else 0

/-- Every raw fibre has the advertised global degree. -/
def HasDegree (c : IndexedHarmonicCertificate G H) (d : ℤ) : Prop :=
  ∀ z, c.fibreDegree z = d

/-- Executable replay of all finite local conditions. -/
def check (c : IndexedHarmonicCertificate G H) : Bool :=
  (@decide (∀ x : G.V, 0 < c.localDegree x)
    Fintype.decidableForallFintype) &&
  (@decide (∀ p : G.V × G.V, c.edgeIndex p.1 p.2 = c.edgeIndex p.2 p.1)
    Fintype.decidableForallFintype) &&
  (@decide (∀ p : G.V × G.V,
    numEdges G p.1 p.2 = 0 → c.edgeIndex p.1 p.2 = 0)
    Fintype.decidableForallFintype) &&
  (@decide (∀ p : G.V × G.V,
    numEdges G p.1 p.2 ≤ c.edgeIndex p.1 p.2)
    Fintype.decidableForallFintype) &&
  (@decide (∀ p : G.V × G.V, numEdges G p.1 p.2 > 0 →
    c.vertexMap p.1 ≠ c.vertexMap p.2 ∧
      numEdges H (c.vertexMap p.1) (c.vertexMap p.2) > 0)
    Fintype.decidableForallFintype) &&
  (@decide (∀ p : G.V × H.V,
    (∑ y : G.V, if c.vertexMap y = p.2 then c.edgeIndex p.1 y else 0) =
      c.localDegree p.1 * numEdges H (c.vertexMap p.1) p.2)
    Fintype.decidableForallFintype)

/-- Executable unit-index check, to be combined with `check` when the
certificate is intended to act on the ordinary source Laplacian. -/
def checkUnitIndexed (c : IndexedHarmonicCertificate G H) : Bool :=
  @decide (∀ p : G.V × G.V,
    c.edgeIndex p.1 p.2 = numEdges G p.1 p.2)
    Fintype.decidableForallFintype

/-- Executable constant-fibre-degree check. -/
def checkDegree (c : IndexedHarmonicCertificate G H) (d : ℤ) : Bool :=
  @decide (∀ z : H.V, c.fibreDegree z = d)
    Fintype.decidableForallFintype

/-- Executable degree check at one chosen target vertex.  For a valid
harmonic certificate into a connected target, this is equivalent to the
otherwise redundant all-fibres check; see
`IndexedHarmonicData.hasDegree_toData_of_fibreDegree_at`. -/
def checkDegreeAt (c : IndexedHarmonicCertificate G H) (z : H.V) (d : ℤ) : Bool :=
  decide (c.fibreDegree z = d)

@[simp] theorem check_eq_true_iff (c : IndexedHarmonicCertificate G H) :
    c.check = true ↔ c.Valid := by
  simp only [check, Bool.and_eq_true]
  simp only [decide_eq_true_eq]
  simp [Valid, and_assoc]

@[simp] theorem checkUnitIndexed_eq_true_iff
    (c : IndexedHarmonicCertificate G H) :
    c.checkUnitIndexed = true ↔ c.UnitIndexed := by
  simp [checkUnitIndexed, UnitIndexed]

@[simp] theorem checkDegree_eq_true_iff
    (c : IndexedHarmonicCertificate G H) (d : ℤ) :
    c.checkDegree d = true ↔ c.HasDegree d := by
  simp [checkDegree, HasDegree]

@[simp] theorem checkDegreeAt_eq_true_iff
    (c : IndexedHarmonicCertificate G H) (z : H.V) (d : ℤ) :
    c.checkDegreeAt z d = true ↔ c.fibreDegree z = d := by
  simp [checkDegreeAt]

/-- A verified raw certificate becomes the mathematical harmonic-map object. -/
def toData (c : IndexedHarmonicCertificate G H) (h : c.Valid) :
    IndexedHarmonicData G H :=
  { vertexMap := c.vertexMap
    localDegree := c.localDegree
    edgeIndex := c.edgeIndex
    localDegree_pos := h.1
    edgeIndex_symmetric := fun x y => h.2.1 (x, y)
    edgeIndex_zero_of_no_source_edge := fun x y => h.2.2.1 (x, y)
    sourceMultiplicity_le_edgeIndex := fun x y => h.2.2.2.1 (x, y)
    maps_source_edges_to_target_edges := fun x y => h.2.2.2.2.1 (x, y)
    harmonic := fun x z => h.2.2.2.2.2 (x, z) }

end IndexedHarmonicCertificate

namespace IndexedHarmonicData

variable {G H : CFGraph}

/-- The target-one-chip fibre, as a divisor on the source. -/
def fibre (f : IndexedHarmonicData G H) (z : H.V) : CFDiv G :=
  fun x => if f.vertexMap x = z then f.localDegree x else 0

/-- Pullback of an arbitrary target divisor using the local degrees. -/
def pullback (f : IndexedHarmonicData G H) (A : CFDiv H) : CFDiv G :=
  fun x => (f.localDegree x : ℤ) * A (f.vertexMap x)

/-- Pull a target firing script back along the vertex map. -/
def pullbackScript (f : IndexedHarmonicData G H) (σ : firingScript H) :
    firingScript G :=
  fun x => σ (f.vertexMap x)

/-- The indexed data uses the ordinary unweighted source Laplacian. -/
def UnitIndexed (f : IndexedHarmonicData G H) : Prop :=
  ∀ x y, f.edgeIndex x y = numEdges G x y

/-- A checked unit-index condition survives conversion from raw certificate
data. -/
theorem unitIndexed_toData
    (c : IndexedHarmonicCertificate G H) (hValid : c.Valid)
    (hUnit : c.UnitIndexed) :
    (c.toData hValid).UnitIndexed := by
  intro x y
  exact hUnit (x, y)

/-- Pullback is additive on subtraction. -/
theorem pullback_sub (f : IndexedHarmonicData G H) (A B : CFDiv H) :
    f.pullback (A - B) = f.pullback A - f.pullback B := by
  funext x
  simp [pullback, mul_sub]

/-- The central Laplacian identity.  For unit-indexed harmonic data, pulling
back a target principal divisor is the principal divisor of the pulled-back
script on the ordinary source graph. -/
theorem pullback_prin_of_unitIndexed
    (f : IndexedHarmonicData G H) (hUnit : f.UnitIndexed)
    (σ : firingScript H) :
    f.pullback (prin H σ) = prin G (f.pullbackScript σ) := by
  funext x
  have hHarmonic (z : H.V) :
      (∑ y : G.V,
          if f.vertexMap y = z then (f.edgeIndex x y : ℤ) else 0) =
        (f.localDegree x : ℤ) * (numEdges H (f.vertexMap x) z : ℤ) := by
    exact_mod_cast f.harmonic x z
  have hUnitInt (y : G.V) :
      (f.edgeIndex x y : ℤ) = (numEdges G x y : ℤ) := by
    exact_mod_cast hUnit x y
  change
    (f.localDegree x : ℤ) *
        (∑ z : H.V, (σ z - σ (f.vertexMap x)) *
          (numEdges H (f.vertexMap x) z : ℤ)) =
      ∑ y : G.V, (σ (f.vertexMap y) - σ (f.vertexMap x)) *
        (numEdges G x y : ℤ)
  calc
    (f.localDegree x : ℤ) *
          (∑ z : H.V, (σ z - σ (f.vertexMap x)) *
            (numEdges H (f.vertexMap x) z : ℤ)) =
        ∑ z : H.V, (σ z - σ (f.vertexMap x)) *
          ((f.localDegree x : ℤ) *
            (numEdges H (f.vertexMap x) z : ℤ)) := by
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro z _
              ring
    _ = ∑ z : H.V, (σ z - σ (f.vertexMap x)) *
          (∑ y : G.V,
            if f.vertexMap y = z then (f.edgeIndex x y : ℤ) else 0) := by
              apply Finset.sum_congr rfl
              intro z _
              rw [hHarmonic z]
    _ = ∑ z : H.V, ∑ y : G.V,
          if f.vertexMap y = z then
            (σ z - σ (f.vertexMap x)) * (f.edgeIndex x y : ℤ)
          else 0 := by
              apply Finset.sum_congr rfl
              intro z _
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro y _
              by_cases hy : f.vertexMap y = z <;> simp [hy]
    _ = ∑ y : G.V, ∑ z : H.V,
          if f.vertexMap y = z then
            (σ z - σ (f.vertexMap x)) * (f.edgeIndex x y : ℤ)
          else 0 := by
              rw [Finset.sum_comm]
    _ = ∑ y : G.V,
          (σ (f.vertexMap y) - σ (f.vertexMap x)) *
            (f.edgeIndex x y : ℤ) := by
              apply Finset.sum_congr rfl
              intro y _
              simp
    _ = ∑ y : G.V,
          (σ (f.vertexMap y) - σ (f.vertexMap x)) *
            (numEdges G x y : ℤ) := by
              apply Finset.sum_congr rfl
              intro y _
              rw [hUnitInt y]

/-- The (constant) degree of the map, expressed as the degree of every fibre.
This is the one global numerical datum needed by the rank-one argument. -/
def HasDegree (f : IndexedHarmonicData G H) (d : ℤ) : Prop :=
  ∀ z, deg (f.fibre z) = d

/-- The degrees of two fibres above adjacent target vertices agree.  This is
the finite double-counting identity behind the usual assertion that the
degree of a harmonic map is independent of the target point. -/
theorem fibre_degree_eq_of_target_edge
    (f : IndexedHarmonicData G H) {z w : H.V}
    (hzw : numEdges H z w > 0) :
    deg (f.fibre z) = deg (f.fibre w) := by
  let m : ℤ := (numEdges H z w : ℤ)
  have hleft : m * deg (f.fibre z) =
      ∑ x : G.V, if f.vertexMap x = z then
        ∑ y : G.V, if f.vertexMap y = w then (f.edgeIndex x y : ℤ) else 0
      else 0 := by
    calc
      m * deg (f.fibre z) =
          ∑ x : G.V, if f.vertexMap x = z then
            m * (f.localDegree x : ℤ) else 0 := by
              rw [show deg (f.fibre z) =
                ∑ x : G.V, if f.vertexMap x = z then
                  (f.localDegree x : ℤ) else 0 by rfl]
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro x _
              by_cases hx : f.vertexMap x = z <;> simp [hx]
      _ = ∑ x : G.V, if f.vertexMap x = z then
            ∑ y : G.V, if f.vertexMap y = w then (f.edgeIndex x y : ℤ) else 0
          else 0 := by
              apply Finset.sum_congr rfl
              intro x _
              by_cases hx : f.vertexMap x = z
              · have h :
                    (∑ y : G.V,
                      if f.vertexMap y = w then (f.edgeIndex x y : ℤ) else 0) =
                    (f.localDegree x : ℤ) *
                      (numEdges H (f.vertexMap x) w : ℤ) := by
                      exact_mod_cast f.harmonic x w
                rw [hx] at h
                simp only [hx, ite_true]
                rw [h]
                dsimp [m]
                ring
              · simp [hx]
  have hright : m * deg (f.fibre w) =
      ∑ y : G.V, if f.vertexMap y = w then
        ∑ x : G.V, if f.vertexMap x = z then (f.edgeIndex y x : ℤ) else 0
      else 0 := by
    calc
      m * deg (f.fibre w) =
          ∑ y : G.V, if f.vertexMap y = w then
            m * (f.localDegree y : ℤ) else 0 := by
              rw [show deg (f.fibre w) =
                ∑ y : G.V, if f.vertexMap y = w then
                  (f.localDegree y : ℤ) else 0 by rfl]
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro y _
              by_cases hy : f.vertexMap y = w <;> simp [hy]
      _ = ∑ y : G.V, if f.vertexMap y = w then
            ∑ x : G.V, if f.vertexMap x = z then (f.edgeIndex y x : ℤ) else 0
          else 0 := by
              apply Finset.sum_congr rfl
              intro y _
              by_cases hy : f.vertexMap y = w
              · have h :
                    (∑ x : G.V,
                      if f.vertexMap x = z then (f.edgeIndex y x : ℤ) else 0) =
                    (f.localDegree y : ℤ) *
                      (numEdges H (f.vertexMap y) z : ℤ) := by
                      exact_mod_cast f.harmonic y z
                rw [hy, num_edges_symmetric H w z] at h
                simp only [hy, ite_true]
                rw [h]
                dsimp [m]
                ring
              · simp [hy]
  have hswap :
      (∑ x : G.V, if f.vertexMap x = z then
        ∑ y : G.V, if f.vertexMap y = w then (f.edgeIndex x y : ℤ) else 0
      else 0) =
      ∑ y : G.V, if f.vertexMap y = w then
        ∑ x : G.V, if f.vertexMap x = z then (f.edgeIndex y x : ℤ) else 0
      else 0 := by
    calc
      _ = ∑ x : G.V, ∑ y : G.V,
          if f.vertexMap x = z then
            if f.vertexMap y = w then (f.edgeIndex x y : ℤ) else 0
          else 0 := by
            apply Finset.sum_congr rfl
            intro x _
            by_cases hx : f.vertexMap x = z <;> simp [hx]
      _ = ∑ y : G.V, ∑ x : G.V,
          if f.vertexMap x = z then
            if f.vertexMap y = w then (f.edgeIndex x y : ℤ) else 0
          else 0 := by rw [Finset.sum_comm]
      _ = ∑ y : G.V, ∑ x : G.V,
          if f.vertexMap y = w then
            if f.vertexMap x = z then (f.edgeIndex y x : ℤ) else 0
          else 0 := by
            apply Finset.sum_congr rfl
            intro y _
            apply Finset.sum_congr rfl
            intro x _
            by_cases hx : f.vertexMap x = z <;>
              by_cases hy : f.vertexMap y = w <;>
              simp [hx, hy, f.edgeIndex_symmetric]
      _ = _ := by
            apply Finset.sum_congr rfl
            intro y _
            by_cases hy : f.vertexMap y = w <;> simp [hy]
  apply mul_left_cancel₀ (show m ≠ 0 by
    dsimp [m]
    exact_mod_cast (Nat.ne_of_gt hzw))
  exact hleft.trans (hswap.trans hright.symm)

/-- A function on the vertices of a connected graph which is constant across
every target edge is constant everywhere.  The cut-based definition of
`graphConnected` makes this a short finite proof. -/
theorem eq_of_graph_connected_of_eq_on_edges
    {α : Type} [DecidableEq α] (F : H.V → α)
    (hConnected : graphConnected H)
    (hEdge : ∀ z w : H.V, numEdges H z w > 0 → F z = F w)
    (z₀ z : H.V) : F z = F z₀ := by
  by_contra hz
  let S : Finset H.V := Finset.univ.filter fun u => F u = F z₀
  have hz₀ : z₀ ∈ S := by simp [S]
  have hznot : z ∉ S := by simpa [S] using hz
  obtain ⟨u, hu, v, hv, huv⟩ := hConnected S ⟨z₀, z, hz₀, hznot⟩
  have huEq : F u = F z₀ := by simpa [S] using hu
  have hvNe : F v ≠ F z₀ := by simpa [S] using hv
  exact hvNe ((hEdge u v huv).symm.trans huEq)

/-- Harmonicity makes the fibre degree locally constant on the target, and
therefore constant on every connected target. -/
theorem fibre_degree_eq_of_target_connected
    (f : IndexedHarmonicData G H) (hConnected : graphConnected H)
    (z w : H.V) :
    deg (f.fibre z) = deg (f.fibre w) :=
  eq_of_graph_connected_of_eq_on_edges (fun u => deg (f.fibre u)) hConnected
    (fun _ _ huv => f.fibre_degree_eq_of_target_edge huv) w z

/-- One fibre-degree calculation suffices for a harmonic map to a connected
target. -/
theorem hasDegree_of_fibre_degree_at
    (f : IndexedHarmonicData G H) (hConnected : graphConnected H)
    (z₀ : H.V) {d : ℤ} (hDegree : deg (f.fibre z₀) = d) :
    f.HasDegree d := by
  intro z
  exact (f.fibre_degree_eq_of_target_connected hConnected z z₀).trans hDegree

/-- A checked raw fibre-degree equation is exactly the divisor-degree
condition used by the rank-one soundness theorem. -/
theorem hasDegree_toData
    (c : IndexedHarmonicCertificate G H) (hValid : c.Valid) {d : ℤ}
    (hDegree : c.HasDegree d) :
    (c.toData hValid).HasDegree d := by
  intro z
  unfold fibre deg
  change (∑ x : G.V,
    if c.vertexMap x = z then (c.localDegree x : ℤ) else 0) = d
  exact hDegree z

/-- The one raw fibre-degree computation transfers directly to the divisor
fibre of validated data. -/
theorem fibreDegree_toData
    (c : IndexedHarmonicCertificate G H) (hValid : c.Valid) (z : H.V) :
    deg ((c.toData hValid).fibre z) = c.fibreDegree z := by
  rfl

/-- The global degree field is redundant for valid harmonic data over a
connected target: checking one raw fibre determines all of them. -/
theorem hasDegree_toData_of_fibreDegree_at
    (c : IndexedHarmonicCertificate G H) (hValid : c.Valid)
    (hConnected : graphConnected H) (z₀ : H.V) {d : ℤ}
    (hDegree : c.fibreDegree z₀ = d) :
    (c.toData hValid).HasDegree d := by
  apply (c.toData hValid).hasDegree_of_fibre_degree_at hConnected z₀
  rw [fibreDegree_toData c hValid z₀]
  exact hDegree

/-- `fibre` really is pullback of a one-chip divisor. -/
theorem pullback_one_chip (f : IndexedHarmonicData G H) (z : H.V) :
    f.pullback (oneChip z) = f.fibre z := by
  funext x
  by_cases hx : f.vertexMap x = z
  · simp [pullback, fibre, hx]
  · simp [pullback, fibre, hx]

/-- A fibre is effective. -/
theorem fibre_effective (f : IndexedHarmonicData G H) (z : H.V) :
    effective (f.fibre z) := by
  intro x
  dsimp [fibre]
  split <;> exact Int.natCast_nonneg _

/-- Removing the chip at `x` from the fibre over its image remains effective.
Nondegeneracy is exactly the needed fact here. -/
theorem fibre_sub_one_chip_effective
    (f : IndexedHarmonicData G H) (x : G.V) :
    effective (f.fibre (f.vertexMap x) - oneChip x) := by
  intro y
  change 0 ≤ f.fibre (f.vertexMap x) y - oneChip x y
  by_cases hxy : y = x
  · subst y
    simp only [fibre, oneChip, ite_eq_left]
    exact sub_nonneg.mpr (by
      exact_mod_cast (Nat.succ_le_iff.mpr (f.localDegree_pos x)))
  · have hEffective := f.fibre_effective (f.vertexMap x) y
    simpa [oneChip, hxy] using hEffective

/-- The target condition actually used by the rank-one proof. -/
def TargetOneChipEquivalent (H : CFGraph) : Prop :=
  ∀ y z : H.V, linearEquiv H (oneChip y) (oneChip z)

/-- A connected genus-zero target has trivial degree-zero chip-firing class
group.  This is the graph-theoretic content of the usual phrase “target is a
tree”; it is stated in the invariant form available in `CFGraph`. -/
theorem targetOneChipEquivalent_of_connected_genus_zero
    (H : CFGraph) (hConnected : graphConnected H) (hGenus : genus H = 0) :
    TargetOneChipEquivalent H := by
  intro y z
  let A : CFDiv H := oneChip y - oneChip z
  have hDegree : deg A = 0 := by
    simp [A]
  have hRank : rank H A ≥ 0 := by
    have h := rank_ge_degree_sub_genus hConnected A
    rw [hDegree, hGenus] at h
    exact h
  obtain ⟨E, hEffective, hAE⟩ : ∃ E : CFDiv H,
      effective E ∧ linearEquiv H A E :=
    (winnable_iff_exists_effective H A).mp
      ((rank_nonneg_iff_winnable H A).mp ((rank_geq_iff H A 0).mpr hRank))
  have hEDegree : deg E = 0 := by
    rw [← linear_equiv_preserves_deg H A E hAE, hDegree]
  have hEZero : E = 0 := eff_degree_zero E hEffective hEDegree
  subst E
  unfold linearEquiv at hAE ⊢
  have hDifference : oneChip z - oneChip y = 0 - A := by
    dsimp [A]
    abel
  rw [hDifference]
  exact hAE

/-- Mathematical pullback compatibility, deliberately separate from the raw
finite data.  The unit-indexed checker implies it below; non-unit metric
dilations still need a future weighted-Laplacian development. -/
def PullbackPrincipalCompatible (f : IndexedHarmonicData G H) : Prop :=
  ∀ A B : CFDiv H, linearEquiv H A B →
    linearEquiv G (f.pullback A) (f.pullback B)

/-- The checked harmonicity equations plus unit edge indices imply the
previously abstract pullback-principal compatibility hypothesis. -/
theorem pullbackPrincipalCompatible_of_unitIndexed
    (f : IndexedHarmonicData G H) (hUnit : f.UnitIndexed) :
    f.PullbackPrincipalCompatible := by
  intro A B hAB
  unfold linearEquiv at hAB ⊢
  rw [principal_iff_eq_prin] at hAB ⊢
  obtain ⟨σ, hσ⟩ := hAB
  refine ⟨f.pullbackScript σ, ?_⟩
  calc
    f.pullback B - f.pullback A = f.pullback (B - A) :=
      (f.pullback_sub B A).symm
    _ = f.pullback (prin H σ) := congrArg f.pullback hσ
    _ = prin G (f.pullbackScript σ) := f.pullback_prin_of_unitIndexed hUnit σ

/-- Boolean-check boundary for pullback compatibility: a raw certificate whose
local equations and unit-index condition both replay successfully supplies the
mathematical hypothesis used by the rank-one theorems. -/
theorem pullbackPrincipalCompatible_of_checks
    (c : IndexedHarmonicCertificate G H)
    (hCheck : c.check = true) (hUnitCheck : c.checkUnitIndexed = true) :
    (c.toData ((c.check_eq_true_iff).mp hCheck)).PullbackPrincipalCompatible := by
  let hValid : c.Valid := (c.check_eq_true_iff).mp hCheck
  have hUnit : c.UnitIndexed := (c.checkUnitIndexed_eq_true_iff).mp hUnitCheck
  exact pullbackPrincipalCompatible_of_unitIndexed (c.toData hValid)
    (unitIndexed_toData c hValid hUnit)

/-- Pullback transports equivalence of target one-chip divisors to
equivalence of fibres. -/
theorem fibre_linear_equiv_of_target
    (f : IndexedHarmonicData G H) (hPullback : f.PullbackPrincipalCompatible)
    {y z : H.V} (hyz : linearEquiv H (oneChip y) (oneChip z)) :
    linearEquiv G (f.fibre y) (f.fibre z) := by
  rw [← f.pullback_one_chip y, ← f.pullback_one_chip z]
  exact hPullback _ _ hyz

/-- A nondegenerate indexed harmonic map into a target with linearly
equivalent one-chip divisors supplies a rank-one divisor of its map degree. -/
theorem rank_ge_one_of_target_one_chip_equiv
    (f : IndexedHarmonicData G H) {d : ℤ} (_hDegree : f.HasDegree d)
    (hPullback : f.PullbackPrincipalCompatible)
    (hTarget : TargetOneChipEquivalent H) (z : H.V) :
    rank G (f.fibre z) ≥ 1 := by
  apply rank_ge_one_of_vertex_certificates G (f.fibre z)
  intro x
  refine ⟨f.fibre (f.vertexMap x) - oneChip x,
    f.fibre_sub_one_chip_effective x, ?_⟩
  have hFibre : linearEquiv G (f.fibre z) (f.fibre (f.vertexMap x)) :=
    f.fibre_linear_equiv_of_target hPullback (hTarget z (f.vertexMap x))
  have hSub : linearEquiv G
      (f.fibre z - oneChip x)
      (f.fibre (f.vertexMap x) - oneChip x) := by
    unfold linearEquiv at hFibre ⊢
    have hEq :
        (f.fibre (f.vertexMap x) - oneChip x) - (f.fibre z - oneChip x) =
          f.fibre (f.vertexMap x) - f.fibre z := by abel
    rw [hEq]
    exact hFibre
  exact hSub

/-- The resulting Brill--Noether witness. -/
theorem bnExists_rank_one_of_target_one_chip_equiv
    (f : IndexedHarmonicData G H) {d : ℤ} (hDegree : f.HasDegree d)
    (hPullback : f.PullbackPrincipalCompatible)
    (hTarget : TargetOneChipEquivalent H) (z : H.V) :
    BNExists G 1 d :=
  ⟨f.fibre z, hDegree z,
    f.rank_ge_one_of_target_one_chip_equiv hDegree hPullback hTarget z⟩

/-- Target-Picard form of the tree theorem, useful when one-chip equivalence is
available directly without going through connectedness and genus. -/
theorem bnExists_rank_one_of_tree_target
    (f : IndexedHarmonicData G H) {d : ℤ} (hDegree : f.HasDegree d)
    (hPullback : f.PullbackPrincipalCompatible)
    (hTreePicard : TargetOneChipEquivalent H) (z : H.V) :
    BNExists G 1 d :=
  f.bnExists_rank_one_of_target_one_chip_equiv hDegree hPullback hTreePicard z

/-- The conventional tree-target corollary, using connectedness and genus zero
instead of exposing the target Picard-group condition. -/
theorem bnExists_rank_one_of_connected_genus_zero_target
    (f : IndexedHarmonicData G H) {d : ℤ} (hDegree : f.HasDegree d)
    (hPullback : f.PullbackPrincipalCompatible)
    (hConnected : graphConnected H) (hGenus : genus H = 0) (z : H.V) :
    BNExists G 1 d :=
  f.bnExists_rank_one_of_target_one_chip_equiv hDegree hPullback
    (targetOneChipEquivalent_of_connected_genus_zero H hConnected hGenus) z

/-- End-to-end kernel boundary for the compact certificate: local harmonicity,
unit indexing, and constant fibre degree are all Boolean-replayed; only the
structural target facts `connected` and `genus = 0` are supplied as proofs. -/
theorem bnExists_rank_one_of_checked_harmonic_tree
    (c : IndexedHarmonicCertificate G H) (d : ℤ)
    (hCheck : c.check = true)
    (hUnitCheck : c.checkUnitIndexed = true)
    (hDegreeCheck : c.checkDegree d = true)
    (hConnected : graphConnected H) (hGenus : genus H = 0) (z : H.V) :
    BNExists G 1 d := by
  let hValid : c.Valid := (c.check_eq_true_iff).mp hCheck
  let f : IndexedHarmonicData G H := c.toData hValid
  have hUnit : f.UnitIndexed :=
    unitIndexed_toData c hValid
      ((c.checkUnitIndexed_eq_true_iff).mp hUnitCheck)
  have hDegree : f.HasDegree d :=
    hasDegree_toData c hValid ((c.checkDegree_eq_true_iff d).mp hDegreeCheck)
  exact f.bnExists_rank_one_of_connected_genus_zero_target hDegree
    (pullbackPrincipalCompatible_of_unitIndexed f hUnit)
    hConnected hGenus z

/-- Degree-reduced end-to-end kernel boundary.  Unlike
`bnExists_rank_one_of_checked_harmonic_tree`, this replays the fibre-degree
equation only at `z₀`: the preceding harmonic double-counting theorem and
target connectedness supply every other fibre equation. -/
theorem bnExists_rank_one_of_checked_harmonic_tree_one_degree
    (c : IndexedHarmonicCertificate G H) (d : ℤ) (z₀ : H.V)
    (hCheck : c.check = true)
    (hUnitCheck : c.checkUnitIndexed = true)
    (hDegreeCheck : c.checkDegreeAt z₀ d = true)
    (hConnected : graphConnected H) (hGenus : genus H = 0) (z : H.V) :
    BNExists G 1 d := by
  let hValid : c.Valid := (c.check_eq_true_iff).mp hCheck
  let f : IndexedHarmonicData G H := c.toData hValid
  have hUnit : f.UnitIndexed :=
    unitIndexed_toData c hValid
      ((c.checkUnitIndexed_eq_true_iff).mp hUnitCheck)
  have hDegree : f.HasDegree d :=
    hasDegree_toData_of_fibreDegree_at c hValid hConnected z₀
      ((c.checkDegreeAt_eq_true_iff z₀ d).mp hDegreeCheck)
  exact f.bnExists_rank_one_of_connected_genus_zero_target hDegree
    (pullbackPrincipalCompatible_of_unitIndexed f hUnit)
    hConnected hGenus z

end IndexedHarmonicData

end MarkedGraphs
