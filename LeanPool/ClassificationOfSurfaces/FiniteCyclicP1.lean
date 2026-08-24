/-
Copyright (c) 2026 ClassificationOfSurfaces contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryan McCorvie, Jack McCarthy
-/
import LeanPool.ClassificationOfSurfaces.FiniteCyclicPresentation

/-!
# Gallier--Xu P1 edge subdivision

This file formalizes the first primitive subdivision from Gallier--Xu, Definition 6.3. For a
chosen oriented edge `a`, P1 globally replaces

* `a` by `b c`, and
* `a⁻¹` by `c⁻¹ b⁻¹`.

The canonical finite implementation retains every old edge name through `Fin.castSucc`, uses the
retained name of `a` for `b`, and uses `Fin.last` for the fresh edge `c`. A contraction deletes
the fresh edge and sends every retained edge back to its old name. This contraction is a left
inverse on words, including cyclic words, so P1 both preserves and reflects cyclic rotation.
The selected underlying edge uses its positive stored orientation canonically. The
`SignedPresentationIso` in `P1Subdivision` allows the two target edge names to be renamed and
reoriented when a different orientation convention is desired.

The presentation-level construction preserves face positions, copies the multiplicity of `a` to
both subdivided edges, and preserves ordinary validity, face-incidence connectivity, and
`IsGallierValid`. `P1Subdivision` closes the canonical construction under signed presentation
isomorphism.
-/

namespace LeanEval
namespace Topology
namespace ClassificationOfSurfaces
namespace FiniteCyclicPresentation

open SurfaceCellComplex

namespace P1

/-- Retain an old signed edge in the enlarged edge type. -/
def castSuccDart {n : ℕ} : SignedDart (Fin n) → SignedDart (Fin (n + 1))
  | .pos e => .pos e.castSucc
  | .neg e => .neg e.castSucc

@[simp]
theorem castSuccDart_pos {n : ℕ} (e : Fin n) :
    castSuccDart (.pos e) = .pos e.castSucc :=
  rfl

@[simp]
theorem castSuccDart_neg {n : ℕ} (e : Fin n) :
    castSuccDart (.neg e) = .neg e.castSucc :=
  rfl

@[simp]
theorem edgeOfDart_castSuccDart {n : ℕ} (d : SignedDart (Fin n)) :
    edgeOfDart (castSuccDart d) = (edgeOfDart d).castSucc := by
  cases d <;> rfl

/-- The fresh second subedge in the canonical P1 expansion. -/
def freshEdge (n : ℕ) : Fin (n + 1) :=
  Fin.last n

/-- The retained first subedge in the canonical P1 expansion. -/
def firstSubedge {n : ℕ} (a : Fin n) : Fin (n + 1) :=
  a.castSucc

theorem firstSubedge_ne_freshEdge {n : ℕ} (a : Fin n) :
    firstSubedge a ≠ freshEdge n :=
  Fin.castSucc_ne_last a

/-- Substitute one signed occurrence according to Gallier--Xu P1. -/
def expandDart {n : ℕ} (a : Fin n) :
    SignedDart (Fin n) → List (SignedDart (Fin (n + 1)))
  | .pos e =>
      if e = a then
        [.pos (firstSubedge a), .pos (freshEdge n)]
      else
        [.pos e.castSucc]
  | .neg e =>
      if e = a then
        [.neg (freshEdge n), .neg (firstSubedge a)]
      else
        [.neg e.castSucc]

@[simp]
theorem expandDart_pos_self {n : ℕ} (a : Fin n) :
    expandDart a (.pos a) = [.pos (firstSubedge a), .pos (freshEdge n)] := by
  simp [expandDart]

@[simp]
theorem expandDart_neg_self {n : ℕ} (a : Fin n) :
    expandDart a (.neg a) = [.neg (freshEdge n), .neg (firstSubedge a)] := by
  simp [expandDart]

theorem expandDart_pos_of_ne {n : ℕ} {a e : Fin n} (h : e ≠ a) :
    expandDart a (.pos e) = [.pos e.castSucc] := by
  simp [expandDart, h]

theorem expandDart_neg_of_ne {n : ℕ} {a e : Fin n} (h : e ≠ a) :
    expandDart a (.neg e) = [.neg e.castSucc] := by
  simp [expandDart, h]

/-- P1 sends the opposite dart to the inverse of the substituted word. -/
@[simp]
theorem expandDart_flip {n : ℕ} (a : Fin n) (d : SignedDart (Fin n)) :
    expandDart a d.flip = inverseWord (expandDart a d) := by
  cases d with
  | pos e =>
      by_cases h : e = a
      · subst e
        simp [expandDart, inverseWord, SignedDart.flip]
      · simp [expandDart, inverseWord, SignedDart.flip, h]
  | neg e =>
      by_cases h : e = a
      · subst e
        simp [expandDart, inverseWord, SignedDart.flip]
      · simp [expandDart, inverseWord, SignedDart.flip, h]

theorem castSuccDart_mem_expandDart {n : ℕ} (a : Fin n)
    (d : SignedDart (Fin n)) :
    castSuccDart d ∈ expandDart a d := by
  cases d with
  | pos e =>
      by_cases h : e = a
      · subst e
        simp [firstSubedge]
      · simp [expandDart, h]
  | neg e =>
      by_cases h : e = a
      · subst e
        simp [firstSubedge]
      · simp [expandDart, h]

/-- Contract one target dart: discard the fresh edge and retain every old edge. -/
def contractDart {n : ℕ} :
    SignedDart (Fin (n + 1)) → Option (SignedDart (Fin n))
  | .pos e => Fin.lastCases none (fun b ↦ some (.pos b)) e
  | .neg e => Fin.lastCases none (fun b ↦ some (.neg b)) e

@[simp]
theorem contractDart_pos_castSucc {n : ℕ} (e : Fin n) :
    contractDart (.pos e.castSucc) = some (.pos e) := by
  simp [contractDart]

@[simp]
theorem contractDart_neg_castSucc {n : ℕ} (e : Fin n) :
    contractDart (.neg e.castSucc) = some (.neg e) := by
  simp [contractDart]

@[simp]
theorem contractDart_pos_freshEdge (n : ℕ) :
    contractDart (.pos (freshEdge n)) = none := by
  simp [contractDart, freshEdge]

@[simp]
theorem contractDart_neg_freshEdge (n : ℕ) :
    contractDart (.neg (freshEdge n)) = none := by
  simp [contractDart, freshEdge]

/-- Apply P1 simultaneously to every occurrence in a linear representative of a cyclic word. -/
def expandWord {n : ℕ} (a : Fin n) (word : List (SignedDart (Fin n))) :
    List (SignedDart (Fin (n + 1))) :=
  word.flatMap (expandDart a)

/-- Contract a P1 word by deleting the fresh subedge. -/
def contractWord {n : ℕ} (word : List (SignedDart (Fin (n + 1)))) :
    List (SignedDart (Fin n)) :=
  word.filterMap contractDart

@[simp]
theorem expandWord_nil {n : ℕ} (a : Fin n) :
    expandWord a [] = [] :=
  rfl

@[simp]
theorem expandWord_cons {n : ℕ} (a : Fin n) (d : SignedDart (Fin n))
    (word : List (SignedDart (Fin n))) :
    expandWord a (d :: word) = expandDart a d ++ expandWord a word :=
  rfl

theorem expandWord_singleton {n : ℕ} (a : Fin n) (d : SignedDart (Fin n)) :
    expandWord a [d] = expandDart a d := by
  simp [expandWord]

@[simp]
theorem expandWord_append {n : ℕ} (a : Fin n)
    (left right : List (SignedDart (Fin n))) :
    expandWord a (left ++ right) = expandWord a left ++ expandWord a right := by
  simp [expandWord]

@[simp]
theorem contractWord_nil {n : ℕ} :
    contractWord ([] : List (SignedDart (Fin (n + 1)))) = [] :=
  rfl

@[simp]
theorem contractWord_append {n : ℕ}
    (left right : List (SignedDart (Fin (n + 1)))) :
    contractWord (left ++ right) = contractWord left ++ contractWord right := by
  simp [contractWord]

/-- Contracting one substituted occurrence returns that occurrence. -/
@[simp]
theorem contractWord_expandDart {n : ℕ} (a : Fin n)
    (d : SignedDart (Fin n)) :
    contractWord (expandDart a d) = [d] := by
  cases d with
  | pos e =>
      by_cases h : e = a
      · subst e
        simp [contractWord, contractDart, firstSubedge, freshEdge]
      · simp [contractWord, contractDart, expandDart, h]
  | neg e =>
      by_cases h : e = a
      · subst e
        simp [contractWord, contractDart, firstSubedge, freshEdge]
      · simp [contractWord, contractDart, expandDart, h]

/-- Contracting the global P1 substitution returns the original word exactly. -/
@[simp]
theorem contractWord_expandWord {n : ℕ} (a : Fin n)
    (word : List (SignedDart (Fin n))) :
    contractWord (expandWord a word) = word := by
  induction word with
  | nil => rfl
  | cons d word ih =>
      rw [expandWord_cons, contractWord_append, contractWord_expandDart, ih]
      rfl

@[simp]
theorem expandWord_eq_nil_iff {n : ℕ} (a : Fin n)
    (word : List (SignedDart (Fin n))) :
    expandWord a word = [] ↔ word = [] := by
  constructor
  · intro h
    have hcontract := congrArg contractWord h
    simpa only [contractWord_expandWord, contractWord_nil] using hcontract
  · rintro rfl
    rfl

/-- P1 commutes with reversal of an oriented cyclic boundary word. -/
@[simp]
theorem expandWord_inverseWord {n : ℕ} (a : Fin n)
    (word : List (SignedDart (Fin n))) :
    expandWord a (inverseWord word) = inverseWord (expandWord a word) := by
  induction word with
  | nil => rfl
  | cons d word ih =>
      calc
        expandWord a (inverseWord (d :: word)) =
            expandWord a (inverseWord word ++ [d.flip]) := by
              simp [inverseWord]
        _ = expandWord a (inverseWord word) ++ expandWord a [d.flip] :=
          expandWord_append a _ _
        _ = inverseWord (expandWord a word) ++ inverseWord (expandDart a d) := by
          rw [ih, expandWord_singleton, expandDart_flip]
        _ = inverseWord (expandDart a d ++ expandWord a word) :=
          (inverseWord_append _ _).symm
        _ = inverseWord (expandWord a (d :: word)) :=
          rfl

/-- A list-valued substitution preserves cyclic rotation. -/
theorem expandWord_isRotated {n : ℕ} {a : Fin n}
    {left right : List (SignedDart (Fin n))}
    (h : left.IsRotated right) :
    (expandWord a left).IsRotated (expandWord a right) := by
  rcases h with ⟨k, rfl⟩
  let m := k % left.length
  have hleft : left = left.take m ++ left.drop m :=
    (List.take_append_drop m left).symm
  have hrotate : left.rotate k = left.drop m ++ left.take m := by
    simpa only [m] using
      (List.rotate_eq_drop_append_take_mod (l := left) (n := k))
  calc
    expandWord a left ~r expandWord a (left.drop m ++ left.take m) := by
      have hexpand :=
        congrArg (expandWord a) hleft
      rw [hexpand]
      simp only [expandWord_append]
      exact List.isRotated_append
    _ = expandWord a (left.rotate k) := congrArg (expandWord a) hrotate.symm

/-- Contraction preserves cyclic rotation even when the cut passes through a subdivided pair. -/
theorem contractWord_isRotated {n : ℕ}
    {left right : List (SignedDart (Fin (n + 1)))}
    (h : left.IsRotated right) :
    (contractWord left).IsRotated (contractWord right) := by
  rcases h with ⟨k, rfl⟩
  let m := k % left.length
  have hleft : left = left.take m ++ left.drop m :=
    (List.take_append_drop m left).symm
  have hrotate : left.rotate k = left.drop m ++ left.take m := by
    simpa only [m] using
      (List.rotate_eq_drop_append_take_mod (l := left) (n := k))
  calc
    contractWord left ~r contractWord (left.drop m ++ left.take m) := by
      have hcontract :=
        congrArg contractWord hleft
      rw [hcontract]
      simp only [contractWord_append]
      exact List.isRotated_append
    _ = contractWord (left.rotate k) := congrArg contractWord hrotate.symm

/-- P1 substitution preserves and reflects cyclic rotation. -/
@[simp]
theorem expandWord_isRotated_iff {n : ℕ} (a : Fin n)
    (left right : List (SignedDart (Fin n))) :
    (expandWord a left).IsRotated (expandWord a right) ↔
      left.IsRotated right := by
  constructor
  · intro h
    simpa only [contractWord_expandWord] using contractWord_isRotated h
  · exact expandWord_isRotated

/-- The occurrence of every retained edge survives the expansion. -/
theorem castSucc_edge_mem_expandWord {n : ℕ} {a e : Fin n}
    {word : List (SignedDart (Fin n))}
    (h : e ∈ word.map edgeOfDart) :
    e.castSucc ∈ (expandWord a word).map edgeOfDart := by
  rcases List.mem_map.mp h with ⟨d, hd, rfl⟩
  refine List.mem_map.mpr ⟨castSuccDart d, ?_, edgeOfDart_castSuccDart d⟩
  exact List.mem_flatMap.mpr ⟨d, hd, castSuccDart_mem_expandDart a d⟩

/-- Each retained edge has exactly its old word multiplicity after P1. -/
theorem count_expandWord_castSucc {n : ℕ} (a e : Fin n)
    (word : List (SignedDart (Fin n))) :
    (word.map edgeOfDart).count e =
      ((expandWord a word).map edgeOfDart).count e.castSucc := by
  induction word with
  | nil => simp
  | cons d word ih =>
      cases d with
      | pos b =>
          by_cases h : b = a
          · subst b
            have hlast : Fin.last n ≠ e.castSucc :=
              Ne.symm (Fin.castSucc_ne_last e)
            simp [expandDart, ih, freshEdge, firstSubedge, edgeOfDart,
              List.count_cons, beq_iff_eq, hlast]
          · simp [expandDart, h, ih, edgeOfDart, List.count_cons, beq_iff_eq]
      | neg b =>
          by_cases h : b = a
          · subst b
            have hlast : Fin.last n ≠ e.castSucc :=
              Ne.symm (Fin.castSucc_ne_last e)
            simp [expandDart, ih, freshEdge, firstSubedge, edgeOfDart,
              List.count_cons, beq_iff_eq, hlast]
          · simp [expandDart, h, ih, edgeOfDart, List.count_cons, beq_iff_eq]

/-- The fresh edge receives exactly the old multiplicity of the subdivided edge. -/
theorem count_expandWord_freshEdge {n : ℕ} (a : Fin n)
    (word : List (SignedDart (Fin n))) :
    (word.map edgeOfDart).count a =
      ((expandWord a word).map edgeOfDart).count (freshEdge n) := by
  induction word with
  | nil => simp
  | cons d word ih =>
      cases d with
      | pos b =>
          by_cases h : b = a
          · subst b
            simp [expandDart, ih, freshEdge, firstSubedge, edgeOfDart]
          · simp [expandDart, h, ih, freshEdge, edgeOfDart]
      | neg b =>
          by_cases h : b = a
          · subst b
            simp [expandDart, ih, freshEdge, firstSubedge, edgeOfDart]
          · simp [expandDart, h, ih, freshEdge, edgeOfDart]

/-- Canonical presentation-level P1 expansion. -/
abbrev expand (P : FiniteCyclicPresentation) (a : P.Edge) :
    FiniteCyclicPresentation where
  edgeCount := P.edgeCount + 1
  faces := P.faces.map (expandWord a)

@[simp]
theorem expand_edgeCount (P : FiniteCyclicPresentation) (a : P.Edge) :
    (expand P a).edgeCount = P.edgeCount + 1 :=
  rfl

theorem expand_faces_length (P : FiniteCyclicPresentation) (a : P.Edge) :
    (expand P a).faces.length = P.faces.length := by
  simp [expand]

/-- P1 preserves face positions. -/
def faceEquiv (P : FiniteCyclicPresentation) (a : P.Edge) :
    P.Face ≃ (expand P a).Face :=
  finCongr (expand_faces_length P a).symm

@[simp]
theorem faceEquiv_apply_val (P : FiniteCyclicPresentation) (a : P.Edge)
    (f : P.Face) :
    (faceEquiv P a f).val = f.val :=
  rfl

@[simp]
theorem expand_boundary (P : FiniteCyclicPresentation) (a : P.Edge)
    (f : P.Face) :
    (expand P a).boundary (faceEquiv P a f) =
      expandWord a (P.boundary f) := by
  simp [boundary, List.get_eq_getElem, expand, faceEquiv]

/-- P1 copies every retained edge's facewise multiplicity. -/
theorem faceEdgeMultiplicity_expand_castSucc
    (P : FiniteCyclicPresentation) (a e : P.Edge) (f : P.Face) :
    P.faceEdgeMultiplicity f e =
      (expand P a).faceEdgeMultiplicity (faceEquiv P a f) e.castSucc := by
  simp only [faceEdgeMultiplicity, expand_boundary]
  exact count_expandWord_castSucc a e (P.boundary f)

/-- P1 gives the fresh edge the subdivided edge's facewise multiplicity. -/
theorem faceEdgeMultiplicity_expand_freshEdge
    (P : FiniteCyclicPresentation) (a : P.Edge) (f : P.Face) :
    P.faceEdgeMultiplicity f a =
      (expand P a).faceEdgeMultiplicity (faceEquiv P a f)
        (freshEdge P.edgeCount) := by
  simp only [faceEdgeMultiplicity, expand_boundary]
  exact count_expandWord_freshEdge a (P.boundary f)

/-- P1 copies every retained edge's total multiplicity. -/
theorem edgeMultiplicity_expand_castSucc
    (P : FiniteCyclicPresentation) (a e : P.Edge) :
    P.edgeMultiplicity e = (expand P a).edgeMultiplicity e.castSucc := by
  unfold edgeMultiplicity
  exact Fintype.sum_equiv (faceEquiv P a) _ _ fun f ↦
    faceEdgeMultiplicity_expand_castSucc P a e f

/-- P1 gives the fresh edge the subdivided edge's total multiplicity. -/
theorem edgeMultiplicity_expand_freshEdge
    (P : FiniteCyclicPresentation) (a : P.Edge) :
    P.edgeMultiplicity a =
      (expand P a).edgeMultiplicity (freshEdge P.edgeCount) := by
  unfold edgeMultiplicity
  exact Fintype.sum_equiv (faceEquiv P a) _ _ fun f ↦
    faceEdgeMultiplicity_expand_freshEdge P a f

/-- P1 sends source face adjacency to target face adjacency. -/
theorem map_faceAdjacent
    (P : FiniteCyclicPresentation) (a : P.Edge) {f g : P.Face}
    (h : P.FaceAdjacent f g) :
    (expand P a).FaceAdjacent (faceEquiv P a f) (faceEquiv P a g) := by
  rcases h with ⟨e, hef, heg⟩
  refine ⟨e.castSucc, ?_, ?_⟩
  · rw [expand_boundary]
    exact castSucc_edge_mem_expandWord hef
  · rw [expand_boundary]
    exact castSucc_edge_mem_expandWord heg

/-- P1 preserves ordinary finite-presentation incidence validity. -/
theorem expand_isSurfaceValid
    (P : FiniteCyclicPresentation) (a : P.Edge) (h : P.IsSurfaceValid) :
    (expand P a).IsSurfaceValid := by
  refine ⟨(faceEquiv P a).nonempty_congr.mp h.1, ?_, ?_, ?_⟩
  · intro q hq
    let f := (faceEquiv P a).symm q
    have hboundary :
        (expand P a).boundary (faceEquiv P a f) =
          expandWord a (P.boundary f) :=
      expand_boundary P a f
    rw [(faceEquiv P a).apply_symm_apply] at hboundary
    have hexpanded : expandWord a (P.boundary f) = [] := by
      rw [← hboundary]
      exact hq
    exact h.2.1 f ((expandWord_eq_nil_iff a (P.boundary f)).mp hexpanded)
  · intro q r hqr
    let f := (faceEquiv P a).symm q
    let g := (faceEquiv P a).symm r
    have htargetBoundary :
        ((expand P a).boundary (faceEquiv P a f)).IsRotated
          ((expand P a).boundary (faceEquiv P a g)) := by
      have hq : faceEquiv P a f = q :=
        (faceEquiv P a).apply_symm_apply q
      have hr : faceEquiv P a g = r :=
        (faceEquiv P a).apply_symm_apply r
      rw [hq, hr]
      exact hqr
    rw [expand_boundary, expand_boundary] at htargetBoundary
    have htarget :
        (expandWord a (P.boundary f)).IsRotated
          (expandWord a (P.boundary g)) :=
      htargetBoundary
    have hsource :=
      (expandWord_isRotated_iff a (P.boundary f) (P.boundary g)).mp htarget
    have hfg := h.2.2.1 f g hsource
    calc
      q = faceEquiv P a f := ((faceEquiv P a).apply_symm_apply q).symm
      _ = faceEquiv P a g := congrArg (faceEquiv P a) hfg
      _ = r := (faceEquiv P a).apply_symm_apply r
  · intro e
    change Fin (P.edgeCount + 1) at e
    refine Fin.lastCases ?_ (fun b ↦ ?_) e
    · have hmultiplicity := h.2.2.2 a
      rw [edgeMultiplicity_expand_freshEdge P a] at hmultiplicity
      simpa only [freshEdge] using hmultiplicity
    · have hmultiplicity := h.2.2.2 b
      rw [edgeMultiplicity_expand_castSucc P a b] at hmultiplicity
      exact hmultiplicity

/-- P1 preserves connectedness of the face-edge incidence graph. -/
theorem expand_isConnected
    (P : FiniteCyclicPresentation) (a : P.Edge) (h : P.IsConnected) :
    (expand P a).IsConnected := by
  refine ⟨(faceEquiv P a).nonempty_congr.mp h.1, ?_⟩
  intro q r
  have hchain := h.2 ((faceEquiv P a).symm q) ((faceEquiv P a).symm r)
  have hmapped := hchain.lift (faceEquiv P a) fun _ _ hadj ↦
    map_faceAdjacent P a hadj
  change Relation.ReflTransGen (expand P a).FaceAdjacent
    (faceEquiv P a ((faceEquiv P a).symm q))
    (faceEquiv P a ((faceEquiv P a).symm r)) at hmapped
  simpa only [(faceEquiv P a).apply_symm_apply] using hmapped

/-- P1 preserves the regular and exceptional branches of Gallier validity.

The exceptional branch is impossible here because selecting `a` already supplies an edge. -/
theorem expand_isGallierValid
    (P : FiniteCyclicPresentation) (a : P.Edge) (h : P.IsGallierValid) :
    (expand P a).IsGallierValid := by
  rcases h with hregular | hempty
  · exact Or.inl
      ⟨expand_isSurfaceValid P a hregular.1,
        expand_isConnected P a hregular.2⟩
  · exact Fin.elim0 (Fin.cast hempty.edgeCount_eq_zero a)

end P1

/-- A Gallier--Xu P1 subdivision, closed under signed relabeling and cyclic face rotation.

This is a syntactic move relation and deliberately does not bundle source validity. The
preservation theorems below transport validity and connectivity when those hypotheses are
available. -/
def P1Subdivision (P Q : FiniteCyclicPresentation) : Prop :=
  ∃ a : P.Edge, Nonempty (SignedPresentationIso (P1.expand P a) Q)

namespace P1Subdivision

/-- The canonical expansion is a P1 subdivision. -/
theorem canonical (P : FiniteCyclicPresentation) (a : P.Edge) :
    P1Subdivision P (P1.expand P a) :=
  ⟨a, ⟨SignedPresentationIso.refl _⟩⟩

/-- P1 subdivisions preserve ordinary incidence validity. -/
theorem isSurfaceValid {P Q : FiniteCyclicPresentation}
    (hPQ : P1Subdivision P Q) (h : P.IsSurfaceValid) :
    Q.IsSurfaceValid := by
  rcases hPQ with ⟨a, ⟨e⟩⟩
  exact e.isSurfaceValid (P1.expand_isSurfaceValid P a h)

/-- P1 subdivisions preserve face-incidence connectivity. -/
theorem isConnected {P Q : FiniteCyclicPresentation}
    (hPQ : P1Subdivision P Q) (h : P.IsConnected) :
    Q.IsConnected := by
  rcases hPQ with ⟨a, ⟨e⟩⟩
  exact e.isConnected (P1.expand_isConnected P a h)

/-- P1 subdivisions preserve Gallier validity. -/
theorem isGallierValid {P Q : FiniteCyclicPresentation}
    (hPQ : P1Subdivision P Q) (h : P.IsGallierValid) :
    Q.IsGallierValid := by
  rcases hPQ with ⟨a, ⟨e⟩⟩
  exact e.isGallierValid (P1.expand_isGallierValid P a h)

end P1Subdivision

end FiniteCyclicPresentation
end ClassificationOfSurfaces
end Topology
end LeanEval
