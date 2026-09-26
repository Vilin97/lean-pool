/-
Copyright (c) 2026 Arthur F. Ramos, David Barros Hulak, Ruy J.G.B. de Queiroz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/
module

public import LeanPool.MarshallHall.MarshallHall.GrushkoFold
public import Mathlib.Combinatorics.Quiver.Cast
public import Mathlib.Combinatorics.Quiver.Symmetric


/-!
## Labelled paths for the Grushko fold argument

The fold proof is carried by a finite graph whose oriented edges are labelled
by elements of the two factors.  This file isolates the path-level semantics:
composition reads as multiplication, reversal reads as inversion, and every
path has an explicit list of factor labels.  The graph-fold construction can
therefore use these operations without introducing a second, informal notion
of path evaluation.
-/

@[expose] public section



open Function Monoid.Coprod Quiver

noncomputable section

namespace MarshallHall
namespace GeneralGrushko

universe u v

variable {G H : Type u} {V : Type v} [Group G] [Group H] [Quiver V]
  [HasInvolutiveReverse V]

omit [Quiver.HasInvolutiveReverse V] in
theorem path_length_cast {a b a' b' : V} (ha : a = a') (hb : b = b')
    (p : Path a b) : (p.cast ha hb).length = p.length := by
  subst_vars
  rfl

/-- An oriented-edge labelling by the two factors, compatible with reversal. -/
structure BinaryLabelling where
  /-- Assigns each oriented edge a label from one of the two group factors. -/
  label : ∀ {a b : V}, (a ⟶ b) → Sum G H
  reverse_label : ∀ {a b : V} (e : a ⟶ b),
    label (Quiver.reverse e) = factorWordInv (G := G) (H := H) (label e)

namespace BinaryLabelling

variable (L : BinaryLabelling (G := G) (H := H) (V := V))

/-- The factor-label list read along a directed path. -/
def pathLabels {a : V} : ∀ {b : V}, Path a b → List (Sum G H)
  | _, Path.nil => []
  | _, Path.cons p e => pathLabels p ++ [L.label e]

/-- The element of the free product read along a directed path. -/
def pathRead {a : V} {b : V} (p : Path a b) : G ∗ H :=
  factorWordProd (G := G) (H := H) (pathLabels L p)

/-- A path is monochromatic when all of its edge labels come from one factor. -/
def IsMonochromatic {a b : V} (p : Path a b) (color : Bool) : Prop :=
  ∀ z ∈ L.pathLabels p,
    binarySumIndex (G := G) (H := H) z = color

@[simp]
theorem pathLabels_nil {a : V} :
    L.pathLabels (Path.nil : Path a a) = [] :=
  rfl

@[simp]
theorem pathLabels_toPath {a b : V} (e : a ⟶ b) :
    L.pathLabels e.toPath = [L.label e] := by
  rfl

theorem pathLabels_eq_of_endpoint_eq {a b c : V} (h : b = c)
    (p : Path a b) :
    L.pathLabels (h ▸ p) = L.pathLabels p := by
  cases h
  rfl

theorem pathLabels_cast {a b a' b' : V} (ha : a = a') (hb : b = b')
    (p : Path a b) :
    L.pathLabels (p.cast ha hb) = L.pathLabels p := by
  subst_vars
  rfl

theorem pathRead_cast {a b a' b' : V} (ha : a = a') (hb : b = b')
    (p : Path a b) :
    L.pathRead (p.cast ha hb) = L.pathRead p := by
  simp only [pathRead, pathLabels_cast]

@[simp]
theorem pathRead_nil {a : V} :
    L.pathRead (Path.nil : Path a a) = 1 := by
  simp [pathRead, pathLabels, factorWordProd]

@[simp]
theorem pathRead_toPath {a b : V} (e : a ⟶ b) :
    L.pathRead e.toPath = separatedMap (L.label e) := by
  simp [pathRead, factorWordProd, separatedMap]

theorem pathLabels_comp {a b : V} (p : Path a b) :
    ∀ {c : V} (q : Path b c), L.pathLabels (p.comp q) =
      L.pathLabels p ++ L.pathLabels q
  | _, Path.nil => by simp
  | _, Path.cons q e => by
      simp only [Path.comp_cons, pathLabels]
      rw [pathLabels_comp p q, List.append_assoc]

theorem pathRead_comp {a b : V} (p : Path a b) :
    ∀ {c : V} (q : Path b c), L.pathRead (p.comp q) =
      L.pathRead p * L.pathRead q
  | _, q => by
      simp only [pathRead, pathLabels_comp, factorWordProd_append]

/-! ### Reading paths in the symmetrized graph -/

/-- Extends edge labels to symmetrized arrows by inverting the label on a formal reverse. -/
def symmLabel {a b : Symmetrify V}
    (e : @Quiver.Hom (Symmetrify V) (@Quiver.symmetrifyQuiver V _) a b) :
    Sum G H :=
  match e with
  | Sum.inl f => L.label f
  | Sum.inr f => factorWordInv (L.label f)

/-- The ordered list of factor labels along a symmetrized path. -/
def symmPathLabels {a : Symmetrify V} :
    ∀ {b : Symmetrify V},
      @Quiver.Path (Symmetrify V) (@Quiver.symmetrifyQuiver V _) a b →
        List (Sum G H)
  | _, Path.nil => []
  | _, Path.cons p e => symmPathLabels p ++ [L.symmLabel e]

/-- The free-product element read along a symmetrized path. -/
def symmPathRead {a b : Symmetrify V}
    (p : @Quiver.Path (Symmetrify V) (@Quiver.symmetrifyQuiver V _) a b) :
  G ∗ H :=
  factorWordProd (G := G) (H := H) (L.symmPathLabels p)

theorem symmPathLabels_cast {a b a' b' : Symmetrify V}
    (ha : a = a') (hb : b = b')
    (p : @Quiver.Path (Symmetrify V) (@Quiver.symmetrifyQuiver V _) a b) :
    L.symmPathLabels (p.cast ha hb) = L.symmPathLabels p := by
  subst_vars
  rfl

theorem symmPathRead_cast {a b a' b' : Symmetrify V}
    (ha : a = a') (hb : b = b')
    (p : @Quiver.Path (Symmetrify V) (@Quiver.symmetrifyQuiver V _) a b) :
    L.symmPathRead (p.cast ha hb) = L.symmPathRead p := by
  simp only [symmPathRead, symmPathLabels_cast]

@[simp]
theorem symmPathLabels_nil {a : Symmetrify V} :
    L.symmPathLabels
      (@Quiver.Path.nil (Symmetrify V) (@Quiver.symmetrifyQuiver V _) a) = [] :=
  rfl

@[simp]
theorem symmPathLabels_toPath {a b : Symmetrify V}
  (e : @Quiver.Hom (Symmetrify V) (@Quiver.symmetrifyQuiver V _) a b) :
    L.symmPathLabels e.toPath = [L.symmLabel e] := by
  rfl

@[simp]
theorem symmPathRead_nil {a : Symmetrify V} :
    L.symmPathRead
      (@Quiver.Path.nil (Symmetrify V) (@Quiver.symmetrifyQuiver V _) a) = 1 := by
  simp [symmPathRead, symmPathLabels, factorWordProd]

@[simp]
theorem symmPathRead_toPath {a b : Symmetrify V}
    (e : @Quiver.Hom (Symmetrify V) (@Quiver.symmetrifyQuiver V _) a b) :
    L.symmPathRead e.toPath = separatedMap (L.symmLabel e) := by
  change factorWordProd [L.symmLabel e] = separatedMap (L.symmLabel e)
  simp [factorWordProd]

theorem symmPathLabels_comp {a b : Symmetrify V}
    (p : @Quiver.Path (Symmetrify V) (@Quiver.symmetrifyQuiver V _) a b) :
    ∀ {c : Symmetrify V}
      (q : @Quiver.Path (Symmetrify V) (@Quiver.symmetrifyQuiver V _) b c),
      L.symmPathLabels (p.comp q) =
        L.symmPathLabels p ++ L.symmPathLabels q
  | _, Path.nil => by
      change L.symmPathLabels p = L.symmPathLabels p ++ []
      simp
  | _, Path.cons q e => by
      simp only [Path.comp_cons, symmPathLabels]
      rw [symmPathLabels_comp p q, List.append_assoc]

theorem symmPathRead_comp {a b : Symmetrify V}
    (p : @Quiver.Path (Symmetrify V) (@Quiver.symmetrifyQuiver V _) a b) :
    ∀ {c : Symmetrify V}
      (q : @Quiver.Path (Symmetrify V) (@Quiver.symmetrifyQuiver V _) b c),
      L.symmPathRead (p.comp q) = L.symmPathRead p * L.symmPathRead q
  | _, q => by
      simp only [symmPathRead, symmPathLabels_comp, factorWordProd_append]

theorem symmLabel_reverse {a b : Symmetrify V}
    (e : @Quiver.Hom (Symmetrify V) (@Quiver.symmetrifyQuiver V _) a b) :
    L.symmLabel (Quiver.reverse e) = factorWordInv (L.symmLabel e) := by
  cases e with
  | inl f =>
      rfl
  | inr f =>
      simp [symmLabel]

theorem symmPathRead_reverse {a b : Symmetrify V}
    (p : @Quiver.Path (Symmetrify V) (@Quiver.symmetrifyQuiver V _) a b) :
    L.symmPathRead p.reverse = (L.symmPathRead p)⁻¹ := by
  induction p with
  | nil => simp
  | cons p e ih =>
      change L.symmPathRead ((Quiver.reverse e).toPath.comp p.reverse) =
        (L.symmPathRead (p.comp e.toPath))⁻¹
      rw [symmPathRead_comp, symmPathRead_toPath, symmLabel_reverse, ih,
        symmPathRead_comp, symmPathRead_toPath]
      simp [separatedMap_factorWordInv, mul_inv_rev]

theorem symmPathRead_map_of {a b : V}
    (p : @Quiver.Path V _ a b) :
    L.symmPathRead
        ((@Quiver.Symmetrify.of V _).mapPath p) = L.pathRead p := by
  induction p with
  | nil => rfl
  | cons p e ih =>
      change L.symmPathRead
          (((@Quiver.Symmetrify.of V _).mapPath p).comp
            ((@Quiver.Symmetrify.of V _).map e).toPath) =
        L.pathRead (p.comp e.toPath)
      rw [symmPathRead_comp, ih, symmPathRead_toPath, L.pathRead_comp,
        L.pathRead_toPath]
      simp [symmLabel]
      rfl

/-- Every label along the symmetrized path belongs to the specified factor. -/
def symmIsMonochromatic {a b : Symmetrify V}
    (p : @Quiver.Path (Symmetrify V) (@Quiver.symmetrifyQuiver V _) a b)
    (color : Bool) : Prop :=
  ∀ z ∈ L.symmPathLabels p,
    binarySumIndex (G := G) (H := H) z = color

@[simp]
theorem symmIsMonochromatic_nil {a : Symmetrify V} (color : Bool) :
    L.symmIsMonochromatic
      (@Quiver.Path.nil (Symmetrify V) (@Quiver.symmetrifyQuiver V _) a) color := by
  simp [symmIsMonochromatic]

theorem symmIsMonochromatic_toPath {a b : Symmetrify V}
    (e : @Quiver.Hom (Symmetrify V) (@Quiver.symmetrifyQuiver V _) a b) :
    L.symmIsMonochromatic e.toPath
      (binarySumIndex (G := G) (H := H) (L.symmLabel e)) := by
  intro z hz
  have hz' : z = L.symmLabel e := by
    simpa only [symmPathLabels_toPath, List.mem_singleton] using hz
  exact congrArg (binarySumIndex (G := G) (H := H)) hz'

theorem symmIsMonochromatic_comp {a b c : Symmetrify V}
    (p : @Quiver.Path (Symmetrify V) (@Quiver.symmetrifyQuiver V _) a b)
    (q : @Quiver.Path (Symmetrify V) (@Quiver.symmetrifyQuiver V _) b c)
    {color : Bool} (hp : L.symmIsMonochromatic p color)
    (hq : L.symmIsMonochromatic q color) :
    L.symmIsMonochromatic (p.comp q) color := by
  intro z hz
  rw [symmPathLabels_comp] at hz
  rcases List.mem_append.mp hz with hz | hz
  · exact hp z hz
  · exact hq z hz

theorem symmPathRead_mono_false {a b : Symmetrify V}
    {p : @Quiver.Path (Symmetrify V) (@Quiver.symmetrifyQuiver V _) a b}
    (hp : L.symmIsMonochromatic p false) :
    ∃ g : G, L.symmPathRead p = Monoid.Coprod.inl g := by
  obtain ⟨l, hl⟩ := exists_map_inl_of_idx_false (G := G) (H := H) (by
    simpa [symmIsMonochromatic] using hp)
  refine ⟨l.prod, ?_⟩
  rw [symmPathRead, hl, factorWordProd_map_inl]

theorem symmPathRead_mono_true {a b : Symmetrify V}
    {p : @Quiver.Path (Symmetrify V) (@Quiver.symmetrifyQuiver V _) a b}
    (hp : L.symmIsMonochromatic p true) :
    ∃ h : H, L.symmPathRead p = Monoid.Coprod.inr h := by
  obtain ⟨l, hl⟩ := exists_map_inr_of_idx_true (G := G) (H := H) (by
    simpa [symmIsMonochromatic] using hp)
  refine ⟨l.prod, ?_⟩
  rw [symmPathRead, hl, factorWordProd_map_inr]

/-- A nonempty monochromatic piece of a symmetrized path, with its endpoints and factor recorded. -/
structure SymmRunPiece where
  /-- The starting vertex of the monochromatic path piece. -/
  source : Symmetrify V
  /-- The ending vertex of the monochromatic path piece. -/
  target : Symmetrify V
  /-- The nonempty path underlying the monochromatic piece. -/
  path : @Quiver.Path (Symmetrify V) (@Quiver.symmetrifyQuiver V _) source target
  /-- The factor containing every label of the path piece. -/
  color : Bool
  monochromatic : L.symmIsMonochromatic path color
  nonempty : path.length ≠ 0

namespace SymmRunPiece

/-- The monochromatic path piece consisting of one symmetrized arrow. -/
@[reducible]
def single {a b : Symmetrify V}
    (e : @Quiver.Hom (Symmetrify V) (@Quiver.symmetrifyQuiver V _) a b) :
    SymmRunPiece L :=
  { source := a
    target := b
    path := e.toPath
    color := binarySumIndex (G := G) (H := H) (L.symmLabel e)
    monochromatic := L.symmIsMonochromatic_toPath e
    nonempty := by simp }

/-- Appends an arrow of the same factor to a monochromatic path piece. -/
@[reducible]
def extend {c : Symmetrify V} (r : SymmRunPiece L)
    (e : @Quiver.Hom (Symmetrify V) (@Quiver.symmetrifyQuiver V _)
      r.target c)
    (hcolor : binarySumIndex (G := G) (H := H) (L.symmLabel e) = r.color) :
    SymmRunPiece L :=
  { source := r.source
    target := c
    path := r.path.comp e.toPath
    color := r.color
    monochromatic := by
      apply L.symmIsMonochromatic_comp r.path e.toPath
        r.monochromatic
      intro z hz
      have hz' : z = L.symmLabel e := by
        simpa only [symmPathLabels_toPath, List.mem_singleton] using hz
      rw [hz', hcolor]
    nonempty := by
      rw [Quiver.Path.length_comp]
      simp }

end SymmRunPiece

/-- The factor-tagged free-product value of a monochromatic path piece. -/
def symmRunTag (r : SymmRunPiece L) : Sum G H :=
  match r.color with
  | false => Sum.inl (Monoid.Coprod.fst (L.symmPathRead r.path))
  | true => Sum.inr (Monoid.Coprod.snd (L.symmPathRead r.path))

theorem separatedMap_symmRunTag (r : SymmRunPiece L) :
    separatedMap (L.symmRunTag r) = L.symmPathRead r.path := by
  cases hc : r.color with
  | false =>
      have hmono : L.symmIsMonochromatic r.path false := by
        simpa [hc] using r.monochromatic
      obtain ⟨g, hg⟩ := L.symmPathRead_mono_false hmono
      simp only [symmRunTag, hc, hg, separatedMap]
      rfl
  | true =>
      have hmono : L.symmIsMonochromatic r.path true := by
        simpa [hc] using r.monochromatic
      obtain ⟨h, hh⟩ := L.symmPathRead_mono_true hmono
      simp only [symmRunTag, hc, hh, separatedMap]
      rfl

/-- A composable chain of nonempty monochromatic path pieces. -/
inductive SymmRunChain (L : BinaryLabelling (G := G) (H := H) (V := V)) :
    Symmetrify V → Symmetrify V → Type (max v 1)
  | nil (a : Symmetrify V) : SymmRunChain L a a
  | cons {a : Symmetrify V} (r : SymmRunPiece L)
      (rest : SymmRunChain L a r.source) : SymmRunChain L a r.target

/-- Concatenates the monochromatic pieces into their underlying path. -/
def SymmRunChain.path : ∀ {a b : Symmetrify V},
    SymmRunChain L a b →
      @Quiver.Path (Symmetrify V) (@Quiver.symmetrifyQuiver V _) a b
  | _, _, .nil _ => Path.nil
  | _, _, .cons r rest => (SymmRunChain.path rest).comp r.path

/-- The factors of the chain's pieces, listed from the final piece backwards. -/
def SymmRunChain.colors : ∀ {a b : Symmetrify V},
    SymmRunChain L a b → List Bool
  | _, _, .nil _ => []
  | _, _, .cons r rest => r.color :: SymmRunChain.colors rest

/-- The monochromatic pieces of the chain in path order. -/
def SymmRunChain.pieces : ∀ {a b : Symmetrify V},
    SymmRunChain L a b → List (SymmRunPiece L)
  | _, _, .nil _ => []
  | _, _, .cons r rest => SymmRunChain.pieces rest ++ [r]

/-- The factors of the chain's pieces in path order. -/
def SymmRunChain.pieceColors : ∀ {a b : Symmetrify V},
    SymmRunChain L a b → List Bool
  | _, _, .nil _ => []
  | _, _, .cons r rest =>
      SymmRunChain.pieceColors rest ++ [r.color]

theorem SymmRunChain.pieceColors_eq_colors_reverse
    {a b : Symmetrify V} (c : SymmRunChain L a b) :
    (c.pieces.map (fun r => r.color)) = c.colors.reverse := by
  induction c with
  | nil => simp [SymmRunChain.pieces, SymmRunChain.colors]
  | cons r rest ih =>
      simp [SymmRunChain.pieces, SymmRunChain.colors, ih]

theorem SymmRunChain.pieceColors_eq_defined
    {a b : Symmetrify V} (c : SymmRunChain L a b) :
    c.pieceColors = c.pieces.map (fun r => r.color) := by
  induction c with
  | nil => simp [SymmRunChain.pieceColors, SymmRunChain.pieces]
  | cons r rest ih =>
      simp [SymmRunChain.pieceColors, SymmRunChain.pieces, ih]

theorem SymmRunChain.pieceColors_isChain
    {a b : Symmetrify V} (c : SymmRunChain L a b)
      (h : c.colors.IsChain (fun x y : Bool => x ≠ y)) :
    (c.pieces.map (fun r => r.color)).IsChain
      (fun x y : Bool => x ≠ y) := by
  rw [SymmRunChain.pieceColors_eq_colors_reverse L c]
  apply List.isChain_reverse.mpr
  simpa [eq_comm] using h

theorem symmRunTag_index (r : SymmRunPiece L) :
    binarySumIndex (G := G) (H := H) (L.symmRunTag r) = r.color := by
  cases hc : r.color <;> simp [symmRunTag, hc]

theorem SymmRunChain.tags_isChain
    {a b : Symmetrify V} (c : SymmRunChain L a b)
    (h : c.colors.IsChain (fun x y : Bool => x ≠ y)) :
    (c.pieces.map L.symmRunTag).IsChain
      (fun x y => binarySumIndex (G := G) (H := H) x ≠
        binarySumIndex (G := G) (H := H) y) := by
  rw [List.isChain_map]
  have hp := SymmRunChain.pieceColors_isChain L c h
  rw [List.isChain_map] at hp
  apply hp.imp
  intro r s hrs
  simpa only [symmRunTag_index] using hrs

theorem SymmRunChain.pathRead_eq_factorWordProd_tags
    {a b : Symmetrify V} (c : SymmRunChain L a b) :
    L.symmPathRead (c.path) =
      factorWordProd (G := G) (H := H)
        (c.pieces.map L.symmRunTag) := by
  induction c with
  | nil => simp [SymmRunChain.path, SymmRunChain.pieces, factorWordProd]
  | cons r rest ih =>
      simp [SymmRunChain.path, SymmRunChain.pieces,
        L.symmPathRead_comp, factorWordProd_append,
        factorWordProd, separatedMap_symmRunTag, ih]

theorem SymmRunChain.pieces_ne_nil_of_path_ne_nil
    {a b : Symmetrify V} (c : SymmRunChain L a b)
    (hpath : c.path.length ≠ 0) :
    c.pieces ≠ [] := by
  cases c with
  | nil => simp [SymmRunChain.path] at hpath
  | cons r rest => simp [SymmRunChain.pieces]

theorem SymmRunChain.exists_path_split_at_run
    {a b : Symmetrify V} (c : SymmRunChain L a b)
    {r : SymmRunPiece L} (hr : r ∈ c.pieces) :
    ∃ p : @Quiver.Path (Symmetrify V) (@Quiver.symmetrifyQuiver V _) a r.source,
      ∃ q : @Quiver.Path (Symmetrify V) (@Quiver.symmetrifyQuiver V _)
        r.target b,
        c.path = p.comp (r.path.comp q) := by
  induction c with
  | nil => simp [SymmRunChain.pieces] at hr
  | cons r₀ rest ih =>
      have hr' : r ∈ rest.pieces ∨ r = r₀ := by
        simpa [SymmRunChain.pieces] using hr
      rcases hr' with hr' | rfl
      · obtain ⟨p, q, hsplit⟩ := ih hr'
        refine ⟨p, q.comp r₀.path, ?_⟩
        simp [SymmRunChain.path, hsplit, Path.comp_assoc]
      · refine ⟨SymmRunChain.path L rest, Path.nil, ?_⟩
        simp [SymmRunChain.path]

theorem exists_shorter_null_path_of_null_loop_run
    {a b : Symmetrify V} (c : SymmRunChain L a b)
    {r : SymmRunPiece L} (hr : r ∈ c.pieces)
    (hloop : r.source = r.target)
    (hread_r : L.symmPathRead r.path = 1)
    (hread_c : L.symmPathRead c.path = 1) :
    ∃ p : @Quiver.Path (Symmetrify V) (@Quiver.symmetrifyQuiver V _) a b,
      L.symmPathRead p = 1 ∧ p.length < c.path.length := by
  obtain ⟨p, q, hsplit⟩ :=
    SymmRunChain.exists_path_split_at_run L c hr
  let q' := q.cast hloop.symm rfl
  refine ⟨p.comp q', ?_, ?_⟩
  · calc
      L.symmPathRead (p.comp q') =
          L.symmPathRead p * L.symmPathRead q' :=
        L.symmPathRead_comp p q'
      _ = L.symmPathRead p * L.symmPathRead q := by
        rw [show L.symmPathRead q' = L.symmPathRead q by
          simpa [q'] using L.symmPathRead_cast hloop.symm rfl q]
      _ = L.symmPathRead p *
          (L.symmPathRead r.path * L.symmPathRead q) := by
        rw [hread_r]
        simp
      _ = L.symmPathRead c.path := by
        rw [hsplit, L.symmPathRead_comp, L.symmPathRead_comp]
      _ = 1 := hread_c
  · have hpos : 0 < r.path.length := Nat.pos_of_ne_zero r.nonempty
    have hqlength : q'.length = q.length := by
      simpa [q'] using path_length_cast hloop.symm rfl q
    rw [Quiver.Path.length_comp, hqlength, hsplit,
      Quiver.Path.length_comp, Quiver.Path.length_comp]
    omega

theorem exists_null_piece_of_null_chain
    {a b : Symmetrify V} (c : SymmRunChain L a b)
    (hcolors : c.colors.IsChain (fun x y : Bool => x ≠ y))
    (hpieces : c.pieces ≠ [])
    (hread : L.symmPathRead c.path = 1) :
    ∃ r ∈ c.pieces, L.symmPathRead r.path = 1 := by
  by_contra h
  have hpiece_ne : ∀ r ∈ c.pieces, L.symmPathRead r.path ≠ 1 := by
    intro r hr hzero
    exact h ⟨r, hr, hzero⟩
  have htag_ne : ∀ z ∈ c.pieces.map L.symmRunTag,
      z ≠ Sum.inl 1 ∧ z ≠ Sum.inr 1 := by
    intro z hz
    obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hz
    constructor
    · intro htag
      apply hpiece_ne r hr
      rw [← separatedMap_symmRunTag, htag]
      simp [separatedMap]
    · intro htag
      apply hpiece_ne r hr
      rw [← separatedMap_symmRunTag, htag]
      simp [separatedMap]
  have htags : c.pieces.map L.symmRunTag ≠ [] := by
    simpa using hpieces
  have hprod_ne :
    factorWordProd (G := G) (H := H)
        (c.pieces.map L.symmRunTag) ≠ 1 :=
    factorWordProd_ne_one_of_reduced htag_ne
      (SymmRunChain.tags_isChain L c hcolors) htags
  apply hprod_ne
  rw [← SymmRunChain.pathRead_eq_factorWordProd_tags L c]
  exact hread

/-- A decomposition of a path into monochromatic pieces with alternating factors. -/
structure SymmRunDecomposition {a b : Symmetrify V}
    (p : @Quiver.Path (Symmetrify V) (@Quiver.symmetrifyQuiver V _) a b) where
  /-- The chain of monochromatic pieces composing the given path. -/
  chain : SymmRunChain L a b
  path_eq : chain.path = p
  alternating : (chain.colors).IsChain (fun x y => x ≠ y)

/-- Splits a symmetrized path into maximal monochromatic pieces. -/
def symmRunDecomposition {a b : Symmetrify V} :
    (p : @Quiver.Path (Symmetrify V) (@Quiver.symmetrifyQuiver V _) a b) →
      SymmRunDecomposition (L := L) p
  | Path.nil =>
      { chain := SymmRunChain.nil a
        path_eq := by simp [SymmRunChain.path]
        alternating := by simp [SymmRunChain.colors] }
  | Path.cons p e => by
      let d : SymmRunDecomposition (L := L) p := symmRunDecomposition p
      obtain ⟨chain, hpath, halt⟩ := d
      cases chain with
      | nil =>
          let r := SymmRunPiece.single (L := L) e
          have hp : p = Path.nil := by
            simpa [SymmRunChain.path] using hpath.symm
          subst p
          exact
            { chain := SymmRunChain.cons r (SymmRunChain.nil a)
              path_eq := by
                simp [SymmRunChain.path, r, SymmRunPiece.single]
              alternating := by
                simpa only [SymmRunChain.colors] using
                  (List.isChain_singleton (R := fun x y : Bool => x ≠ y)
                    r.color) }
      | cons r rest =>
          by_cases hcolor :
              binarySumIndex (G := G) (H := H) (L.symmLabel e) = r.color
          · let r' := SymmRunPiece.extend L r e hcolor
            exact
              { chain := SymmRunChain.cons r' rest
                path_eq := by
                  simpa [SymmRunChain.path, r', SymmRunPiece.extend] using
                    congrArg (fun q => q.cons e) hpath
                alternating := by
                  simpa [SymmRunChain.colors, r', SymmRunPiece.extend]
                    using halt }
          · let s := SymmRunPiece.single L e
            exact
              { chain := SymmRunChain.cons s (SymmRunChain.cons r rest)
                path_eq := by
                  simpa [SymmRunChain.path, s, SymmRunPiece.single] using
                    congrArg (fun q => q.cons e) hpath
                alternating := by
                  simp only [SymmRunChain.colors]
                  exact List.isChain_cons_cons.mpr
                    ⟨hcolor, by simpa only [SymmRunChain.colors] using halt⟩ }
  termination_by p => p.length
  decreasing_by
    simp_wf

theorem exists_null_monochromatic_run_of_null_path
    {a b : Symmetrify V}
    (p : @Quiver.Path (Symmetrify V) (@Quiver.symmetrifyQuiver V _) a b)
    (hp : p.length ≠ 0)
    (hread : L.symmPathRead p = 1) :
    ∃ r ∈ (symmRunDecomposition (L := L) p).chain.pieces,
      L.symmPathRead r.path = 1 := by
  let d := symmRunDecomposition (L := L) p
  have hpieces : d.chain.pieces ≠ [] := by
    apply SymmRunChain.pieces_ne_nil_of_path_ne_nil L d.chain
    rw [d.path_eq]
    exact hp
  have hchainread : L.symmPathRead d.chain.path = 1 := by
    rw [d.path_eq]
    exact hread
  obtain ⟨r, hr, hrread⟩ :=
    exists_null_piece_of_null_chain L d.chain d.alternating hpieces hchainread
  exact ⟨r, hr, hrread⟩

omit [Quiver.HasInvolutiveReverse V] in
theorem exists_first_edge_comp
    {a b : Symmetrify V}
    (p : @Quiver.Path (Symmetrify V) (@Quiver.symmetrifyQuiver V _) a b)
    (hp : p.length ≠ 0) :
    ∃ c : Symmetrify V,
      ∃ e : @Quiver.Hom (Symmetrify V) (@Quiver.symmetrifyQuiver V _) a c,
        ∃ q : @Quiver.Path (Symmetrify V) (@Quiver.symmetrifyQuiver V _) c b,
          p = e.toPath.comp q := by
  induction p with
  | nil => simp at hp
  | cons p e ih =>
      by_cases hzero : p.length = 0
      · have hend := Path.eq_of_length_zero p hzero
        cases hend
        have hnil : p = Path.nil := Path.eq_nil_of_length_zero p hzero
        subst p
        refine ⟨_, e, Path.nil, ?_⟩
        rfl
      · obtain ⟨c, f, q, hpq⟩ := ih hzero
        refine ⟨c, f, q.comp e.toPath, ?_⟩
        rw [← Path.comp_toPath_eq_cons, ← Path.comp_assoc, hpq]

theorem exists_null_nonloop_run_of_minimal_null_path
    {a b : Symmetrify V}
    (p : @Quiver.Path (Symmetrify V) (@Quiver.symmetrifyQuiver V _) a b)
    (hp : p.length ≠ 0)
    (hread : L.symmPathRead p = 1)
    (hminimal : ∀ q : @Quiver.Path (Symmetrify V)
        (@Quiver.symmetrifyQuiver V _) a b,
        L.symmPathRead q = 1 → ¬ q.length < p.length) :
    ∃ r ∈ (symmRunDecomposition (L := L) p).chain.pieces,
      L.symmPathRead r.path = 1 ∧ r.source ≠ r.target := by
  let d := symmRunDecomposition (L := L) p
  have hpieces : d.chain.pieces ≠ [] := by
    apply SymmRunChain.pieces_ne_nil_of_path_ne_nil L d.chain
    rw [d.path_eq]
    exact hp
  have hchainread : L.symmPathRead d.chain.path = 1 := by
    rw [d.path_eq]
    exact hread
  obtain ⟨r, hr, hrread⟩ :=
    exists_null_piece_of_null_chain L d.chain d.alternating hpieces hchainread
  refine ⟨r, ?_, hrread, ?_⟩
  · simpa [d] using hr
  · intro hloop
    obtain ⟨q, hqread, hqlength⟩ :=
      exists_shorter_null_path_of_null_loop_run L d.chain hr hloop
        hrread hchainread
    apply hminimal q hqread
    rw [← d.path_eq]
    exact hqlength

theorem pathLabels_reverse {a b : V} (p : Path a b) :
    L.pathLabels p.reverse =
      (L.pathLabels p).reverse.map (factorWordInv (G := G) (H := H)) := by
  induction p with
  | nil => rfl
  | cons p e ih =>
      rw [Path.reverse, pathLabels_comp]
      rw [pathLabels_toPath, L.reverse_label]
      simp [pathLabels, ih]

theorem pathRead_reverse {a b : V} (p : Path a b) :
    L.pathRead p.reverse = (L.pathRead p)⁻¹ := by
  simp only [pathRead, pathLabels_reverse, factorWordProd_reverse_inv]

theorem isMonochromatic_reverse {a b : V} {p : Path a b} {color : Bool}
    (hp : L.IsMonochromatic p color) :
    L.IsMonochromatic p.reverse color := by
  intro z hz
  rw [pathLabels_reverse] at hz
  obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hz
  simp only [binarySumIndex_factorWordInv]
  exact hp y (by simpa using hy)

theorem pathRead_mono_false {a b : V} {p : Path a b}
    (hp : L.IsMonochromatic p false) :
    ∃ g : G, L.pathRead p = Monoid.Coprod.inl g := by
  obtain ⟨l, hl⟩ := exists_map_inl_of_idx_false (G := G) (H := H)
    (by simpa [IsMonochromatic] using hp)
  refine ⟨l.prod, ?_⟩
  rw [pathRead, hl, factorWordProd_map_inl]

theorem pathRead_mono_true {a b : V} {p : Path a b}
    (hp : L.IsMonochromatic p true) :
    ∃ h : H, L.pathRead p = Monoid.Coprod.inr h := by
  obtain ⟨l, hl⟩ := exists_map_inr_of_idx_true (G := G) (H := H)
    (by simpa [IsMonochromatic] using hp)
  refine ⟨l.prod, ?_⟩
  rw [pathRead, hl, factorWordProd_map_inr]

/-! ### Marked loop moves

The fundamental-group part of a fold changes a marked family of based loops by
permuting loops, reversing a loop, or concatenating two loops.  These are the
path-level counterparts of the algebraic Nielsen generators. -/

/-- An elementary Nielsen move on a tuple of based loops. -/
inductive LoopNielsenStep {b : V} {n : ℕ}
    (x y : Fin n → Path b b) : Prop
  | perm (e : Fin n ≃ Fin n) (h : y = x ∘ e) : LoopNielsenStep x y
  | invert (i : Fin n) (h : y = Function.update x i (x i).reverse) :
      LoopNielsenStep x y
  | mulRight (i j : Fin n) (hij : i ≠ j)
      (h : y = Function.update x i ((x i).comp (x j))) :
      LoopNielsenStep x y

/-- Two loop tuples are connected by finitely many elementary Nielsen moves. -/
def LoopNielsenEquivalent {b : V} {n : ℕ}
    (x y : Fin n → Path b b) : Prop :=
  Relation.ReflTransGen (fun u v : Fin n → Path b b => LoopNielsenStep u v) x y

/-- Reads a tuple of based loops as a tuple of free-product elements. -/
def loopRead {b : V} {n : ℕ} (x : Fin n → Path b b) : Fin n → G ∗ H :=
  fun i => L.pathRead (x i)

theorem loopNielsenStep_read {b : V} {n : ℕ}
    {x y : Fin n → Path b b} (h : LoopNielsenStep x y) :
    NielsenStep (L.loopRead x) (L.loopRead y) := by
  cases h with
  | perm e hEq =>
      apply NielsenStep.perm e
      rw [hEq]
      rfl
  | invert i hEq =>
      apply NielsenStep.invert i
      funext k
      by_cases hki : k = i
      · subst k
        simp [hEq, loopRead, pathRead_reverse]
      · simp [hEq, loopRead, hki]
  | mulRight i j hij hEq =>
      apply NielsenStep.mulRight i j hij
      funext k
      by_cases hki : k = i
      · subst k
        simp [hEq, loopRead, pathRead_comp]
      · simp [hEq, loopRead, hki]

theorem loopNielsenEquivalent_read {b : V} {n : ℕ}
    {x y : Fin n → Path b b} (h : LoopNielsenEquivalent x y) :
    NielsenEquivalent (L.loopRead x) (L.loopRead y) := by
  induction h using Relation.ReflTransGen.trans_induction_on with
  | refl => exact Relation.ReflTransGen.refl
  | single hstep => exact Relation.ReflTransGen.single (loopNielsenStep_read L hstep)
  | trans h₁ h₂ ih₁ ih₂ => exact Relation.ReflTransGen.trans ih₁ ih₂

theorem loopNielsenStep_read_closure_eq {b : V} {n : ℕ}
    {x y : Fin n → Path b b} (h : LoopNielsenStep x y) :
    Subgroup.closure (Set.range (L.loopRead x)) =
      Subgroup.closure (Set.range (L.loopRead y)) := by
  exact nielsenStep_closure_eq (loopNielsenStep_read L h)

theorem loopNielsenEquivalent_read_closure_eq {b : V} {n : ℕ}
    {x y : Fin n → Path b b} (h : LoopNielsenEquivalent x y) :
    Subgroup.closure (Set.range (L.loopRead x)) =
      Subgroup.closure (Set.range (L.loopRead y)) := by
  exact nielsenEquivalent_closure_eq (loopNielsenEquivalent_read L h)

end BinaryLabelling

/-! ### A marked finite graph interface

The eventual fold induction acts on a connected finite graph together with a
finite marked family of based loops.  The definition below keeps the marking
separate from the fold operation: it records exactly the data needed to state
that the labelled loops generate the free product, while the path lemmas above
prove how that data behaves under a graph-level Nielsen move. -/

/-- A graph labelled by two factors and marked by a finite tuple of based loops. -/
structure MarkedBinaryGraph (n : ℕ) where
  /-- The common base vertex of the marking loops. -/
  base : V
  /-- The factor labelling assigned to the graph's edges. -/
  labeling : BinaryLabelling (G := G) (H := H) (V := V)
  /-- The finite tuple of loops marking the graph. -/
  loops : Fin n → Path base base

namespace MarkedBinaryGraph

variable (M : MarkedBinaryGraph (G := G) (H := H) (V := V) n)

/-- The free-product elements read along the marking loops. -/
def read : Fin n → G ∗ H :=
  M.labeling.loopRead M.loops

/-- The marking loops read a generating tuple of the free product. -/
def IsGenerating : Prop :=
  Subgroup.closure (Set.range M.read) = ⊤

/-- Every vertex can be reached from the base after allowing formal reverse edges. -/
def WeaklyConnected : Prop :=
  ∀ v : V, Nonempty (@Path (Symmetrify V) _ M.base v)

theorem read_nielsenEquivalent {x y : Fin n → Path M.base M.base}
    (h : BinaryLabelling.LoopNielsenEquivalent x y) :
    NielsenEquivalent (M.labeling.loopRead x) (M.labeling.loopRead y) := by
  exact M.labeling.loopNielsenEquivalent_read h

theorem generating_of_loopNielsenEquivalent
    {x y : Fin n → Path M.base M.base}
    (hx : Subgroup.closure (Set.range (M.labeling.loopRead x)) = ⊤)
    (h : BinaryLabelling.LoopNielsenEquivalent x y) :
    Subgroup.closure (Set.range (M.labeling.loopRead y)) = ⊤ := by
  rw [← M.labeling.loopNielsenEquivalent_read_closure_eq h]
  exact hx

theorem isGenerating_iff :
    M.IsGenerating ↔ Subgroup.closure (Set.range
      (M.labeling.loopRead M.loops)) = ⊤ :=
  Iff.rfl

/-! ### Paths representing the generated subgroup

The marked loops generate the target group, so every target element is read by
some based loop.  This is the small algebraic bridge needed to append a loop to
a path whose endpoints are different. -/

/-- The subgroup consisting of all elements read by loops at the marked base. -/
def loopReadSubgroup : Subgroup (G ∗ H) where
  carrier := {g | ∃ p : Path M.base M.base, M.labeling.pathRead p = g}
  one_mem' := by
    exact ⟨Path.nil, by simp⟩
  mul_mem' := by
    rintro g h ⟨p, hp⟩ ⟨q, hq⟩
    refine ⟨p.comp q, ?_⟩
    rw [M.labeling.pathRead_comp, hp, hq]
  inv_mem' := by
    rintro g ⟨p, hp⟩
    refine ⟨p.reverse, ?_⟩
    rw [M.labeling.pathRead_reverse, hp]

theorem mem_loopReadSubgroup_of_marked (i : Fin n) :
    M.read i ∈ M.loopReadSubgroup := by
  exact ⟨M.loops i, rfl⟩

theorem exists_loop_read (hM : M.IsGenerating) (g : G ∗ H) :
    ∃ p : Path M.base M.base, M.labeling.pathRead p = g := by
  have hsub : Subgroup.closure (Set.range M.read) ≤ M.loopReadSubgroup := by
    apply (Subgroup.closure_le _).mpr
    rintro g ⟨i, rfl⟩
    exact M.mem_loopReadSubgroup_of_marked i
  have hg : g ∈ Subgroup.closure (Set.range M.read) := by
    rw [hM]
    trivial
  exact hsub hg

theorem exists_null_path (hM : M.IsGenerating) {v : V}
    (hv : Nonempty (@Path (Symmetrify V) _ M.base v)) :
    ∃ p : @Path (Symmetrify V) _ M.base v,
      M.labeling.symmPathRead p = 1 := by
  obtain ⟨p⟩ := hv
  obtain ⟨q, hq⟩ := M.exists_loop_read hM (M.labeling.symmPathRead p)⁻¹
  refine ⟨(@Quiver.Symmetrify.of V _).mapPath q |>.comp p, ?_⟩
  calc
    M.labeling.symmPathRead
        ((@Quiver.Symmetrify.of V _).mapPath q |>.comp p) =
      M.labeling.symmPathRead ((@Quiver.Symmetrify.of V _).mapPath q) *
        M.labeling.symmPathRead p :=
      M.labeling.symmPathRead_comp
        ((@Quiver.Symmetrify.of V _).mapPath q) p
    _ = M.labeling.pathRead q * M.labeling.symmPathRead p := by
      rw [M.labeling.symmPathRead_map_of]
    _ = 1 := by rw [hq]; simp

theorem exists_null_nonloop_path [Fintype V] (hgen : M.IsGenerating)
    (hconn : M.WeaklyConnected) (hcard : 1 < Fintype.card V) :
    ∃ v : V, v ≠ M.base ∧
      ∃ p : @Path (Symmetrify V) _ M.base v,
        M.labeling.symmPathRead p = 1 := by
  have hex : ∃ v : V, v ≠ M.base := by
    by_contra h
    have hall : ∀ v : V, v = M.base := by
      intro v
      by_contra hv
      exact h ⟨v, hv⟩
    let : Subsingleton V := ⟨fun x y => (hall x).trans (hall y).symm⟩
    have hle : Fintype.card V ≤ 1 :=
      Fintype.card_le_one_iff_subsingleton.mpr inferInstance
    omega
  obtain ⟨v, hv⟩ := hex
  obtain ⟨p⟩ := hconn v
  exact ⟨v, hv, exists_null_path M hgen ⟨p⟩ |>.choose,
    (exists_null_path M hgen ⟨p⟩).choose_spec⟩

theorem exists_minimal_null_nonloop_path [Fintype V]
    (hgen : M.IsGenerating) (hconn : M.WeaklyConnected)
    (hcard : 1 < Fintype.card V) :
    ∃ v : V, v ≠ M.base ∧
      ∃ p : @Path (Symmetrify V) _ M.base v,
        M.labeling.symmPathRead p = 1 ∧
        ∀ q : @Path (Symmetrify V) _ M.base v,
          M.labeling.symmPathRead q = 1 → ¬ q.length < p.length := by
  classical
  let good : ℕ → Prop := fun n =>
    ∃ v : V, v ≠ M.base ∧
      ∃ p : @Path (Symmetrify V) _ M.base v,
        p.length = n ∧ M.labeling.symmPathRead p = 1
  obtain ⟨v₀, hv₀, p₀, hp₀⟩ :=
    M.exists_null_nonloop_path hgen hconn hcard
  have hgood : ∃ n, good n := by
    refine ⟨p₀.length, v₀, hv₀, p₀, rfl, hp₀⟩
  obtain ⟨v, hv, p, hplen, hpread⟩ := by
    simpa [good] using Nat.find_spec hgood
  refine ⟨v, hv, p, hpread, ?_⟩
  intro q hq hlt
  have hlt' : q.length < Nat.find hgood := by
    rw [← hplen]
    exact hlt
  have hnot : ¬ good q.length := Nat.find_min hgood hlt'
  apply hnot
  exact ⟨v, hv, q, rfl, hq⟩

end MarkedBinaryGraph

end GeneralGrushko
end MarshallHall
