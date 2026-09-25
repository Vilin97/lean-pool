/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

module

public import LeanPool.RegtsSevenster.RS.Common.MathlibDeps

/-!
# The statement surface, defined

Every definition the theorems of record are phrased in, in one self-contained
module: the flag model of multigraph fragments with its gluing, fragment
isomorphism, composition, the connection pairing and the edge-rank hypothesis,
Eulerian edge subsets, the mixed partition function (Regts–Sevenster's
Definition 5), the three named statements, the symmetric monoidal category of
super vector spaces, the vocabulary of Deligne's hypotheses, and Deligne's
theorem, which `RS/Classical/Deligne/` proves.

This module imports only the Mathlib funnel (`RS/Common/MathlibDeps.lean`, an
import list with no content), so its meaning is determined by this file
against Mathlib alone. It is the trusted surface of the comparator
certification: `Challenge.lean` carries a copy of the sections below, against
Mathlib alone, and states the theorems of record with `sorry`; `Solution.lean`
proves each by the theorem of record of the same name, against the definitions
here. Comparator confirms at the kernel-export level that the two sides prove
identical statements about identical definitions — the definitions below. The
rest of the tree imports them from here rather than restating them, so this
file is the single source of what the theorems mean.

**How to read it.** Each section names the theory it carries; the rest of the
repository builds on these declarations by import, so what is written here is,
verbatim, what the theorems of record are about. The order is: the sorting
sign; fragments and gluing; fragment isomorphism; composition; connection
pairings and the edge-rank hypothesis; Eulerian edge subsets; the mixed
partition function; the named statements; super vector spaces; the vocabulary
of Deligne's hypotheses; and Deligne's theorem. -/

@[expose] public section

namespace RS

/-! ## 1. Inversions and the sorting sign

The sorting sign supplies the antisymmetry of the odd-colour evaluation in
Definition 5: reordering the odd colours multiplies the vertex value by the
sign of the permutation, realized as `(−1)` to the inversion count. -/

/-- The number of inversions of a list over a linear order. -/
def inversions {α : Type} [LinearOrder α] : List α → ℕ
  | [] => 0
  | a :: l => (l.filter (fun b => b < a)).length + inversions l

/-- The sorting sign of a list: `(−1)` to the number of
inversions. -/
def sortSign {α : Type} [LinearOrder α] (l : List α) : ℤ :=
  (-1) ^ inversions l

/-! ## 2. The flag model of multigraph fragments

A *fragment* is a finite multigraph in half-edge (flag) form: flags attach to
internal vertices or to boundary labels, a fixed-point-free involution pairs
flags into edges, each boundary label carries exactly one flag, and free
circles are counted separately. Gluing two boundary labels either closes an
edge into a free circle (when the two flags bound a common edge) or rewires
the two edges end to end. These are the graphs the main theorems quantify
over; `ClosedFragment` below is the case of no boundary labels. -/

/-- A fragment over the boundary-label type `α`: a finite multigraph
in half-edge (flag) form whose dangling flags are labelled
bijectively by `α`, together with a count of free circles. -/
structure Fragment (α : Type) where
  /-- The type of flags (half-edges). -/
  Flag : Type
  /-- The type of internal vertices. -/
  Vertex : Type
  /-- Flags form a finite type with decidable equality. -/
  [flagFintype : Fintype Flag]
  [flagDecEq : DecidableEq Flag]
  /-- Vertices form a finite type. -/
  [vertexFintype : Fintype Vertex]
  /-- Each flag is attached to an internal vertex or to a boundary
  label. -/
  attach : Flag → Vertex ⊕ α
  /-- The edge involution: every flag has a partner. -/
  pairing : Flag → Flag
  /-- The pairing is an involution. -/
  pairing_invol : ∀ f, pairing (pairing f) = f
  /-- The pairing has no fixed points. -/
  pairing_ne : ∀ f, pairing f ≠ f
  /-- The flag at each boundary label. -/
  boundaryFlag : α → Flag
  /-- The boundary flag of `ℓ` is attached to `ℓ`. -/
  attach_boundaryFlag : ∀ ℓ, attach (boundaryFlag ℓ) = Sum.inr ℓ
  /-- Any flag attached to `ℓ` is the boundary flag of `ℓ`. -/
  eq_boundaryFlag : ∀ ℓ f, attach f = Sum.inr ℓ → f = boundaryFlag ℓ
  /-- Free circles, counted separately. -/
  circles : ℕ

attribute [instance] Fragment.flagFintype Fragment.flagDecEq
  Fragment.vertexFintype

namespace Fragment

variable {α β : Type}

/-- Boundary flags of distinct labels are distinct. -/
theorem boundaryFlag_injective (W : Fragment α) :
    Function.Injective W.boundaryFlag := by
  intro i j hij
  have hi := W.attach_boundaryFlag i
  have hj := W.attach_boundaryFlag j
  rw [hij, hj] at hi
  exact (Sum.inr.inj hi).symm

/-- Bounding a common edge is symmetric in the two labels: if the
flag at `i` pairs to the flag at `j`, then the flag at `j` pairs back
to the flag at `i`. -/
theorem pairing_boundaryFlag_comm (W : Fragment α) {i j : α}
    (h : W.pairing (W.boundaryFlag i) = W.boundaryFlag j) :
    W.pairing (W.boundaryFlag j) = W.boundaryFlag i := by
  rw [← h, W.pairing_invol]

/-- The closed fragment with no flags, no vertices, and a given
number of free circles. -/
def circlesOnly (c : ℕ) : Fragment Empty where
  Flag := Empty
  Vertex := Empty
  attach := Empty.elim
  pairing := Empty.elim
  pairing_invol := fun f => f.elim
  pairing_ne := fun f => f.elim
  boundaryFlag := Empty.elim
  attach_boundaryFlag := fun ℓ => ℓ.elim
  eq_boundaryFlag := fun ℓ => ℓ.elim
  circles := c

/-- Transport a fragment along an equivalence of label types. -/
def relabel (W : Fragment α) (e : α ≃ β) : Fragment β where
  Flag := W.Flag
  Vertex := W.Vertex
  attach := fun f => (W.attach f).map id e
  pairing := W.pairing
  pairing_invol := W.pairing_invol
  pairing_ne := W.pairing_ne
  boundaryFlag := fun ℓ => W.boundaryFlag (e.symm ℓ)
  attach_boundaryFlag := fun ℓ => by
    simp [W.attach_boundaryFlag (e.symm ℓ)]
  eq_boundaryFlag := fun ℓ f h => by
    rcases ha : W.attach f with v | ℓ'
    · simp [ha] at h
    · simp only [ha, Sum.map_inr] at h
      obtain rfl : e ℓ' = ℓ := Sum.inr.inj h
      rw [Equiv.symm_apply_apply]
      exact W.eq_boundaryFlag ℓ' f ha
  circles := W.circles

/-- Disjoint union of fragments, over the sum of the label types. -/
def disjUnion (W₁ : Fragment α) (W₂ : Fragment β) :
    Fragment (α ⊕ β) where
  Flag := W₁.Flag ⊕ W₂.Flag
  Vertex := W₁.Vertex ⊕ W₂.Vertex
  attach := Sum.elim
    (fun f => (W₁.attach f).map Sum.inl Sum.inl)
    (fun f => (W₂.attach f).map Sum.inr Sum.inr)
  pairing := Sum.map W₁.pairing W₂.pairing
  pairing_invol := fun f => by
    cases f <;> simp [W₁.pairing_invol, W₂.pairing_invol]
  pairing_ne := fun f => by
    cases f with
    | inl g => simpa using fun h => W₁.pairing_ne g h
    | inr g => simpa using fun h => W₂.pairing_ne g h
  boundaryFlag := Sum.elim
    (fun ℓ => Sum.inl (W₁.boundaryFlag ℓ))
    (fun ℓ => Sum.inr (W₂.boundaryFlag ℓ))
  attach_boundaryFlag := fun ℓ => by
    cases ℓ <;> simp [W₁.attach_boundaryFlag, W₂.attach_boundaryFlag]
  eq_boundaryFlag := fun ℓ f h => by
    cases ℓ with
    | inl ℓ₁ =>
      cases f with
      | inl g =>
        rcases ha : W₁.attach g with v | ℓ' <;> simp? [ha] at h
        subst h
        simp [W₁.eq_boundaryFlag ℓ' g ha]
      | inr g =>
        rcases ha : W₂.attach g with v | ℓ' <;> simp [ha] at h
    | inr ℓ₂ =>
      cases f with
      | inl g =>
        rcases ha : W₁.attach g with v | ℓ' <;> simp [ha] at h
      | inr g =>
        rcases ha : W₂.attach g with v | ℓ' <;> simp? [ha] at h
        subst h
        simp [W₂.eq_boundaryFlag ℓ' g ha]
  circles := W₁.circles + W₂.circles

/-! ### Single-pair gluing -/

section GluePair

/-- The labels surviving a glue at `{i, j}`. -/
abbrev SurvivingLabel (α : Type) (i j : α) : Type :=
  {x : α // x ≠ i ∧ x ≠ j}

/-- The flags surviving a glue at `{i, j}`: all but the two glued
boundary flags. -/
abbrev SurvivingFlag (W : Fragment α) (i j : α) : Type :=
  {f : W.Flag // f ≠ W.boundaryFlag i ∧ f ≠ W.boundaryFlag j}

/-- A surviving flag is never attached to a glued label. -/
theorem survivingFlag_attach_ne {W : Fragment α} {i j : α}
    (f : SurvivingFlag W i j) :
    W.attach f.val ≠ Sum.inr i ∧ W.attach f.val ≠ Sum.inr j :=
  ⟨fun h => f.prop.1 (W.eq_boundaryFlag i f.val h),
   fun h => f.prop.2 (W.eq_boundaryFlag j f.val h)⟩

/-- The attachment map computed at a *given* value of `W.attach`,
which is supplied together with the equation identifying it.  Taking
the value as a parameter is what lets every proof below reason by
cases on it, so `glueAttach` itself is never unfolded. -/
def glueAttachOn (W : Fragment α) (i j : α) (f : SurvivingFlag W i j) :
    ∀ s : W.Vertex ⊕ α, W.attach f.val = s →
      W.Vertex ⊕ SurvivingLabel α i j
  | Sum.inl v, _ => Sum.inl v
  | Sum.inr ℓ, ha => Sum.inr ⟨ℓ,
      fun h => (survivingFlag_attach_ne f).1 (h ▸ ha),
      fun h => (survivingFlag_attach_ne f).2 (h ▸ ha)⟩

/-- The attachment map after gluing at `{i, j}`: unchanged, with the
label type restricted to the surviving labels. -/
def glueAttach (W : Fragment α) (i j : α) (f : SurvivingFlag W i j) :
    W.Vertex ⊕ SurvivingLabel α i j :=
  glueAttachOn W i j f (W.attach f.val) rfl

/-- `glueAttachOn` returns, under the label inclusion, exactly the
value of `attach` it was handed. -/
theorem glueAttachOn_spec (W : Fragment α) (i j : α)
    (f : SurvivingFlag W i j) (s : W.Vertex ⊕ α) (h : W.attach f.val = s) :
    (glueAttachOn W i j f s h).map id Subtype.val = s := by
  cases s <;> rfl

/-- `glueAttach` agrees with `attach` under the label inclusion. -/
theorem glueAttach_spec (W : Fragment α) (i j : α)
    (f : SurvivingFlag W i j) :
    (glueAttach W i j f).map id Subtype.val = W.attach f.val :=
  glueAttachOn_spec W i j f _ rfl

end GluePair

section GluePairRewire

variable {W : Fragment α} {i j : α}

/-- The rewired pairing for an *open* glue (the two glued flags do
not bound a common edge): the far ends of the two glued edges become
partners; all other flags keep their partners. -/
def rewire (hopen : W.pairing (W.boundaryFlag i) ≠ W.boundaryFlag j)
    (f : SurvivingFlag W i j) : SurvivingFlag W i j :=
  if hfi : W.pairing f.val = W.boundaryFlag i then
    ⟨W.pairing (W.boundaryFlag j),
      fun h => hopen (W.pairing_boundaryFlag_comm h),
      fun h => W.pairing_ne (W.boundaryFlag j) h⟩
  else if hfj : W.pairing f.val = W.boundaryFlag j then
    ⟨W.pairing (W.boundaryFlag i),
      fun h => W.pairing_ne (W.boundaryFlag i) h,
      fun h => hopen h⟩
  else
    ⟨W.pairing f.val, hfi, hfj⟩

/-- Rewiring across an open glue is an involution: it is the glued
fragment's edge pairing. -/
theorem rewire_invol (hij : i ≠ j)
    (hopen : W.pairing (W.boundaryFlag i) ≠ W.boundaryFlag j)
    (f : SurvivingFlag W i j) :
    rewire hopen (rewire hopen f) = f := by
  have hbne : W.boundaryFlag i ≠ W.boundaryFlag j :=
    fun h => hij (W.boundaryFlag_injective h)
  unfold rewire
  split
  · -- f is the far end of i's edge; its rewired partner is the far
    -- end of j's edge, whose rewired partner is back at f.
    rename_i hfi
    rw [dite_eq_right (by
      rw [W.pairing_invol]
      exact fun h => hbne h.symm)]
    rw [dite_eq_left (by rw [W.pairing_invol])]
    refine Subtype.ext ?_
    have h2 := congrArg W.pairing hfi
    rw [W.pairing_invol] at h2
    exact h2.symm
  · split
    · rename_i hfi hfj
      rw [dite_eq_left (by rw [W.pairing_invol])]
      refine Subtype.ext ?_
      have h2 := congrArg W.pairing hfj
      rw [W.pairing_invol] at h2
      exact h2.symm
    · rename_i hfi hfj
      rw [dite_eq_right (by rw [W.pairing_invol]; exact fun h => f.prop.1 h)]
      rw [dite_eq_right (by rw [W.pairing_invol]; exact fun h => f.prop.2 h)]
      exact Subtype.ext (W.pairing_invol f.val)

/-- And fixed-point-free, so the glued fragment is again a
fragment. -/
theorem rewire_ne (hij : i ≠ j)
    (hopen : W.pairing (W.boundaryFlag i) ≠ W.boundaryFlag j)
    (f : SurvivingFlag W i j) : rewire hopen f ≠ f := by
  have hbne : W.boundaryFlag i ≠ W.boundaryFlag j :=
    fun h => hij (W.boundaryFlag_injective h)
  unfold rewire
  split
  · rename_i hfi
    intro h
    have hval := congrArg Subtype.val h
    have : W.pairing f.val = W.boundaryFlag j := by
      rw [← hval, W.pairing_invol]
    exact hbne (hfi ▸ this)
  · split
    · rename_i hfi hfj
      intro h
      have hval := congrArg Subtype.val h
      exact hfi (by rw [← hval, W.pairing_invol])
    · intro h
      exact W.pairing_ne f.val (congrArg Subtype.val h)

end GluePairRewire

/-! ### The glued fragment -/

section Glue

variable (W : Fragment α) (i j : α)

/-- The boundary flag of a surviving label survives the glue. -/
def glueBoundaryFlag (ℓ : SurvivingLabel α i j) : SurvivingFlag W i j :=
  ⟨W.boundaryFlag ℓ.val,
    fun h => ℓ.prop.1 (W.boundaryFlag_injective h),
    fun h => ℓ.prop.2 (W.boundaryFlag_injective h)⟩

variable {W i j}

/-- The glued attachment lands on a surviving label exactly when
the original attachment lands on its underlying label. -/
theorem glueAttach_inr_iff (f : SurvivingFlag W i j)
    (ℓ : SurvivingLabel α i j) :
    glueAttach W i j f = Sum.inr ℓ ↔ W.attach f.val = Sum.inr ℓ.val := by
  constructor
  · intro h
    have := glueAttach_spec W i j f
    rw [h] at this
    simpa using this.symm
  · intro h
    have hs := glueAttach_spec W i j f
    rw [h] at hs
    cases hg : glueAttach W i j f with
    | inl v => rw [hg] at hs; exact absurd hs (by simp)
    | inr m =>
      rw [hg] at hs
      simp only [Sum.map_inr, Sum.inr.injEq] at hs
      exact congrArg Sum.inr (Subtype.ext hs)

/-- The glued attachment lands on a vertex exactly when the original
attachment does.  With `glueAttach_inr_iff` this characterises
`glueAttach`, so no proof needs to unfold it. -/
theorem glueAttach_inl_iff (f : SurvivingFlag W i j) (v : W.Vertex) :
    glueAttach W i j f = Sum.inl v ↔ W.attach f.val = Sum.inl v := by
  have hs := glueAttach_spec W i j f
  constructor
  · intro h; rw [h] at hs; simpa using hs.symm
  · intro h
    rw [h] at hs
    cases hg : glueAttach W i j f with
    | inl v' => rw [hg] at hs; simp only [Sum.map_inl, id_eq,
        Sum.inl.injEq] at hs; rw [hs]
    | inr m => rw [hg] at hs; exact absurd hs (by simp)

/-- The surviving label a flag glues onto, with its equation. -/
theorem exists_glueAttach_inr (f : SurvivingFlag W i j) {ℓ : α}
    (ha : W.attach f.val = Sum.inr ℓ) :
    ∃ p : SurvivingLabel α i j,
      glueAttach W i j f = Sum.inr p ∧ p.val = ℓ :=
  ⟨⟨ℓ, fun e => (survivingFlag_attach_ne f).1 (e ▸ ha),
       fun e => (survivingFlag_attach_ne f).2 (e ▸ ha)⟩,
   (glueAttach_inr_iff f _).mpr ha, rfl⟩

/-- Case analysis on `glueAttach`, phrased on the value of `attach`.
This is the eliminator every proof below uses: it replaces unfolding
the definition, so `glueAttach` is never unfolded anywhere. -/
@[elab_as_elim]
theorem glueAttach_cases {motive : W.Vertex ⊕ SurvivingLabel α i j → Prop}
    (f : SurvivingFlag W i j)
    (hinl : ∀ v, W.attach f.val = Sum.inl v → motive (Sum.inl v))
    (hinr : ∀ p : SurvivingLabel α i j,
      W.attach f.val = Sum.inr p.val → motive (Sum.inr p)) :
    motive (glueAttach W i j f) := by
  cases hg : glueAttach W i j f with
  | inl v => exact hinl v ((glueAttach_inl_iff f v).mp hg)
  | inr p => exact hinr p ((glueAttach_inr_iff f p).mp hg)

variable (W i j)

/-- The glued attachment of a surviving label's flag is that
label. -/
theorem glue_attach_boundaryFlag (ℓ : SurvivingLabel α i j) :
    glueAttach W i j (glueBoundaryFlag W i j ℓ) = Sum.inr ℓ :=
  (glueAttach_inr_iff _ _).mpr (W.attach_boundaryFlag ℓ.val)

/-- A surviving flag attached to a surviving label is that label's
boundary flag. -/
theorem glue_eq_boundaryFlag (ℓ : SurvivingLabel α i j)
    (f : SurvivingFlag W i j) (h : glueAttach W i j f = Sum.inr ℓ) :
    f = glueBoundaryFlag W i j ℓ :=
  Subtype.ext (W.eq_boundaryFlag ℓ.val f.val ((glueAttach_inr_iff _ _).mp h))

/-- A glue at `{i, j}` with a prescribed pairing and circle count.

Flags, vertices, attachment and boundary flags of a single-pair glue
are determined by `W` alone; only the pairing and the circle count
tell the closed and open glues apart.  Naming that common part gives
the two glues a single shape, so any fact about a glue that does not
mention its pairing is proved once. -/
def glueWith (p : SurvivingFlag W i j → SurvivingFlag W i j)
    (hinvol : ∀ f, p (p f) = f) (hne : ∀ f, p f ≠ f) (c : ℕ) :
    Fragment (SurvivingLabel α i j) where
  Flag := SurvivingFlag W i j
  Vertex := W.Vertex
  attach := glueAttach W i j
  pairing := p
  pairing_invol := hinvol
  pairing_ne := hne
  boundaryFlag := glueBoundaryFlag W i j
  attach_boundaryFlag := glue_attach_boundaryFlag W i j
  eq_boundaryFlag := glue_eq_boundaryFlag W i j
  circles := c

/-- Gluing the boundary labels `i ≠ j` when their flags bound a
common edge: the edge closes into a free circle. -/
def gluePairClosed (hclosed : W.pairing (W.boundaryFlag i) = W.boundaryFlag j) :
    Fragment (SurvivingLabel α i j) :=
  glueWith W i j
    (fun f =>
      ⟨W.pairing f.val,
        fun h => f.prop.2 (by
          rw [← W.pairing_invol f.val, h, hclosed]),
        fun h => f.prop.1 (by
          rw [← W.pairing_invol f.val, h, ← hclosed, W.pairing_invol])⟩)
    (fun f => Subtype.ext (W.pairing_invol f.val))
    (fun f h => W.pairing_ne f.val (congrArg Subtype.val h))
    (W.circles + 1)

/-- Gluing the boundary labels `i ≠ j` when their flags bound
distinct edges: the two edges are unified by rewiring. -/
def gluePairOpen (hij : i ≠ j)
    (hopen : W.pairing (W.boundaryFlag i) ≠ W.boundaryFlag j) :
    Fragment (SurvivingLabel α i j) :=
  glueWith W i j (rewire hopen) (rewire_invol hij hopen)
    (rewire_ne hij hopen) W.circles

/-- Gluing a pair of distinct boundary labels: the two half-edges at
`i` and `j` are joined.  If they bound a common edge it closes into a
free circle; otherwise their edges are unified end to end. -/
def gluePair (hij : i ≠ j) : Fragment (SurvivingLabel α i j) :=
  if hclosed : W.pairing (W.boundaryFlag i) = W.boundaryFlag j then
    gluePairClosed W i j hclosed
  else
    gluePairOpen W i j hij hclosed

end Glue

/-! ## 3. Isomorphism of fragments

The hypothesis class asks parameters to be isomorphism-invariant; this is the
notion of isomorphism. (`RS/Novel/Skein/FragmentEquiv.lean` proves the
equivalences form a groupoid and are congruences for the fragment operations.)
-/

/-- An equivalence of fragments: a pair of type equivalences on
flags and vertices commuting with attachment, pairing, and
boundary-flag data, preserving the circle count. -/
structure Equiv (W₁ W₂ : Fragment α) where
  /-- The equivalence of flag types. -/
  flagEquiv : W₁.Flag ≃ W₂.Flag
  /-- The equivalence of vertex types. -/
  vertexEquiv : W₁.Vertex ≃ W₂.Vertex
  /-- The flag equivalence commutes with attachment. -/
  attach_comm : ∀ f, W₂.attach (flagEquiv f) =
    (W₁.attach f).map vertexEquiv id
  /-- The flag equivalence commutes with pairing. -/
  pairing_comm : ∀ f, flagEquiv (W₁.pairing f) =
    W₂.pairing (flagEquiv f)
  /-- The circle counts agree. -/
  circles_eq : W₁.circles = W₂.circles

end Fragment

/-! ## 4. Composition of fragments

An `(s + t)`-fragment and a `(t + u)`-fragment compose by gluing the last `t`
labels of the first to the first `t` of the second, top pair first, through
the single-pair gluing above; the label bookkeeping is by one-point removals
of `Fin` indices. Composition is what the connection pairing evaluates. -/

/-! ### Removing a point -/

/-- Removing one point from `Fin (n + 1)` leaves `Fin n`. -/
noncomputable def finRemoveEquiv {n : ℕ} (a : Fin (n + 1)) :
    {x : Fin (n + 1) // x ≠ a} ≃ Fin n where
  toFun x := ((finSuccEquiv' a) x.val).get (by
    rw [Option.isSome_iff_ne_none]
    intro h
    exact x.prop ((finSuccEquiv' a).injective (h.trans (finSuccEquiv'_at
      a).symm)))
  invFun y := ⟨(finSuccEquiv' a).symm (some y), by
    intro h
    have happ := (finSuccEquiv' a).apply_symm_apply (some y)
    rw [h, finSuccEquiv'_at] at happ
    exact Option.some_ne_none y happ.symm⟩
  left_inv x := Subtype.ext (by simp)
  right_inv y := by simp

/-- Removing `inl a` and `inr b` from a sum splits into the two
one-point removals. -/
def sumRemoveSplitEquiv {A B : Type} (a : A) (b : B) :
    {x : A ⊕ B // x ≠ Sum.inl a ∧ x ≠ Sum.inr b} ≃
      {x : A // x ≠ a} ⊕ {y : B // y ≠ b} where
  toFun := fun
    | ⟨Sum.inl v, h⟩ => Sum.inl ⟨v, fun he => h.1 (congrArg Sum.inl he)⟩
    | ⟨Sum.inr w, h⟩ => Sum.inr ⟨w, fun he => h.2 (congrArg Sum.inr he)⟩
  invFun := fun
    | Sum.inl v => ⟨Sum.inl v.val,
        fun h => v.prop (Sum.inl.inj h), fun h => Sum.inl_ne_inr h⟩
    | Sum.inr w => ⟨Sum.inr w.val,
        fun h => Sum.inr_ne_inl h, fun h => w.prop (Sum.inr.inj h)⟩
  left_inv := fun
    | ⟨Sum.inl _, _⟩ => rfl
    | ⟨Sum.inr _, _⟩ => rfl
  right_inv := fun
    | Sum.inl _ => rfl
    | Sum.inr _ => rfl

/-- Removing label `t` from `Fin (t + 1 + u)` leaves `Fin (t + u)`. -/
noncomputable def rightRemoveEquiv (t u : ℕ) :
    {x : Fin (t + 1 + u) // x ≠ ⟨t, by omega⟩} ≃ Fin (t + u) :=
  Equiv.trans
    (Equiv.subtypeEquiv (finCongr (by omega : t + 1 + u = (t + u) + 1))
      (fun x => by simp [Fin.ext_iff]))
    (finRemoveEquiv ⟨t, by omega⟩)

/-- The label re-indexing after gluing the top interface pair:
removing the last label on the left and label `t` on the right. -/
noncomputable def interfaceStepEquiv (s t u : ℕ) :
    {x : Fin (s + t + 1) ⊕ Fin (t + 1 + u) //
      x ≠ Sum.inl ⟨s + t, Nat.lt_succ_self _⟩ ∧
      x ≠ Sum.inr ⟨t, by omega⟩} ≃ Fin (s + t) ⊕ Fin (t + u) :=
  Equiv.trans (sumRemoveSplitEquiv _ _)
    (Equiv.sumCongr (finRemoveEquiv _) (rightRemoveEquiv t u))

/-! ### Gluing an interface -/

/-- Glue the `t` interface labels of a fragment over
`Fin (s + t) ⊕ Fin (t + u)`: the pairs `(inl (s + k), inr k)` for
`k < t`, glued top pair first. -/
noncomputable def glueInterface (s : ℕ) :
    (t : ℕ) → (u : ℕ) → Fragment (Fin (s + t) ⊕ Fin (t + u)) →
      Fragment (Fin s ⊕ Fin u)
  | 0, _, W => W.relabel
      (Equiv.sumCongr (finCongr (by omega)) (finCongr (by omega)))
  | t + 1, u, W =>
      let W' := W.gluePair (Sum.inl ⟨s + t, by omega⟩)
        (Sum.inr ⟨t, by omega⟩) (by simp)
      glueInterface s t u (W'.relabel (interfaceStepEquiv s t u))

/-- Composition of fragments: glue the last `t` labels of `F` to the
first `t` labels of `G`, in order. -/
noncomputable def Fragment.compose {s t u : ℕ}
    (F : Fragment (Fin (s + t))) (G : Fragment (Fin (t + u))) :
    Fragment (Fin (s + u)) :=
  (glueInterface s t u (F.disjUnion G)).relabel finSumFinEquiv

/-! ## 5. Connection pairings and the edge-rank hypothesis

The connection pairing of a parameter at arity `t` closes two `t`-fragments
against each other; the edge-rank hypothesis bounds, for every `t`, the rank
of that pairing by `R ^ t`, phrased as the `Module.rank` of the range of the
curried pairing (`RS/Novel/Skein/ConnectionRank.lean` proves this equivalent
to the finite-submatrix reading of the literature; that equivalence is a
theorem *about* the hypothesis and is not needed to state it).
`EdgeRankParameter` packages the hypothesis class of the forward direction:
normalized at the empty graph, isomorphism-invariant, rank-bounded. -/

/-- A closed fragment: no boundary labels. -/
abbrev ClosedFragment : Type 1 := Fragment (Fin 0)

/-- The full closure of two `t`-fragments: compose them as a
`(0 + t)`- and a `(t + 0)`-fragment. -/
noncomputable def pairClose {t : ℕ} (F G : Fragment (Fin t)) :
    ClosedFragment :=
  (F.relabel (finCongr (by omega : t = 0 + t))).compose
    (G.relabel (finCongr (by omega : t = t + 0)))

/-- The connection pairing of a parameter at arity `t`. -/
noncomputable def connectionPairing (f : ClosedFragment → ℂ) (t : ℕ)
    (F G : Fragment (Fin t)) : ℂ :=
  f (pairClose F G)

/-- The curried connection pairing as a linear map from the free
module on `t`-fragments to the function space. -/
noncomputable def connectionMap (f : ClosedFragment → ℂ) (t : ℕ) :
    (Fragment (Fin t) →₀ ℂ) →ₗ[ℂ] (Fragment (Fin t) → ℂ) :=
  Finsupp.lift _ ℂ _ (fun F G => connectionPairing f t F G)

/-- The edge-rank hypothesis `H2`: the connection pairing at every
arity has rank at most `R ^ t`. -/
def EdgeRankBounded (f : ClosedFragment → ℂ) (R : ℕ) : Prop :=
  ∀ t : ℕ, Module.rank ℂ (LinearMap.range (connectionMap f t)) ≤
    (R : Cardinal) ^ t

/-- The empty closed fragment. -/
noncomputable def emptyClosedFragment : ClosedFragment :=
  (Fragment.circlesOnly 0).relabel (Equiv.equivOfIsEmpty Empty (Fin 0))

/-- The hypothesis class of the main theorem: a parameter on closed
fragments, normalized on the empty graph, with exponentially
bounded connection rank. -/
structure EdgeRankParameter (R : ℕ) where
  /-- The parameter, on concrete closed fragments. -/
  val : ClosedFragment → ℂ
  /-- The parameter takes the value `1` on the empty graph. -/
  val_empty : val emptyClosedFragment = 1
  /-- The parameter is invariant under fragment isomorphism. -/
  iso_invariant : ∀ W₁ W₂ : ClosedFragment, W₁.Equiv W₂ → val W₁ = val W₂
  /-- The rank bound. -/
  rank_bounded : EdgeRankBounded val R

/-! ## 6. Eulerian edge subsets and circuit data

Definition 5 sums over pairing-closed flag subsets in which every vertex has
even degree. A *transition system* is the local pairing `κ` of Definition 5: a
second fixed-point-free involution matching participating flags at common
vertices. Following an edge and then the matching generates the circuit walks;
each geometric circuit of `n` edges appears as two walk-cycles (its two
directions) when `n ≥ 2` and as two walk fixed points when `n = 1`, so the
circuit count is half the number of orbits. -/

variable {α : Type}

/-- An edge subset of a fragment: a flag set closed under the edge
pairing. -/
structure EdgeSubset (W : Fragment α) where
  /-- The participating flags. -/
  flags : Finset W.Flag
  /-- The set is closed under the edge pairing. -/
  pairing_mem : ∀ f ∈ flags, W.pairing f ∈ flags

namespace EdgeSubset

variable {W : Fragment α}

/-- The degree of a vertex within an edge subset: the number of
participating flags attached to it. -/
noncomputable def deg (F : EdgeSubset W) (v : W.Vertex) : ℕ :=
  letI := Classical.decEq (W.Vertex ⊕ α)
  (F.flags.filter (fun f => W.attach f = Sum.inl v)).card

/-- An edge subset is Eulerian when every vertex has even degree
within it. -/
def Eulerian (F : EdgeSubset W) : Prop :=
  ∀ v : W.Vertex, Even (F.deg v)

/-- A transition system on an edge subset: a fixed-point-free
involution of its flags matching flags at a common internal
vertex.  This is the local pairing data `κ` of Definition 5. -/
structure TransitionSystem (F : EdgeSubset W) where
  /-- The matching. -/
  match_ : W.Flag → W.Flag
  /-- The matching is an involution on the participating flags. -/
  match_invol : ∀ f ∈ F.flags, match_ (match_ f) = f
  /-- The matching has no fixed points on the participating flags. -/
  match_ne : ∀ f ∈ F.flags, match_ f ≠ f
  /-- The matching stays within the participating flags. -/
  match_mem : ∀ f ∈ F.flags, match_ f ∈ F.flags
  /-- Matched flags share an internal vertex. -/
  match_vertex : ∀ f ∈ F.flags, ∀ v : W.Vertex,
    W.attach f = Sum.inl v → W.attach (match_ f) = Sum.inl v
  /-- Only internally attached flags participate. -/
  attach_internal : ∀ f ∈ F.flags, ∃ v : W.Vertex,
    W.attach f = Sum.inl v

/-- The walk map of a transition system: follow the edge to the
partner flag, then the matching at its vertex. -/
def TransitionSystem.walk {F : EdgeSubset W} (κ : TransitionSystem F)
    (f : W.Flag) : W.Flag :=
  κ.match_ (W.pairing f)

/-- The walk map preserves the participating flags. -/
theorem TransitionSystem.walk_mem {F : EdgeSubset W}
    (κ : TransitionSystem F) {f : W.Flag} (hf : f ∈ F.flags) :
    κ.walk f ∈ F.flags :=
  κ.match_mem _ (F.pairing_mem f hf)

/-- The walk map is injective on the participating flags. -/
theorem TransitionSystem.walk_injOn {F : EdgeSubset W}
    (κ : TransitionSystem F) {f g : W.Flag} (hf : f ∈ F.flags)
    (hg : g ∈ F.flags) (h : κ.walk f = κ.walk g) : f = g := by
  have hpf : W.pairing f ∈ F.flags := F.pairing_mem f hf
  have hpg : W.pairing g ∈ F.flags := F.pairing_mem g hg
  have hm : W.pairing f = W.pairing g := by
    have h1 := κ.match_invol _ hpf
    have h2 := κ.match_invol _ hpg
    have h' : κ.match_ (W.pairing f) = κ.match_ (W.pairing g) := h
    calc W.pairing f = κ.match_ (κ.match_ (W.pairing f)) := h1.symm
      _ = κ.match_ (κ.match_ (W.pairing g)) := by rw [h']
      _ = W.pairing g := h2
  calc f = W.pairing (W.pairing f) := (W.pairing_invol f).symm
    _ = W.pairing (W.pairing g) := by rw [hm]
    _ = g := W.pairing_invol g

/-- The walk permutation of a transition system: the walk map as a
permutation of the participating flags. -/
noncomputable def TransitionSystem.walkPerm {F : EdgeSubset W}
    (κ : TransitionSystem F) : Equiv.Perm {f : W.Flag // f ∈ F.flags} :=
  Equiv.ofBijective
    (fun f => ⟨κ.walk f.val, κ.walk_mem f.prop⟩)
    (Finite.injective_iff_bijective.mp
      (fun f g h => Subtype.ext
        (κ.walk_injOn f.prop g.prop (congrArg Subtype.val h))))

/-- The circuit count of a transition system: each geometric circuit
of `n` edges carries two walk-cycles of length `n` when `n ≥ 2` and
two walk fixed points when `n = 1`, so the count is half the total
number of orbits. -/
noncomputable def TransitionSystem.circuitCount {F : EdgeSubset W}
    (κ : TransitionSystem F) : ℕ :=
  (κ.walkPerm.cycleType.card +
    Fintype.card (Function.fixedPoints κ.walkPerm)) / 2

end EdgeSubset

/-! ## 7. The mixed partition function (Definition 5)

A `(k, 2ℓ)` mixed vertex functional assigns a value to a multiset of even
colours and a *set* of odd colours; the alternating evaluation on an ordered
odd list is recovered through the sorting sign, so antisymmetry is a theorem
of the evaluator rather than a condition on the data. The summand of an
Eulerian subset is its circuit sign times the colouring sum of vertex values,
odd colours contributing through the symplectic pairing (`oddPartner`,
`oddPartnerSign`); the value of the subset is choice-free because the tree
proves it independent of the transition data, and `mixedPartition` is the
free-circle factor `(k − 2ℓ)^circles` times the sum over Eulerian subsets. -/

/-- The data of a `(k, 2ℓ)` mixed vertex functional: a value for
each multiset of even colours and set of odd colours. -/
def MixedFunctional (k ℓ : ℕ) : Type :=
  Multiset (Fin k) → Finset (Fin (2 * ℓ)) → ℂ

/-- The alternating evaluation of a mixed functional on an ordered
list of odd colours: zero on repetitions, otherwise the sorting
sign times the value on the underlying set. -/
def MixedFunctional.evalOdd {k ℓ : ℕ} (h : MixedFunctional k ℓ)
    (μ : Multiset (Fin k)) (w : List (Fin (2 * ℓ))) : ℂ :=
  if w.Nodup then (sortSign w : ℂ) * h μ w.toFinset else 0

/-- The odd-colour index pairing of the standard symplectic basis:
the partner of colour `c` is `c + ℓ` when `c < ℓ` and `c − ℓ`
otherwise. -/
def oddPartner (ℓ : ℕ) (c : Fin (2 * ℓ)) : Fin (2 * ℓ) :=
  if h : c.val < ℓ then ⟨c.val + ℓ, by omega⟩
  else ⟨c.val - ℓ, by omega⟩

/-- The sign of the odd-colour pairing: `g_c = −f_{c+ℓ}` for
`c < ℓ` and `g_c = f_{c−ℓ}` otherwise. -/
def oddPartnerSign (ℓ : ℕ) (c : Fin (2 * ℓ)) : ℤ :=
  if c.val < ℓ then -1 else 1

/-- An orientation compatible with a transition system: an in/out
designation of the participating flags, flipped both by the vertex
matching and by the edge pairing (so circuits are traversed
consistently). -/
structure EdgeSubset.TransitionSystem.Orientation {α : Type}
    {W : Fragment α} {F : EdgeSubset W} (κ : F.TransitionSystem) where
  /-- Whether a flag is an outgoing end. -/
  isOut : W.Flag → Bool
  /-- The vertex matching pairs incoming with outgoing flags. -/
  match_flip : ∀ f ∈ F.flags, isOut (κ.match_ f) = !isOut f
  /-- Each edge has one outgoing and one incoming end. -/
  pairing_flip : ∀ f ∈ F.flags, isOut (W.pairing f) = !isOut f

-- Deliberately semireducible: the order is an enumeration artefact,
-- only ever supplied explicitly via `letI`, never by instance search.
/-- An arbitrary but fixed linear order on the flags of a fragment,
transported from an enumeration.  Used only to enumerate vertex
pairings; the evaluated summands are independent of the choice
because pair blocks move by even permutations. -/
@[instance_reducible]
noncomputable def Fragment.flagOrder {α : Type} (W : Fragment α) :
    LinearOrder W.Flag :=
  LinearOrder.lift' (Fintype.equivFin W.Flag)
    (Fintype.equivFin W.Flag).injective

/-- The incoming participating flags at a vertex, in the fixed flag
order. -/
noncomputable def EdgeSubset.inFlagsAt {α : Type} {W : Fragment α}
    (F : EdgeSubset W) {κ : F.TransitionSystem}
    (o : κ.Orientation) (v : W.Vertex) : List W.Flag :=
  letI := W.flagOrder
  letI := Classical.dec
  (F.flags.filter
      (fun f => W.attach f = Sum.inl v ∧ o.isOut f = false)).sort (· ≤ ·)

section Summand

variable {α : Type} {W : Fragment α}

/-- The complement of an edge subset is closed under the pairing. -/
theorem EdgeSubset.pairing_not_mem (F : EdgeSubset W) {f : W.Flag}
    (hf : f ∉ F.flags) : W.pairing f ∉ F.flags := fun hmem => by
  have := F.pairing_mem _ hmem
  rw [W.pairing_invol] at this
  exact hf this

/-- Even colourings of the non-participating edges: pairing-constant
colours on the flags outside the subset. -/
def EdgeSubset.EvenColouring (F : EdgeSubset W) (k : ℕ) : Type :=
  {ψ : {f : W.Flag // f ∉ F.flags} → Fin k //
    ∀ f : {f : W.Flag // f ∉ F.flags},
      ψ ⟨W.pairing f.val, F.pairing_not_mem f.prop⟩ = ψ f}

/-- Odd colourings of the participating edges: pairing-constant
colours on the flags of the subset. -/
def EdgeSubset.OddColouring (F : EdgeSubset W) (ℓ : ℕ) : Type :=
  {φ : {f : W.Flag // f ∈ F.flags} → Fin (2 * ℓ) //
    ∀ f : {f : W.Flag // f ∈ F.flags},
      φ ⟨W.pairing f.val, F.pairing_mem _ f.prop⟩ = φ f}

open Classical in
/-- Even colourings are finite in number. -/
noncomputable instance EdgeSubset.EvenColouring.instFintype
    (F : EdgeSubset W) (k : ℕ) : Fintype (F.EvenColouring k) := by
  unfold EdgeSubset.EvenColouring
  infer_instance

open Classical in
/-- And so are odd ones, so Definition 5's sum is finite. -/
noncomputable instance EdgeSubset.OddColouring.instFintype
    (F : EdgeSubset W) (ℓ : ℕ) : Fintype (F.OddColouring ℓ) := by
  unfold EdgeSubset.OddColouring
  infer_instance

open Classical in
/-- The even-colour multiset at a vertex: the colours of the
non-participating flags attached to it. -/
noncomputable def EdgeSubset.evenColoursAt (F : EdgeSubset W) {k : ℕ}
    (ψ : F.EvenColouring k) (v : W.Vertex) : Multiset (Fin k) :=
  ((Finset.univ.filter
      (fun f : {f : W.Flag // f ∉ F.flags} =>
        W.attach f.val = Sum.inl v)).val).map ψ.val

/-- Every in-flag at a vertex participates in the edge subset. -/
theorem EdgeSubset.mem_of_mem_inFlagsAt {F : EdgeSubset W}
    {κ : F.TransitionSystem} {o : κ.Orientation} {v : W.Vertex}
    {f : W.Flag} (hf : f ∈ F.inFlagsAt o v) : f ∈ F.flags := by
  let := W.flagOrder
  let := Classical.dec
  unfold EdgeSubset.inFlagsAt at hf
  exact (Finset.mem_filter.mp ((Finset.mem_sort _).mp hf)).1

open Classical in
/-- The odd pair contributed by an incoming participating flag: its
edge colour followed by the partner index of its matched outgoing
flag's edge colour. -/
noncomputable def EdgeSubset.oddPairFn (F : EdgeSubset W) {ℓ : ℕ}
    (κ : F.TransitionSystem) (φ : F.OddColouring ℓ)
    (f : {f : W.Flag // f ∈ F.flags}) : List (Fin (2 * ℓ)) :=
  [φ.val f, oddPartner ℓ (φ.val ⟨κ.match_ f.val, κ.match_mem _ f.prop⟩)]

open Classical in
/-- The odd-pairing sign contributed by an incoming participating
flag: the partner sign of its matched outgoing flag's colour. -/
noncomputable def EdgeSubset.oddSignFn (F : EdgeSubset W) {ℓ : ℕ}
    (κ : F.TransitionSystem) (φ : F.OddColouring ℓ)
    (f : {f : W.Flag // f ∈ F.flags}) : ℤ :=
  oddPartnerSign ℓ (φ.val ⟨κ.match_ f.val, κ.match_mem _ f.prop⟩)

open Classical in
/-- The odd-colour list at a vertex: the odd pairs of the incoming
flags in the fixed order. -/
noncomputable def EdgeSubset.oddListAt (F : EdgeSubset W) {ℓ : ℕ}
    {κ : F.TransitionSystem} (o : κ.Orientation)
    (φ : F.OddColouring ℓ) (v : W.Vertex) : List (Fin (2 * ℓ)) :=
  ((F.inFlagsAt o v).attachWith (· ∈ F.flags)
      (fun _ hf => F.mem_of_mem_inFlagsAt hf)).flatMap (F.oddPairFn κ φ)

open Classical in
/-- The odd-pairing sign at a vertex: the product of the partner
signs of the outgoing colours. -/
noncomputable def EdgeSubset.oddSignAt (F : EdgeSubset W) {ℓ : ℕ}
    {κ : F.TransitionSystem} (o : κ.Orientation)
    (φ : F.OddColouring ℓ) (v : W.Vertex) : ℤ :=
  (((F.inFlagsAt o v).attachWith (· ∈ F.flags)
      (fun _ hf => F.mem_of_mem_inFlagsAt hf)).map (F.oddSignFn κ φ)).prod

open Classical in
/-- The Definition 5 summand of an Eulerian edge subset with chosen
transition system and orientation: the circuit sign times the
colouring sum of the vertex values. -/
noncomputable def EdgeSubset.mixedSummand (F : EdgeSubset W)
    {k ℓ : ℕ} (h : MixedFunctional k ℓ)
    {κ : F.TransitionSystem} (o : κ.Orientation) : ℂ :=
  ((-1 : ℂ) ^ κ.circuitCount) *
    ∑ ψ : F.EvenColouring k, ∑ φ : F.OddColouring ℓ,
      ∏ v : W.Vertex,
        ((F.oddSignAt o φ v : ℂ) *
          h.evalOdd (F.evenColoursAt ψ v) (F.oddListAt o φ v))

open Classical in
/-- The Definition 5 value of an edge subset: the summand for a
choice of transition system and orientation, zero when none
exists.  (Every Eulerian subset admits one; the value is
independent of the choice by the Eulerian-independence input.) -/
noncomputable def EdgeSubset.mixedValue (F : EdgeSubset W)
    {k ℓ : ℕ} (h : MixedFunctional k ℓ) : ℂ :=
  if hne : Nonempty ((κ : F.TransitionSystem) × κ.Orientation) then
    F.mixedSummand h (Classical.choice hne).2
  else 0

end Summand

open Classical in
/-- **The mixed partition function** (Regts–Sevenster Definition 5)
of a fragment: the free-circle factor times the sum over Eulerian
edge subsets of their circuit-signed colouring sums. -/
noncomputable def mixedPartition {α : Type} {k ℓ : ℕ}
    (h : MixedFunctional k ℓ) (W : Fragment α) : ℂ :=
  ((k : ℂ) - 2 * ℓ) ^ W.circles *
    ∑ s : Finset W.Flag,
      if hc : ∀ f ∈ s, W.pairing f ∈ s then
        if (EdgeSubset.mk s hc).Eulerian then
          (EdgeSubset.mk s hc).mixedValue h
        else 0
      else 0

/-- A parameter on closed fragments is a mixed partition function
when it is the Definition 5 value of some mixed functional. -/
def IsMixedPartitionFunction (f : ClosedFragment → ℂ) : Prop :=
  ∃ (k ℓ : ℕ) (h : MixedFunctional k ℓ),
    ∀ W : ClosedFragment, f W = mixedPartition h W

/-! ## 8. The named statements

The forward direction, the separate parity bound `⌊2eR⌋`, the sharp total
colour bound `R`, and the converse with its explicit base. -/

/-- **THE REGTS–SEVENSTER CONJECTURE.**  Every graph parameter with
exponentially bounded edge-connection rank is a mixed partition
function. -/
def RegtsSevensterStatement : Prop :=
  ∀ (R : ℕ) (f : EdgeRankParameter R), IsMixedPartitionFunction f.val

/-- A mixed partition function with explicit dimension bounds: the
functional's even dimension `k` and odd dimension `2ℓ` are both at
most `B`. -/
def IsMixedPartitionFunctionBounded (f : ClosedFragment → ℂ)
    (B : ℕ) : Prop :=
  ∃ (k ℓ : ℕ) (h : MixedFunctional k ℓ),
    k ≤ B ∧ 2 * ℓ ≤ B ∧
      ∀ W : ClosedFragment, f W = mixedPartition h W

/-- **THE QUANTITATIVE REGTS–SEVENSTER STATEMENT**: every graph
parameter with edge-connection rank at most `R ^ t` is a mixed
partition function of a `(k, 2ℓ)`-functional with
`k, 2ℓ ≤ ⌊2eR⌋`. -/
def RegtsSevensterStatementQuant : Prop :=
  ∀ (R : ℕ) (f : EdgeRankParameter R),
    IsMixedPartitionFunctionBounded f.val
      ⌊2 * Real.exp 1 * (R : ℝ)⌋₊

/-- A mixed model with a bound on the sum of its even and odd
dimensions. The named fields retain the functional and its agreement
with the graph parameter as part of the witness. -/
structure TotalBoundedMixedModel (f : ClosedFragment → ℂ) (B : ℕ) where
  /-- The number of even colours. -/
  k : ℕ
  /-- Half the number of odd colours. -/
  ℓ : ℕ
  /-- The vertex functional of the model. -/
  functional : MixedFunctional k ℓ
  /-- The total number of colours is bounded by `B`. -/
  dimension_le : k + 2 * ℓ ≤ B
  /-- The model evaluates to the given parameter on every fragment. -/
  partition_eq : ∀ W : ClosedFragment, f W = mixedPartition functional W

/-- A parameter admits a mixed model with at most `B` colours in
total, counting both the even and odd components. -/
def IsMixedPartitionFunctionTotalBounded (f : ClosedFragment → ℂ)
    (B : ℕ) : Prop :=
  Nonempty (TotalBoundedMixedModel f B)

/-- The total-dimension Regts–Sevenster statement: an edge-rank base
`R` bounds the total number of colours of a representing mixed model. -/
def RegtsSevensterStatementTotal : Prop :=
  ∀ (R : ℕ) (f : EdgeRankParameter R),
    IsMixedPartitionFunctionTotalBounded f.val R

/-- **THE CONVERSE STATEMENT**: every mixed partition function is
an edge-rank-bounded parameter with base `max 1 (k + 2ℓ)`
(Regts–Sevenster, arXiv:1807.04494, Theorem 6). -/
def RegtsSevensterConverseStatement : Prop :=
  ∀ (k ℓ : ℕ) (h : MixedFunctional k ℓ),
    ∃ g : EdgeRankParameter (max 1 (k + 2 * ℓ)),
      ∀ W : ClosedFragment, g.val W = mixedPartition h W

/-! ## 9. The symmetric monoidal category of super vector spaces

The codomain of the fibre functor in Deligne's conclusion: finite-dimensional
ℤ/2-graded complex vector spaces with grading-preserving maps, the graded
tensor product, and the braiding that carries the *Koszul sign* — the odd⊗odd
block acquires a factor of −1 under the swap (`koszulEvenAux`, second
component). This is the longest section; its content is one structure, its
category structure, and the monoidal, braided, symmetric, additive and
ℂ-linear instances, together with the computation lemmas their coherence
proofs run on. An auditor checking what Deligne's theorem *says* should read
the objects, `tensorObj`, `tensorUnit` and the two Koszul blocks; the rest is
coherence. -/

noncomputable section

open CategoryTheory
open scoped TensorProduct

/-- A *super vector space* over ℂ: a pair of finite-dimensional
complex vector spaces, called the *even* and *odd* components. -/
structure SuperVect where
  /-- The even-graded component. -/
  even : Type
  /-- The odd-graded component. -/
  odd : Type
  [evenAddCommGroup : AddCommGroup even]
  [evenModule : Module ℂ even]
  [oddAddCommGroup : AddCommGroup odd]
  [oddModule : Module ℂ odd]
  [evenFinite : FiniteDimensional ℂ even]
  [oddFinite : FiniteDimensional ℂ odd]

attribute [instance] SuperVect.evenAddCommGroup SuperVect.evenModule
  SuperVect.oddAddCommGroup SuperVect.oddModule
  SuperVect.evenFinite SuperVect.oddFinite

namespace SuperVect

/-- A morphism of super vector spaces: a pair of ℂ-linear maps
preserving the grading. -/
@[ext]
structure Hom (V W : SuperVect) where
  /-- The even component of the morphism. -/
  evenMap : V.even →ₗ[ℂ] W.even
  /-- The odd component of the morphism. -/
  oddMap : V.odd →ₗ[ℂ] W.odd

/-- The identity morphism on a super vector space. -/
@[simp]
def Hom.id (V : SuperVect) : Hom V V where
  evenMap := LinearMap.id
  oddMap := LinearMap.id

/-- Composition of super-vector-space morphisms. -/
@[simp]
def Hom.comp {V W X : SuperVect} (g : Hom W X) (f : Hom V W) : Hom V X where
  evenMap := g.evenMap.comp f.evenMap
  oddMap := g.oddMap.comp f.oddMap

/-- Super vector spaces and grading-preserving maps form a
category. -/
instance instCategoryStruct : CategoryStruct SuperVect where
  Hom := Hom
  id := Hom.id
  comp f g := Hom.comp g f

/-- Two morphisms agreeing in both components are equal. -/
@[ext]
theorem hom_ext {V W : SuperVect} {f g : V ⟶ W}
    (he : (f : Hom V W).evenMap = (g : Hom V W).evenMap)
    (ho : (f : Hom V W).oddMap = (g : Hom V W).oddMap) : f = g :=
  Hom.ext he ho

/-- SuperVect forms a category with grading-preserving linear maps. -/
instance instCategory : Category SuperVect where
  id_comp _ := by ext <;> simp [CategoryStruct.comp, CategoryStruct.id]
  comp_id _ := by ext <;> simp [CategoryStruct.comp, CategoryStruct.id]
  assoc _ _ _ := by ext <;> simp [CategoryStruct.comp]

/-! ### Tensor product -/

/-- The graded tensor product of two super vector spaces.  The even
component is `(V.even ⊗ W.even) × (V.odd ⊗ W.odd)` and the odd
component is `(V.even ⊗ W.odd) × (V.odd ⊗ W.even)`. -/
def tensorObj (V W : SuperVect) : SuperVect where
  even := (V.even ⊗[ℂ] W.even) × (V.odd ⊗[ℂ] W.odd)
  odd := (V.even ⊗[ℂ] W.odd) × (V.odd ⊗[ℂ] W.even)

/-- The tensor product of two grading-preserving maps acts
component-wise on each tensor block. -/
def tensorHom {V₁ V₂ W₁ W₂ : SuperVect}
    (f : Hom V₁ V₂) (g : Hom W₁ W₂) :
    Hom (tensorObj V₁ W₁) (tensorObj V₂ W₂) := by
  refine ⟨?_, ?_⟩
  · change (V₁.even ⊗[ℂ] W₁.even) × (V₁.odd ⊗[ℂ] W₁.odd) →ₗ[ℂ]
           (V₂.even ⊗[ℂ] W₂.even) × (V₂.odd ⊗[ℂ] W₂.odd)
    exact LinearMap.prodMap
      (TensorProduct.map f.evenMap g.evenMap)
      (TensorProduct.map f.oddMap g.oddMap)
  · change (V₁.even ⊗[ℂ] W₁.odd) × (V₁.odd ⊗[ℂ] W₁.even) →ₗ[ℂ]
           (V₂.even ⊗[ℂ] W₂.odd) × (V₂.odd ⊗[ℂ] W₂.even)
    exact LinearMap.prodMap
      (TensorProduct.map f.evenMap g.oddMap)
      (TensorProduct.map f.oddMap g.evenMap)

/-- The monoidal unit: ℂ in even degree, the zero module in odd
degree.  Marked reducible so that `tensorUnit.odd` reduces to `PUnit`
during type-class synthesis. -/
@[reducible]
def tensorUnit : SuperVect where
  even := ℂ
  odd := PUnit

/-! ### The Koszul braiding -/

/-- Module-level even Koszul block: `TensorProduct.comm` on the
first factor and *minus* `TensorProduct.comm` on the second.
Stated over bare modules so that instances of it at compound
objects have syntactically reduced types. -/
def koszulEvenAux (A B C D : Type*)
    [AddCommGroup A] [Module ℂ A] [AddCommGroup B] [Module ℂ B]
    [AddCommGroup C] [Module ℂ C] [AddCommGroup D] [Module ℂ D] :
    ((A ⊗[ℂ] B) × (C ⊗[ℂ] D)) →ₗ[ℂ] ((B ⊗[ℂ] A) × (D ⊗[ℂ] C)) :=
  LinearMap.prodMap
    (TensorProduct.comm ℂ A B).toLinearMap
    (-(TensorProduct.comm ℂ C D).toLinearMap)

/-- Module-level odd Koszul block: swaps the two summands and
applies `TensorProduct.comm` on each (no sign). -/
def koszulOddAux (A B C D : Type*)
    [AddCommGroup A] [Module ℂ A] [AddCommGroup B] [Module ℂ B]
    [AddCommGroup C] [Module ℂ C] [AddCommGroup D] [Module ℂ D] :
    ((A ⊗[ℂ] B) × (C ⊗[ℂ] D)) →ₗ[ℂ] ((D ⊗[ℂ] C) × (B ⊗[ℂ] A)) :=
  LinearMap.prod
    ((TensorProduct.comm ℂ C D).toLinearMap.comp (LinearMap.snd ℂ _ _))
    ((TensorProduct.comm ℂ A B).toLinearMap.comp (LinearMap.fst ℂ _ _))

/-- The even component of the Koszul braiding: applies
`TensorProduct.comm` on the even⊗even block and
*minus* `TensorProduct.comm` on the odd⊗odd block. -/
def koszulBraidingEven (V W : SuperVect) :
    (V.even ⊗[ℂ] W.even) × (V.odd ⊗[ℂ] W.odd) →ₗ[ℂ]
    (W.even ⊗[ℂ] V.even) × (W.odd ⊗[ℂ] V.odd) :=
  koszulEvenAux V.even W.even V.odd W.odd

/-- The odd component of the Koszul braiding: swaps the two
blocks and applies `TensorProduct.comm` on each (no sign,
since even⊗odd and odd⊗even contribute (−1)^(0·1) = 1). -/
def koszulBraidingOdd (V W : SuperVect) :
    (V.even ⊗[ℂ] W.odd) × (V.odd ⊗[ℂ] W.even) →ₗ[ℂ]
    (W.even ⊗[ℂ] V.odd) × (W.odd ⊗[ℂ] V.even) :=
  koszulOddAux V.even W.odd V.odd W.even

/-- The Koszul braiding morphism `V ⊗ W → W ⊗ V` in SuperVect,
carrying the sign (−1)^(p·q) on the swap of homogeneous elements
of parity p and q. -/
def koszulBraiding (V W : SuperVect) :
    Hom (tensorObj V W) (tensorObj W V) := by
  refine ⟨?_, ?_⟩
  · change (V.even ⊗[ℂ] W.even) × (V.odd ⊗[ℂ] W.odd) →ₗ[ℂ]
           (W.even ⊗[ℂ] V.even) × (W.odd ⊗[ℂ] V.odd)
    exact koszulBraidingEven V W
  · change (V.even ⊗[ℂ] W.odd) × (V.odd ⊗[ℂ] W.even) →ₗ[ℂ]
           (W.even ⊗[ℂ] V.odd) × (W.odd ⊗[ℂ] V.even)
    exact koszulBraidingOdd V W

/-- The Koszul braiding is a self-inverse: the two applications of
the sign on the odd⊗odd block cancel, and the component swaps on
the odd part compose to the identity. -/
theorem koszulBraiding_self_inverse (V W : SuperVect) :
    Hom.comp (koszulBraiding W V) (koszulBraiding V W) = Hom.id (tensorObj V W)
      := by
  apply Hom.ext
  · -- Even component: comm ∘ comm = id, (-comm) ∘ (-comm) = comm ∘ comm = id
    change (koszulBraidingEven W V).comp (koszulBraidingEven V W) = LinearMap.id
    apply LinearMap.ext; intro ⟨x, y⟩
    simp only [koszulBraidingEven, koszulEvenAux, LinearMap.comp_apply,
      LinearMap.prodMap_apply,
      LinearMap.neg_apply, LinearMap.id_apply, map_neg, neg_neg,
      LinearEquiv.coe_toLinearMap, TensorProduct.comm_comm]
  · -- Odd component: swap ∘ swap = id, comm ∘ comm = id
    change (koszulBraidingOdd W V).comp (koszulBraidingOdd V W) = LinearMap.id
    apply LinearMap.ext; intro ⟨x, y⟩
    simp only [koszulBraidingOdd, koszulOddAux, LinearMap.comp_apply,
      LinearMap.prod_apply,
      LinearMap.snd_apply, LinearMap.fst_apply, LinearMap.id_apply,
        Function.prod,
      LinearEquiv.coe_toLinearMap, TensorProduct.comm_comm]

/-- Application of the Koszul odd braiding to a pair of elements. -/
@[simp]
theorem koszulBraidingOdd_pair (V W : SuperVect)
    (x : V.even ⊗[ℂ] W.odd) (y : V.odd ⊗[ℂ] W.even) :
    koszulBraidingOdd V W ⟨x, y⟩ =
    ⟨(TensorProduct.comm ℂ V.odd W.even) y,
     (TensorProduct.comm ℂ V.even W.odd) x⟩ := rfl

/-! ### Koszul braiding as a categorical isomorphism -/

/-- The Koszul braiding as an isomorphism in SuperVect. -/
def koszulBraidingIso (V W : SuperVect) :
    tensorObj V W ≅ tensorObj W V where
  hom := koszulBraiding V W
  inv := koszulBraiding W V
  hom_inv_id := koszulBraiding_self_inverse V W
  inv_hom_id := koszulBraiding_self_inverse W V

/-! ### Left and right unitors -/

/-- The left unitor isomorphism `𝟙_ ⊗ V ≅ V`. -/
def leftUnitor (V : SuperVect) :
    tensorObj tensorUnit V ≅ V where
  hom := by
    refine ⟨?_, ?_⟩
    · change (ℂ ⊗[ℂ] V.even) × (PUnit ⊗[ℂ] V.odd) →ₗ[ℂ] V.even
      exact (TensorProduct.lid ℂ V.even).toLinearMap.comp (LinearMap.fst ℂ _ _)
    · change (ℂ ⊗[ℂ] V.odd) × (PUnit ⊗[ℂ] V.even) →ₗ[ℂ] V.odd
      exact (TensorProduct.lid ℂ V.odd).toLinearMap.comp (LinearMap.fst ℂ _ _)
  inv := by
    refine ⟨?_, ?_⟩
    · change V.even →ₗ[ℂ] (ℂ ⊗[ℂ] V.even) × (PUnit ⊗[ℂ] V.odd)
      exact LinearMap.inl ℂ _ _ ∘ₗ (TensorProduct.lid ℂ V.even).symm.toLinearMap
    · change V.odd →ₗ[ℂ] (ℂ ⊗[ℂ] V.odd) × (PUnit ⊗[ℂ] V.even)
      exact LinearMap.inl ℂ _ _ ∘ₗ (TensorProduct.lid ℂ V.odd).symm.toLinearMap
  hom_inv_id := by
    apply Hom.ext
    · change ((LinearMap.inl ℂ _ _ ∘ₗ (TensorProduct.lid ℂ
      V.even).symm.toLinearMap).comp
        ((TensorProduct.lid ℂ V.even).toLinearMap.comp (LinearMap.fst ℂ _ _))) =
          LinearMap.id
      apply LinearMap.ext; intro ⟨x, y⟩
      simp [Subsingleton.elim y 0]
    · change ((LinearMap.inl ℂ _ _ ∘ₗ (TensorProduct.lid ℂ
      V.odd).symm.toLinearMap).comp
        ((TensorProduct.lid ℂ V.odd).toLinearMap.comp (LinearMap.fst ℂ _ _))) =
          LinearMap.id
      apply LinearMap.ext; intro ⟨x, y⟩
      simp [Subsingleton.elim y 0]
  inv_hom_id := by
    apply Hom.ext
    · change ((TensorProduct.lid ℂ V.even).toLinearMap.comp (LinearMap.fst ℂ _
      _)).comp
        (LinearMap.inl ℂ _ _ ∘ₗ (TensorProduct.lid ℂ V.even).symm.toLinearMap) =
          LinearMap.id
      apply LinearMap.ext; intro x; simp
    · change ((TensorProduct.lid ℂ V.odd).toLinearMap.comp (LinearMap.fst ℂ _
      _)).comp
        (LinearMap.inl ℂ _ _ ∘ₗ (TensorProduct.lid ℂ V.odd).symm.toLinearMap) =
          LinearMap.id
      apply LinearMap.ext; intro x; simp

/-- The right unitor isomorphism `V ⊗ 𝟙_ ≅ V`. -/
def rightUnitor (V : SuperVect) :
    tensorObj V tensorUnit ≅ V where
  hom := by
    refine ⟨?_, ?_⟩
    · change (V.even ⊗[ℂ] ℂ) × (V.odd ⊗[ℂ] PUnit) →ₗ[ℂ] V.even
      exact (TensorProduct.rid ℂ V.even).toLinearMap.comp (LinearMap.fst ℂ _ _)
    · change (V.even ⊗[ℂ] PUnit) × (V.odd ⊗[ℂ] ℂ) →ₗ[ℂ] V.odd
      exact (TensorProduct.rid ℂ V.odd).toLinearMap.comp (LinearMap.snd ℂ _ _)
  inv := by
    refine ⟨?_, ?_⟩
    · change V.even →ₗ[ℂ] (V.even ⊗[ℂ] ℂ) × (V.odd ⊗[ℂ] PUnit)
      exact LinearMap.inl ℂ _ _ ∘ₗ (TensorProduct.rid ℂ V.even).symm.toLinearMap
    · change V.odd →ₗ[ℂ] (V.even ⊗[ℂ] PUnit) × (V.odd ⊗[ℂ] ℂ)
      exact LinearMap.inr ℂ _ _ ∘ₗ (TensorProduct.rid ℂ V.odd).symm.toLinearMap
  hom_inv_id := by
    apply Hom.ext
    · change ((LinearMap.inl ℂ _ _ ∘ₗ (TensorProduct.rid ℂ
      V.even).symm.toLinearMap).comp
        ((TensorProduct.rid ℂ V.even).toLinearMap.comp (LinearMap.fst ℂ _ _))) =
          LinearMap.id
      apply LinearMap.ext; intro ⟨x, y⟩
      simp [Subsingleton.elim y 0]
    · change ((LinearMap.inr ℂ _ _ ∘ₗ (TensorProduct.rid ℂ
      V.odd).symm.toLinearMap).comp
        ((TensorProduct.rid ℂ V.odd).toLinearMap.comp (LinearMap.snd ℂ _ _))) =
          LinearMap.id
      apply LinearMap.ext; intro ⟨x, y⟩
      simp [Subsingleton.elim x 0]
  inv_hom_id := by
    apply Hom.ext
    · change ((TensorProduct.rid ℂ V.even).toLinearMap.comp (LinearMap.fst ℂ _
      _)).comp
        (LinearMap.inl ℂ _ _ ∘ₗ (TensorProduct.rid ℂ V.even).symm.toLinearMap) =
          LinearMap.id
      apply LinearMap.ext; intro x; simp
    · change ((TensorProduct.rid ℂ V.odd).toLinearMap.comp (LinearMap.snd ℂ _
      _)).comp
        (LinearMap.inr ℂ _ _ ∘ₗ (TensorProduct.rid ℂ V.odd).symm.toLinearMap) =
          LinearMap.id
      apply LinearMap.ext; intro x; simp

/-! ### Associator -/

/-- Permutation of product components used in the associator:
`((A × B) × (C × D)) ≃ₗ ((A × C) × (D × B))`.  The mapping is
`(a, b, c, d) ↦ (a, c, d, b)`.  All field proofs hold by `rfl`
because the permutation is a definitional reshuffling of product
components. -/
def prod4Perm (A B C D : Type*)
    [AddCommGroup A] [Module ℂ A] [AddCommGroup B] [Module ℂ B]
    [AddCommGroup C] [Module ℂ C] [AddCommGroup D] [Module ℂ D] :
    ((A × B) × (C × D)) ≃ₗ[ℂ] ((A × C) × (D × B)) :=
  { toFun := fun ⟨⟨a, b⟩, ⟨c, d⟩⟩ => ⟨⟨a, c⟩, ⟨d, b⟩⟩
    map_add' := fun ⟨⟨_, _⟩, ⟨_, _⟩⟩ ⟨⟨_, _⟩, ⟨_, _⟩⟩ => rfl
    map_smul' := fun _ ⟨⟨_, _⟩, ⟨_, _⟩⟩ => rfl
    invFun := fun ⟨⟨a, c⟩, ⟨d, b⟩⟩ => ⟨⟨a, b⟩, ⟨c, d⟩⟩
    left_inv := fun ⟨⟨_, _⟩, ⟨_, _⟩⟩ => rfl
    right_inv := fun ⟨⟨_, _⟩, ⟨_, _⟩⟩ => rfl }

/-- Module-level associator block.  The construction distributes
the tensor over products (via `prodLeft` and `prodRight`),
reassociates each tensor block (via `TensorProduct.assoc`), and
permutes the four summands via `prod4Perm`.  Stated over bare
modules so that instances of it at compound objects have
syntactically reduced types; the even and odd components of the
SuperVect associator are its instantiations with the two `C`-slots
in the two orders. -/
def assocAux (A₁ A₂ B₁ B₂ C₁ C₂ : Type*)
    [AddCommGroup A₁] [Module ℂ A₁] [AddCommGroup A₂] [Module ℂ A₂]
    [AddCommGroup B₁] [Module ℂ B₁] [AddCommGroup B₂] [Module ℂ B₂]
    [AddCommGroup C₁] [Module ℂ C₁] [AddCommGroup C₂] [Module ℂ C₂] :
    ((((A₁ ⊗[ℂ] B₁) × (A₂ ⊗[ℂ] B₂)) ⊗[ℂ] C₁) ×
    (((A₁ ⊗[ℂ] B₂) × (A₂ ⊗[ℂ] B₁)) ⊗[ℂ] C₂)) ≃ₗ[ℂ]
    ((A₁ ⊗[ℂ] ((B₁ ⊗[ℂ] C₁) × (B₂ ⊗[ℂ] C₂))) ×
    (A₂ ⊗[ℂ] ((B₁ ⊗[ℂ] C₂) × (B₂ ⊗[ℂ] C₁)))) :=
  let s1 := LinearEquiv.prodCongr
    (TensorProduct.prodLeft ℂ ℂ (A₁ ⊗[ℂ] B₁) (A₂ ⊗[ℂ] B₂) C₁)
    (TensorProduct.prodLeft ℂ ℂ (A₁ ⊗[ℂ] B₂) (A₂ ⊗[ℂ] B₁) C₂)
  let s2 := prod4Perm
    ((A₁ ⊗[ℂ] B₁) ⊗[ℂ] C₁) ((A₂ ⊗[ℂ] B₂) ⊗[ℂ] C₁)
    ((A₁ ⊗[ℂ] B₂) ⊗[ℂ] C₂) ((A₂ ⊗[ℂ] B₁) ⊗[ℂ] C₂)
  let s3 := LinearEquiv.prodCongr
    (LinearEquiv.prodCongr (TensorProduct.assoc ℂ A₁ B₁ C₁)
      (TensorProduct.assoc ℂ A₁ B₂ C₂))
    (LinearEquiv.prodCongr (TensorProduct.assoc ℂ A₂ B₁ C₂)
      (TensorProduct.assoc ℂ A₂ B₂ C₁))
  let s4 := LinearEquiv.prodCongr
    (LinearEquiv.symm (TensorProduct.prodRight ℂ ℂ A₁
      (B₁ ⊗[ℂ] C₁) (B₂ ⊗[ℂ] C₂)))
    (LinearEquiv.symm (TensorProduct.prodRight ℂ ℂ A₂
      (B₁ ⊗[ℂ] C₂) (B₂ ⊗[ℂ] C₁)))
  s1 ≪≫ₗ s2 ≪≫ₗ s3 ≪≫ₗ s4

/-- The even component of the associator equivalence. -/
def assocEvenEquiv (V W X : SuperVect) :
    ((((V.even ⊗[ℂ] W.even) × (V.odd ⊗[ℂ] W.odd)) ⊗[ℂ] X.even) ×
    (((V.even ⊗[ℂ] W.odd) × (V.odd ⊗[ℂ] W.even)) ⊗[ℂ] X.odd)) ≃ₗ[ℂ]
    ((V.even ⊗[ℂ] ((W.even ⊗[ℂ] X.even) × (W.odd ⊗[ℂ] X.odd))) ×
    (V.odd ⊗[ℂ] ((W.even ⊗[ℂ] X.odd) × (W.odd ⊗[ℂ] X.even)))) :=
  assocAux V.even V.odd W.even W.odd X.even X.odd

/-- The odd component of the associator equivalence: `assocAux`
with the roles of the two `X`-slots swapped. -/
def assocOddEquiv (V W X : SuperVect) :
    ((((V.even ⊗[ℂ] W.even) × (V.odd ⊗[ℂ] W.odd)) ⊗[ℂ] X.odd) ×
    (((V.even ⊗[ℂ] W.odd) × (V.odd ⊗[ℂ] W.even)) ⊗[ℂ] X.even)) ≃ₗ[ℂ]
    ((V.even ⊗[ℂ] ((W.even ⊗[ℂ] X.odd) × (W.odd ⊗[ℂ] X.even))) ×
    (V.odd ⊗[ℂ] ((W.even ⊗[ℂ] X.even) × (W.odd ⊗[ℂ] X.odd)))) :=
  assocAux V.even V.odd W.even W.odd X.odd X.even

/-- The associator isomorphism `(V ⊗ W) ⊗ X ≅ V ⊗ (W ⊗ X)` in SuperVect.
Distributes tensor over products, reassociates each block, and
permutes the summands back into the canonical grading order. -/
def associator (V W X : SuperVect) :
    tensorObj (tensorObj V W) X ≅ tensorObj V (tensorObj W X) where
  hom := by
    refine ⟨?_, ?_⟩
    · change (((V.even ⊗[ℂ] W.even) × (V.odd ⊗[ℂ] W.odd)) ⊗[ℂ] X.even) ×
             (((V.even ⊗[ℂ] W.odd) × (V.odd ⊗[ℂ] W.even)) ⊗[ℂ] X.odd) →ₗ[ℂ]
             (V.even ⊗[ℂ] ((W.even ⊗[ℂ] X.even) × (W.odd ⊗[ℂ] X.odd))) ×
             (V.odd ⊗[ℂ] ((W.even ⊗[ℂ] X.odd) × (W.odd ⊗[ℂ] X.even)))
      exact LinearEquiv.toLinearMap (assocEvenEquiv V W X)
    · change (((V.even ⊗[ℂ] W.even) × (V.odd ⊗[ℂ] W.odd)) ⊗[ℂ] X.odd) ×
             (((V.even ⊗[ℂ] W.odd) × (V.odd ⊗[ℂ] W.even)) ⊗[ℂ] X.even) →ₗ[ℂ]
             (V.even ⊗[ℂ] ((W.even ⊗[ℂ] X.odd) × (W.odd ⊗[ℂ] X.even))) ×
             (V.odd ⊗[ℂ] ((W.even ⊗[ℂ] X.even) × (W.odd ⊗[ℂ] X.odd)))
      exact LinearEquiv.toLinearMap (assocOddEquiv V W X)
  inv := by
    refine ⟨?_, ?_⟩
    · change (V.even ⊗[ℂ] ((W.even ⊗[ℂ] X.even) × (W.odd ⊗[ℂ] X.odd))) ×
             (V.odd ⊗[ℂ] ((W.even ⊗[ℂ] X.odd) × (W.odd ⊗[ℂ] X.even))) →ₗ[ℂ]
             (((V.even ⊗[ℂ] W.even) × (V.odd ⊗[ℂ] W.odd)) ⊗[ℂ] X.even) ×
             (((V.even ⊗[ℂ] W.odd) × (V.odd ⊗[ℂ] W.even)) ⊗[ℂ] X.odd)
      exact LinearEquiv.toLinearMap (LinearEquiv.symm (assocEvenEquiv V W X))
    · change (V.even ⊗[ℂ] ((W.even ⊗[ℂ] X.odd) × (W.odd ⊗[ℂ] X.even))) ×
             (V.odd ⊗[ℂ] ((W.even ⊗[ℂ] X.even) × (W.odd ⊗[ℂ] X.odd))) →ₗ[ℂ]
             (((V.even ⊗[ℂ] W.even) × (V.odd ⊗[ℂ] W.odd)) ⊗[ℂ] X.odd) ×
             (((V.even ⊗[ℂ] W.odd) × (V.odd ⊗[ℂ] W.even)) ⊗[ℂ] X.even)
      exact LinearEquiv.toLinearMap (LinearEquiv.symm (assocOddEquiv V W X))
  hom_inv_id := by
    apply Hom.ext <;> {
      apply LinearMap.ext; intro x
      simp only [CategoryStruct.comp, CategoryStruct.id, Hom.comp, Hom.id,
        LinearMap.comp_apply, LinearMap.id_apply]
      exact LinearEquiv.symm_apply_apply _ x }
  inv_hom_id := by
    apply Hom.ext <;> {
      apply LinearMap.ext; intro x
      simp only [CategoryStruct.comp, CategoryStruct.id, Hom.comp, Hom.id,
        LinearMap.comp_apply, LinearMap.id_apply]
      exact LinearEquiv.apply_symm_apply _ x }

/-! ### Associator computation lemmas -/

/-- The first component of the zero pair. -/
@[simp]
lemma prod_fst_zero {A B : Type*} [Zero A] [Zero B] :
    (0 : A × B).1 = 0 := rfl

/-- The second component of the zero pair. -/
@[simp]
lemma prod_snd_zero {A B : Type*} [Zero A] [Zero B] :
    (0 : A × B).2 = 0 := rfl

/-- The pair of zeros is the zero pair. -/
@[simp]
lemma prod_mk_zero {A B : Type*} [Zero A] [Zero B] :
    ((0 : A), (0 : B)) = (0 : A × B) := rfl

/-- `prod4Perm`, applied. -/
@[simp]
lemma prod4Perm_apply {A B C D : Type*}
    [AddCommGroup A] [Module ℂ A] [AddCommGroup B] [Module ℂ B]
    [AddCommGroup C] [Module ℂ C] [AddCommGroup D] [Module ℂ D]
    (x : (A × B) × (C × D)) :
    prod4Perm A B C D x = ((x.1.1, x.2.1), (x.2.2, x.1.2)) := by
  obtain ⟨⟨a, b⟩, ⟨c, d⟩⟩ := x; rfl

/-- The inverse product-distribution on a first-summand pure
tensor. -/
lemma prodRight_symm_tmul_fst {M₁ M₂ M₃ : Type*}
    [AddCommGroup M₁] [Module ℂ M₁] [AddCommGroup M₂] [Module ℂ M₂]
    [AddCommGroup M₃] [Module ℂ M₃] (m₁ : M₁) (m₂ : M₂) :
    (TensorProduct.prodRight ℂ ℂ M₁ M₂ M₃).symm (m₁ ⊗ₜ m₂, 0) =
      m₁ ⊗ₜ[ℂ] ((m₂, 0) : M₂ × M₃) := by
  apply (TensorProduct.prodRight ℂ ℂ M₁ M₂ M₃).injective
  simp [TensorProduct.prodRight_tmul]

/-- The inverse product-distribution on a second-summand pure
tensor. -/
lemma prodRight_symm_tmul_snd {M₁ M₂ M₃ : Type*}
    [AddCommGroup M₁] [Module ℂ M₁] [AddCommGroup M₂] [Module ℂ M₂]
    [AddCommGroup M₃] [Module ℂ M₃] (m₁ : M₁) (m₃ : M₃) :
    (TensorProduct.prodRight ℂ ℂ M₁ M₂ M₃).symm (0, m₁ ⊗ₜ m₃) =
      m₁ ⊗ₜ[ℂ] ((0, m₃) : M₂ × M₃) := by
  apply (TensorProduct.prodRight ℂ ℂ M₁ M₂ M₃).injective
  simp [TensorProduct.prodRight_tmul]

-- Computation of `assocAux` on the four pure tensor generators.

/-- The associator block on a pure tensor of the `A₁ ⊗ B₁` summand
with `C₁`. -/
@[simp]
lemma assocAux_ee {A₁ A₂ B₁ B₂ C₁ C₂ : Type*}
    [AddCommGroup A₁] [Module ℂ A₁] [AddCommGroup A₂] [Module ℂ A₂]
    [AddCommGroup B₁] [Module ℂ B₁] [AddCommGroup B₂] [Module ℂ B₂]
    [AddCommGroup C₁] [Module ℂ C₁] [AddCommGroup C₂] [Module ℂ C₂]
    (a : A₁) (b : B₁) (c : C₁) :
    assocAux A₁ A₂ B₁ B₂ C₁ C₂
        (((a ⊗ₜ[ℂ] b, 0) ⊗ₜ[ℂ] c, 0) :
        ((((A₁ ⊗[ℂ] B₁) × (A₂ ⊗[ℂ] B₂)) ⊗[ℂ] C₁) ×
        (((A₁ ⊗[ℂ] B₂) × (A₂ ⊗[ℂ] B₁)) ⊗[ℂ] C₂))) =
      ((a ⊗ₜ[ℂ] ((b ⊗ₜ[ℂ] c, 0) : (B₁ ⊗[ℂ] C₁) × (B₂ ⊗[ℂ] C₂)), 0) :
        ((A₁ ⊗[ℂ] ((B₁ ⊗[ℂ] C₁) × (B₂ ⊗[ℂ] C₂))) ×
        (A₂ ⊗[ℂ] ((B₁ ⊗[ℂ] C₂) × (B₂ ⊗[ℂ] C₁))))) := by
  unfold assocAux
  simp only [LinearEquiv.trans_apply, LinearEquiv.prodCongr_apply,
    prod_fst_zero, prod_snd_zero, prod_mk_zero, TensorProduct.prodLeft_tmul,
    TensorProduct.zero_tmul, map_zero, prod4Perm_apply,
    TensorProduct.assoc_tmul, prodRight_symm_tmul_fst]

/-- The associator block on a pure tensor of the `A₂ ⊗ B₂` summand
with `C₁`. -/
@[simp]
lemma assocAux_oo {A₁ A₂ B₁ B₂ C₁ C₂ : Type*}
    [AddCommGroup A₁] [Module ℂ A₁] [AddCommGroup A₂] [Module ℂ A₂]
    [AddCommGroup B₁] [Module ℂ B₁] [AddCommGroup B₂] [Module ℂ B₂]
    [AddCommGroup C₁] [Module ℂ C₁] [AddCommGroup C₂] [Module ℂ C₂]
    (p : A₂) (q : B₂) (c : C₁) :
    assocAux A₁ A₂ B₁ B₂ C₁ C₂
        ((((0 : A₁ ⊗[ℂ] B₁), p ⊗ₜ[ℂ] q) ⊗ₜ[ℂ] c, 0) :
        ((((A₁ ⊗[ℂ] B₁) × (A₂ ⊗[ℂ] B₂)) ⊗[ℂ] C₁) ×
        (((A₁ ⊗[ℂ] B₂) × (A₂ ⊗[ℂ] B₁)) ⊗[ℂ] C₂))) =
      (((0 : A₁ ⊗[ℂ] ((B₁ ⊗[ℂ] C₁) × (B₂ ⊗[ℂ] C₂))),
          p ⊗ₜ[ℂ] (((0 : B₁ ⊗[ℂ] C₂), q ⊗ₜ[ℂ] c) :
            (B₁ ⊗[ℂ] C₂) × (B₂ ⊗[ℂ] C₁))) :
        ((A₁ ⊗[ℂ] ((B₁ ⊗[ℂ] C₁) × (B₂ ⊗[ℂ] C₂))) ×
        (A₂ ⊗[ℂ] ((B₁ ⊗[ℂ] C₂) × (B₂ ⊗[ℂ] C₁))))) := by
  unfold assocAux
  simp only [LinearEquiv.trans_apply, LinearEquiv.prodCongr_apply,
    prod_fst_zero, prod_snd_zero, prod_mk_zero, TensorProduct.prodLeft_tmul,
    TensorProduct.zero_tmul, map_zero, prod4Perm_apply,
    TensorProduct.assoc_tmul, prodRight_symm_tmul_snd]

/-- The associator block on a pure tensor of the `A₁ ⊗ B₂` summand
with `C₂`. -/
@[simp]
lemma assocAux_eo {A₁ A₂ B₁ B₂ C₁ C₂ : Type*}
    [AddCommGroup A₁] [Module ℂ A₁] [AddCommGroup A₂] [Module ℂ A₂]
    [AddCommGroup B₁] [Module ℂ B₁] [AddCommGroup B₂] [Module ℂ B₂]
    [AddCommGroup C₁] [Module ℂ C₁] [AddCommGroup C₂] [Module ℂ C₂]
    (a : A₁) (b : B₂) (c : C₂) :
    assocAux A₁ A₂ B₁ B₂ C₁ C₂
        (((0 : ((A₁ ⊗[ℂ] B₁) × (A₂ ⊗[ℂ] B₂)) ⊗[ℂ] C₁), (a ⊗ₜ[ℂ] b, 0) ⊗ₜ[ℂ] c) :
        ((((A₁ ⊗[ℂ] B₁) × (A₂ ⊗[ℂ] B₂)) ⊗[ℂ] C₁) ×
        (((A₁ ⊗[ℂ] B₂) × (A₂ ⊗[ℂ] B₁)) ⊗[ℂ] C₂))) =
      ((a ⊗ₜ[ℂ] (((0 : B₁ ⊗[ℂ] C₁), b ⊗ₜ[ℂ] c) : (B₁ ⊗[ℂ] C₁) × (B₂ ⊗[ℂ] C₂)),
        0) :
        ((A₁ ⊗[ℂ] ((B₁ ⊗[ℂ] C₁) × (B₂ ⊗[ℂ] C₂))) ×
        (A₂ ⊗[ℂ] ((B₁ ⊗[ℂ] C₂) × (B₂ ⊗[ℂ] C₁))))) := by
  unfold assocAux
  simp only [LinearEquiv.trans_apply, LinearEquiv.prodCongr_apply,
    prod_fst_zero, prod_snd_zero, prod_mk_zero, TensorProduct.prodLeft_tmul,
    TensorProduct.zero_tmul, map_zero, prod4Perm_apply,
    TensorProduct.assoc_tmul, prodRight_symm_tmul_snd]

/-- The associator block on a pure tensor of the `A₂ ⊗ B₁` summand
with `C₂`. -/
@[simp]
lemma assocAux_oe {A₁ A₂ B₁ B₂ C₁ C₂ : Type*}
    [AddCommGroup A₁] [Module ℂ A₁] [AddCommGroup A₂] [Module ℂ A₂]
    [AddCommGroup B₁] [Module ℂ B₁] [AddCommGroup B₂] [Module ℂ B₂]
    [AddCommGroup C₁] [Module ℂ C₁] [AddCommGroup C₂] [Module ℂ C₂]
    (p : A₂) (q : B₁) (c : C₂) :
    assocAux A₁ A₂ B₁ B₂ C₁ C₂
        (((0 : ((A₁ ⊗[ℂ] B₁) × (A₂ ⊗[ℂ] B₂)) ⊗[ℂ] C₁), ((0 : A₁ ⊗[ℂ] B₂), p
          ⊗ₜ[ℂ] q) ⊗ₜ[ℂ] c) :
        ((((A₁ ⊗[ℂ] B₁) × (A₂ ⊗[ℂ] B₂)) ⊗[ℂ] C₁) ×
        (((A₁ ⊗[ℂ] B₂) × (A₂ ⊗[ℂ] B₁)) ⊗[ℂ] C₂))) =
      (((0 : A₁ ⊗[ℂ] ((B₁ ⊗[ℂ] C₁) × (B₂ ⊗[ℂ] C₂))),
          p ⊗ₜ[ℂ] ((q ⊗ₜ[ℂ] c, 0) :
            (B₁ ⊗[ℂ] C₂) × (B₂ ⊗[ℂ] C₁))) :
        ((A₁ ⊗[ℂ] ((B₁ ⊗[ℂ] C₁) × (B₂ ⊗[ℂ] C₂))) ×
        (A₂ ⊗[ℂ] ((B₁ ⊗[ℂ] C₂) × (B₂ ⊗[ℂ] C₁))))) := by
  unfold assocAux
  simp only [LinearEquiv.trans_apply, LinearEquiv.prodCongr_apply,
    prod_fst_zero, prod_snd_zero, prod_mk_zero, TensorProduct.prodLeft_tmul,
    TensorProduct.zero_tmul, map_zero, prod4Perm_apply,
    TensorProduct.assoc_tmul, prodRight_symm_tmul_fst]

-- The inverse of `assocAux` on the image generators, by
-- `symm_apply_eq` from the forward lemmas.

/-- The inverse associator block on a pure tensor of `A₁` with the
`B₁ ⊗ C₁` summand. -/
@[simp]
lemma assocAux_symm_ee {A₁ A₂ B₁ B₂ C₁ C₂ : Type*}
    [AddCommGroup A₁] [Module ℂ A₁] [AddCommGroup A₂] [Module ℂ A₂]
    [AddCommGroup B₁] [Module ℂ B₁] [AddCommGroup B₂] [Module ℂ B₂]
    [AddCommGroup C₁] [Module ℂ C₁] [AddCommGroup C₂] [Module ℂ C₂]
    (a : A₁) (b : B₁) (c : C₁) :
    (assocAux A₁ A₂ B₁ B₂ C₁ C₂).symm
        ((a ⊗ₜ[ℂ] ((b ⊗ₜ[ℂ] c, 0) : (B₁ ⊗[ℂ] C₁) × (B₂ ⊗[ℂ] C₂)), 0) :
        ((A₁ ⊗[ℂ] ((B₁ ⊗[ℂ] C₁) × (B₂ ⊗[ℂ] C₂))) ×
        (A₂ ⊗[ℂ] ((B₁ ⊗[ℂ] C₂) × (B₂ ⊗[ℂ] C₁))))) =
      (((a ⊗ₜ[ℂ] b, 0) ⊗ₜ[ℂ] c, 0) :
        ((((A₁ ⊗[ℂ] B₁) × (A₂ ⊗[ℂ] B₂)) ⊗[ℂ] C₁) ×
        (((A₁ ⊗[ℂ] B₂) × (A₂ ⊗[ℂ] B₁)) ⊗[ℂ] C₂))) := by
  rw [LinearEquiv.symm_apply_eq, assocAux_ee]

/-- The inverse associator block on a pure tensor of `A₂` with the
`B₂ ⊗ C₁` summand. -/
@[simp]
lemma assocAux_symm_oo {A₁ A₂ B₁ B₂ C₁ C₂ : Type*}
    [AddCommGroup A₁] [Module ℂ A₁] [AddCommGroup A₂] [Module ℂ A₂]
    [AddCommGroup B₁] [Module ℂ B₁] [AddCommGroup B₂] [Module ℂ B₂]
    [AddCommGroup C₁] [Module ℂ C₁] [AddCommGroup C₂] [Module ℂ C₂]
    (p : A₂) (q : B₂) (c : C₁) :
    (assocAux A₁ A₂ B₁ B₂ C₁ C₂).symm
        (((0 : A₁ ⊗[ℂ] ((B₁ ⊗[ℂ] C₁) × (B₂ ⊗[ℂ] C₂))),
          p ⊗ₜ[ℂ] (((0 : B₁ ⊗[ℂ] C₂), q ⊗ₜ[ℂ] c) :
            (B₁ ⊗[ℂ] C₂) × (B₂ ⊗[ℂ] C₁))) :
        ((A₁ ⊗[ℂ] ((B₁ ⊗[ℂ] C₁) × (B₂ ⊗[ℂ] C₂))) ×
        (A₂ ⊗[ℂ] ((B₁ ⊗[ℂ] C₂) × (B₂ ⊗[ℂ] C₁))))) =
      ((((0 : A₁ ⊗[ℂ] B₁), p ⊗ₜ[ℂ] q) ⊗ₜ[ℂ] c, 0) :
        ((((A₁ ⊗[ℂ] B₁) × (A₂ ⊗[ℂ] B₂)) ⊗[ℂ] C₁) ×
        (((A₁ ⊗[ℂ] B₂) × (A₂ ⊗[ℂ] B₁)) ⊗[ℂ] C₂))) := by
  rw [LinearEquiv.symm_apply_eq, assocAux_oo]

/-- The inverse associator block on a pure tensor of `A₁` with the
`B₂ ⊗ C₂` summand. -/
@[simp]
lemma assocAux_symm_eo {A₁ A₂ B₁ B₂ C₁ C₂ : Type*}
    [AddCommGroup A₁] [Module ℂ A₁] [AddCommGroup A₂] [Module ℂ A₂]
    [AddCommGroup B₁] [Module ℂ B₁] [AddCommGroup B₂] [Module ℂ B₂]
    [AddCommGroup C₁] [Module ℂ C₁] [AddCommGroup C₂] [Module ℂ C₂]
    (a : A₁) (b : B₂) (c : C₂) :
    (assocAux A₁ A₂ B₁ B₂ C₁ C₂).symm
        ((a ⊗ₜ[ℂ] (((0 : B₁ ⊗[ℂ] C₁), b ⊗ₜ[ℂ] c) : (B₁ ⊗[ℂ] C₁) × (B₂ ⊗[ℂ] C₂)),
          0) :
        ((A₁ ⊗[ℂ] ((B₁ ⊗[ℂ] C₁) × (B₂ ⊗[ℂ] C₂))) ×
        (A₂ ⊗[ℂ] ((B₁ ⊗[ℂ] C₂) × (B₂ ⊗[ℂ] C₁))))) =
      (((0 : ((A₁ ⊗[ℂ] B₁) × (A₂ ⊗[ℂ] B₂)) ⊗[ℂ] C₁), (a ⊗ₜ[ℂ] b, 0) ⊗ₜ[ℂ] c) :
        ((((A₁ ⊗[ℂ] B₁) × (A₂ ⊗[ℂ] B₂)) ⊗[ℂ] C₁) ×
        (((A₁ ⊗[ℂ] B₂) × (A₂ ⊗[ℂ] B₁)) ⊗[ℂ] C₂))) := by
  rw [LinearEquiv.symm_apply_eq, assocAux_eo]

/-- The inverse associator block on a pure tensor of `A₂` with the
`B₁ ⊗ C₂` summand. -/
@[simp]
lemma assocAux_symm_oe {A₁ A₂ B₁ B₂ C₁ C₂ : Type*}
    [AddCommGroup A₁] [Module ℂ A₁] [AddCommGroup A₂] [Module ℂ A₂]
    [AddCommGroup B₁] [Module ℂ B₁] [AddCommGroup B₂] [Module ℂ B₂]
    [AddCommGroup C₁] [Module ℂ C₁] [AddCommGroup C₂] [Module ℂ C₂]
    (p : A₂) (q : B₁) (c : C₂) :
    (assocAux A₁ A₂ B₁ B₂ C₁ C₂).symm
        (((0 : A₁ ⊗[ℂ] ((B₁ ⊗[ℂ] C₁) × (B₂ ⊗[ℂ] C₂))),
          p ⊗ₜ[ℂ] ((q ⊗ₜ[ℂ] c, 0) :
            (B₁ ⊗[ℂ] C₂) × (B₂ ⊗[ℂ] C₁))) :
        ((A₁ ⊗[ℂ] ((B₁ ⊗[ℂ] C₁) × (B₂ ⊗[ℂ] C₂))) ×
        (A₂ ⊗[ℂ] ((B₁ ⊗[ℂ] C₂) × (B₂ ⊗[ℂ] C₁))))) =
      (((0 : ((A₁ ⊗[ℂ] B₁) × (A₂ ⊗[ℂ] B₂)) ⊗[ℂ] C₁), ((0 : A₁ ⊗[ℂ] B₂), p ⊗ₜ[ℂ]
        q) ⊗ₜ[ℂ] c) :
        ((((A₁ ⊗[ℂ] B₁) × (A₂ ⊗[ℂ] B₂)) ⊗[ℂ] C₁) ×
        (((A₁ ⊗[ℂ] B₂) × (A₂ ⊗[ℂ] B₁)) ⊗[ℂ] C₂))) := by
  rw [LinearEquiv.symm_apply_eq, assocAux_oe]

-- Computation of the Koszul blocks on the two generator shapes;
-- the sign of the even block is emitted outside the pair so the
-- associator computation lemmas can fire beneath it.
/-- The even Koszul block on the first summand: plain
commutation, no sign. -/
@[simp]
lemma koszulEvenAux_fst {A B C D : Type*}
    [AddCommGroup A] [Module ℂ A] [AddCommGroup B] [Module ℂ B]
    [AddCommGroup C] [Module ℂ C] [AddCommGroup D] [Module ℂ D]
    (a : A) (b : B) :
    koszulEvenAux A B C D ((a ⊗ₜ[ℂ] b, 0) : (A ⊗[ℂ] B) × (C ⊗[ℂ] D)) =
      ((b ⊗ₜ[ℂ] a, 0) : (B ⊗[ℂ] A) × (D ⊗[ℂ] C)) := by
  simp [koszulEvenAux]

/-- **The Koszul sign**: on the second summand — the odd⊗odd
block — the even block commutes *and* negates. -/
@[simp]
lemma koszulEvenAux_snd {A B C D : Type*}
    [AddCommGroup A] [Module ℂ A] [AddCommGroup B] [Module ℂ B]
    [AddCommGroup C] [Module ℂ C] [AddCommGroup D] [Module ℂ D]
    (c : C) (d : D) :
    koszulEvenAux A B C D ((0, c ⊗ₜ[ℂ] d) : (A ⊗[ℂ] B) × (C ⊗[ℂ] D)) =
      -(((0, d ⊗ₜ[ℂ] c)) : (B ⊗[ℂ] A) × (D ⊗[ℂ] C)) := by
  simp only [koszulEvenAux, LinearMap.prodMap_apply, map_zero,
    LinearMap.neg_apply, LinearEquiv.coe_toLinearMap,
    TensorProduct.comm_tmul]
  ext <;> simp

/-- The odd Koszul block on the first summand: commutation into
the other summand, no sign. -/
@[simp]
lemma koszulOddAux_fst {A B C D : Type*}
    [AddCommGroup A] [Module ℂ A] [AddCommGroup B] [Module ℂ B]
    [AddCommGroup C] [Module ℂ C] [AddCommGroup D] [Module ℂ D]
    (a : A) (b : B) :
    koszulOddAux A B C D ((a ⊗ₜ[ℂ] b, 0) : (A ⊗[ℂ] B) × (C ⊗[ℂ] D)) =
      ((0, b ⊗ₜ[ℂ] a) : (D ⊗[ℂ] C) × (B ⊗[ℂ] A)) := by
  simp [koszulOddAux]

/-- The odd Koszul block on the second summand: likewise
unsigned — only the odd⊗odd block carries the sign. -/
@[simp]
lemma koszulOddAux_snd {A B C D : Type*}
    [AddCommGroup A] [Module ℂ A] [AddCommGroup B] [Module ℂ B]
    [AddCommGroup C] [Module ℂ C] [AddCommGroup D] [Module ℂ D]
    (c : C) (d : D) :
    koszulOddAux A B C D ((0, c ⊗ₜ[ℂ] d) : (A ⊗[ℂ] B) × (C ⊗[ℂ] D)) =
      ((d ⊗ₜ[ℂ] c, 0) : (D ⊗[ℂ] C) × (B ⊗[ℂ] A)) := by
  simp [koszulOddAux]

-- Sign bookkeeping for the hexagon proofs: negations are kept
-- outside pairs (the `Prod.neg_mk` normal form is disabled there),
-- so single-sided negated pairs must re-assemble to negated pairs.
/-- A left-negated pair is a negated pair. -/
lemma prod_mk_neg_left {A B : Type*}
    [AddCommGroup A] [AddCommGroup B] (u : A) :
    ((-u, (0 : B)) : A × B) = -(u, 0) := by
  ext <;> simp

/-- A right-negated pair is a negated pair. -/
lemma prod_mk_neg_right {A B : Type*}
    [AddCommGroup A] [AddCommGroup B] (v : B) :
    (((0 : A), -v) : A × B) = -((0 : A), v) := by
  ext <;> simp

/-- The triangle coherence of the module-level associator block
against the unit slots `ℂ` (even) and `PUnit` (odd).  Both graded
components of the SuperVect triangle are instantiations. -/
theorem assocAux_triangle (A₁ A₂ B₁ B₂ : Type*)
    [AddCommGroup A₁] [Module ℂ A₁] [AddCommGroup A₂] [Module ℂ A₂]
    [AddCommGroup B₁] [Module ℂ B₁] [AddCommGroup B₂] [Module ℂ B₂] :
    LinearMap.prodMap
        (TensorProduct.map LinearMap.id
          ((TensorProduct.lid ℂ B₁).toLinearMap ∘ₗ
            LinearMap.fst ℂ (ℂ ⊗[ℂ] B₁) (PUnit ⊗[ℂ] B₂)))
        (TensorProduct.map LinearMap.id
          ((TensorProduct.lid ℂ B₂).toLinearMap ∘ₗ
            LinearMap.fst ℂ (ℂ ⊗[ℂ] B₂) (PUnit ⊗[ℂ] B₁))) ∘ₗ
      (assocAux A₁ A₂ ℂ PUnit B₁ B₂).toLinearMap =
    LinearMap.prodMap
        (TensorProduct.map
          ((TensorProduct.rid ℂ A₁).toLinearMap ∘ₗ
            LinearMap.fst ℂ (A₁ ⊗[ℂ] ℂ) (A₂ ⊗[ℂ] PUnit)) LinearMap.id)
        (TensorProduct.map
          ((TensorProduct.rid ℂ A₂).toLinearMap ∘ₗ
            LinearMap.snd ℂ (A₁ ⊗[ℂ] PUnit) (A₂ ⊗[ℂ] ℂ)) LinearMap.id) := by
  ext x
  all_goals simp

/-- The forward hexagon for the even graded component, at the
module level: braiding past a tensor product in two steps agrees
with braiding past its factors. -/
theorem koszulAux_hexagon_fwd_even (A₁ A₂ B₁ B₂ C₁ C₂ : Type*)
    [AddCommGroup A₁] [Module ℂ A₁] [AddCommGroup A₂] [Module ℂ A₂]
    [AddCommGroup B₁] [Module ℂ B₁] [AddCommGroup B₂] [Module ℂ B₂]
    [AddCommGroup C₁] [Module ℂ C₁] [AddCommGroup C₂] [Module ℂ C₂] :
    ((assocAux B₁ B₂ C₁ C₂ A₁ A₂).toLinearMap ∘ₗ
      koszulEvenAux A₁ ((B₁ ⊗[ℂ] C₁) × (B₂ ⊗[ℂ] C₂)) A₂ ((B₁ ⊗[ℂ] C₂) × (B₂ ⊗[ℂ]
        C₁))) ∘ₗ
    (assocAux A₁ A₂ B₁ B₂ C₁ C₂).toLinearMap =
    (LinearMap.prodMap
        (TensorProduct.map LinearMap.id (koszulEvenAux A₁ C₁ A₂ C₂))
        (TensorProduct.map LinearMap.id (koszulOddAux A₁ C₂ A₂ C₁)) ∘ₗ
      (assocAux B₁ B₂ A₁ A₂ C₁ C₂).toLinearMap) ∘ₗ
    LinearMap.prodMap
        (TensorProduct.map (koszulEvenAux A₁ B₁ A₂ B₂) LinearMap.id)
        (TensorProduct.map (koszulOddAux A₁ B₂ A₂ B₁) LinearMap.id) := by
  ext x
  all_goals simp [-Prod.neg_mk, TensorProduct.neg_tmul,
    TensorProduct.tmul_neg, prod_mk_neg_left, prod_mk_neg_right]

/-- The forward hexagon for the odd graded component. -/
theorem koszulAux_hexagon_fwd_odd (A₁ A₂ B₁ B₂ C₁ C₂ : Type*)
    [AddCommGroup A₁] [Module ℂ A₁] [AddCommGroup A₂] [Module ℂ A₂]
    [AddCommGroup B₁] [Module ℂ B₁] [AddCommGroup B₂] [Module ℂ B₂]
    [AddCommGroup C₁] [Module ℂ C₁] [AddCommGroup C₂] [Module ℂ C₂] :
    ((assocAux B₁ B₂ C₁ C₂ A₂ A₁).toLinearMap ∘ₗ
      koszulOddAux A₁ ((B₁ ⊗[ℂ] C₂) × (B₂ ⊗[ℂ] C₁)) A₂ ((B₁ ⊗[ℂ] C₁) × (B₂ ⊗[ℂ]
        C₂))) ∘ₗ
    (assocAux A₁ A₂ B₁ B₂ C₂ C₁).toLinearMap =
    (LinearMap.prodMap
        (TensorProduct.map LinearMap.id (koszulOddAux A₁ C₂ A₂ C₁))
        (TensorProduct.map LinearMap.id (koszulEvenAux A₁ C₁ A₂ C₂)) ∘ₗ
      (assocAux B₁ B₂ A₁ A₂ C₂ C₁).toLinearMap) ∘ₗ
    LinearMap.prodMap
        (TensorProduct.map (koszulEvenAux A₁ B₁ A₂ B₂) LinearMap.id)
        (TensorProduct.map (koszulOddAux A₁ B₂ A₂ B₁) LinearMap.id) := by
  ext x
  all_goals simp [-Prod.neg_mk, TensorProduct.neg_tmul,
    TensorProduct.tmul_neg, prod_mk_neg_left]

/-- The reverse hexagon for the even graded component, phrased
through the inverse associator blocks. -/
theorem koszulAux_hexagon_rev_even (A₁ A₂ B₁ B₂ C₁ C₂ : Type*)
    [AddCommGroup A₁] [Module ℂ A₁] [AddCommGroup A₂] [Module ℂ A₂]
    [AddCommGroup B₁] [Module ℂ B₁] [AddCommGroup B₂] [Module ℂ B₂]
    [AddCommGroup C₁] [Module ℂ C₁] [AddCommGroup C₂] [Module ℂ C₂] :
    ((assocAux C₁ C₂ A₁ A₂ B₁ B₂).symm.toLinearMap ∘ₗ
      koszulEvenAux ((A₁ ⊗[ℂ] B₁) × (A₂ ⊗[ℂ] B₂)) C₁ ((A₁ ⊗[ℂ] B₂) × (A₂ ⊗[ℂ]
        B₁)) C₂) ∘ₗ
    (assocAux A₁ A₂ B₁ B₂ C₁ C₂).symm.toLinearMap =
    (LinearMap.prodMap
        (TensorProduct.map (koszulEvenAux A₁ C₁ A₂ C₂) LinearMap.id)
        (TensorProduct.map (koszulOddAux A₁ C₂ A₂ C₁) LinearMap.id) ∘ₗ
      (assocAux A₁ A₂ C₁ C₂ B₁ B₂).symm.toLinearMap) ∘ₗ
    LinearMap.prodMap
        (TensorProduct.map LinearMap.id (koszulEvenAux B₁ C₁ B₂ C₂))
        (TensorProduct.map LinearMap.id (koszulOddAux B₁ C₂ B₂ C₁)) := by
  ext x
  all_goals simp [-Prod.neg_mk, TensorProduct.neg_tmul,
    TensorProduct.tmul_neg, prod_mk_neg_left, prod_mk_neg_right]

/-- The reverse hexagon for the odd graded component. -/
theorem koszulAux_hexagon_rev_odd (A₁ A₂ B₁ B₂ C₁ C₂ : Type*)
    [AddCommGroup A₁] [Module ℂ A₁] [AddCommGroup A₂] [Module ℂ A₂]
    [AddCommGroup B₁] [Module ℂ B₁] [AddCommGroup B₂] [Module ℂ B₂]
    [AddCommGroup C₁] [Module ℂ C₁] [AddCommGroup C₂] [Module ℂ C₂] :
    ((assocAux C₁ C₂ A₁ A₂ B₂ B₁).symm.toLinearMap ∘ₗ
      koszulOddAux ((A₁ ⊗[ℂ] B₁) × (A₂ ⊗[ℂ] B₂)) C₂ ((A₁ ⊗[ℂ] B₂) × (A₂ ⊗[ℂ]
        B₁)) C₁) ∘ₗ
    (assocAux A₁ A₂ B₁ B₂ C₂ C₁).symm.toLinearMap =
    (LinearMap.prodMap
        (TensorProduct.map (koszulEvenAux A₁ C₁ A₂ C₂) LinearMap.id)
        (TensorProduct.map (koszulOddAux A₁ C₂ A₂ C₁) LinearMap.id) ∘ₗ
      (assocAux A₁ A₂ C₁ C₂ B₂ B₁).symm.toLinearMap) ∘ₗ
    LinearMap.prodMap
        (TensorProduct.map LinearMap.id (koszulOddAux B₁ C₂ B₂ C₁))
        (TensorProduct.map LinearMap.id (koszulEvenAux B₁ C₁ B₂ C₂)) := by
  ext x
  all_goals simp [-Prod.neg_mk, TensorProduct.neg_tmul,
    TensorProduct.tmul_neg, prod_mk_neg_right]

/-- The pentagon coherence of the module-level associator block:
both routes from a four-fold graded product to its right-nested
form agree.  Both graded components of the SuperVect pentagon are
instantiations. -/
theorem assocAux_pentagon (A₁ A₂ B₁ B₂ C₁ C₂ D₁ D₂ : Type*)
    [AddCommGroup A₁] [Module ℂ A₁] [AddCommGroup A₂] [Module ℂ A₂]
    [AddCommGroup B₁] [Module ℂ B₁] [AddCommGroup B₂] [Module ℂ B₂]
    [AddCommGroup C₁] [Module ℂ C₁] [AddCommGroup C₂] [Module ℂ C₂]
    [AddCommGroup D₁] [Module ℂ D₁] [AddCommGroup D₂] [Module ℂ D₂] :
    (LinearMap.prodMap
        (TensorProduct.map LinearMap.id (assocAux B₁ B₂ C₁ C₂ D₁
          D₂).toLinearMap)
        (TensorProduct.map LinearMap.id (assocAux B₁ B₂ C₁ C₂ D₂
          D₁).toLinearMap) ∘ₗ
      (assocAux A₁ A₂ ((B₁ ⊗[ℂ] C₁) × (B₂ ⊗[ℂ] C₂))
        ((B₁ ⊗[ℂ] C₂) × (B₂ ⊗[ℂ] C₁)) D₁ D₂).toLinearMap) ∘ₗ
    LinearMap.prodMap
        (TensorProduct.map (assocAux A₁ A₂ B₁ B₂ C₁ C₂).toLinearMap
          LinearMap.id)
        (TensorProduct.map (assocAux A₁ A₂ B₁ B₂ C₂ C₁).toLinearMap
          LinearMap.id) =
    (assocAux A₁ A₂ B₁ B₂ ((C₁ ⊗[ℂ] D₁) × (C₂ ⊗[ℂ] D₂))
      ((C₁ ⊗[ℂ] D₂) × (C₂ ⊗[ℂ] D₁))).toLinearMap ∘ₗ
    (assocAux ((A₁ ⊗[ℂ] B₁) × (A₂ ⊗[ℂ] B₂))
      ((A₁ ⊗[ℂ] B₂) × (A₂ ⊗[ℂ] B₁)) C₁ C₂ D₁ D₂).toLinearMap := by
  ext x
  all_goals simp

/-! ### Component projection lemmas -/

/-- The even component of a categorical composite. -/
@[simp]
theorem cat_comp_evenMap {V W X : SuperVect} (f : V ⟶ W) (g : W ⟶ X) :
    (f ≫ g).evenMap = g.evenMap.comp f.evenMap := rfl

/-- The odd component of a categorical composite. -/
@[simp]
theorem cat_comp_oddMap {V W X : SuperVect} (f : V ⟶ W) (g : W ⟶ X) :
    (f ≫ g).oddMap = g.oddMap.comp f.oddMap := rfl

/-- The even component of a categorical identity. -/
@[simp]
theorem cat_id_evenMap (V : SuperVect) :
    (𝟙 V : Hom V V).evenMap = LinearMap.id := rfl

/-- The odd component of a categorical identity. -/
@[simp]
theorem cat_id_oddMap (V : SuperVect) :
    (𝟙 V : Hom V V).oddMap = LinearMap.id := rfl

/-- The even component of a tensor of morphisms: even⊗even and
odd⊗odd in parallel. -/
@[simp]
theorem tensorHom_evenMap {V₁ V₂ W₁ W₂ : SuperVect}
    (f : Hom V₁ V₂) (g : Hom W₁ W₂) :
    (tensorHom f g).evenMap = LinearMap.prodMap
      (TensorProduct.map f.evenMap g.evenMap)
      (TensorProduct.map f.oddMap g.oddMap) := rfl

/-- The odd component of a tensor of morphisms: even⊗odd and
odd⊗even in parallel. -/
@[simp]
theorem tensorHom_oddMap {V₁ V₂ W₁ W₂ : SuperVect}
    (f : Hom V₁ V₂) (g : Hom W₁ W₂) :
    (tensorHom f g).oddMap = LinearMap.prodMap
      (TensorProduct.map f.evenMap g.oddMap)
      (TensorProduct.map f.oddMap g.evenMap) := rfl

/-- The associator's even component is the even associator
equivalence. -/
@[simp]
theorem associator_hom_evenMap (V W X : SuperVect) :
    ((associator V W X).hom).evenMap =
      (assocEvenEquiv V W X).toLinearMap := rfl

/-- The associator's odd component is the odd associator
equivalence. -/
@[simp]
theorem associator_hom_oddMap (V W X : SuperVect) :
    ((associator V W X).hom).oddMap =
      (assocOddEquiv V W X).toLinearMap := rfl

/-- The inverse associator's even component. -/
@[simp]
theorem associator_inv_evenMap (V W X : SuperVect) :
    ((associator V W X).inv).evenMap =
      (assocEvenEquiv V W X).symm.toLinearMap := rfl

/-- The inverse associator's odd component. -/
@[simp]
theorem associator_inv_oddMap (V W X : SuperVect) :
    ((associator V W X).inv).oddMap =
      (assocOddEquiv V W X).symm.toLinearMap := rfl

/-- The left unitor's even component: the unit's odd part is zero,
so only the first summand survives. -/
@[simp]
theorem leftUnitor_hom_evenMap (V : SuperVect) :
    ((leftUnitor V).hom).evenMap =
      (TensorProduct.lid ℂ V.even).toLinearMap.comp (LinearMap.fst ℂ _ _) := rfl

/-- The left unitor's odd component. -/
@[simp]
theorem leftUnitor_hom_oddMap (V : SuperVect) :
    ((leftUnitor V).hom).oddMap =
      (TensorProduct.lid ℂ V.odd).toLinearMap.comp (LinearMap.fst ℂ _ _) := rfl

/-- The right unitor's even component. -/
@[simp]
theorem rightUnitor_hom_evenMap (V : SuperVect) :
    ((rightUnitor V).hom).evenMap =
      (TensorProduct.rid ℂ V.even).toLinearMap.comp (LinearMap.fst ℂ _ _) := rfl

/-- The right unitor's odd component: here it is the *second*
summand that survives, the unit sitting on the right. -/
@[simp]
theorem rightUnitor_hom_oddMap (V : SuperVect) :
    ((rightUnitor V).hom).oddMap =
      (TensorProduct.rid ℂ V.odd).toLinearMap.comp (LinearMap.snd ℂ _ _) := rfl

/-- The braiding's even component. -/
@[simp]
theorem koszulBraiding_evenMap (V W : SuperVect) :
    (koszulBraiding V W).evenMap = koszulBraidingEven V W := rfl

/-- The braiding's odd component. -/
@[simp]
theorem koszulBraiding_oddMap (V W : SuperVect) :
    (koszulBraiding V W).oddMap = koszulBraidingOdd V W := rfl

/-! ### Monoidal structure -/

/-- The monoidal category structure on SuperVect: graded tensor
product, ℂ unit, standard associator/unitors. -/
instance instMonoidalCategoryStruct : MonoidalCategoryStruct SuperVect where
  tensorObj := tensorObj
  whiskerLeft := fun (X : SuperVect) {Y₁ : SuperVect} {Y₂ : SuperVect}
    (f : Y₁ ⟶ Y₂) =>
    SuperVect.tensorHom (Hom.id X) f
  whiskerRight := fun {X₁ : SuperVect} {X₂ : SuperVect} (f : X₁ ⟶ X₂)
    (Y : SuperVect) =>
    SuperVect.tensorHom f (Hom.id Y)
  tensorHom := fun f g => SuperVect.tensorHom f g
  tensorUnit := tensorUnit
  associator := associator
  leftUnitor := leftUnitor
  rightUnitor := rightUnitor

/-! ### MonoidalCategory axioms -/

/-- `tensorHom id id = id`: the tensor of identity morphisms is
the identity on the tensor product. -/
theorem tensorHom_id_id (X₁ X₂ : SuperVect) :
    SuperVect.tensorHom (Hom.id X₁) (Hom.id X₂) = Hom.id (tensorObj X₁ X₂) := by
  apply Hom.ext <;> {
    change LinearMap.prodMap
        (TensorProduct.map LinearMap.id LinearMap.id)
        (TensorProduct.map LinearMap.id LinearMap.id) = LinearMap.id
    simp [TensorProduct.map_id] }

/-- Composition distributes over tensor product of morphisms. -/
theorem tensorHom_comp (X₁ Y₁ Z₁ X₂ Y₂ Z₂ : SuperVect)
    (f₁ : Hom X₁ Y₁) (f₂ : Hom X₂ Y₂) (g₁ : Hom Y₁ Z₁) (g₂ : Hom Y₂ Z₂) :
    Hom.comp (SuperVect.tensorHom g₁ g₂) (SuperVect.tensorHom f₁ f₂) =
    SuperVect.tensorHom (Hom.comp g₁ f₁) (Hom.comp g₂ f₂) := by
  apply Hom.ext <;> {
    change LinearMap.comp _ _ = _
    simp only [Hom.comp, SuperVect.tensorHom]
    change (LinearMap.prodMap _ _).comp (LinearMap.prodMap _ _) =
           LinearMap.prodMap _ _
    simp [LinearMap.prodMap_comp, TensorProduct.map_comp] }

/-- The full monoidal category structure on SuperVect, constructed
via `ofTensorHom`. -/
instance instMonoidalCategory : MonoidalCategory SuperVect :=
  MonoidalCategory.ofTensorHom
    (id_tensorHom_id := fun X₁ X₂ => tensorHom_id_id X₁ X₂)
    (id_tensorHom := fun _ {_ _} _ => rfl)
    (tensorHom_id := fun {_ _} _ _ => rfl)
    (tensorHom_comp_tensorHom := fun {_ _ _ _ _ _} f₁ f₂ g₁ g₂ => by
      change Hom.comp (SuperVect.tensorHom g₁ g₂) (SuperVect.tensorHom f₁ f₂) =
           SuperVect.tensorHom (Hom.comp g₁ f₁) (Hom.comp g₂ f₂)
      exact tensorHom_comp _ _ _ _ _ _ f₁ f₂ g₁ g₂)
    -- ═══════ ASSOCIATOR NATURALITY ═══════
    (associator_naturality := fun {X₁ X₂ X₃ Y₁ Y₂ Y₃} f₁ f₂ f₃ => by
      apply Hom.ext
      · change
          (assocAux Y₁.even Y₁.odd Y₂.even Y₂.odd Y₃.even Y₃.odd).toLinearMap ∘ₗ
          LinearMap.prodMap
              (TensorProduct.map
                (LinearMap.prodMap (TensorProduct.map f₁.evenMap f₂.evenMap)
                  (TensorProduct.map f₁.oddMap f₂.oddMap)) f₃.evenMap)
              (TensorProduct.map
                (LinearMap.prodMap (TensorProduct.map f₁.evenMap f₂.oddMap)
                  (TensorProduct.map f₁.oddMap f₂.evenMap)) f₃.oddMap) =
          LinearMap.prodMap
              (TensorProduct.map f₁.evenMap
                (LinearMap.prodMap (TensorProduct.map f₂.evenMap f₃.evenMap)
                  (TensorProduct.map f₂.oddMap f₃.oddMap)))
              (TensorProduct.map f₁.oddMap
                (LinearMap.prodMap (TensorProduct.map f₂.evenMap f₃.oddMap)
                  (TensorProduct.map f₂.oddMap f₃.evenMap))) ∘ₗ
          (assocAux X₁.even X₁.odd X₂.even X₂.odd X₃.even X₃.odd).toLinearMap
        ext x
        all_goals simp
      · change
          (assocAux Y₁.even Y₁.odd Y₂.even Y₂.odd Y₃.odd Y₃.even).toLinearMap ∘ₗ
          LinearMap.prodMap
              (TensorProduct.map
                (LinearMap.prodMap (TensorProduct.map f₁.evenMap f₂.evenMap)
                  (TensorProduct.map f₁.oddMap f₂.oddMap)) f₃.oddMap)
              (TensorProduct.map
                (LinearMap.prodMap (TensorProduct.map f₁.evenMap f₂.oddMap)
                  (TensorProduct.map f₁.oddMap f₂.evenMap)) f₃.evenMap) =
          LinearMap.prodMap
              (TensorProduct.map f₁.evenMap
                (LinearMap.prodMap (TensorProduct.map f₂.evenMap f₃.oddMap)
                  (TensorProduct.map f₂.oddMap f₃.evenMap)))
              (TensorProduct.map f₁.oddMap
                (LinearMap.prodMap (TensorProduct.map f₂.evenMap f₃.evenMap)
                  (TensorProduct.map f₂.oddMap f₃.oddMap))) ∘ₗ
          (assocAux X₁.even X₁.odd X₂.even X₂.odd X₃.odd X₃.even).toLinearMap
        ext x
        all_goals simp)
    -- ═══════ LEFT UNITOR NATURALITY ═══════
    (leftUnitor_naturality := fun {X Y} (f : X ⟶ Y) => by
      apply Hom.ext
      · -- even component
        change ((TensorProduct.lid ℂ Y.even).toLinearMap.comp (LinearMap.fst ℂ _
          _)).comp
            (LinearMap.prodMap (TensorProduct.map LinearMap.id f.evenMap)
              (TensorProduct.map LinearMap.id f.oddMap)) =
          f.evenMap.comp
            ((TensorProduct.lid ℂ X.even).toLinearMap.comp (LinearMap.fst ℂ _
              _))
        apply LinearMap.ext; intro ⟨x, y⟩
        simp only [LinearMap.comp_apply, LinearMap.fst_apply,
          LinearMap.prodMap_apply,
          LinearEquiv.coe_toLinearMap]
        induction x using TensorProduct.inductionOn with
        | tmul r m => simp [TensorProduct.lid_tmul, TensorProduct.map_tmul,
          map_smul]
        | add x₁ x₂ hx₁ hx₂ => simp only [map_add, hx₁, hx₂]
      · -- odd component
        change ((TensorProduct.lid ℂ Y.odd).toLinearMap.comp (LinearMap.fst ℂ _
          _)).comp
            (LinearMap.prodMap (TensorProduct.map LinearMap.id f.oddMap)
              (TensorProduct.map LinearMap.id f.evenMap)) =
          f.oddMap.comp
            ((TensorProduct.lid ℂ X.odd).toLinearMap.comp (LinearMap.fst ℂ _ _))
        apply LinearMap.ext; intro ⟨x, y⟩
        simp only [LinearMap.comp_apply, LinearMap.fst_apply,
          LinearMap.prodMap_apply,
          LinearEquiv.coe_toLinearMap]
        induction x using TensorProduct.inductionOn with
        | tmul r m => simp [TensorProduct.lid_tmul, TensorProduct.map_tmul,
          map_smul]
        | add x₁ x₂ hx₁ hx₂ => simp only [map_add, hx₁, hx₂])
    -- ═══════ RIGHT UNITOR NATURALITY ═══════
    (rightUnitor_naturality := fun {X Y} (f : X ⟶ Y) => by
      apply Hom.ext
      · -- even component: (rid ∘ fst) ∘ prodMap (map f.e id) (map f.o id) = f.e
        --   ∘ (rid ∘ fst)
        change ((TensorProduct.rid ℂ Y.even).toLinearMap.comp (LinearMap.fst ℂ _
          _)).comp
            (LinearMap.prodMap (TensorProduct.map f.evenMap LinearMap.id)
              (TensorProduct.map f.oddMap LinearMap.id)) =
          f.evenMap.comp
            ((TensorProduct.rid ℂ X.even).toLinearMap.comp (LinearMap.fst ℂ _
              _))
        apply LinearMap.ext; intro ⟨x, y⟩
        simp only [LinearMap.comp_apply, LinearMap.fst_apply,
          LinearMap.prodMap_apply,
          LinearEquiv.coe_toLinearMap]
        induction x using TensorProduct.inductionOn with
        | tmul m r => simp [TensorProduct.rid_tmul, TensorProduct.map_tmul,
          map_smul]
        | add x₁ x₂ hx₁ hx₂ => simp only [map_add, hx₁, hx₂]
      · -- odd component: (rid ∘ snd) ∘ prodMap (map f.e id) (map f.o id) = f.o
        --   ∘ (rid ∘ snd)
        change ((TensorProduct.rid ℂ Y.odd).toLinearMap.comp (LinearMap.snd ℂ _
          _)).comp
            (LinearMap.prodMap (TensorProduct.map f.evenMap LinearMap.id)
              (TensorProduct.map f.oddMap LinearMap.id)) =
          f.oddMap.comp
            ((TensorProduct.rid ℂ X.odd).toLinearMap.comp (LinearMap.snd ℂ _ _))
        apply LinearMap.ext; intro ⟨x, y⟩
        simp only [LinearMap.comp_apply, LinearMap.snd_apply,
          LinearMap.prodMap_apply,
          LinearEquiv.coe_toLinearMap]
        induction y using TensorProduct.inductionOn with
        | tmul m r => simp [TensorProduct.rid_tmul, TensorProduct.map_tmul,
          map_smul]
        | add y₁ y₂ hy₁ hy₂ => simp only [map_add, hy₁, hy₂])
    -- ═══════ PENTAGON AND TRIANGLE ═══════
    (pentagon := fun W X Y Z => by
      apply Hom.ext
      · exact assocAux_pentagon W.even W.odd X.even X.odd
          Y.even Y.odd Z.even Z.odd
      · exact assocAux_pentagon W.even W.odd X.even X.odd
          Y.even Y.odd Z.odd Z.even)
    (triangle := fun X Y => by
      apply Hom.ext
      · exact assocAux_triangle X.even X.odd Y.even Y.odd
      · exact assocAux_triangle X.even X.odd Y.odd Y.even)

/-! ### Braided and symmetric structure -/

private theorem koszulBraiding_naturality_right (X : SuperVect)
    {Y Z : SuperVect} (f : Y ⟶ Z) :
    MonoidalCategory.whiskerLeft X f ≫ (koszulBraidingIso X Z).hom =
      (koszulBraidingIso X Y).hom ≫ MonoidalCategory.whiskerRight f X := by
  apply Hom.ext
  · -- even component
    change (koszulBraidingEven X Z).comp
        (LinearMap.prodMap (TensorProduct.map LinearMap.id f.evenMap)
          (TensorProduct.map LinearMap.id f.oddMap)) =
      (LinearMap.prodMap (TensorProduct.map f.evenMap LinearMap.id)
          (TensorProduct.map f.oddMap LinearMap.id)).comp
        (koszulBraidingEven X Y)
    apply LinearMap.ext; intro ⟨x, y⟩
    simp only [LinearMap.comp_apply, LinearMap.prodMap_apply,
      koszulBraidingEven, koszulEvenAux,
      LinearMap.neg_apply, LinearEquiv.coe_toLinearMap, Prod.mk.injEq]
    refine ⟨?_, ?_⟩
    · induction x using TensorProduct.inductionOn with
      | tmul a b => simp [TensorProduct.comm_tmul, TensorProduct.map_tmul]
      | add x₁ x₂ hx₁ hx₂ => simp only [map_add, hx₁, hx₂]
    · induction y using TensorProduct.inductionOn with
      | tmul a b =>
        simp [TensorProduct.comm_tmul, TensorProduct.map_tmul, map_neg]
      | add y₁ y₂ hy₁ hy₂ =>
        simp only [map_add, neg_add]; exact congr_arg₂ (· + ·) hy₁ hy₂
  · -- odd component
    change (koszulBraidingOdd X Z).comp
        (LinearMap.prodMap (TensorProduct.map LinearMap.id f.oddMap)
          (TensorProduct.map LinearMap.id f.evenMap)) =
      (LinearMap.prodMap (TensorProduct.map f.evenMap LinearMap.id)
          (TensorProduct.map f.oddMap LinearMap.id)).comp
        (koszulBraidingOdd X Y)
    apply LinearMap.ext; intro ⟨x, y⟩
    simp only [LinearMap.comp_apply, LinearMap.prodMap_apply,
      koszulBraidingOdd_pair, Prod.mk.injEq]
    refine ⟨?_, ?_⟩
    · induction y using TensorProduct.inductionOn with
      | tmul a b => simp [TensorProduct.comm_tmul, TensorProduct.map_tmul]
      | add y₁ y₂ hy₁ hy₂ => simp only [map_add, hy₁, hy₂]
    · induction x using TensorProduct.inductionOn with
      | tmul a b => simp [TensorProduct.comm_tmul, TensorProduct.map_tmul]
      | add x₁ x₂ hx₁ hx₂ => simp only [map_add, hx₁, hx₂]

/-- SuperVect is a braided monoidal category with the Koszul
braiding: swapping odd ⊗ odd elements picks up a factor of −1. -/
instance instBraidedCategory : BraidedCategory SuperVect where
  braiding := koszulBraidingIso
  braiding_naturality_right := fun X {_ _} f => by
    exact koszulBraiding_naturality_right X f
  braiding_naturality_left := fun {X Y} f Z => by
    apply Hom.ext
    · -- even component
      change (koszulBraidingEven Y Z).comp
          (LinearMap.prodMap (TensorProduct.map f.evenMap LinearMap.id)
            (TensorProduct.map f.oddMap LinearMap.id)) =
        (LinearMap.prodMap (TensorProduct.map LinearMap.id f.evenMap)
            (TensorProduct.map LinearMap.id f.oddMap)).comp
          (koszulBraidingEven X Z)
      apply LinearMap.ext; intro ⟨x, y⟩
      simp only [LinearMap.comp_apply, LinearMap.prodMap_apply,
        koszulBraidingEven, koszulEvenAux,
        LinearMap.neg_apply, LinearEquiv.coe_toLinearMap, Prod.mk.injEq]
      refine ⟨?_, ?_⟩
      · induction x using TensorProduct.inductionOn with
        | tmul a b => simp [TensorProduct.comm_tmul, TensorProduct.map_tmul]
        | add x₁ x₂ hx₁ hx₂ => simp only [map_add, hx₁, hx₂]
      · induction y using TensorProduct.inductionOn with
        | tmul a b =>
          simp [TensorProduct.comm_tmul, TensorProduct.map_tmul, map_neg]
        | add y₁ y₂ hy₁ hy₂ =>
          simp only [map_add, neg_add]; exact congr_arg₂ (· + ·) hy₁ hy₂
    · -- odd component
      change (koszulBraidingOdd Y Z).comp
          (LinearMap.prodMap (TensorProduct.map f.evenMap LinearMap.id)
            (TensorProduct.map f.oddMap LinearMap.id)) =
        (LinearMap.prodMap (TensorProduct.map LinearMap.id f.oddMap)
            (TensorProduct.map LinearMap.id f.evenMap)).comp
          (koszulBraidingOdd X Z)
      apply LinearMap.ext; intro ⟨x, y⟩
      simp only [LinearMap.comp_apply, LinearMap.prodMap_apply,
        koszulBraidingOdd_pair, Prod.mk.injEq]
      refine ⟨?_, ?_⟩
      · induction y using TensorProduct.inductionOn with
        | tmul a b => simp [TensorProduct.comm_tmul, TensorProduct.map_tmul]
        | add y₁ y₂ hy₁ hy₂ => simp only [map_add, hy₁, hy₂]
      · induction x using TensorProduct.inductionOn with
        | tmul a b => simp [TensorProduct.comm_tmul, TensorProduct.map_tmul]
        | add x₁ x₂ hx₁ hx₂ => simp only [map_add, hx₁, hx₂]
  hexagon_forward := fun X Y Z => by
    apply Hom.ext
    · exact koszulAux_hexagon_fwd_even X.even X.odd Y.even Y.odd
        Z.even Z.odd
    · exact koszulAux_hexagon_fwd_odd X.even X.odd Y.even Y.odd
        Z.even Z.odd
  hexagon_reverse := fun X Y Z => by
    apply Hom.ext
    · exact koszulAux_hexagon_rev_even X.even X.odd Y.even Y.odd
        Z.even Z.odd
    · exact koszulAux_hexagon_rev_odd X.even X.odd Y.even Y.odd
        Z.even Z.odd

/-- SuperVect is a symmetric monoidal category: applying the
Koszul braiding twice recovers the identity. -/
instance instSymmetricCategory : SymmetricCategory SuperVect where
  symmetry := fun X Y => koszulBraiding_self_inverse X Y

/-! ### Additive and linear structure -/

/-- The zero morphism: zero in both components. -/
instance {V W : SuperVect} : Zero (V ⟶ W) :=
  ⟨⟨0, 0⟩⟩

/-- Componentwise addition of morphisms. -/
instance {V W : SuperVect} : Add (V ⟶ W) :=
  ⟨fun f g => ⟨f.evenMap + g.evenMap, f.oddMap + g.oddMap⟩⟩

/-- Componentwise negation. -/
instance {V W : SuperVect} : Neg (V ⟶ W) :=
  ⟨fun f => ⟨-f.evenMap, -f.oddMap⟩⟩

/-- Componentwise subtraction. -/
instance {V W : SuperVect} : Sub (V ⟶ W) :=
  ⟨fun f g => ⟨f.evenMap - g.evenMap, f.oddMap - g.oddMap⟩⟩

/-- Componentwise scaling by a complex number. -/
instance {V W : SuperVect} : SMul ℂ (V ⟶ W) :=
  ⟨fun c f => ⟨c • f.evenMap, c • f.oddMap⟩⟩

/-- Componentwise natural scaling, given definitionally so that the
`AddCommGroup` structure below has no transported `nsmul` field. -/
instance {V W : SuperVect} : SMul ℕ (V ⟶ W) :=
  ⟨fun n f => ⟨n • f.evenMap, n • f.oddMap⟩⟩

/-- Componentwise integer scaling, likewise definitional. -/
instance {V W : SuperVect} : SMul ℤ (V ⟶ W) :=
  ⟨fun n f => ⟨n • f.evenMap, n • f.oddMap⟩⟩

/-- The components of a morphism determine it; the additive and
module structures are pulled back componentwise. -/
def homComponents {V W : SuperVect} (f : V ⟶ W) :
    (V.even →ₗ[ℂ] W.even) × (V.odd →ₗ[ℂ] W.odd) :=
  (f.evenMap, f.oddMap)

/-- Componentwise equality of morphisms. -/
theorem homComponents_injective {V W : SuperVect} :
    Function.Injective (homComponents (V := V) (W := W)) :=
  fun _ _ h => Hom.ext (congrArg Prod.fst h) (congrArg Prod.snd h)

/-- Morphisms form an abelian group, pulled back along the injection
into the pair of component maps. -/
instance {V W : SuperVect} : AddCommGroup (V ⟶ W) :=
  homComponents_injective.addCommGroup homComponents
    rfl (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl) (fun _ _ => rfl)

/-- Morphisms form a ℂ-module, pulled back the same way: SuperVect
is ℂ-linear. -/
instance {V W : SuperVect} : Module ℂ (V ⟶ W) :=
  homComponents_injective.module ℂ
    { toFun := homComponents
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
    (fun _ _ => rfl)

/-- Addition of morphisms is componentwise on the even part. -/
@[simp]
theorem add_evenMap {V W : SuperVect} (f g : V ⟶ W) :
    (f + g).evenMap = f.evenMap + g.evenMap := rfl

/-- Addition of morphisms is componentwise on the odd part. -/
@[simp]
theorem add_oddMap {V W : SuperVect} (f g : V ⟶ W) :
    (f + g).oddMap = f.oddMap + g.oddMap := rfl

/-- The zero morphism's even component is zero. -/
@[simp]
theorem zero_evenMap {V W : SuperVect} :
    (0 : V ⟶ W).evenMap = 0 := rfl

/-- The zero morphism's odd component is zero. -/
@[simp]
theorem zero_oddMap {V W : SuperVect} :
    (0 : V ⟶ W).oddMap = 0 := rfl

/-- Scalar multiplication is componentwise on the even part. -/
@[simp]
theorem smul_evenMap {V W : SuperVect} (c : ℂ) (f : V ⟶ W) :
    (c • f).evenMap = c • f.evenMap := rfl

/-- Scalar multiplication is componentwise on the odd part. -/
@[simp]
theorem smul_oddMap {V W : SuperVect} (c : ℂ) (f : V ⟶ W) :
    (c • f).oddMap = c • f.oddMap := rfl

/-- SuperVect is preadditive: composition is bilinear
componentwise. -/
instance instPreadditive : Preadditive SuperVect where
  add_comp _ _ _ f f' g := by
    apply Hom.ext
    · change g.evenMap ∘ₗ (f.evenMap + f'.evenMap) = _
      exact LinearMap.comp_add _ _ _
    · change g.oddMap ∘ₗ (f.oddMap + f'.oddMap) = _
      exact LinearMap.comp_add _ _ _
  comp_add _ _ _ f g g' := by
    apply Hom.ext
    · change (g.evenMap + g'.evenMap) ∘ₗ f.evenMap = _
      exact LinearMap.add_comp _ _ _
    · change (g.oddMap + g'.oddMap) ∘ₗ f.oddMap = _
      exact LinearMap.add_comp _ _ _

/-- SuperVect is ℂ-linear: composition is ℂ-bilinear
componentwise. -/
instance instLinear : CategoryTheory.Linear ℂ SuperVect where
  smul_comp _ _ _ c f g := by
    apply Hom.ext
    · change g.evenMap ∘ₗ (c • f.evenMap) = _
      exact LinearMap.comp_smul _ _ _
    · change g.oddMap ∘ₗ (c • f.oddMap) = _
      exact LinearMap.comp_smul _ _ _
  comp_smul _ _ _ f c g := by
    apply Hom.ext
    · change (c • g.evenMap) ∘ₗ f.evenMap = _
      exact LinearMap.smul_comp _ _ _
    · change (c • g.oddMap) ∘ₗ f.oddMap = _
      exact LinearMap.smul_comp _ _ _

end SuperVect

end

/-! ## 10. The vocabulary of Deligne's hypotheses

Subquotients and bounded composition length, scalar unit endomorphisms,
iterated and mixed tensor powers, finite ⊗-generation, and moderate growth:
exactly the predicates in which the hypothesis list of Théorème 0.6 is
phrased. (Their theory continues in `RS/Classical/CatTheory/`.) -/

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory

universe v u

section

variable {C : Type u}

/-- **`Y` is a subquotient of `Z`**: a quotient of a subobject of
`Z`.  This is the relation Deligne's tensor-generation hypothesis is
stated with. -/
def IsSubquotientOf [Category.{v} C]
    (Y Z : C) : Prop :=
  ∃ (S : C) (i : S ⟶ Z) (p : S ⟶ Y), Mono i ∧ Epi p

/-- A retract is in particular a subquotient: a splitting makes the
inclusion a mono, and the object is a quotient of itself. -/
theorem isSubquotientOf_of_retract [Category.{v} C]
    {Y Z : C} (i : Y ⟶ Z) (r : Z ⟶ Y)
    (h : i ≫ r = 𝟙 Y) : IsSubquotientOf Y Z := by
  have : IsSplitMono i := ⟨⟨r, h⟩⟩
  exact ⟨Y, i, 𝟙 Y, inferInstance, inferInstance⟩

/-- `LengthLE Y k` states that the subobject order of `Y` contains
no strictly increasing chain of `k + 2` subobjects; equivalently,
every chain `0 = Y₀ < ⋯ < Y_ℓ = Y` has `ℓ ≤ k`, so the composition
length of `Y` is at most `k`. -/
def LengthLE [Category.{v} C]
    (Y : C) (k : ℕ) : Prop :=
  ∀ f : Fin (k + 2) → Subobject Y, ¬ StrictMono f

end

section

variable (A : Type u)

/-- The unit's endomorphisms are the scalars. -/
def HasScalarUnit [Category.{v} A]
    [Preadditive A] [Linear ℂ A] [MonoidalCategory A] : Prop :=
  Function.Bijective
    (fun c : ℂ => (c • 𝟙 (𝟙_ A) : 𝟙_ A ⟶ 𝟙_ A))

end

section

variable (A : Type u)

/-- Iterated tensor power of an object. -/
def tensorPow [Category.{v} A] [MonoidalCategory A]
    (X : A) : ℕ → A
  | 0 => 𝟙_ A
  | n + 1 => tensorObj (tensorPow X n) X

/-- A mixed tensor power of `X`: `X ^ ⊗ a ⊗ (Xᘁ) ^ ⊗ b`. -/
def mixedPow [Category.{v} A] [MonoidalCategory A]
    [RigidCategory A] (X : A) (a b : ℕ) : A :=
  tensorPow A X a ⊗ tensorPow A (Xᘁ) b

/-- **Finite tensor generation**, in the sense of Deligne's
hypothesis: every object is a subquotient of a finite biproduct of
mixed tensor powers of `X` — a quotient of a subobject of such a
biproduct. -/
def TensorGeneratedBy [Category.{v} A] [MonoidalCategory A]
    [Preadditive A] [HasFiniteBiproducts A] [RigidCategory A] (X : A) : Prop :=
  ∀ Y : A, ∃ (k : ℕ) (ab : Fin k → ℕ × ℕ),
    IsSubquotientOf Y (⨁ fun t => mixedPow A X (ab t).1 (ab t).2)

/-- Every object has moderate tensor-power growth, measured by
composition length. -/
def ModerateLengthGrowth [Category.{v} A] [MonoidalCategory A] : Prop :=
  ∀ Y : A, ∃ C c : ℕ, ∀ N : ℕ, LengthLE (tensorPow A Y N) (C * c ^ N)

end

end

/-! ## 11. Deligne's theorem

The correspondence with the published hypotheses, item by item: essentially
small — `[EssentiallySmall.{v} A]`; abelian ℂ-linear with ℂ-bilinear tensor —
`[Abelian A]`, `[Linear ℂ A]`, `[MonoidalPreadditive A]`, `[MonoidalLinear ℂ
A]`; rigid symmetric monoidal — `[MonoidalCategory A]`, `[SymmetricCategory
A]`, `[RigidCategory A]`; `End 𝟙 = ℂ` — `HasScalarUnit A`; finitely
⊗-generated — `∃ X, TensorGeneratedBy A X`; moderate growth —
`ModerateLengthGrowth A`. Exactness of the tensor product needs no separate
hypothesis (rigidity makes `X ⊗ −` a two-sided adjoint), and
`[HasFiniteBiproducts A]` is implied by `[Abelian A]`, named only so the
generation predicate can be stated. The conclusion is taken in fibre-functor
form — weaker than Deligne's ⊗-equivalence with the representations of an
affine supergroup scheme, which yields the functor by composing with the
forgetful functor.

Reference: Pierre Deligne, *Catégories tensorielles*, Moscow Math. J. **2**
(2002), 227–248, Théorème 0.6 (with §0.1 for the definitions); see also Victor
Ostrik, *Tensor categories (after P. Deligne)*, arXiv:math/0401347, Thm 2.3.
-/

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory

universe u v

/-- The conclusion of Deligne's theorem for a candidate tensor
category: an exact faithful ℂ-linear symmetric monoidal functor into
super vector spaces.  This extends the consumed interface
(`DelignePackage`) by the conclusions the development does not use:
faithfulness, and exactness in the form of preservation of finite
limits and finite colimits. -/
structure DeligneFibreFunctor (A : Type*) [Category A]
    [MonoidalCategory A] [SymmetricCategory A] [Preadditive A]
    [Linear ℂ A] where
  /-- The fibre functor. -/
  ω : A ⥤ SuperVect
  /-- The fibre functor is symmetric monoidal. -/
  braided : ω.Braided
  /-- The fibre functor is additive. -/
  additive : ω.Additive
  /-- The fibre functor is ℂ-linear. -/
  linear : ω.Linear ℂ
  /-- The fibre functor is faithful. -/
  faithful : ω.Faithful
  /-- The fibre functor preserves finite limits: the left half of
  exactness. -/
  preservesFiniteLimits : PreservesFiniteLimits ω
  /-- The fibre functor preserves finite colimits: the right half of
  exactness. -/
  preservesFiniteColimits : PreservesFiniteColimits ω

/-- **Deligne's theorem** (Catégories tensorielles, Théorème 0.6):
every essentially small abelian ℂ-linear rigid symmetric monoidal
category with ℂ-bilinear tensor product, scalar unit endomorphisms,
a finite tensor generator and moderate growth of the lengths of its
tensor powers admits an exact faithful ℂ-linear symmetric monoidal
fibre functor to finite-dimensional super vector spaces. -/
def DeligneTheoremStatement : Prop :=
  ∀ (A : Type u) [Category.{v} A] [Abelian A] [Linear ℂ A]
    [MonoidalCategory A] [SymmetricCategory A]
    [MonoidalPreadditive A] [MonoidalLinear ℂ A]
    [HasFiniteBiproducts A] [RigidCategory A]
    [EssentiallySmall.{v} A],
    HasScalarUnit A →
    (∃ X : A, TensorGeneratedBy A X) →
    ModerateLengthGrowth A →
    Nonempty (DeligneFibreFunctor A)

end

end RS
