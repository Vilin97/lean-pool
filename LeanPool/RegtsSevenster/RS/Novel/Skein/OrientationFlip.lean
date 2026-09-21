/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

import LeanPool.RegtsSevenster.RS.Novel.Skein.VertexOddSign

/-!
# Orientation invariance of the constrained summand: circuit flips

For a *fixed* boundary-relative transition system `κ`, the corrected
constrained summand `throughSummand` is invariant under changing the
orientation, **provided every internal flag on which the two
orientations disagree has an internal pairing partner** — that is,
the difference set is supported on fully internal edges (equivalently,
on closed circuits; flips of path components are excluded).

## The proof

The difference set `orientDiff o o'` of two orientations is closed
under the matching (from both `match_flip`s) and — under the
pairing-internality hypothesis — under the edge pairing (from both
`pairing_flip`s).  The colouring reindexing `flipColouring` applies
the odd-partner involution `∂` edge-wise on the difference set; it is
an involution of the core odd colourings fixing all boundary flags,
so the odd boundary constraint is preserved.  At each vertex the
in-flags under `o'` are the unflipped in-flags under `o` together
with the matches of the flipped ones; each flipped visit contributes
a reversed pair block (one adjacent-swap sign) and trades the sign
factor `∂`-partner-sign of the outgoing colour for that of the
incoming one.  The two `(−1)`s per visit cancel, and the leftover
ratio `sign(in) · sign(out)` telescopes over the whole vertex product
to `∏_{f ∈ diff} sign(φ f)`, which is `1` because the difference set
is a disjoint union of full edges and the colouring is
pairing-constant.

## Why the hypothesis is necessary

Unrestricted orientation invariance is **false**.  Counterexample
(`ℓ = 2`): one vertex `v` with two pendant edges `{f₁, b₁}`,
`{f₂, b₂}` to boundary labels `i₁, i₂`, the matching `f₁ ↔ f₂`, and
odd state colours `st i₁ = 0`, `st i₂ = 1`.  The boundary constraint
pins the unique contributing colouring, and the two orientations of
the path give summands proportional to `−h(μ, {0, 3})` and
`−h(μ, {1, 2})` respectively — different for generic `h`.  The
per-visit sign ratio `sign(x)·sign(y)` telescopes to `1` only around
closed circuits; on a path it leaves the pinned end-colour signs, and
the `∂`-reindexing moreover violates the pinned boundary values.
Consequently any orientation-independence interface must restrict to
circuit-supported differences (or fix path orientations by
convention).
-/

namespace RS

open scoped Classical

variable {α : Type} {W : Fragment α}

namespace EdgeSubset

section Diff

variable {F : EdgeSubset W} {κ : F.RelTransitionSystem}

/-! ## Bool helpers -/

private theorem bool_not_inj {a b : Bool} (h : (!a) = (!b)) : a = b := by
  cases a <;> cases b <;> simp_all

/-! ## The difference set of two orientations -/

/-- The internal flags on which two orientations of the same relative
transition system disagree. -/
noncomputable def orientDiff (o o' : κ.Orientation) : Finset W.Flag :=
  F.internalFlags.filter (fun f => o.isOut f ≠ o'.isOut f)

/-- Membership in the difference set: an internal flag the two
orientations direct oppositely. -/
theorem mem_orientDiff {o o' : κ.Orientation} {f : W.Flag} :
    f ∈ orientDiff o o' ↔
      f ∈ F.internalFlags ∧ o.isOut f ≠ o'.isOut f :=
  Finset.mem_filter

/-- The difference set consists of internal flags. -/
theorem orientDiff_subset_internal (o o' : κ.Orientation)
    {f : W.Flag} (hf : f ∈ orientDiff o o') : f ∈ F.internalFlags :=
  (mem_orientDiff.mp hf).1

/-- Off the difference set, internal flags are oriented identically. -/
theorem isOut_eq_of_notMem_orientDiff {o o' : κ.Orientation}
    {f : W.Flag} (hf : f ∈ F.internalFlags)
    (hnot : f ∉ orientDiff o o') : o.isOut f = o'.isOut f := by
  by_contra hne
  exact hnot (mem_orientDiff.mpr ⟨hf, hne⟩)

/-- The difference set is closed under the matching. -/
theorem match_mem_orientDiff {o o' : κ.Orientation} {f : W.Flag}
    (hf : f ∈ orientDiff o o') : κ.match_ f ∈ orientDiff o o' := by
  obtain ⟨hint, hne⟩ := mem_orientDiff.mp hf
  refine mem_orientDiff.mpr ⟨κ.match_mem f hint, ?_⟩
  rw [o.match_flip f hint, o'.match_flip f hint]
  exact fun hcon => hne (bool_not_inj hcon)

/-- The complement of the difference set is closed under the matching
on internal flags. -/
theorem match_notMem_orientDiff {o o' : κ.Orientation} {f : W.Flag}
    (hf : f ∈ F.internalFlags) (hnot : f ∉ orientDiff o o') :
    κ.match_ f ∉ orientDiff o o' := by
  intro hmem
  have h2 := match_mem_orientDiff hmem
  rw [κ.match_invol f hf] at h2
  exact hnot h2

/-- Under the pairing-internality hypothesis, the difference set is
closed under the edge pairing. -/
theorem pairing_mem_orientDiff {o o' : κ.Orientation}
    (hpair : ∀ f ∈ F.internalFlags,
      o.isOut f ≠ o'.isOut f → W.pairing f ∈ F.internalFlags)
    {f : W.Flag} (hf : f ∈ orientDiff o o') :
    W.pairing f ∈ orientDiff o o' := by
  obtain ⟨hint, hne⟩ := mem_orientDiff.mp hf
  have hp := hpair f hint hne
  refine mem_orientDiff.mpr ⟨hp, ?_⟩
  rw [o.pairing_flip f hint hp, o'.pairing_flip f hint hp]
  exact fun hcon => hne (bool_not_inj hcon)

/-- The complement of the difference set is closed under the pairing. -/
theorem pairing_notMem_orientDiff {o o' : κ.Orientation}
    (hpair : ∀ f ∈ F.internalFlags,
      o.isOut f ≠ o'.isOut f → W.pairing f ∈ F.internalFlags)
    {f : W.Flag} (hnot : f ∉ orientDiff o o') :
    W.pairing f ∉ orientDiff o o' := by
  intro hmem
  have h2 := pairing_mem_orientDiff hpair hmem
  rw [W.pairing_invol] at h2
  exact hnot h2

/-- Boundary flags are never in the difference set. -/
theorem boundaryFlag_notMem_orientDiff (o o' : κ.Orientation)
    (i : α) : W.boundaryFlag i ∉ orientDiff o o' := by
  intro hmem
  obtain ⟨v, hv⟩ :=
    F.attach_internal_of_mem (orientDiff_subset_internal o o' hmem)
  rw [W.attach_boundaryFlag] at hv
  cases hv

/-! ## The colouring reindexing -/

/-- The `∂`-flip of a core odd colouring on the edges of the
difference set: the crux bijection for orientation invariance. -/
noncomputable def flipColouring (o o' : κ.Orientation)
    (hpair : ∀ f ∈ F.internalFlags,
      o.isOut f ≠ o'.isOut f → W.pairing f ∈ F.internalFlags)
    {ℓ : ℕ} (φ : F.CoreOddColouring ℓ) : F.CoreOddColouring ℓ :=
  ⟨fun g => if g.val ∈ orientDiff o o' then oddPartner ℓ (φ.val g)
    else φ.val g,
   fun g => by
     have hbeta : (if W.pairing g.val ∈ orientDiff o o' then
           oddPartner ℓ (φ.val
             ⟨W.pairing g.val, F.pairing_mem_coreFlags g.prop⟩)
         else φ.val
           ⟨W.pairing g.val, F.pairing_mem_coreFlags g.prop⟩) =
         (if g.val ∈ orientDiff o o' then oddPartner ℓ (φ.val g)
         else φ.val g) := by
       by_cases hg : g.val ∈ orientDiff o o'
       · rw [if_pos (pairing_mem_orientDiff hpair hg), if_pos hg,
           φ.prop g]
       · rw [if_neg (pairing_notMem_orientDiff hpair hg), if_neg hg,
           φ.prop g]
     exact hbeta⟩

/-- On the difference set the colouring is `∂`-flipped. -/
theorem flipColouring_val_of_mem (o o' : κ.Orientation)
    (hpair : ∀ f ∈ F.internalFlags,
      o.isOut f ≠ o'.isOut f → W.pairing f ∈ F.internalFlags)
    {ℓ : ℕ} (φ : F.CoreOddColouring ℓ)
    (g : {g : W.Flag // g ∈ F.coreFlags})
    (hg : g.val ∈ orientDiff o o') :
    (flipColouring o o' hpair φ).val g = oddPartner ℓ (φ.val g) :=
  if_pos hg

/-- Off it the colouring is unchanged. -/
theorem flipColouring_val_of_notMem (o o' : κ.Orientation)
    (hpair : ∀ f ∈ F.internalFlags,
      o.isOut f ≠ o'.isOut f → W.pairing f ∈ F.internalFlags)
    {ℓ : ℕ} (φ : F.CoreOddColouring ℓ)
    (g : {g : W.Flag // g ∈ F.coreFlags})
    (hg : g.val ∉ orientDiff o o') :
    (flipColouring o o' hpair φ).val g = φ.val g :=
  if_neg hg

/-- The flip negates the incoming sign on the difference set: the
flip colouring is the colour flip on `orientDiff o o'`. -/
theorem inSign_flipColouring_of_mem (o o' : κ.Orientation)
    (hpair : ∀ f ∈ F.internalFlags,
      o.isOut f ≠ o'.isOut f → W.pairing f ∈ F.internalFlags)
    {ℓ : ℕ} (φ : F.CoreOddColouring ℓ) {g : W.Flag}
    (hg : g ∈ orientDiff o o') :
    inSign (flipColouring o o' hpair φ) g = -inSign φ g :=
  inSign_flip_of_mem (S := orientDiff o o') (fun _ => rfl) hg
    (F.internalFlags_subset_coreFlags
      (orientDiff_subset_internal o o' hg))

/-- The flip leaves the incoming sign off the difference set
alone. -/
theorem inSign_flipColouring_of_notMem (o o' : κ.Orientation)
    (hpair : ∀ f ∈ F.internalFlags,
      o.isOut f ≠ o'.isOut f → W.pairing f ∈ F.internalFlags)
    {ℓ : ℕ} (φ : F.CoreOddColouring ℓ) {g : W.Flag}
    (hg : g ∉ orientDiff o o') :
    inSign (flipColouring o o' hpair φ) g = inSign φ g :=
  inSign_flip_of_notMem (S := orientDiff o o') (fun _ => rfl) hg

/-- The flip is an involution, so it is a bijection of the
colouring sum. -/
theorem flipColouring_involutive (o o' : κ.Orientation)
    (hpair : ∀ f ∈ F.internalFlags,
      o.isOut f ≠ o'.isOut f → W.pairing f ∈ F.internalFlags)
    {ℓ : ℕ} :
    Function.Involutive
      (flipColouring o o' hpair (F := F) (ℓ := ℓ)) := by
  intro φ
  apply Subtype.ext
  funext g
  show (if g.val ∈ orientDiff o o' then
      oddPartner ℓ ((flipColouring o o' hpair φ).val g)
    else (flipColouring o o' hpair φ).val g) = φ.val g
  by_cases hg : g.val ∈ orientDiff o o'
  · rw [if_pos hg, flipColouring_val_of_mem o o' hpair φ g hg,
      oddPartner_invol]
  · rw [if_neg hg, flipColouring_val_of_notMem o o' hpair φ g hg]

/-- The reindexing preserves the odd boundary constraint. -/
theorem coreOddBoundaryMatch_flipColouring {k ℓ : ℕ}
    (st : GenBoundaryState k ℓ α) (o o' : κ.Orientation)
    (hpair : ∀ f ∈ F.internalFlags,
      o.isOut f ≠ o'.isOut f → W.pairing f ∈ F.internalFlags)
    (φ : F.CoreOddColouring ℓ) :
    F.coreOddBoundaryMatch st (flipColouring o o' hpair φ) ↔
      F.coreOddBoundaryMatch st φ := by
  have hval : ∀ (i : α) (hcore : W.boundaryFlag i ∈ F.coreFlags),
      (flipColouring o o' hpair φ).val ⟨W.boundaryFlag i, hcore⟩ =
        φ.val ⟨W.boundaryFlag i, hcore⟩ :=
    fun i hcore => flipColouring_val_of_notMem o o' hpair φ _
      (boundaryFlag_notMem_orientDiff o o' i)
  unfold coreOddBoundaryMatch
  constructor
  · intro H i c hst hcore
    rw [← hval i hcore]
    exact H i c hst hcore
  · intro H i c hst hcore
    rw [hval i hcore]
    exact H i c hst hcore

/-! ## Vertex-local in-sets -/

/-- The in-flags kept fixed by the orientation change. -/
private noncomputable def keepIn (o o' : κ.Orientation)
    (v : W.Vertex) : Finset W.Flag :=
  (relInSetAt o v).filter (fun g => g ∉ orientDiff o o')

/-- The in-flags flipped by the orientation change. -/
private noncomputable def flipIn (o o' : κ.Orientation)
    (v : W.Vertex) : Finset W.Flag :=
  (relInSetAt o v).filter (fun g => g ∈ orientDiff o o')

private theorem mem_keepIn {o o' : κ.Orientation} {v : W.Vertex}
    {g : W.Flag} :
    g ∈ keepIn o o' v ↔ g ∈ relInSetAt o v ∧ g ∉ orientDiff o o' :=
  Finset.mem_filter

private theorem mem_flipIn {o o' : κ.Orientation} {v : W.Vertex}
    {g : W.Flag} :
    g ∈ flipIn o o' v ↔ g ∈ relInSetAt o v ∧ g ∈ orientDiff o o' :=
  Finset.mem_filter

private theorem inSet_val_eq (o o' : κ.Orientation) (v : W.Vertex) :
    (relInSetAt o v).val =
      (keepIn o o' v).val + (flipIn o o' v).val := by
  unfold keepIn flipIn
  rw [Finset.filter_val, Finset.filter_val, add_comm]
  exact (Multiset.filter_add_not
    (fun g => g ∈ orientDiff o o') (relInSetAt o v).val).symm

private theorem match_injOn_flipIn (o o' : κ.Orientation)
    (v : W.Vertex) :
    ∀ x ∈ flipIn o o' v, ∀ y ∈ flipIn o o' v,
      κ.match_ x = κ.match_ y → x = y := by
  intro x hx y hy hxy
  have hxint := relInSetAt_subset_internal (mem_flipIn.mp hx).1
  have hyint := relInSetAt_subset_internal (mem_flipIn.mp hy).1
  calc x = κ.match_ (κ.match_ x) := (κ.match_invol x hxint).symm
    _ = κ.match_ (κ.match_ y) := by rw [hxy]
    _ = y := κ.match_invol y hyint

private theorem keepIn_disjoint_image (o o' : κ.Orientation)
    (v : W.Vertex) :
    Disjoint (keepIn o o' v) ((flipIn o o' v).image κ.match_) := by
  rw [Finset.disjoint_left]
  intro g hgk hgi
  obtain ⟨f, hf, rfl⟩ := Finset.mem_image.mp hgi
  exact (mem_keepIn.mp hgk).2
    (match_mem_orientDiff (mem_flipIn.mp hf).2)

/-- **The in-set identity**: the in-flags under `o'` are the kept
in-flags under `o` together with the matches of the flipped ones. -/
private theorem inSet_flip_eq (o o' : κ.Orientation) (v : W.Vertex) :
    relInSetAt o' v = (keepIn o o' v).disjUnion
      ((flipIn o o' v).image κ.match_)
      (keepIn_disjoint_image o o' v) := by
  apply Finset.ext
  intro g
  rw [Finset.mem_disjUnion, mem_relInSetAt]
  constructor
  · rintro ⟨hgfl, hgat, hgout'⟩
    have hgint : g ∈ F.internalFlags :=
      mem_internalFlags_of hgfl ⟨v, hgat⟩
    by_cases hgD : g ∈ orientDiff o o'
    · right
      refine Finset.mem_image.mpr
        ⟨κ.match_ g, ?_, κ.match_invol g hgint⟩
      have hmD := match_mem_orientDiff hgD
      have hmint := κ.match_mem g hgint
      have hone : o.isOut g = true := by
        have hne := (mem_orientDiff.mp hgD).2
        cases hb : o.isOut g
        · exact absurd (hb.trans hgout'.symm) hne
        · rfl
      refine mem_flipIn.mpr ⟨mem_relInSetAt.mpr
        ⟨mem_flags_of_internalFlags F hmint,
          κ.match_vertex g hgint v hgat, ?_⟩, hmD⟩
      rw [o.match_flip g hgint, hone]
      rfl
    · left
      refine mem_keepIn.mpr ⟨mem_relInSetAt.mpr ⟨hgfl, hgat, ?_⟩, hgD⟩
      rw [isOut_eq_of_notMem_orientDiff hgint hgD]
      exact hgout'
  · rintro (hg | hg)
    · obtain ⟨hgin, hgD⟩ := mem_keepIn.mp hg
      obtain ⟨h1, h2, h3⟩ := mem_relInSetAt.mp hgin
      have hgint : g ∈ F.internalFlags := mem_internalFlags_of h1 ⟨v, h2⟩
      refine ⟨h1, h2, ?_⟩
      rw [← isOut_eq_of_notMem_orientDiff hgint hgD]
      exact h3
    · obtain ⟨f, hf, rfl⟩ := Finset.mem_image.mp hg
      obtain ⟨hfin, hfD⟩ := mem_flipIn.mp hf
      obtain ⟨h1, h2, h3⟩ := mem_relInSetAt.mp hfin
      have hfint : f ∈ F.internalFlags := mem_internalFlags_of h1 ⟨v, h2⟩
      have hmint := κ.match_mem f hfint
      refine ⟨mem_flags_of_internalFlags F hmint,
        κ.match_vertex f hfint v h2, ?_⟩
      have hmD := match_mem_orientDiff hfD
      have hne := (mem_orientDiff.mp hmD).2
      have ho : o.isOut (κ.match_ f) = true := by
        rw [o.match_flip f hfint, h3]
        rfl
      cases hb : o'.isOut (κ.match_ f)
      · rfl
      · exact absurd (ho.trans hb.symm) hne

/-! ## Signs as finset products -/

private theorem oddPartnerSign_mul_self (ℓ : ℕ) (c : Fin (2 * ℓ)) :
    oddPartnerSign ℓ c * oddPartnerSign ℓ c = 1 := by
  unfold oddPartnerSign
  by_cases h : c.val < ℓ <;> simp [h]

private theorem coreOddSignFn_eq {ℓ : ℕ} (φ : F.CoreOddColouring ℓ)
    (f : {f : W.Flag // f ∈ F.internalFlags}) :
    F.coreOddSignFn κ φ f = inSign φ (κ.match_ f.val) := by
  unfold EdgeSubset.coreOddSignFn inSign
  rw [dif_pos
    (F.internalFlags_subset_coreFlags (κ.match_mem _ f.prop))]

private theorem coreOddSignAt_eq_prod {ℓ : ℕ} (o : κ.Orientation)
    (φ : F.CoreOddColouring ℓ) (v : W.Vertex) :
    F.coreOddSignAt o φ v =
      ∏ g ∈ relInSetAt o v, inSign φ (κ.match_ g) := by
  unfold EdgeSubset.coreOddSignAt
  rw [attachWith_map_eq (F.coreOddSignFn κ φ)
    (fun g => inSign φ (κ.match_ g))
    (fun g hg => coreOddSignFn_eq φ ⟨g, hg⟩) (F.relInFlagsAt o v) _]
  exact list_map_prod_eq_finset_prod (relInSetAt o v) _
    (relInFlagsAt_coe o v) _

private theorem prod_inSet_split {M : Type*} [CommMonoid M]
    (o o' : κ.Orientation) (v : W.Vertex) (f : W.Flag → M) :
    ∏ g ∈ relInSetAt o v, f g =
      (∏ g ∈ flipIn o o' v, f g) * ∏ g ∈ keepIn o o' v, f g := by
  unfold flipIn keepIn
  exact (Finset.prod_filter_mul_prod_filter_not (relInSetAt o v) _ f).symm

/-- **The per-vertex sign identity**: flipping the orientation and
the colouring multiplies the vertex sign by one `−1` per flipped
visit and by the incoming-over-outgoing sign ratio. -/
private theorem coreOddSignAt_flip {ℓ : ℕ} (o o' : κ.Orientation)
    (hpair : ∀ f ∈ F.internalFlags,
      o.isOut f ≠ o'.isOut f → W.pairing f ∈ F.internalFlags)
    (φ : F.CoreOddColouring ℓ) (v : W.Vertex) :
    F.coreOddSignAt o' (flipColouring o o' hpair φ) v =
      (-1 : ℤ) ^ (flipIn o o' v).card *
        (∏ f ∈ flipIn o o' v,
          inSign φ f * inSign φ (κ.match_ f)) *
        F.coreOddSignAt o φ v := by
  rw [coreOddSignAt_eq_prod o' _ v, coreOddSignAt_eq_prod o φ v]
  rw [inSet_flip_eq o o' v, Finset.prod_disjUnion]
  have hkeep : ∏ g ∈ keepIn o o' v,
      inSign (flipColouring o o' hpair φ) (κ.match_ g) =
      ∏ g ∈ keepIn o o' v, inSign φ (κ.match_ g) := by
    refine Finset.prod_congr rfl (fun g hg => ?_)
    have hgint := relInSetAt_subset_internal (mem_keepIn.mp hg).1
    exact inSign_flipColouring_of_notMem o o' hpair φ
      (match_notMem_orientDiff hgint (mem_keepIn.mp hg).2)
  have himg : ∏ g ∈ (flipIn o o' v).image κ.match_,
      inSign (flipColouring o o' hpair φ) (κ.match_ g) =
      ∏ f ∈ flipIn o o' v, -inSign φ f := by
    rw [Finset.prod_image (match_injOn_flipIn o o' v)]
    refine Finset.prod_congr rfl (fun f hf => ?_)
    have hfint := relInSetAt_subset_internal (mem_flipIn.mp hf).1
    rw [κ.match_invol f hfint]
    exact inSign_flipColouring_of_mem o o' hpair φ (mem_flipIn.mp hf).2
  rw [hkeep, himg,
    prod_inSet_split o o' v (fun g => inSign φ (κ.match_ g)),
    Finset.prod_neg]
  have hsq : ∏ f ∈ flipIn o o' v, inSign φ f =
      (∏ f ∈ flipIn o o' v,
        inSign φ f * inSign φ (κ.match_ f)) *
        ∏ f ∈ flipIn o o' v, inSign φ (κ.match_ f) := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl (fun f _ => ?_)
    rw [mul_assoc, inSign_mul_self, mul_one]
  rw [hsq]
  ring

/-! ## The global sign telescopes -/

/-- The difference flags attached to a vertex. -/
private noncomputable def diffAt (o o' : κ.Orientation)
    (v : W.Vertex) : Finset W.Flag :=
  (orientDiff o o').filter (fun g => W.attach g = Sum.inl v)

private theorem flipIn_disjoint_image (o o' : κ.Orientation)
    (v : W.Vertex) :
    Disjoint (flipIn o o' v) ((flipIn o o' v).image κ.match_) := by
  rw [Finset.disjoint_left]
  intro g hgf hgi
  obtain ⟨f, hf, rfl⟩ := Finset.mem_image.mp hgi
  have hfint := relInSetAt_subset_internal (mem_flipIn.mp hf).1
  have hffalse := (mem_relInSetAt.mp (mem_flipIn.mp hf).1).2.2
  have hmtrue : o.isOut (κ.match_ f) = true := by
    rw [o.match_flip f hfint, hffalse]
    rfl
  have hmfalse := (mem_relInSetAt.mp (mem_flipIn.mp hgf).1).2.2
  rw [hmtrue] at hmfalse
  cases hmfalse

/-- The difference flags at a vertex split into flipped in-flags and
their matches. -/
private theorem diffAt_eq (o o' : κ.Orientation) (v : W.Vertex) :
    diffAt o o' v = (flipIn o o' v).disjUnion
      ((flipIn o o' v).image κ.match_)
      (flipIn_disjoint_image o o' v) := by
  apply Finset.ext
  intro g
  rw [Finset.mem_disjUnion]
  unfold diffAt
  rw [Finset.mem_filter]
  constructor
  · rintro ⟨hgD, hgat⟩
    have hgint := orientDiff_subset_internal o o' hgD
    cases hb : o.isOut g
    · left
      exact mem_flipIn.mpr ⟨mem_relInSetAt.mpr
        ⟨mem_flags_of_internalFlags F hgint, hgat, hb⟩, hgD⟩
    · right
      refine Finset.mem_image.mpr
        ⟨κ.match_ g, ?_, κ.match_invol g hgint⟩
      have hmD := match_mem_orientDiff hgD
      have hmint := κ.match_mem g hgint
      refine mem_flipIn.mpr ⟨mem_relInSetAt.mpr
        ⟨mem_flags_of_internalFlags F hmint,
          κ.match_vertex g hgint v hgat, ?_⟩, hmD⟩
      rw [o.match_flip g hgint, hb]
      rfl
  · rintro (hg | hg)
    · exact ⟨(mem_flipIn.mp hg).2,
        (mem_relInSetAt.mp (mem_flipIn.mp hg).1).2.1⟩
    · obtain ⟨f, hf, rfl⟩ := Finset.mem_image.mp hg
      have hfint := relInSetAt_subset_internal (mem_flipIn.mp hf).1
      exact ⟨match_mem_orientDiff (mem_flipIn.mp hf).2,
        κ.match_vertex f hfint v
          (mem_relInSetAt.mp (mem_flipIn.mp hf).1).2.1⟩

private theorem orientDiff_eq_biUnion (o o' : κ.Orientation) :
    orientDiff o o' =
      Finset.univ.biUnion (fun v => diffAt o o' v) := by
  apply Finset.ext
  intro g
  rw [Finset.mem_biUnion]
  constructor
  · intro hg
    obtain ⟨v, hv⟩ :=
      F.attach_internal_of_mem (orientDiff_subset_internal o o' hg)
    exact ⟨v, Finset.mem_univ v, Finset.mem_filter.mpr ⟨hg, hv⟩⟩
  · rintro ⟨v, _, hv⟩
    exact (Finset.mem_filter.mp hv).1

private theorem diffAt_pairwiseDisjoint (o o' : κ.Orientation) :
    Set.PairwiseDisjoint (↑(Finset.univ : Finset W.Vertex))
      (fun v => diffAt o o' v) := by
  intro v _ w _ hvw
  refine Finset.disjoint_left.mpr (fun g hgv hgw => hvw ?_)
  have h1 := (Finset.mem_filter.mp hgv).2
  have h2 := (Finset.mem_filter.mp hgw).2
  rw [h1] at h2
  exact Sum.inl.inj h2

/-- **The telescoping identity**: the product over all vertices of
the flipped-visit sign ratios is the product of `sign(φ)` over the
whole difference set, which is `1` edge by edge. -/
private theorem flipSign_prod_eq_one {ℓ : ℕ} (o o' : κ.Orientation)
    (hpair : ∀ f ∈ F.internalFlags,
      o.isOut f ≠ o'.isOut f → W.pairing f ∈ F.internalFlags)
    (φ : F.CoreOddColouring ℓ) :
    ∏ v : W.Vertex, ∏ f ∈ flipIn o o' v,
      (inSign φ f * inSign φ (κ.match_ f)) = 1 := by
  have hv : ∀ v : W.Vertex,
      ∏ f ∈ flipIn o o' v,
        (inSign φ f * inSign φ (κ.match_ f)) =
        ∏ g ∈ diffAt o o' v, inSign φ g := by
    intro v
    rw [diffAt_eq o o' v, Finset.prod_disjUnion,
      Finset.prod_image (match_injOn_flipIn o o' v),
      Finset.prod_mul_distrib]
  rw [Finset.prod_congr rfl (fun v _ => hv v),
    ← Finset.prod_biUnion (diffAt_pairwiseDisjoint o o'),
    ← orientDiff_eq_biUnion o o']
  refine Finset.prod_involution (fun g _ => W.pairing g) ?_ ?_ ?_ ?_
  · intro g hg
    have hcore : g ∈ F.coreFlags :=
      F.internalFlags_subset_coreFlags
        (orientDiff_subset_internal o o' hg)
    rw [inSign_pairing φ hcore]
    exact inSign_mul_self φ g
  · exact fun g _ _ => W.pairing_ne g
  · exact fun g hg => pairing_mem_orientDiff hpair hg
  · exact fun g _ => W.pairing_invol g

/-! ## The pair-list reindexing -/

private theorem coreOddPairFn_eq {ℓ : ℕ} (φ : F.CoreOddColouring ℓ) :
    F.coreOddPairFn κ φ =
      fun f => [pairA φ f, pairB (κ₀ := κ) φ f] := rfl

/-- **The per-vertex list identity**: flipping the orientation and
the colouring changes the alternating evaluation by one `−1` per
flipped visit. -/
private theorem evalOdd_coreOddListAt_flip {k ℓ : ℕ}
    (h : MixedFunctional k ℓ) (μ : Multiset (Fin k))
    (o o' : κ.Orientation)
    (hpair : ∀ f ∈ F.internalFlags,
      o.isOut f ≠ o'.isOut f → W.pairing f ∈ F.internalFlags)
    (φ : F.CoreOddColouring ℓ) (v : W.Vertex) :
    h.evalOdd μ
        (F.coreOddListAt o' (flipColouring o o' hpair φ) v) =
      (-1 : ℂ) ^ (flipIn o o' v).card *
        h.evalOdd μ (F.coreOddListAt o φ v) := by
  have Hk : ∀ g ∈ (keepIn o o' v).toList, g ∈ F.internalFlags :=
    fun g hg => relInSetAt_subset_internal
      (mem_keepIn.mp (Finset.mem_toList.mp hg)).1
  have Hf : ∀ g ∈ (flipIn o o' v).toList, g ∈ F.internalFlags :=
    fun g hg => relInSetAt_subset_internal
      (mem_flipIn.mp (Finset.mem_toList.mp hg)).1
  have H2 : ∀ g ∈ (keepIn o o' v).toList ++
      (flipIn o o' v).toList.map κ.match_, g ∈ F.internalFlags := by
    intro g hg
    rcases List.mem_append.mp hg with hg | hg
    · exact Hk g hg
    · obtain ⟨f, hf, rfl⟩ := List.mem_map.mp hg
      exact κ.match_mem f (Hf f hf)
  have H3 : ∀ g ∈ (keepIn o o' v).toList ++ (flipIn o o' v).toList,
      g ∈ F.internalFlags := by
    intro g hg
    rcases List.mem_append.mp hg with hg | hg
    · exact Hk g hg
    · exact Hf g hg
  -- ═══════ BOTH IN-FLAG ENUMERATIONS, SPLIT BY THE FLIP ═══════
  -- The unflipped in-flags are common to the two orientations; the
  -- flipped ones appear under `o'` through the matching.
  have hbase : (F.relInFlagsAt o v).Perm
      ((keepIn o o' v).toList ++ (flipIn o o' v).toList) := by
    rw [← Multiset.coe_eq_coe, relInFlagsAt_coe o v,
      ← Multiset.coe_add, Finset.coe_toList, Finset.coe_toList]
    exact inSet_val_eq o o' v
  have hbase' : (F.relInFlagsAt o' v).Perm
      ((keepIn o o' v).toList ++
        (flipIn o o' v).toList.map κ.match_) := by
    rw [← Multiset.coe_eq_coe, relInFlagsAt_coe o' v,
      ← Multiset.coe_add, Finset.coe_toList, ← Multiset.map_coe,
      Finset.coe_toList]
    rw [inSet_flip_eq o o' v, Finset.disjUnion_val,
      Finset.image_val_of_injOn (fun x hx y hy =>
        match_injOn_flipIn o o' v x (Finset.mem_coe.mp hx) y
          (Finset.mem_coe.mp hy))]
  unfold EdgeSubset.coreOddListAt
  simp only [List.attachWith]
  calc h.evalOdd μ ((List.pmap Subtype.mk (F.relInFlagsAt o' v)
        (fun _ hf => F.mem_internal_of_mem_relInFlagsAt hf)).flatMap
        (F.coreOddPairFn κ (flipColouring o o' hpair φ)))
      = h.evalOdd μ ((List.pmap Subtype.mk
          ((keepIn o o' v).toList ++
            (flipIn o o' v).toList.map κ.match_) H2).flatMap
          (F.coreOddPairFn κ (flipColouring o o' hpair φ))) := by
        have hp := h.evalOdd_flatMap_perm μ
          (F.coreOddPairFn κ (flipColouring o o' hpair φ))
          (fun _ => rfl)
          (perm_pmap Subtype.mk hbase'
            (fun _ hf => F.mem_internal_of_mem_relInFlagsAt hf) H2)
          []
        simpa using hp
    _ = h.evalOdd μ
          ((List.pmap Subtype.mk (keepIn o o' v).toList Hk).flatMap
            (F.coreOddPairFn κ φ) ++
          (List.pmap Subtype.mk (flipIn o o' v).toList Hf).flatMap
            (fun fs => [pairB (κ₀ := κ) φ fs, pairA φ fs])) := by
        rw [List.pmap_append, List.flatMap_append]
        refine congrArg (h.evalOdd μ) (congrArg₂
          (fun x y : List (Fin (2 * ℓ)) => x ++ y) ?_ ?_)
        · refine pmap_flatMap_congr _ _ _ _ _ _ _ ?_
          intro g hg h₁ h₂
          have hgD : g ∉ orientDiff o o' :=
            (mem_keepIn.mp (Finset.mem_toList.mp hg)).2
          have hmD : κ.match_ g ∉ orientDiff o o' :=
            match_notMem_orientDiff h₁ hgD
          show [(flipColouring o o' hpair φ).val
              ⟨g, F.internalFlags_subset_coreFlags h₁⟩,
            oddPartner ℓ ((flipColouring o o' hpair φ).val
              ⟨κ.match_ g, F.internalFlags_subset_coreFlags
                (κ.match_mem _ h₁)⟩)] =
            [φ.val ⟨g, F.internalFlags_subset_coreFlags h₂⟩,
              oddPartner ℓ (φ.val ⟨κ.match_ g,
                F.internalFlags_subset_coreFlags
                  (κ.match_mem _ h₂)⟩)]
          rw [flipColouring_val_of_notMem o o' hpair φ _ hgD,
            flipColouring_val_of_notMem o o' hpair φ _ hmD]
        · rw [List.pmap_map]
          refine pmap_flatMap_congr _ _ _ _ _ _ _ ?_
          intro f hf h₁ h₂
          have hfD : f ∈ orientDiff o o' :=
            (mem_flipIn.mp (Finset.mem_toList.mp hf)).2
          have hmD : κ.match_ f ∈ orientDiff o o' :=
            match_mem_orientDiff hfD
          have hsub : (⟨κ.match_ (κ.match_ f),
              F.internalFlags_subset_coreFlags
                (κ.match_mem _ h₁)⟩ :
              {g : W.Flag // g ∈ F.coreFlags}) =
              ⟨f, F.internalFlags_subset_coreFlags h₂⟩ :=
            Subtype.ext (κ.match_invol f h₂)
          show [(flipColouring o o' hpair φ).val
              ⟨κ.match_ f, F.internalFlags_subset_coreFlags h₁⟩,
            oddPartner ℓ ((flipColouring o o' hpair φ).val
              ⟨κ.match_ (κ.match_ f),
                F.internalFlags_subset_coreFlags
                  (κ.match_mem _ h₁)⟩)] =
            [pairB (κ₀ := κ) φ ⟨f, h₂⟩, pairA φ ⟨f, h₂⟩]
          rw [hsub,
            flipColouring_val_of_mem o o' hpair φ _ hmD,
            flipColouring_val_of_mem o o' hpair φ _ hfD,
            oddPartner_invol]
          rfl
    _ = (-1 : ℂ) ^ (flipIn o o' v).card * h.evalOdd μ
          ((List.pmap Subtype.mk (keepIn o o' v).toList Hk).flatMap
            (F.coreOddPairFn κ φ) ++
          (List.pmap Subtype.mk (flipIn o o' v).toList Hf).flatMap
            (fun fs => [pairA φ fs, pairB (κ₀ := κ) φ fs])) := by
        have hrev := evalOdd_flatMap_rev h μ (pairA φ)
          (pairB (κ₀ := κ) φ)
          (List.pmap Subtype.mk (flipIn o o' v).toList Hf)
          ((List.pmap Subtype.mk (keepIn o o' v).toList Hk).flatMap
            (F.coreOddPairFn κ φ))
        rw [hrev, List.length_pmap, Finset.length_toList]
    _ = (-1 : ℂ) ^ (flipIn o o' v).card * h.evalOdd μ
          ((List.pmap Subtype.mk
            ((keepIn o o' v).toList ++ (flipIn o o' v).toList)
            H3).flatMap (F.coreOddPairFn κ φ)) := by
        rw [List.pmap_append, List.flatMap_append]
        rw [coreOddPairFn_eq (κ := κ) φ]
    _ = (-1 : ℂ) ^ (flipIn o o' v).card * h.evalOdd μ
          ((List.pmap Subtype.mk (F.relInFlagsAt o v)
            (fun _ hf =>
              F.mem_internal_of_mem_relInFlagsAt hf)).flatMap
            (F.coreOddPairFn κ φ)) := by
        have hp := h.evalOdd_flatMap_perm μ (F.coreOddPairFn κ φ)
          (fun _ => rfl)
          (perm_pmap Subtype.mk hbase.symm H3
            (fun _ hf => F.mem_internal_of_mem_relInFlagsAt hf))
          []
        simp only [List.nil_append] at hp
        rw [hp]

/-! ## Assembly -/

/-- **The vertex-product identity**: the full product over vertices
of sign times alternating evaluation is invariant under flipping the
orientation together with the colouring. -/
private theorem vertexProd_flip {k ℓ : ℕ} (h : MixedFunctional k ℓ)
    (o o' : κ.Orientation)
    (hpair : ∀ f ∈ F.internalFlags,
      o.isOut f ≠ o'.isOut f → W.pairing f ∈ F.internalFlags)
    (φ : F.CoreOddColouring ℓ) (μf : W.Vertex → Multiset (Fin k)) :
    ∏ v : W.Vertex,
        ((F.coreOddSignAt o' (flipColouring o o' hpair φ) v : ℂ) *
          h.evalOdd (μf v)
            (F.coreOddListAt o' (flipColouring o o' hpair φ) v)) =
      ∏ v : W.Vertex,
        ((F.coreOddSignAt o φ v : ℂ) *
          h.evalOdd (μf v) (F.coreOddListAt o φ v)) := by
  have hglobal : ∏ v : W.Vertex, ∏ f ∈ flipIn o o' v,
      ((inSign φ f : ℂ) * (inSign φ (κ.match_ f) : ℂ)) = 1 := by
    have h1 := flipSign_prod_eq_one o o' hpair φ
    have h2 : ((∏ v : W.Vertex, ∏ f ∈ flipIn o o' v,
        (inSign φ f * inSign φ (κ.match_ f)) : ℤ) : ℂ) = 1 := by
      rw [h1]
      norm_num
    push_cast at h2
    exact h2
  have hv : ∀ v : W.Vertex,
      ((F.coreOddSignAt o' (flipColouring o o' hpair φ) v : ℂ) *
        h.evalOdd (μf v)
          (F.coreOddListAt o' (flipColouring o o' hpair φ) v)) =
      (∏ f ∈ flipIn o o' v,
        ((inSign φ f : ℂ) * (inSign φ (κ.match_ f) : ℂ))) *
        ((F.coreOddSignAt o φ v : ℂ) *
          h.evalOdd (μf v) (F.coreOddListAt o φ v)) := by
    intro v
    rw [coreOddSignAt_flip o o' hpair φ v,
      evalOdd_coreOddListAt_flip h (μf v) o o' hpair φ v]
    have hsq : (-1 : ℂ) ^ (flipIn o o' v).card *
        (-1 : ℂ) ^ (flipIn o o' v).card = 1 := by
      rw [← mul_pow]
      norm_num
    push_cast
    calc ((-1 : ℂ) ^ (flipIn o o' v).card *
          (∏ f ∈ flipIn o o' v,
            ((inSign φ f : ℂ) * (inSign φ (κ.match_ f) : ℂ))) *
          (F.coreOddSignAt o φ v : ℂ)) *
        ((-1 : ℂ) ^ (flipIn o o' v).card *
          h.evalOdd (μf v) (F.coreOddListAt o φ v)) =
        ((-1 : ℂ) ^ (flipIn o o' v).card *
          (-1 : ℂ) ^ (flipIn o o' v).card) *
        ((∏ f ∈ flipIn o o' v,
            ((inSign φ f : ℂ) * (inSign φ (κ.match_ f) : ℂ))) *
          ((F.coreOddSignAt o φ v : ℂ) *
            h.evalOdd (μf v) (F.coreOddListAt o φ v))) := by
          ring
      _ = (∏ f ∈ flipIn o o' v,
            ((inSign φ f : ℂ) * (inSign φ (κ.match_ f) : ℂ))) *
          ((F.coreOddSignAt o φ v : ℂ) *
            h.evalOdd (μf v) (F.coreOddListAt o φ v)) := by
          rw [hsq, one_mul]
  rw [Finset.prod_congr rfl (fun v _ => hv v),
    Finset.prod_mul_distrib, hglobal, one_mul]

/-- **The colouring-sum identity**: the constrained inner sum over
core odd colourings is invariant under the orientation flip. -/
private theorem phiSum_flip {k ℓ : ℕ} (h : MixedFunctional k ℓ)
    (st : GenBoundaryState k ℓ α) (o o' : κ.Orientation)
    (hpair : ∀ f ∈ F.internalFlags,
      o.isOut f ≠ o'.isOut f → W.pairing f ∈ F.internalFlags)
    (μf : W.Vertex → Multiset (Fin k)) :
    ∑ φ : F.CoreOddColouring ℓ,
        (if F.coreOddBoundaryMatch st φ then
          ∏ v : W.Vertex, ((F.coreOddSignAt o' φ v : ℂ) *
            h.evalOdd (μf v) (F.coreOddListAt o' φ v))
        else 0) =
      ∑ φ : F.CoreOddColouring ℓ,
        (if F.coreOddBoundaryMatch st φ then
          ∏ v : W.Vertex, ((F.coreOddSignAt o φ v : ℂ) *
            h.evalOdd (μf v) (F.coreOddListAt o φ v))
        else 0) := by
  refine ((Equiv.sum_comp (Function.Involutive.toPerm _
      (flipColouring_involutive o o' hpair (ℓ := ℓ))) _).symm).trans
    (Finset.sum_congr rfl (fun φ _ => ?_))
  show (if F.coreOddBoundaryMatch st (flipColouring o o' hpair φ)
      then ∏ v : W.Vertex,
        ((F.coreOddSignAt o' (flipColouring o o' hpair φ) v : ℂ) *
          h.evalOdd (μf v)
            (F.coreOddListAt o' (flipColouring o o' hpair φ) v))
      else 0) =
    (if F.coreOddBoundaryMatch st φ then
      ∏ v : W.Vertex, ((F.coreOddSignAt o φ v : ℂ) *
        h.evalOdd (μf v) (F.coreOddListAt o φ v))
    else 0)
  exact if_congr
    (coreOddBoundaryMatch_flipColouring st o o' hpair φ)
    (vertexProd_flip h o o' hpair φ μf) rfl

end Diff

/-! ## The orientation-invariance theorems -/

open Classical in
-- Raised budget: invariance is proved over all internal flags at
-- once, so the summand unfolds for both orientations.
/-- **Invariance under circuit flips**: for a fixed relative
transition system,
the corrected constrained summand is invariant under changing the
orientation, provided every internal flag on which the orientations
disagree lies on a fully internal edge.  (Unrestricted invariance is
false: flipping a boundary-to-boundary path changes the summand —
see the module docstring.) -/
theorem throughSummand_orientation_invariant [LinearOrder α]
    (F : EdgeSubset W) {k ℓ : ℕ} (h : MixedFunctional k ℓ)
    (st : GenBoundaryState k ℓ α)
    (hbnd : genBoundarySubsetMatches W F.flags st)
    {κ : F.RelTransitionSystem} (o o' : κ.Orientation)
    (hpair : ∀ f ∈ F.internalFlags,
      o.isOut f ≠ o'.isOut f → W.pairing f ∈ F.internalFlags)
    (c : ℕ) :
    F.throughSummand h st hbnd o c =
      F.throughSummand h st hbnd o' c := by
  unfold EdgeSubset.throughSummand
  congr 1
  refine Finset.sum_congr rfl (fun ψ _ => ?_)
  exact if_congr Iff.rfl
    (phiSum_flip h st o o' hpair (F.evenColoursAt ψ)).symm rfl

end EdgeSubset

end RS

-- The counterexample lives outside the `open scoped Classical`
-- region: its concrete finite objects are decided computationally.
namespace RS

/-!
## Necessity of the hypothesis: a path-flip counterexample

One vertex with two pendant edges to boundary labels `0 < 1`, the
matching joining the two internal flags, and odd state colours `0`
and `1` (with `ℓ = 2`).  The odd boundary constraint pins the unique
contributing colouring; the two orientations of the resulting
boundary-to-boundary path give summands `−1` and `0` for the
functional supported on the colour set `{0, 3}`.
-/

section Counterexample

open EdgeSubset

-- Deliberately reducible: instance search must see the concrete
-- carrier types (`Fin 4`, `Unit`) of this example object.
/-- One vertex, two pendant edges: flags `0, 1` at the vertex, flags
`2, 3` at boundary labels `0, 1`; edges `{0, 2}` and `{1, 3}`. -/
@[reducible] private def exFragment : Fragment (Fin 2) where
  Flag := Fin 4
  Vertex := Unit
  attach := ![Sum.inl (), Sum.inl (), Sum.inr 0, Sum.inr 1]
  pairing := ![2, 3, 0, 1]
  pairing_invol := by decide
  pairing_ne := by decide
  boundaryFlag := ![2, 3]
  attach_boundaryFlag := by decide
  eq_boundaryFlag := by decide
  circles := 0

/-- The full edge subset. -/
private def exSubset : EdgeSubset exFragment :=
  ⟨Finset.univ, fun f _ => Finset.mem_univ (exFragment.pairing f)⟩

private instance : IsEmpty {f : exFragment.Flag // f ∉ exSubset.flags} :=
  ⟨fun f => f.prop (Finset.mem_univ f.val)⟩

private instance : Subsingleton (exSubset.EvenColouring 0) :=
  ⟨fun _ _ => Subtype.ext (funext fun f => isEmptyElim f)⟩

end Counterexample

end RS
