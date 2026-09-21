/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

import LeanPool.RegtsSevenster.RS.Novel.Coordinates.OrbitCard
import LeanPool.RegtsSevenster.RS.Novel.Skein.InvolutionCard

/-!
# Directed perfect matchings and the rotation of their union

A directed perfect matching is a fixed-point-free involution
together with a choice of tail at each edge.  Two of them on the
same set have a union in which every point carries one arc of each,
so the union decomposes into alternating cycles.

When the union is Eulerian — at every point one arc enters and one
leaves — the cycles are coherently directed, and following the arc
that leaves is a permutation whose cycles are exactly the union's
components.  That permutation carries the second matching to the
first, direction and all, and its sign is `(-1)` to the number of
components, because every component has even length.

This is the sign lemma the Gram identity for mixed partition
functions runs on: the product of two matchings' signs is `(-1)` to
the number of components of their union.
-/

namespace RS

open Equiv Function

/-- A directed perfect matching: a fixed-point-free involution with
a chosen tail at each edge. -/
structure DirMatching (α : Type) where
  /-- The matched partner. -/
  edge : α → α
  /-- The partner map is an involution. -/
  edge_invol : ∀ a, edge (edge a) = a
  /-- No point is its own partner. -/
  edge_ne : ∀ a, edge a ≠ a
  /-- Whether the arc at this point leaves it. -/
  tail : α → Bool
  /-- Each arc leaves exactly one of its two ends. -/
  tail_flip : ∀ a, tail (edge a) = !tail a

namespace DirMatching

variable {α : Type}

/-- **The union is Eulerian**: at every point exactly one of the two
matchings' arcs leaves it. -/
def Alternating (M N : DirMatching α) : Prop :=
  ∀ a, N.tail a = !M.tail a

/-- The rotation of an Eulerian union: follow the arc that leaves. -/
def rot (M N : DirMatching α) (a : α) : α :=
  if M.tail a then M.edge a else N.edge a

/-- The step backwards: follow the arc that enters. -/
def rotInv (M N : DirMatching α) (a : α) : α :=
  if M.tail a then N.edge a else M.edge a

variable {M N : DirMatching α}

/-- Along an Eulerian union the second matching's tails are the
first's, flipped. -/
theorem tail_edge_alt (h : Alternating M N) (a : α) :
    M.tail (N.edge a) = !M.tail a := by
  have h1 : N.tail (N.edge a) = !N.tail a := N.tail_flip a
  rw [h (N.edge a), h a, Bool.not_not] at h1
  rw [← h1, Bool.not_not]

/-- The rotation lands on the other end of the arc it followed. -/
theorem tail_rot (h : Alternating M N) (a : α) :
    M.tail (M.rot N a) = !M.tail a := by
  unfold rot
  by_cases ha : M.tail a = true
  · rw [if_pos ha, M.tail_flip a]
  · rw [if_neg ha, tail_edge_alt h a]

/-- The rotation is undone by the backward step. -/
theorem rotInv_rot (h : Alternating M N) (a : α) :
    M.rotInv N (M.rot N a) = a := by
  unfold rot rotInv
  by_cases ha : M.tail a = true
  · rw [if_pos ha, if_neg (by rw [M.tail_flip a, ha]; simp),
      M.edge_invol]
  · rw [if_neg ha, if_pos (by rw [tail_edge_alt h a]; simp [ha]),
      N.edge_invol]

/-- And undoes it. -/
theorem rot_rotInv (h : Alternating M N) (a : α) :
    M.rot N (M.rotInv N a) = a := by
  unfold rot rotInv
  by_cases ha : M.tail a = true
  · rw [if_pos ha, if_neg (by rw [tail_edge_alt h a, ha]; simp),
      N.edge_invol]
  · rw [if_neg ha, if_pos (by rw [M.tail_flip a]; simp [ha]),
      M.edge_invol]

/-- **The rotation of an Eulerian union**, as a permutation. -/
def rotPerm (M N : DirMatching α) (h : Alternating M N) :
    Equiv.Perm α where
  toFun := M.rot N
  invFun := M.rotInv N
  left_inv := rotInv_rot h
  right_inv := rot_rotInv h

/-- The rotation permutation acts by following the arc that
leaves. -/
@[simp]
theorem rotPerm_apply (h : Alternating M N) (a : α) :
    M.rotPerm N h a = M.rot N a := rfl

/-- **The rotation reaches the first matching's partner.**  Together
with the next lemma this is the statement that the rotation's orbits
are exactly the connected components of the union: one step of the
rotation, forwards or backwards, crosses each of the two arcs at a
point. -/
theorem sameCycle_rot_edge (h : Alternating M N) (a : α) :
    (M.rotPerm N h).SameCycle a (M.edge a) := by
  by_cases ha : M.tail a = true
  · exact ⟨1, by
      show (M.rotPerm N h ^ (1 : ℤ)) a = M.edge a
      rw [zpow_one]
      show M.rot N a = M.edge a
      rw [rot, if_pos ha]⟩
  · exact ⟨-1, by
      show (M.rotPerm N h ^ (-1 : ℤ)) a = M.edge a
      rw [zpow_neg, zpow_one]
      show (M.rotPerm N h).symm a = M.edge a
      show M.rotInv N a = M.edge a
      rw [rotInv, if_neg ha]⟩

/-- **The rotation reaches the second matching's partner.** -/
theorem sameCycle_rot_edge' (h : Alternating M N) (a : α) :
    (M.rotPerm N h).SameCycle a (N.edge a) := by
  by_cases ha : M.tail a = true
  · exact ⟨-1, by
      show (M.rotPerm N h ^ (-1 : ℤ)) a = N.edge a
      rw [zpow_neg, zpow_one]
      show (M.rotPerm N h).symm a = N.edge a
      show M.rotInv N a = N.edge a
      rw [rotInv, if_pos ha]⟩
  · exact ⟨1, by
      show (M.rotPerm N h ^ (1 : ℤ)) a = N.edge a
      rw [zpow_one]
      show M.rot N a = N.edge a
      rw [rot, if_neg ha]⟩

/-- **A directed perfect matching forces an even ground set**: the
partner map exchanges the tails with the heads. -/
theorem even_card [Fintype α] [DecidableEq α] (M : DirMatching α) :
    Even (Fintype.card α) := by
  classical
  have hcard : (Finset.univ.filter (fun a : α => M.tail a = true)).card
      = (Finset.univ.filter (fun a : α => ¬ (M.tail a = true))).card := by
    refine Finset.card_nbij' (i := M.edge) (j := M.edge) ?_ ?_ ?_ ?_
    · intro a ha
      simp only [Finset.coe_filter, Set.mem_setOf_eq,
        Finset.mem_univ, true_and] at ha ⊢
      rw [M.tail_flip a, ha]
      simp
    · intro b hb
      simp only [Finset.coe_filter, Set.mem_setOf_eq,
        Finset.mem_univ, true_and] at hb ⊢
      rw [M.tail_flip b]
      simpa using hb
    · exact fun a _ => M.edge_invol a
    · exact fun b _ => M.edge_invol b
  have hsum := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset α)) (p := fun a : α => M.tail a = true)
  refine ⟨(Finset.univ.filter (fun a : α => M.tail a = true)).card, ?_⟩
  rw [← Finset.card_univ, ← hsum, hcard]

/-- The tails of a directed matching, as a subtype. -/
abbrev Tail (M : DirMatching α) : Type := {a : α // M.tail a = true}

/-- **The partner map exchanges tails and heads.** -/
noncomputable def tailHeadEquiv (M : DirMatching α) :
    {a : α // ¬ (M.tail a = true)} ≃ {a : α // M.tail a = true} where
  toFun a := ⟨M.edge a.val, by rw [M.tail_flip]; simpa using a.prop⟩
  invFun a := ⟨M.edge a.val, by rw [M.tail_flip, a.prop]; simp⟩
  left_inv a := Subtype.ext (M.edge_invol a.val)
  right_inv a := Subtype.ext (M.edge_invol a.val)

/-- **The ground set is twice the tails.** -/
theorem two_mul_card_tail [Fintype α] [DecidableEq α]
    (M : DirMatching α) :
    2 * Fintype.card M.Tail = Fintype.card α := by
  have h1 : Fintype.card {a : α // ¬ (M.tail a = true)}
      = Fintype.card M.Tail :=
    Fintype.card_congr M.tailHeadEquiv
  have h2 := Fintype.card_subtype_compl
    (p := fun a : α => M.tail a = true)
  have h3 : Fintype.card M.Tail ≤ Fintype.card α :=
    Fintype.card_subtype_le _
  have h4 : Fintype.card M.Tail
      = Fintype.card {x : α // M.tail x = true} :=
    Fintype.card_congr (Equiv.refl _)
  rw [h1, h4] at h2
  rw [h4] at h3 ⊢
  omega

/-! ### Symmetries of a directed matching are even

A permutation commuting with the partner map and preserving the
tails is determined by its restriction to the tails, and the
restriction to the heads is that same permutation conjugated by the
partner map.  The two restrictions therefore have equal sign, and
their product — the whole permutation — has sign one.
-/

/-- A symmetry of a directed matching: it commutes with the partner
map and fixes each point's direction. -/
structure Stab (M : DirMatching α) (g : Equiv.Perm α) : Prop where
  /-- It commutes with the partner map. -/
  edge : ∀ a, g (M.edge a) = M.edge (g a)
  /-- It preserves the tails. -/
  tail : ∀ a, M.tail (g a) = M.tail a

/-- **A symmetry of a directed matching is even.** -/
theorem sign_of_stab [Fintype α] [DecidableEq α] {M : DirMatching α}
    {g : Equiv.Perm α} (h : Stab M g) : Perm.sign g = 1 := by
  classical
  have hp' : ∀ a, (M.tail (g a) = true) ↔ (M.tail a = true) :=
    fun a => by rw [h.tail a]
  have hdecomp := perm_eq_ofSubtype_mul g (fun a => M.tail a = true) hp'
  let e : {a : α // ¬ (M.tail a = true)} ≃ {a : α // M.tail a = true} :=
    { toFun := fun a => ⟨M.edge a.val, by
        rw [M.tail_flip]; simpa using a.prop⟩
      invFun := fun a => ⟨M.edge a.val, by
        rw [M.tail_flip, a.prop]; simp⟩
      left_inv := fun a => Subtype.ext (M.edge_invol a.val)
      right_inv := fun a => Subtype.ext (M.edge_invol a.val) }
  have hconj : g.subtypePerm (p := fun a => M.tail a = true) hp'
      = e.permCongr (g.subtypePerm
        (p := fun a => ¬ (M.tail a = true)) (fun a => (hp' a).not)) := by
    refine Equiv.ext (fun a => Subtype.ext ?_)
    change g a.val = M.edge (g (M.edge a.val))
    rw [h.edge a.val, M.edge_invol]
  have hsign : Perm.sign
        (g.subtypePerm (p := fun a => M.tail a = true) hp')
      = Perm.sign (g.subtypePerm
        (p := fun a => ¬ (M.tail a = true)) (fun a => (hp' a).not)) := by
    rw [hconj, Equiv.Perm.sign_permCongr]
  rw [hdecomp, map_mul, Equiv.Perm.sign_ofSubtype,
    Equiv.Perm.sign_ofSubtype, ← hsign]
  exact Int.units_mul_self _

/-! ### The rotation carries one matching to the other -/

/-- **The rotation conjugates the second matching into the
first.** -/
theorem edge_rot (h : Alternating M N) (a : α) :
    M.edge (M.rot N a) = M.rot N (N.edge a) := by
  unfold rot
  by_cases ha : M.tail a = true
  · rw [if_pos ha, M.edge_invol,
      if_neg (by rw [tail_edge_alt h a, ha]; simp), N.edge_invol]
  · rw [if_neg ha, if_pos (by rw [tail_edge_alt h a]; simp [ha])]

/-- **The rotation carries the second matching's directions to the
first's.** -/
theorem tail_rot_eq (h : Alternating M N) (a : α) :
    M.tail (M.rot N a) = N.tail a := by
  rw [tail_rot h a, h a]

/-! ### Its sign counts the components -/

/-- **The rotation's sign is `(-1)` to its number of orbits.**  The
orbits are the components of the union, and each has even length, so
this is the sign lemma for a matching pair. -/
theorem sign_rotPerm [Fintype α] [DecidableEq α] (h : Alternating M N)
    (hcard : Even (Fintype.card α)) :
    ((Perm.sign (M.rotPerm N h) : ℤ) : ℂ)
      = (-1 : ℂ) ^ orbitCount (M.rotPerm N h) := by
  rw [neg_one_pow_orbitCount, Even.neg_one_pow hcard, one_mul]

/-! ### Every carrier has the rotation's sign

A permutation carrying one directed matching to the other differs
from the rotation by a symmetry of the target, so all carriers share
the rotation's sign — and that sign counts the union's components.
This is the matching-sign lemma the Gram identity uses.
-/

/-- A permutation carrying one directed matching onto another. -/
structure Carries (M N : DirMatching α) (σ : Equiv.Perm α) : Prop where
  /-- It intertwines the two partner maps. -/
  edge : ∀ a, σ (N.edge a) = M.edge (σ a)
  /-- It matches the directions. -/
  tail : ∀ a, M.tail (σ a) = N.tail a

/-- A carrier's inverse intertwines the partner maps the other
way. -/
theorem Carries.edge_symm {σ : Equiv.Perm α} (hσ : Carries M N σ)
    (a : α) : σ.symm (M.edge a) = N.edge (σ.symm a) := by
  have := hσ.edge (σ.symm a)
  rw [Equiv.apply_symm_apply] at this
  rw [← this, Equiv.symm_apply_apply]

/-- **The rotation carries.** -/
theorem carries_rotPerm (h : Alternating M N) :
    Carries M N (M.rotPerm N h) :=
  ⟨fun a => (edge_rot h a).symm, tail_rot_eq h⟩

/-- **Any two carriers have the same sign.**  They differ by a
symmetry of the target, and symmetries are even.  No Eulerian
hypothesis is needed: this is what makes a directed matching's sign
well defined. -/
theorem sign_eq_of_carries_pair [Fintype α] [DecidableEq α]
    {σ τ : Equiv.Perm α} (hσ : Carries M N σ) (hτ : Carries M N τ) :
    Perm.sign σ = Perm.sign τ := by
  have hg : Stab M (σ * τ⁻¹) := by
    constructor
    · intro a
      show σ (τ.symm (M.edge a)) = M.edge (σ (τ.symm a))
      rw [hτ.edge_symm a, hσ.edge]
    · intro a
      show M.tail (σ (τ.symm a)) = M.tail a
      rw [hσ.tail]
      conv_rhs => rw [← Equiv.apply_symm_apply τ a]
      rw [hτ.tail]
  have h1 := sign_of_stab hg
  rw [map_mul, map_inv] at h1
  exact mul_inv_eq_one.mp h1

/-! ### A carrier always exists

RS21 speaks of "a permutation that sends `M(ω,κ)` to the standard
matching" without exhibiting one.  Any bijection between the two
matchings' tails extends over the partner maps to a carrier, and
the tails are half the ground set on both sides, so such a
bijection exists whenever the ground sets agree.
-/

/-- The carrier built from a bijection of tails: send a tail where
the bijection does, and a head to the partner of its tail's
image. -/
noncomputable def ofTailEquiv (M N : DirMatching α)
    (b : N.Tail ≃ M.Tail) : Equiv.Perm α where
  toFun a :=
    if h : N.tail a = true then (b ⟨a, h⟩).val
    else M.edge (b ⟨N.edge a, by
      rw [N.tail_flip]; simpa using h⟩).val
  invFun a :=
    if h : M.tail a = true then (b.symm ⟨a, h⟩).val
    else N.edge (b.symm ⟨M.edge a, by
      rw [M.tail_flip]; simpa using h⟩).val
  left_inv a := by
    by_cases h : N.tail a = true
    · have hm : M.tail (b ⟨a, h⟩).val = true := (b ⟨a, h⟩).prop
      simp only [dif_pos h, dif_pos hm]
      have : (⟨(b ⟨a, h⟩).val, hm⟩ : M.Tail) = b ⟨a, h⟩ := rfl
      rw [this, Equiv.symm_apply_apply]
    · have hne : N.tail (N.edge a) = true := by
        rw [N.tail_flip]; simpa using h
      have hm : M.tail (b ⟨N.edge a, hne⟩).val = true :=
        (b ⟨N.edge a, hne⟩).prop
      have hm' : ¬ (M.tail (M.edge (b ⟨N.edge a, hne⟩).val) = true) := by
        rw [M.tail_flip, hm]; simp
      simp only [dif_neg h, dif_neg hm', M.edge_invol]
      have : (⟨(b ⟨N.edge a, hne⟩).val, hm⟩ : M.Tail)
          = b ⟨N.edge a, hne⟩ := rfl
      rw [this, Equiv.symm_apply_apply, N.edge_invol]
  right_inv a := by
    by_cases h : M.tail a = true
    · have hn : N.tail (b.symm ⟨a, h⟩).val = true := (b.symm ⟨a, h⟩).prop
      simp only [dif_pos h, dif_pos hn]
      have : (⟨(b.symm ⟨a, h⟩).val, hn⟩ : N.Tail) = b.symm ⟨a, h⟩ := rfl
      rw [this, Equiv.apply_symm_apply]
    · have hme : M.tail (M.edge a) = true := by
        rw [M.tail_flip]; simpa using h
      have hn : N.tail (b.symm ⟨M.edge a, hme⟩).val = true :=
        (b.symm ⟨M.edge a, hme⟩).prop
      have hn' : ¬ (N.tail (N.edge (b.symm ⟨M.edge a, hme⟩).val) = true) := by
        rw [N.tail_flip, hn]; simp
      simp only [dif_neg h, dif_neg hn', N.edge_invol]
      have : (⟨(b.symm ⟨M.edge a, hme⟩).val, hn⟩ : N.Tail)
          = b.symm ⟨M.edge a, hme⟩ := rfl
      rw [this, Equiv.apply_symm_apply, M.edge_invol]

/-- **The tail bijection's extension carries.** -/
theorem carries_ofTailEquiv [Fintype α] [DecidableEq α]
    (M N : DirMatching α)
    (b : N.Tail ≃ M.Tail) : Carries M N (ofTailEquiv M N b) := by
  constructor
  · intro a
    by_cases h : N.tail a = true
    · have hne : ¬ (N.tail (N.edge a) = true) := by
        rw [N.tail_flip, h]; simp
      show (if h' : N.tail (N.edge a) = true then _ else _) = _
      rw [dif_neg hne]
      show M.edge (b ⟨N.edge (N.edge a), _⟩).val
        = M.edge (if h' : N.tail a = true then (b ⟨a, h'⟩).val else _)
      rw [dif_pos h]
      exact congrArg (fun z : M.Tail => M.edge z.val)
        (congrArg b (Subtype.ext (N.edge_invol a)))
    · have hne : N.tail (N.edge a) = true := by
        rw [N.tail_flip]; simpa using h
      show (if h' : N.tail (N.edge a) = true then (b ⟨N.edge a, h'⟩).val
          else _) = _
      rw [dif_pos hne]
      show _ = M.edge (if h' : N.tail a = true then _
        else M.edge (b ⟨N.edge a, _⟩).val)
      rw [dif_neg h, M.edge_invol]
  · intro a
    by_cases h : N.tail a = true
    · show M.tail (if h' : N.tail a = true then (b ⟨a, h'⟩).val else _)
        = N.tail a
      rw [dif_pos h, h]
      exact (b ⟨a, h⟩).prop
    · have hne : N.tail (N.edge a) = true := by
        rw [N.tail_flip]; simpa using h
      show M.tail (if h' : N.tail a = true then _
        else M.edge (b ⟨N.edge a, _⟩).val) = N.tail a
      rw [dif_neg h, M.tail_flip, (b ⟨N.edge a, hne⟩).prop]
      simpa using (Bool.eq_false_iff.mpr h).symm

/-- **A carrier exists between any two directed matchings on the
same set.** -/
theorem exists_carries [Fintype α] [DecidableEq α] (M N : DirMatching α) :
    ∃ σ : Equiv.Perm α, Carries M N σ := by
  have hcard : Fintype.card N.Tail = Fintype.card M.Tail := by
    have h1 := M.two_mul_card_tail
    have h2 := N.two_mul_card_tail
    omega
  exact ⟨ofTailEquiv M N (Fintype.equivOfCardEq hcard),
    carries_ofTailEquiv M N _⟩

/-! ### The sign of a directed matching

RS21 fixes a reference matching — the one with arcs
`(i₁,i₂),…,(i_{|S|−1},i_{|S|})` — and takes a matching's sign to be
that of any permutation carrying it to the reference.  Well
definedness is `sign_eq_of_carries_pair`.  What the Gram identity
uses is not the sign itself but the product of two of them, and
that product is the sign of a carrier between them — independent of
which reference was fixed.
-/

/-- Carriers compose. -/
theorem Carries.comp {P : DirMatching α} {σ τ : Equiv.Perm α}
    (hσ : Carries M N σ) (hτ : Carries N P τ) :
    Carries M P (σ * τ) := by
  constructor
  · intro a
    show σ (τ (P.edge a)) = M.edge (σ (τ a))
    rw [hτ.edge a, hσ.edge (τ a)]
  · intro a
    show M.tail (σ (τ a)) = P.tail a
    rw [hσ.tail (τ a), hτ.tail a]

/-- Carriers invert. -/
theorem Carries.inv {σ : Equiv.Perm α} (hσ : Carries M N σ) :
    Carries N M σ⁻¹ := by
  constructor
  · intro a
    exact hσ.edge_symm a
  · intro a
    show N.tail (σ.symm a) = M.tail a
    conv_rhs => rw [← Equiv.apply_symm_apply σ a]
    rw [hσ.tail]

/-- **The sign of a directed matching against a reference.** -/
noncomputable def sgnRel [Fintype α] [DecidableEq α] (R M : DirMatching α) : ℤˣ
  :=
  Perm.sign (Classical.choose (exists_carries R M))

/-- The sign is that of any carrier to the reference. -/
theorem sgnRel_eq_of_carries [Fintype α] [DecidableEq α] (R M : DirMatching α)
    {σ : Equiv.Perm α} (hσ : Carries R M σ) :
    sgnRel R M = Perm.sign σ :=
  sign_eq_of_carries_pair (Classical.choose_spec (exists_carries R M))
    hσ

/-- **The product of two matchings' signs is the sign of a carrier
between them**, whatever reference was fixed. -/
theorem sgnRel_mul_sgnRel [Fintype α] [DecidableEq α] (R M N : DirMatching α)
    {σ : Equiv.Perm α} (hσ : Carries M N σ) :
    sgnRel R M * sgnRel R N = Perm.sign σ := by
  obtain ⟨σM, hσM⟩ := exists_carries R M
  have hN : sgnRel R N = Perm.sign σM * Perm.sign σ := by
    rw [← map_mul]
    exact sgnRel_eq_of_carries R N (hσM.comp hσ)
  rw [sgnRel_eq_of_carries R M hσM, hN, ← mul_assoc,
    Int.units_mul_self, one_mul]

/-! ### The interface matching

Composing two fragments identifies each label of the first with the
same label of the second.  On the labels that is a directed perfect
matching in its own right — the one RS21 pairs with the chord
matching to form the union whose components count the circuits the
gluing closes.
-/

/-- **The interface matching**: each label of one side paired with
the same label of the other. -/
def interfaceMatching (γ : Type) : DirMatching (γ ⊕ γ) where
  edge := Sum.swap
  edge_invol x := by rcases x with a | a <;> rfl
  edge_ne x := by rcases x with a | a <;> simp
  tail := Sum.isLeft
  tail_flip x := by rcases x with a | a <;> rfl

/-- The interface matching pairs a label with its copy on the other
side. -/
@[simp] theorem interfaceMatching_edge {γ : Type} (x : γ ⊕ γ) :
    (interfaceMatching γ).edge x = x.swap := rfl

/-- Its arcs are directed out of the left side. -/
@[simp] theorem interfaceMatching_tail {γ : Type} (x : γ ⊕ γ) :
    (interfaceMatching γ).tail x = x.isLeft := rfl

/-! ### The standard matching

RS21 fixes the matching with arcs `(i₁,i₂),…,(i_{|S|−1},i_{|S|})`
on `S = {i₁ < ⋯ < i_{|S|}}`.  On `Fin (2m)` that is the pairing of
`2j` with `2j+1`, directed upward; on any linearly ordered set of
even size it is that one transported along the order isomorphism.
-/

/-- Transport a directed matching along an equivalence. -/
def map {β : Type} (e : α ≃ β) (M : DirMatching α) : DirMatching β where
  edge b := e (M.edge (e.symm b))
  edge_invol b := by simp [M.edge_invol]
  edge_ne b := by
    intro hx
    refine M.edge_ne (e.symm b) ?_
    have h2 := congrArg e.symm hx
    rwa [Equiv.symm_apply_apply] at h2
  tail b := M.tail (e.symm b)
  tail_flip b := by
    simp only [Equiv.symm_apply_apply]
    exact M.tail_flip _

/-- **The standard directed matching on `Fin (2m)`**: `2j` paired
with `2j+1`, directed upward. -/
def finStd (m : ℕ) : DirMatching (Fin (2 * m)) where
  edge i := ⟨if i.val % 2 = 0 then i.val + 1 else i.val - 1, by
    have := i.isLt; split_ifs <;> omega⟩
  edge_invol i := by
    have := i.isLt
    refine Fin.ext ?_
    by_cases h : i.val % 2 = 0
    · simp only [if_pos h,
        if_neg (show ¬ ((i.val + 1) % 2 = 0) by omega)]
      omega
    · simp only [if_neg h,
        if_pos (show (i.val - 1) % 2 = 0 by omega)]
      omega
  edge_ne i := by
    have := i.isLt
    intro hx
    have h2 := congrArg Fin.val hx
    simp only at h2
    split_ifs at h2 <;> omega
  tail i := decide (i.val % 2 = 0)
  tail_flip i := by
    have := i.isLt
    by_cases h : i.val % 2 = 0
    · show decide ((⟨if i.val % 2 = 0 then i.val + 1 else i.val - 1,
        _⟩ : Fin (2 * m)).val % 2 = 0) = _
      simp only [if_pos h]
      rw [decide_eq_false (show ¬ ((i.val + 1) % 2 = 0) by omega),
        decide_eq_true h]
      rfl
    · show decide ((⟨if i.val % 2 = 0 then i.val + 1 else i.val - 1,
        _⟩ : Fin (2 * m)).val % 2 = 0) = _
      simp only [if_neg h]
      rw [decide_eq_true (show (i.val - 1) % 2 = 0 by omega),
        decide_eq_false h]
      rfl

/-- **The standard directed matching** on a linearly ordered set of
even size. -/
noncomputable def stdMatching [LinearOrder α] [Fintype α] {m : ℕ}
    (hcard : Fintype.card α = 2 * m) : DirMatching α :=
  (finStd m).map (monoEquivOfFin α hcard).toEquiv

/-! ### Transporting a matching

The two fragments of a composition carry matchings on their own
used labels.  Comparing them means transporting one along the
bijection the shared labelling gives, and the sign against a
transported reference is unchanged.
-/

/-- A carrier transports along a bijection. -/
theorem carries_map {β : Type} (e : α ≃ β) {R M : DirMatching α}
    {σ : Equiv.Perm α} (hσ : Carries R M σ) :
    Carries (R.map e) (M.map e) (e.permCongr σ) := by
  constructor
  · intro b
    show e (σ (e.symm (e (M.edge (e.symm b)))))
      = e (R.edge (e.symm (e (σ (e.symm b)))))
    rw [Equiv.symm_apply_apply, Equiv.symm_apply_apply]
    exact congrArg e (hσ.edge (e.symm b))
  · intro b
    show R.tail (e.symm (e (σ (e.symm b)))) = M.tail (e.symm b)
    rw [Equiv.symm_apply_apply]
    exact hσ.tail (e.symm b)

/-- Transport composes. -/
theorem map_map {β γ : Type} (e : α ≃ β) (f : β ≃ γ)
    (M : DirMatching α) : (M.map e).map f = M.map (e.trans f) := rfl

/-- **The sign is unchanged by transport.** -/
theorem sgnRel_map [Fintype α] [DecidableEq α] {β : Type}
    [Fintype β] [DecidableEq β] (e : α ≃ β) (R M : DirMatching α) :
    sgnRel (R.map e) (M.map e) = sgnRel R M := by
  obtain ⟨σ, hσ⟩ := exists_carries R M
  rw [sgnRel_eq_of_carries R M hσ,
    sgnRel_eq_of_carries (R.map e) (M.map e) (carries_map e hσ),
    Equiv.Perm.sign_permCongr]

/-- **The standard matching is natural in the order.** -/
theorem stdMatching_map [LinearOrder α] [Fintype α] {β : Type}
    [LinearOrder β] [Fintype β] (e : α ≃o β) {m : ℕ}
    (h : Fintype.card α = 2 * m) (h' : Fintype.card β = 2 * m) :
    (stdMatching h).map e.toEquiv = stdMatching h' := by
  unfold stdMatching
  rw [map_map]
  refine congrArg (fun z : Fin (2 * m) ≃ β => (finStd m).map z) ?_
  exact congrArg (fun z : Fin (2 * m) ≃o β => z.toEquiv)
    (Subsingleton.elim ((monoEquivOfFin α h).trans e)
      (monoEquivOfFin β h'))

/-- **The two fragments' signs, on a common reference.**  With the
second matching transported along an order isomorphism of the two
used-label sets, the product of the two signs is the sign of a
carrier between them — reference-free, as RS21's Lemma 11 needs. -/
theorem sgnRel_mul_sgnRel_map [LinearOrder α] [Fintype α]
    {β : Type} [LinearOrder β] [Fintype β] (e : α ≃o β) {m : ℕ}
    (h : Fintype.card α = 2 * m) (h' : Fintype.card β = 2 * m)
    (M : DirMatching α) (N : DirMatching β) {σ : Equiv.Perm α}
    (hσ : Carries M (N.map e.symm.toEquiv) σ) :
    sgnRel (stdMatching h) M * sgnRel (stdMatching h') N
      = Perm.sign σ := by
  have hN : sgnRel (stdMatching h') N
      = sgnRel (stdMatching h) (N.map e.symm.toEquiv) := by
    rw [← sgnRel_map e.symm.toEquiv (stdMatching h') N,
      stdMatching_map e.symm h' h]
  rw [hN]
  exact sgnRel_mul_sgnRel (stdMatching h) M
    (N.map e.symm.toEquiv) hσ

/-- **RS21's Lemma 11 for a composition**: with the union of the two
fragments' matchings Eulerian, the product of their signs is `(-1)`
to the number of components of that union. -/
theorem sgnRel_mul_sgnRel_map_alternating [LinearOrder α] [Fintype α]
    {β : Type} [LinearOrder β] [Fintype β] (e : α ≃o β) {m : ℕ}
    (h : Fintype.card α = 2 * m) (h' : Fintype.card β = 2 * m)
    (M : DirMatching α) (N : DirMatching β)
    (halt : Alternating M (N.map e.symm.toEquiv)) :
    ((sgnRel (stdMatching h) M * sgnRel (stdMatching h') N : ℤˣ) : ℂ)
      = (-1 : ℂ) ^ orbitCount (M.rotPerm (N.map e.symm.toEquiv) halt)
      := by
  have hs := sgnRel_mul_sgnRel_map e h h' M N (carries_rotPerm halt)
  rw [hs]
  exact sign_rotPerm halt M.even_card

/-! ### Reversing one arc

RS21's invariance (12) turns on the observation that inverting a
directed trail changes `M(ω,κ)` by reversing the direction of one
arc, and that this flips the matching's sign.  Reversing an arc
composes any carrier with the transposition of that arc's two ends.
-/

/-- **Reverse the direction of one arc**, leaving the pairing
alone. -/
def reverseArc [DecidableEq α] (M : DirMatching α) (a : α) :
    DirMatching α where
  edge := M.edge
  edge_invol := M.edge_invol
  edge_ne := M.edge_ne
  tail b := if b = a ∨ b = M.edge a then !M.tail b else M.tail b
  tail_flip b := by
    by_cases h1 : b = a
    · subst h1
      rw [if_pos (Or.inr rfl), if_pos (Or.inl rfl), M.tail_flip,
        Bool.not_not]
    · by_cases h2 : b = M.edge a
      · subst h2
        rw [if_pos (Or.inl (M.edge_invol a)),
          if_pos (Or.inr rfl), M.tail_flip, Bool.not_not]
      · have h3 : ¬ (M.edge b = a ∨ M.edge b = M.edge a) := by
          rintro (hx | hx)
          · exact h2 (by rw [← hx, M.edge_invol])
          · exact h1 (by
              have := congrArg M.edge hx
              rwa [M.edge_invol, M.edge_invol] at this)
        rw [if_neg h3, if_neg (fun hx => hx.elim h1 h2), M.tail_flip]

/-- The reversed matching's directions, pointwise. -/
theorem reverseArc_tail [DecidableEq α] (M : DirMatching α) (a b : α) :
    (M.reverseArc a).tail b
      = if b = a ∨ b = M.edge a then !M.tail b else M.tail b := rfl

/-- The arc-reversing transposition commutes with the pairing. -/
theorem swap_edge_comm [DecidableEq α] (M : DirMatching α) (a b : α) :
    Equiv.swap a (M.edge a) (M.edge b)
      = M.edge (Equiv.swap a (M.edge a) b) := by
  by_cases h1 : b = a
  · subst h1
    rw [Equiv.swap_apply_right, Equiv.swap_apply_left, M.edge_invol]
  · by_cases h2 : b = M.edge a
    · subst h2
      rw [M.edge_invol, Equiv.swap_apply_left,
        Equiv.swap_apply_right]
    · have h3 : M.edge b ≠ a := fun hx =>
        h2 (by rw [← hx, M.edge_invol])
      have h4 : M.edge b ≠ M.edge a := fun hx =>
        h1 (by
          have := congrArg M.edge hx
          rwa [M.edge_invol, M.edge_invol] at this)
      rw [Equiv.swap_apply_of_ne_of_ne h3 h4,
        Equiv.swap_apply_of_ne_of_ne h1 h2]

/-- **A carrier for the reversed matching**: compose with the
transposition of the reversed arc's two ends. -/
theorem carries_reverseArc [DecidableEq α] {σ : Equiv.Perm α}
    (hσ : Carries R M σ)
    (a : α) :
    Carries R (M.reverseArc a) (σ * Equiv.swap a (M.edge a)) := by
  constructor
  · intro b
    show σ (Equiv.swap a (M.edge a) (M.edge b))
      = R.edge (σ (Equiv.swap a (M.edge a) b))
    rw [swap_edge_comm M a b, hσ.edge]
  · intro b
    show R.tail (σ (Equiv.swap a (M.edge a) b))
      = (M.reverseArc a).tail b
    rw [hσ.tail]
    show M.tail (Equiv.swap a (M.edge a) b)
      = if b = a ∨ b = M.edge a then !M.tail b else M.tail b
    by_cases h1 : b = a
    · subst h1
      rw [Equiv.swap_apply_left, if_pos (Or.inl rfl), M.tail_flip]
    · by_cases h2 : b = M.edge a
      · subst h2
        rw [Equiv.swap_apply_right, if_pos (Or.inr rfl),
          M.tail_flip, Bool.not_not]
      · rw [Equiv.swap_apply_of_ne_of_ne h1 h2,
          if_neg (fun hx => hx.elim h1 h2)]

/-- **Reversing an arc flips the sign** — RS21's
`sgn(M(ω,κ)) = -sgn(M(ω′,κ′))`. -/
theorem sgnRel_reverseArc [Fintype α] [DecidableEq α] (R M : DirMatching α) (a :
  α) :
    sgnRel R (M.reverseArc a) = -sgnRel R M := by
  obtain ⟨σ, hσ⟩ := exists_carries R M
  rw [sgnRel_eq_of_carries R M hσ,
    sgnRel_eq_of_carries R (M.reverseArc a) (carries_reverseArc hσ a),
    map_mul, Equiv.Perm.sign_swap (M.edge_ne a).symm]
  simp

/-- Two directed matchings agreeing on partners and directions are
equal. -/
theorem ext {M N : DirMatching α} (he : M.edge = N.edge)
    (ht : M.tail = N.tail) : M = N := by
  cases M
  cases N
  simp_all

/-! ### Lemma 11 in general

RS21's Lemma 11 reads the sign of a permutation carrying one
directed matching to another as `(-1)^{c(M∪N)+o(M∪N)}`, where
`o(M∪N)` is the parity of the number of arcs that must be reversed
to make the union Eulerian.  The Eulerian case above is `o = 0`;
RS21 reduces to it by (12), which is available for a directed trail
but not for an edge joining two labels directly, so the general
case is what a fragment's matchings need.

The general case follows from the Eulerian one by reversing arcs.
Two matchings with the same pairing differ on a set of points
closed under that pairing — a set of whole arcs — and reversing
those arcs one at a time carries one to the other, flipping the
sign each time.
-/

/-- The points at which two matchings disagree on direction. -/
def flipSet [Fintype α] (P P' : DirMatching α) : Finset α :=
  Finset.univ.filter (fun a => P'.tail a ≠ P.tail a)

/-- Membership in the disagreement set. -/
theorem mem_flipSet [Fintype α] {P P' : DirMatching α} {a : α} :
    a ∈ flipSet P P' ↔ P'.tail a ≠ P.tail a := by
  rw [flipSet, Finset.mem_filter]
  exact ⟨fun h => h.2, fun h => ⟨Finset.mem_univ a, h⟩⟩

/-- Booleans that differ are negations of one another. -/
private theorem bool_eq_not_of_ne {x y : Bool} (h : x ≠ y) :
    x = !y := by
  revert h
  revert x y
  decide

/-- **The disagreement set is a set of whole arcs**: matchings with
the same pairing disagree at both ends of an arc or at neither. -/
theorem edge_mem_flipSet [Fintype α] {P P' : DirMatching α}
    (he : P'.edge = P.edge) {a : α} (ha : a ∈ flipSet P P') :
    P.edge a ∈ flipSet P P' := by
  rw [mem_flipSet] at ha ⊢
  intro hx
  refine ha ?_
  have h1 : P'.tail (P.edge a) = !P'.tail a := by
    rw [← he]; exact P'.tail_flip a
  rw [hx, P.tail_flip a] at h1
  exact (Bool.not_inj h1).symm

/-- The disagreement set has an even number of points. -/
theorem even_card_flipSet [Fintype α] [DecidableEq α]
    {P P' : DirMatching α} (he : P'.edge = P.edge) :
    Even (flipSet P P').card :=
  even_card_of_involution _ P.edge
    (fun _ ha => edge_mem_flipSet he ha)
    (fun a _ => P.edge_invol a) (fun a _ => P.edge_ne a)

/-- Reversing an arc removes it from the disagreement set and
leaves the rest alone. -/
theorem flipSet_reverseArc [Fintype α] [DecidableEq α]
    {P P' : DirMatching α} (he : P'.edge = P.edge) {a : α}
    (ha : a ∈ flipSet P P') :
    flipSet (P.reverseArc a) P' = (flipSet P P') \ {a, P.edge a} := by
  have hea : P.edge a ∈ flipSet P P' := edge_mem_flipSet he ha
  refine Finset.ext (fun b => ?_)
  rw [mem_flipSet, Finset.mem_sdiff, mem_flipSet, Finset.mem_insert,
    Finset.mem_singleton, reverseArc_tail]
  by_cases hb : b = a ∨ b = P.edge a
  · rw [if_pos hb]
    have hbmem : b ∈ flipSet P P' := by
      rcases hb with rfl | rfl
      · exact ha
      · exact hea
    rw [mem_flipSet] at hbmem
    exact ⟨fun hx => absurd (bool_eq_not_of_ne hbmem) hx,
      fun hx => absurd hb hx.2⟩
  · rw [if_neg hb]
    exact ⟨fun hx => ⟨hx, hb⟩, fun hx => hx.1⟩

/-! ### Repairing a union to Eulerian position

RS21 puts the union of two matchings into Eulerian position before
applying Lemma 11, by reversing arcs of each.  Such a repair always
exists: reversing arcs is free to choose a direction at each point,
subject only to the two arcs at a point pointing opposite ways, so a
repair is exactly a two-colouring of the union — a `T : α → Bool`
flipped by both pairings.

The union of two fixed-point-free involutions is a disjoint union of
cycles of even length, so it is two-colourable, and the colouring is
built here without decomposing into cycles.  Write `p` for the
composite of the two pairings.  A colouring is a function constant on
`p`-cycles that the first pairing flips, so it is a choice of one
cycle from each pair `{C, e₁C}` — and those two cycles are always
distinct, by the dihedral relation `e₁ p e₁ = p⁻¹` together with the
fixed-point-freeness of both pairings.
-/

/-- The pairing of a matching, as a permutation. -/
def edgePerm (M : DirMatching α) : Equiv.Perm α where
  toFun := M.edge
  invFun := M.edge
  left_inv := M.edge_invol
  right_inv := M.edge_invol

/-- The pairing permutation acts by the partner map. -/
@[simp] theorem edgePerm_apply (M : DirMatching α) (a : α) :
    M.edgePerm a = M.edge a := rfl

/-- A pairing is its own inverse. -/
theorem edgePerm_inv (M : DirMatching α) : M.edgePerm⁻¹ = M.edgePerm :=
  inv_eq_of_mul_eq_one_left (Equiv.ext (fun x => M.edge_invol x))

/-- The composite of two pairings inverts by taking them in the
other order. -/
theorem inv_edgePerm_mul (M N : DirMatching α) :
    (N.edgePerm * M.edgePerm)⁻¹ = M.edgePerm * N.edgePerm := by
  rw [mul_inv_rev, edgePerm_inv, edgePerm_inv]

/-- **The dihedral relation**: conjugating the composite by either
pairing inverts it. -/
theorem edgePerm_conj (M N : DirMatching α) (i : ℤ) :
    M.edgePerm * (N.edgePerm * M.edgePerm) ^ i * M.edgePerm
      = (N.edgePerm * M.edgePerm) ^ (-i) := by
  have hcc : M.edgePerm * M.edgePerm = 1 :=
    Equiv.ext (fun x => M.edge_invol x)
  have hinv : M.edgePerm⁻¹ = M.edgePerm := edgePerm_inv M
  have hbase : (MulAut.conj M.edgePerm) (N.edgePerm * M.edgePerm)
      = (N.edgePerm * M.edgePerm)⁻¹ := by
    rw [MulAut.conj_apply, hinv, inv_edgePerm_mul]
    calc M.edgePerm * (N.edgePerm * M.edgePerm) * M.edgePerm
        = M.edgePerm * N.edgePerm * (M.edgePerm * M.edgePerm) := by
          group
      _ = M.edgePerm * N.edgePerm := by rw [hcc, mul_one]
  have h2 := map_zpow (MulAut.conj M.edgePerm)
    (N.edgePerm * M.edgePerm) i
  rw [hbase, MulAut.conj_apply, hinv, inv_zpow'] at h2
  exact h2

/-- **The cycle of a point and the cycle of its partner are
distinct.**  Were they the same, the dihedral relation would place a
fixed point of one of the two pairings on that cycle: at the midpoint
of the displacement when it is even, one step further when it is odd.
This is the even length of the union's cycles, in the only form the
repair needs. -/
theorem not_sameCycle_edge (M N : DirMatching α) (a : α) :
    ¬ (N.edgePerm * M.edgePerm).SameCycle a (M.edge a) := by
  set p : Equiv.Perm α := N.edgePerm * M.edgePerm with hp
  rintro ⟨j, hj⟩
  have hstep : ∀ i : ℤ, M.edge ((p ^ i) a) = (p ^ (j - i)) a := by
    intro i
    have h1 : M.edge ((p ^ i) a)
        = (M.edgePerm * p ^ i * M.edgePerm) (M.edge a) := by
      show M.edge ((p ^ i) a)
        = M.edge ((p ^ i) (M.edge (M.edge a)))
      rw [M.edge_invol]
    rw [h1, hp, edgePerm_conj M N i, ← hj, ← hp]
    show (p ^ (-i)) ((p ^ j) a) = (p ^ (j - i)) a
    rw [← Equiv.Perm.mul_apply, ← zpow_add]
    congr 2
    ring
  have hNstep : ∀ i : ℤ, N.edge ((p ^ i) a) = (p ^ (j - i + 1)) a := by
    intro i
    have h2 : N.edge ((p ^ i) a) = p (M.edge ((p ^ i) a)) := by
      show N.edge ((p ^ i) a) = N.edge (M.edge (M.edge ((p ^ i) a)))
      rw [M.edge_invol]
    rw [h2, hstep i]
    show p ((p ^ (j - i)) a) = (p ^ (j - i + 1)) a
    rw [show j - i + 1 = 1 + (j - i) from by ring, zpow_add, zpow_one]
    rfl
  rcases Int.even_or_odd j with ⟨i, hi⟩ | ⟨i, hi⟩
  · refine M.edge_ne ((p ^ i) a) ?_
    rw [hstep i, hi, show i + i - i = i from by ring]
  · refine N.edge_ne ((p ^ (i + 1)) a) ?_
    rw [hNstep (i + 1), hi,
      show 2 * i + 1 - (i + 1) + 1 = i + 1 from by ring]

/-- The cycle of a point, as a finset. -/
noncomputable def cycleOf [Fintype α] [DecidableEq α]
    (p : Equiv.Perm α) (a : α) : Finset α :=
  Finset.univ.filter (fun x => p.SameCycle a x)

/-- Membership in a cycle: being on the same cycle as the base
point. -/
theorem mem_cycleOf [Fintype α] [DecidableEq α] {p : Equiv.Perm α}
    {a x : α} : x ∈ cycleOf p a ↔ p.SameCycle a x := by
  rw [cycleOf, Finset.mem_filter]
  exact ⟨fun h => h.2, fun h => ⟨Finset.mem_univ x, h⟩⟩

/-- A point lies on its own cycle. -/
theorem self_mem_cycleOf [Fintype α] [DecidableEq α]
    (p : Equiv.Perm α) (a : α) : a ∈ cycleOf p a :=
  mem_cycleOf.mpr (Equiv.Perm.SameCycle.refl p a)

/-- Points on one cycle have the same cycle. -/
theorem cycleOf_eq [Fintype α] [DecidableEq α] {p : Equiv.Perm α}
    {a b : α} (h : p.SameCycle a b) : cycleOf p a = cycleOf p b :=
  Finset.ext (fun x => by
    rw [mem_cycleOf, mem_cycleOf]
    exact ⟨fun hx => h.symm.trans hx, fun hx => h.trans hx⟩)

/-- **The key of a cycle**: the least index of a point on it. -/
noncomputable def cycleKey [Fintype α] [DecidableEq α]
    (p : Equiv.Perm α) (a : α) : Fin (Fintype.card α) :=
  ((cycleOf p a).image (Fintype.equivFin α)).min'
    ⟨Fintype.equivFin α a,
      Finset.mem_image_of_mem _ (self_mem_cycleOf p a)⟩

/-- Points on the same cycle have the same key, so the key names
the cycle. -/
theorem cycleKey_eq [Fintype α] [DecidableEq α] {p : Equiv.Perm α}
    {a b : α} (h : p.SameCycle a b) :
    cycleKey p a = cycleKey p b := by
  unfold cycleKey
  congr 1
  rw [cycleOf_eq h]

/-- Distinct cycles have distinct keys: a key is attained on its own
cycle, and two cycles sharing a point coincide. -/
theorem sameCycle_of_cycleKey_eq [Fintype α] [DecidableEq α]
    {p : Equiv.Perm α} {a b : α} (h : cycleKey p a = cycleKey p b) :
    p.SameCycle a b := by
  obtain ⟨x, hx, hfx⟩ := Finset.mem_image.mp
    (Finset.min'_mem ((cycleOf p a).image (Fintype.equivFin α))
      ⟨Fintype.equivFin α a,
        Finset.mem_image_of_mem _ (self_mem_cycleOf p a)⟩)
  obtain ⟨y, hy, hfy⟩ := Finset.mem_image.mp
    (Finset.min'_mem ((cycleOf p b).image (Fintype.equivFin α))
      ⟨Fintype.equivFin α b,
        Finset.mem_image_of_mem _ (self_mem_cycleOf p b)⟩)
  have hxy : x = y := (Fintype.equivFin α).injective (by
    rw [hfx, hfy]; exact h)
  have h1 : p.SameCycle a y := hxy ▸ mem_cycleOf.mp hx
  exact h1.trans (mem_cycleOf.mp hy).symm

/-- **Any two matchings admit a common repair to Eulerian
position** — RS21's `σ₁` and `σ₂`.  The repair leaves both pairings
alone and makes the union alternating. -/
theorem exists_alternating_repair [Fintype α] [DecidableEq α]
    (M N : DirMatching α) :
    ∃ M' N' : DirMatching α,
      M'.edge = M.edge ∧ N'.edge = N.edge ∧ Alternating M' N' := by
  classical
  set p : Equiv.Perm α := N.edgePerm * M.edgePerm with hp
  set T : α → Bool :=
    fun a => decide (cycleKey p a < cycleKey p (M.edge a)) with hT
  have hne : ∀ a, cycleKey p a ≠ cycleKey p (M.edge a) := fun a hx =>
    not_sameCycle_edge M N a (sameCycle_of_cycleKey_eq hx)
  have hflip : ∀ a : α, ∀ u v : Fin (Fintype.card α), u ≠ v →
      decide (v < u) = !decide (u < v) := by
    intro _ u v huv
    rcases lt_trichotomy u v with h | h | h
    · rw [decide_eq_false (not_lt.mpr h.le), decide_eq_true h]; rfl
    · exact absurd h huv
    · rw [decide_eq_true h, decide_eq_false (not_lt.mpr h.le)]; rfl
  have hMflip : ∀ a, T (M.edge a) = !T a := by
    intro a
    show decide (cycleKey p (M.edge a)
        < cycleKey p (M.edge (M.edge a)))
      = !decide (cycleKey p a < cycleKey p (M.edge a))
    rw [M.edge_invol]
    exact hflip a _ _ (hne a)
  have hkeyN : ∀ a, cycleKey p (N.edge a) = cycleKey p (M.edge a) := by
    intro a
    refine (cycleKey_eq (⟨1, ?_⟩ : p.SameCycle (M.edge a) (N.edge a))).symm
    show (p ^ (1 : ℤ)) (M.edge a) = N.edge a
    rw [zpow_one, hp]
    show N.edge (M.edge (M.edge a)) = N.edge a
    rw [M.edge_invol]
  have hkeyMN : ∀ a, cycleKey p (M.edge (N.edge a)) = cycleKey p a := by
    intro a
    refine (cycleKey_eq (⟨-1, ?_⟩ : p.SameCycle a (M.edge (N.edge a)))).symm
    show (p ^ (-1 : ℤ)) a = M.edge (N.edge a)
    rw [zpow_neg, zpow_one, hp, inv_edgePerm_mul]
    rfl
  have hNflip : ∀ a, T (N.edge a) = !T a := by
    intro a
    show decide (cycleKey p (N.edge a)
        < cycleKey p (M.edge (N.edge a)))
      = !decide (cycleKey p a < cycleKey p (M.edge a))
    rw [hkeyN a, hkeyMN a]
    exact hflip a _ _ (hne a)
  refine ⟨{ edge := M.edge, edge_invol := M.edge_invol,
            edge_ne := M.edge_ne, tail := T, tail_flip := hMflip },
          { edge := N.edge, edge_invol := N.edge_invol,
            edge_ne := N.edge_ne, tail := fun a => !T a,
            tail_flip := fun a => by rw [hNflip a] },
          rfl, rfl, fun _ => rfl⟩

/-- **The direction hypothesis is automatic** along an arc of the
interface matching: the union being Eulerian at the two identified
labels is exactly what the contraction needs. -/
theorem tail_ne_of_alternating {M N : DirMatching α}
    (h : Alternating M N) {i j : α} (hN : N.edge i = j) :
    M.tail j = !M.tail i := by
  have h1 : N.tail j = !N.tail i := by
    rw [← hN]
    exact N.tail_flip i
  rw [h j, h i, Bool.not_not] at h1
  rw [← h1, Bool.not_not]

/-! ### Contracting a matching at an identified pair

Gluing one interface pair identifies two labels.  On the chord
matching that is a contraction: the two labels are removed and their
partners are matched to one another, which is the same rewiring the
flag model performs on the edge pairing.

The contraction is defined when the two identified labels are not
already partners.  When they are, gluing closes a circuit instead,
and the two labels simply disappear — that dichotomy is what makes
the circuit count go up by one exactly once per component of the
union.

Directions contract only when the two identified labels carry
opposite ones, which is RS21's requirement that the two Eulerian
orientations induce an Eulerian orientation of the glued subset.
-/

/-- The points surviving the identification of `i` and `j`. -/
abbrev Surviving (i j : α) : Type := {x : α // x ≠ i ∧ x ≠ j}

/-- **An excursion through the identified pair has length two.** -/
theorem rot_rot_of_interface (h : Alternating M N) {i j : α}
    (hN : N.edge i = j) (x : Surviving i j)
    (hs : M.rot N x.val = i ∨ M.rot N x.val = j) :
    M.rot N (M.rot N x.val) = i ∨ M.rot N (M.rot N x.val) = j := by
  have hNj : N.edge j = i := by rw [← hN, N.edge_invol]
  have hdir := tail_ne_of_alternating h hN
  have hx : M.tail x.val = true := by
    by_contra hx
    have hrot : M.rot N x.val = N.edge x.val := by
      unfold rot; rw [if_neg hx]
    rcases hs with hs | hs <;> rw [hrot] at hs
    · exact x.prop.2 (((N.edge_invol x.val).symm.trans
        (congrArg N.edge hs)).trans hN)
    · exact x.prop.1 (((N.edge_invol x.val).symm.trans
        (congrArg N.edge hs)).trans hNj)
  have hrot : M.rot N x.val = M.edge x.val := by
    unfold rot; rw [if_pos hx]
  rcases hs with hs | hs
  · refine Or.inr ?_
    have hti : M.tail i = false := by
      have hf := M.tail_flip x.val
      rw [← hrot, hs, hx] at hf
      exact hf
    rw [hs]
    unfold rot
    rw [if_neg (by rw [hti]; exact Bool.noConfusion), hN]
  · refine Or.inl ?_
    have htj : M.tail j = false := by
      have hf := M.tail_flip x.val
      rw [← hrot, hs, hx] at hf
      exact hf
    rw [hs]
    unfold rot
    rw [if_neg (by rw [htj]; exact Bool.noConfusion), hNj]

/-- The contracted partner map: the partners of the two identified
points are matched to one another. -/
def contractEdge [DecidableEq α] (M : DirMatching α) (i j : α)
    (x : α) : α :=
  if M.edge x = i then M.edge j
  else if M.edge x = j then M.edge i
  else M.edge x

/-- The contracted partner map reads only the pairing. -/
theorem contractEdge_congr [DecidableEq α] {M M' : DirMatching α}
    (h : M'.edge = M.edge) (i j : α) (x : α) :
    M'.contractEdge i j x = M.contractEdge i j x := by
  unfold contractEdge
  rw [h]

/-- The contracted partner map avoids the two identified points:
they are gone from the contracted set. -/
theorem contractEdge_ne [DecidableEq α] (M : DirMatching α) {i j : α}
    (hopen : M.edge i ≠ j) (x : α) :
    M.contractEdge i j x ≠ i ∧ M.contractEdge i j x ≠ j := by
  unfold contractEdge
  by_cases h1 : M.edge x = i
  · rw [if_pos h1]
    refine ⟨fun hx => hopen ?_, fun hx => M.edge_ne j hx⟩
    rw [← hx, M.edge_invol]
  · by_cases h2 : M.edge x = j
    · rw [if_neg h1, if_pos h2]
      exact ⟨M.edge_ne i, hopen⟩
    · rw [if_neg h1, if_neg h2]
      exact ⟨h1, h2⟩

/-- It is an involution on the survivors. -/
theorem contractEdge_invol [DecidableEq α] (M : DirMatching α) {i j : α}
    (hij : i ≠ j)
    (x : α) (hx : x ≠ i) (hx' : x ≠ j) :
    M.contractEdge i j (M.contractEdge i j x) = x := by
  unfold contractEdge
  by_cases h1 : M.edge x = i
  · rw [if_pos h1, if_neg (by rw [M.edge_invol]; exact Ne.symm hij),
      if_pos (by rw [M.edge_invol])]
    rw [← h1, M.edge_invol]
  · by_cases h2 : M.edge x = j
    · rw [if_neg h1, if_pos h2, if_pos (by rw [M.edge_invol])]
      rw [← h2, M.edge_invol]
    · rw [if_neg h1, if_neg h2,
        if_neg (by rw [M.edge_invol]; exact hx),
        if_neg (by rw [M.edge_invol]; exact hx'), M.edge_invol]

/-- And fixed-point-free, so it is again a perfect matching. -/
theorem contractEdge_ne_self [DecidableEq α] (M : DirMatching α) {i j : α}
    (hij : i ≠ j) (x : α) : M.contractEdge i j x ≠ x := by
  unfold contractEdge
  by_cases h1 : M.edge x = i
  · rw [if_pos h1]
    intro hx
    refine Ne.symm hij ?_
    rw [← hx] at h1
    rwa [M.edge_invol] at h1
  · by_cases h2 : M.edge x = j
    · rw [if_neg h1, if_pos h2]
      intro hx
      refine hij ?_
      rw [← hx] at h2
      rwa [M.edge_invol] at h2
    · rw [if_neg h1, if_neg h2]
      exact M.edge_ne x

/-- **The contraction of a matching at an identified pair.**  The
two identified points must carry opposite directions, which is what
makes the contracted directions consistent — RS21's requirement that
the two Eulerian orientations induce an Eulerian orientation of the
glued subset. -/
def contract [DecidableEq α] (M : DirMatching α) {i j : α} (hij : i ≠ j)
    (hopen : M.edge i ≠ j) (hdir : M.tail j = !M.tail i) :
    DirMatching (Surviving i j) where
  edge x := ⟨M.contractEdge i j x.val,
    M.contractEdge_ne hopen x.val⟩
  edge_invol x := Subtype.ext
    (M.contractEdge_invol hij x.val x.prop.1 x.prop.2)
  edge_ne x hx := M.contractEdge_ne_self hij x.val
    (congrArg Subtype.val hx)
  tail x := M.tail x.val
  tail_flip x := by
    show M.tail (M.contractEdge i j x.val) = !M.tail x.val
    unfold contractEdge
    by_cases h1 : M.edge x.val = i
    · rw [if_pos h1, M.tail_flip j, hdir, Bool.not_not]
      have hxx := M.tail_flip x.val
      rw [h1] at hxx
      exact hxx
    · by_cases h2 : M.edge x.val = j
      · rw [if_neg h1, if_pos h2, M.tail_flip i]
        have hxx := M.tail_flip x.val
        rw [h2, hdir] at hxx
        exact hxx
      · rw [if_neg h1, if_neg h2, M.tail_flip x.val]

/-! ### The interface matching after one identification

Gluing one interface pair consumes one arc of the interface
matching and contracts the chord matching at its two ends.  The
remaining interface arcs restrict to the surviving labels, and the
union of the two matchings stays Eulerian, so the step can be
iterated.
-/

/-- The interface matching restricted to the labels surviving the
identification of one of its own arcs. -/
def restrict (N : DirMatching α) {i j : α} (hN : N.edge i = j) :
    DirMatching (Surviving i j) where
  edge x := ⟨N.edge x.val, by
    have hNj : N.edge j = i := by rw [← hN, N.edge_invol]
    refine ⟨fun hx => x.prop.2 ?_, fun hx => x.prop.1 ?_⟩
    · exact ((N.edge_invol x.val).symm.trans
        (congrArg N.edge hx)).trans hN
    · exact ((N.edge_invol x.val).symm.trans
        (congrArg N.edge hx)).trans hNj⟩
  edge_invol x := Subtype.ext (N.edge_invol x.val)
  edge_ne x hx := N.edge_ne x.val (congrArg Subtype.val hx)
  tail x := N.tail x.val
  tail_flip x := N.tail_flip x.val

/-- **The union stays Eulerian after one identification.** -/
theorem alternating_contract [DecidableEq α] {M N : DirMatching α}
    (h : Alternating M N) {i j : α} (hij : i ≠ j)
    (hN : N.edge i = j) (hopen : M.edge i ≠ j) :
    Alternating (M.contract hij hopen (tail_ne_of_alternating h hN))
      (N.restrict hN) :=
  fun x => h x.val

/-! ### One step of the contracted rotation

One step of the contracted rotation is one or three steps of the
original: the contraction short-circuits the two identified labels,
so a step that would have landed on one of them instead continues
past both.  Either way the step stays inside a single orbit of the
original rotation, which is what carries orbits across the
contraction.
-/

/-- **A contracted step stays in one orbit of the original
rotation.** -/
theorem sameCycle_rot_contract [DecidableEq α] {M N : DirMatching α}
    (h : Alternating M N) {i j : α} (hij : i ≠ j)
    (hN : N.edge i = j) (hopen : M.edge i ≠ j)
    (x : Surviving i j) :
    (M.rotPerm N h).SameCycle x.val
      (((M.contract hij hopen (tail_ne_of_alternating h hN)).rotPerm
        (N.restrict hN) (alternating_contract h hij hN hopen)) x).val := by
  have hNj : N.edge j = i := by rw [← hN, N.edge_invol]
  have hval : (((M.contract hij hopen
        (tail_ne_of_alternating h hN)).rotPerm (N.restrict hN)
        (alternating_contract h hij hN hopen)) x).val
      = if M.tail x.val then M.contractEdge i j x.val
        else N.edge x.val := by
    show ((M.contract hij hopen
      (tail_ne_of_alternating h hN)).rot (N.restrict hN) x).val = _
    unfold rot
    by_cases hx : M.tail x.val = true
    · rw [if_pos (show (M.contract hij hopen
        (tail_ne_of_alternating h hN)).tail x = true from hx),
        if_pos hx]
      rfl
    · rw [if_neg (show ¬ ((M.contract hij hopen
        (tail_ne_of_alternating h hN)).tail x = true) from hx),
        if_neg hx]
      rfl
  rw [hval]
  by_cases hx : M.tail x.val = true
  · rw [if_pos hx]
    unfold contractEdge
    by_cases h1 : M.edge x.val = i
    · rw [if_pos h1]
      refine ((sameCycle_rot_edge h x.val).trans ?_).trans
        (sameCycle_rot_edge h j)
      rw [h1, ← hN]
      exact sameCycle_rot_edge' h i
    · by_cases h2 : M.edge x.val = j
      · rw [if_neg h1, if_pos h2]
        refine ((sameCycle_rot_edge h x.val).trans ?_).trans
          (sameCycle_rot_edge h i)
        rw [h2, ← hNj]
        exact sameCycle_rot_edge' h j
      · rw [if_neg h1, if_neg h2]
        exact sameCycle_rot_edge h x.val
  · rw [if_neg hx]
    exact sameCycle_rot_edge' h x.val

/-- **The contraction's orbits map to the original's.** -/
theorem sameCycle_of_contract [DecidableEq α] {M N : DirMatching α}
    (h : Alternating M N) {i j : α} (hij : i ≠ j)
    (hN : N.edge i = j) (hopen : M.edge i ≠ j)
    {x y : Surviving i j}
    (hxy : ((M.contract hij hopen (tail_ne_of_alternating h hN)).rotPerm
      (N.restrict hN)
      (alternating_contract h hij hN hopen)).SameCycle x y) :
    (M.rotPerm N h).SameCycle x.val y.val :=
  sameCycle_of_step Subtype.val
    (fun z => sameCycle_rot_contract h hij hN hopen z) hxy

/-! ### The contracted rotation is the original, short-circuited

A survivor whose rotation step lands on a surviving point takes the
same step in the contraction.  A survivor whose step lands on one of
the two identified points is carried three steps instead: through
both of them and out the far side.  Those are the only two cases,
and together they say the contracted rotation is the original with
the identified pair skipped.
-/

/-- The rotation's step at a survivor, in the contraction. -/
theorem rot_contract_val [DecidableEq α] (h : Alternating M N) {i j : α}
    (hij : i ≠ j)
    (hN : N.edge i = j) (hopen : M.edge i ≠ j) (x : Surviving i j) :
    (((M.contract hij hopen (tail_ne_of_alternating h hN)).rotPerm
        (N.restrict hN) (alternating_contract h hij hN hopen)) x).val
      = if M.tail x.val then M.contractEdge i j x.val
        else N.edge x.val := by
  show ((M.contract hij hopen
    (tail_ne_of_alternating h hN)).rot (N.restrict hN) x).val = _
  unfold rot
  by_cases hx : M.tail x.val = true
  · rw [if_pos (show (M.contract hij hopen
      (tail_ne_of_alternating h hN)).tail x = true from hx),
      if_pos hx]
    rfl
  · rw [if_neg (show ¬ ((M.contract hij hopen
      (tail_ne_of_alternating h hN)).tail x = true) from hx),
      if_neg hx]
    rfl

/-- **A step landing on a survivor is unchanged.** -/
theorem rot_contract_eq_rot [DecidableEq α] (h : Alternating M N) {i j : α}
    (hij : i ≠ j) (hN : N.edge i = j) (hopen : M.edge i ≠ j)
    (x : Surviving i j) (hs : M.rot N x.val ≠ i)
    (hs' : M.rot N x.val ≠ j) :
    (((M.contract hij hopen (tail_ne_of_alternating h hN)).rotPerm
        (N.restrict hN) (alternating_contract h hij hN hopen)) x).val
      = M.rot N x.val := by
  rw [rot_contract_val h hij hN hopen x]
  unfold rot at hs hs' ⊢
  by_cases hx : M.tail x.val = true
  · rw [if_pos hx] at hs hs'
    rw [if_pos hx, if_pos hx]
    unfold contractEdge
    rw [if_neg hs, if_neg hs']
  · rw [if_neg hx] at hs hs'
    rw [if_neg hx, if_neg hx]

/-- **A step landing on an identified point runs three steps.** -/
theorem rot_contract_eq_rot_three [DecidableEq α] (h : Alternating M N)
    {i j : α}
    (hij : i ≠ j) (hN : N.edge i = j) (hopen : M.edge i ≠ j)
    (x : Surviving i j) (hs : M.rot N x.val = i ∨ M.rot N x.val = j) :
    (((M.contract hij hopen (tail_ne_of_alternating h hN)).rotPerm
        (N.restrict hN) (alternating_contract h hij hN hopen)) x).val
      = M.rot N (M.rot N (M.rot N x.val)) := by
  have hNj : N.edge j = i := by rw [← hN, N.edge_invol]
  have hdir := tail_ne_of_alternating h hN
  -- the step cannot be along the interface matching
  have hx : M.tail x.val = true := by
    by_contra hx
    have hrot : M.rot N x.val = N.edge x.val := by
      unfold rot; rw [if_neg hx]
    rcases hs with hs | hs <;> rw [hrot] at hs
    · exact x.prop.2 (((N.edge_invol x.val).symm.trans
        (congrArg N.edge hs)).trans hN)
    · exact x.prop.1 (((N.edge_invol x.val).symm.trans
        (congrArg N.edge hs)).trans hNj)
  have hrot : M.rot N x.val = M.edge x.val := by
    unfold rot; rw [if_pos hx]
  rw [rot_contract_val h hij hN hopen x, if_pos hx]
  unfold contractEdge
  rcases hs with hs | hs <;> rw [hrot] at hs
  · -- the step lands on `i`; continue `i → j → M.edge j`
    have hti : M.tail i = false := by
      have := M.tail_flip x.val
      rw [hs, hx] at this
      exact this
    have htj : M.tail j = true := by
      rw [hdir, hti]; rfl
    rw [if_pos hs, hrot, hs]
    have h1 : M.rot N i = j := by
      unfold rot; rw [if_neg (by rw [hti]; exact Bool.noConfusion), hN]
    have h2 : M.rot N j = M.edge j := by
      unfold rot; rw [if_pos htj]
    rw [h1, h2]
  · -- the step lands on `j`; continue `j → i → M.edge i`
    have htj : M.tail j = false := by
      have := M.tail_flip x.val
      rw [hs, hx] at this
      exact this
    have hti : M.tail i = true := by
      cases hb : M.tail i
      · rw [hb] at hdir
        rw [hdir] at htj
        exact Bool.noConfusion htj
      · rfl
    rw [if_neg (fun hxi => hij (hxi.symm.trans hs)), if_pos hs,
      hrot, hs]
    have h1 : M.rot N j = i := by
      unfold rot; rw [if_neg (by rw [htj]; exact Bool.noConfusion), hNj]
    have h2 : M.rot N i = M.edge i := by
      unfold rot; rw [if_pos hti]
    rw [h1, h2]

/-! ### The converse: the contraction loses no orbits

A rotation path between two survivors passes through the identified
pair only in excursions of length two, and the contraction takes
each such excursion in a single step.  So survivors joined by the
original rotation are joined by the contracted one, and together
with the forward direction the two rotations have the same orbits.
-/

/-- The survivor standing for a point: itself where it survives, and
otherwise the partner of the first identified label, which lies on
the same orbit as both of them. -/
noncomputable def pickSurvivor [DecidableEq α] (M : DirMatching α)
    {i j : α}
    (hopen : M.edge i ≠ j) (a : α) : Surviving i j :=
  if ha : a ≠ i ∧ a ≠ j then ⟨a, ha⟩
  else ⟨M.edge i, M.edge_ne i, hopen⟩

/-- A point and the survivor standing for it lie on the same cycle
of the rotation, so the choice does not move between components. -/
theorem sameCycle_pickSurvivor [DecidableEq α] (h : Alternating M N)
    {i j : α}
    (hN : N.edge i = j) (hopen : M.edge i ≠ j) (a : α) :
    (M.rotPerm N h).SameCycle a (M.pickSurvivor hopen a).val := by
  have hNj : N.edge j = i := by rw [← hN, N.edge_invol]
  unfold pickSurvivor
  by_cases ha : a ≠ i ∧ a ≠ j
  · rw [dif_pos ha]
  · rw [dif_neg ha]
    have ha' : a = i ∨ a = j := by
      by_contra hc
      exact ha ⟨fun hx => hc (Or.inl hx), fun hx => hc (Or.inr hx)⟩
    rcases ha' with h1 | h1
    · rw [h1]
      exact sameCycle_rot_edge h i
    · rw [h1]
      have h2 : (M.rotPerm N h).SameCycle j i := by
        have hj := sameCycle_rot_edge' h j
        rwa [hNj] at hj
      exact h2.trans (sameCycle_rot_edge h i)

/-- **Survivors joined by the original rotation are joined by the
contracted one.** -/
theorem sameCycle_contract_of_sameCycle [Fintype α] [DecidableEq α]
    (h : Alternating M N)
    {i j : α} (hij : i ≠ j) (hN : N.edge i = j)
    (hopen : M.edge i ≠ j) {x y : Surviving i j}
    (hxy : (M.rotPerm N h).SameCycle x.val y.val) :
    ((M.contract hij hopen (tail_ne_of_alternating h hN)).rotPerm
        (N.restrict hN)
        (alternating_contract h hij hN hopen)).SameCycle x y := by
  obtain ⟨n, hn⟩ := hxy.exists_nat_pow_eq
  clear hxy
  induction n using Nat.strong_induction_on generalizing x with
  | _ n ih =>
    match n, hn with
    | 0, hn =>
      have hval : x.val = y.val := hn
      exact ⟨0, by rw [zpow_zero]; exact Subtype.ext hval⟩
    | (m + 1), hn =>
      have hstep : ((M.rotPerm N h) ^ (m + 1)) x.val
          = ((M.rotPerm N h) ^ m) (M.rot N x.val) := by
        rw [pow_succ]
        rfl
      rw [hstep] at hn
      by_cases hz : M.rot N x.val = i ∨ M.rot N x.val = j
      · -- an excursion: three steps of the original, one of the
        -- contraction
        have hz2 := rot_rot_of_interface h hN x hz
        have hm3 : 3 ≤ m + 1 := by
          by_contra hlt
          have hm2 : m < 2 := by omega
          interval_cases m
          · have hy : M.rot N x.val = y.val := hn
            rcases hz with hz | hz
            · exact y.prop.1 (hy.symm.trans hz)
            · exact y.prop.2 (hy.symm.trans hz)
          · have hy : M.rot N (M.rot N x.val) = y.val := hn
            rcases hz2 with hz2 | hz2
            · exact y.prop.1 (hy.symm.trans hz2)
            · exact y.prop.2 (hy.symm.trans hz2)
        set x' := ((M.contract hij hopen
          (tail_ne_of_alternating h hN)).rotPerm (N.restrict hN)
          (alternating_contract h hij hN hopen)) x with hx'
        have hval : x'.val = M.rot N (M.rot N (M.rot N x.val)) :=
          rot_contract_eq_rot_three h hij hN hopen x hz
        have hrest : ((M.rotPerm N h) ^ (m + 1 - 3)) x'.val = y.val := by
          rw [hval]
          rw [show m = (m + 1 - 3) + 2 from by omega, pow_add] at hn
          exact hn
        have hone : ((M.contract hij hopen
            (tail_ne_of_alternating h hN)).rotPerm (N.restrict hN)
            (alternating_contract h hij hN hopen)).SameCycle x x' :=
          ⟨1, by rw [zpow_one]⟩
        exact hone.trans (ih (m + 1 - 3) (by omega) (x := x') hrest)
      · -- an ordinary step
        push Not at hz
        set x' : Surviving i j := ⟨M.rot N x.val, hz⟩ with hx'
        have hval : (((M.contract hij hopen
            (tail_ne_of_alternating h hN)).rotPerm (N.restrict hN)
            (alternating_contract h hij hN hopen)) x) = x' :=
          Subtype.ext (rot_contract_eq_rot h hij hN hopen x hz.1 hz.2)
        have hone : ((M.contract hij hopen
            (tail_ne_of_alternating h hN)).rotPerm (N.restrict hN)
            (alternating_contract h hij hN hopen)).SameCycle x x' :=
          ⟨1, by rw [zpow_one]; exact hval⟩
        exact hone.trans (ih m (by omega) (x := x') hn)

/-! ### An open glue step preserves the orbit count

The two directions together say the contraction's orbits are the
original's, so gluing a pair whose two labels are not already
partners changes neither the components of the union nor their
number.  That is the half of RS21's circuit-count bookkeeping in
which no circuit closes.
-/

/-- **The contraction has the same orbits.** -/
noncomputable def orbitsEquivContract [Fintype α] [DecidableEq α]
    (h : Alternating M N)
    {i j : α} (hij : i ≠ j) (hN : N.edge i = j)
    (hopen : M.edge i ≠ j) :
    Orbits ((M.contract hij hopen (tail_ne_of_alternating h hN)).rotPerm
        (N.restrict hN) (alternating_contract h hij hN hopen))
      ≃ Orbits (M.rotPerm N h) where
  toFun := Quotient.lift
    (fun x => Quotient.mk (Equiv.Perm.SameCycle.setoid (M.rotPerm N h)) x.val)
    (fun _ _ hab =>
      orbit_eq_iff.mpr (sameCycle_of_contract h hij hN hopen hab))
  invFun := Quotient.lift
    (fun a => Quotient.mk
      (Equiv.Perm.SameCycle.setoid ((M.contract hij hopen
        (tail_ne_of_alternating h hN)).rotPerm (N.restrict hN)
        (alternating_contract h hij hN hopen)))
      (M.pickSurvivor hopen a))
    (fun a b hab => orbit_eq_iff.mpr
      (sameCycle_contract_of_sameCycle h hij hN hopen
        (((sameCycle_pickSurvivor h hN hopen a).symm.trans hab).trans
          (sameCycle_pickSurvivor h hN hopen b))))
  left_inv := by
    refine Quotient.ind (fun x => ?_)
    have hpick : M.pickSurvivor hopen x.val = x := by
      unfold pickSurvivor
      rw [dif_pos x.prop]
    show Quotient.mk _ (M.pickSurvivor hopen x.val) = Quotient.mk _ x
    rw [hpick]
  right_inv := by
    refine Quotient.ind (fun a => ?_)
    exact orbit_eq_iff.mpr
      (sameCycle_pickSurvivor h hN hopen a).symm

/-- **An open glue step preserves the number of components.** -/
theorem orbitCount_contract [Fintype α] [DecidableEq α]
    (h : Alternating M N) {i j : α}
    (hij : i ≠ j) (hN : N.edge i = j) (hopen : M.edge i ≠ j) :
    orbitCount ((M.contract hij hopen
        (tail_ne_of_alternating h hN)).rotPerm (N.restrict hN)
        (alternating_contract h hij hN hopen))
      = orbitCount (M.rotPerm N h) :=
  orbitCount_eq_of_orbitsEquiv (orbitsEquivContract h hij hN hopen)

/-! ### A closed glue step closes one circuit

When the two identified labels are already partners in the chord
matching, they form a component of the union by themselves: the
rotation carries each to the other and nothing else meets them.
Gluing that pair closes it into a circuit and removes it, so the
number of components drops by exactly one.  This is the other half
of RS21's circuit-count bookkeeping, and the only half in which a
circuit appears.
-/

/-- The rotation carries each identified label to the other. -/
theorem rot_closed {i j : α}
    (hM : M.edge i = j) (hN : N.edge i = j) :
    M.rot N i = j ∧ M.rot N j = i := by
  have hMj : M.edge j = i := by rw [← hM, M.edge_invol]
  have hNj : N.edge j = i := by rw [← hN, N.edge_invol]
  constructor
  · unfold rot
    by_cases hb : M.tail i = true
    · rw [if_pos hb, hM]
    · rw [if_neg hb, hN]
  · unfold rot
    by_cases hb : M.tail j = true
    · rw [if_pos hb, hMj]
    · rw [if_neg hb, hNj]

/-- Nothing outside the identified pair meets it. -/
theorem rot_survivor_closed {i j : α} (hM : M.edge i = j)
    (hN : N.edge i = j) (x : Surviving i j) :
    M.rot N x.val ≠ i ∧ M.rot N x.val ≠ j := by
  have hMj : M.edge j = i := by rw [← hM, M.edge_invol]
  have hNj : N.edge j = i := by rw [← hN, N.edge_invol]
  have key : ∀ P : DirMatching α, P.edge i = j → P.edge j = i →
      P.edge x.val ≠ i ∧ P.edge x.val ≠ j := by
    intro P hPi hPj
    refine ⟨fun hx => x.prop.2 ?_, fun hx => x.prop.1 ?_⟩
    · exact ((P.edge_invol x.val).symm.trans
        (congrArg P.edge hx)).trans hPi
    · exact ((P.edge_invol x.val).symm.trans
        (congrArg P.edge hx)).trans hPj
  unfold rot
  by_cases hb : M.tail x.val = true
  · rw [if_pos hb]
    exact key M hM hMj
  · rw [if_neg hb]
    exact key N hN hNj

/-- **The restricted rotation is the rotation restricted.** -/
theorem rotPerm_restrict (h : Alternating M N) {i j : α}
    (hM : M.edge i = j) (hN : N.edge i = j) (x : Surviving i j) :
    (((M.restrict hM).rotPerm (N.restrict hN)
        (fun z => h z.val)) x).val = M.rot N x.val := by
  show ((M.restrict hM).rot (N.restrict hN) x).val = _
  unfold rot
  by_cases hb : M.tail x.val = true
  · rw [if_pos (show (M.restrict hM).tail x = true from hb),
      if_pos hb]
    rfl
  · rw [if_neg (show ¬ ((M.restrict hM).tail x = true) from hb),
      if_neg hb]
    rfl

/-- The identified pair is invariant under the rotation, and so is
its complement. -/
theorem rot_surviving_iff [DecidableEq α] (h : Alternating M N)
    {i j : α} (hM : M.edge i = j) (hN : N.edge i = j) (x : α) :
    ((M.rotPerm N h) x ≠ i ∧ (M.rotPerm N h) x ≠ j)
      ↔ (x ≠ i ∧ x ≠ j) := by
  obtain ⟨hi, hj⟩ := rot_closed hM hN
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨fun hx => h2 ?_, fun hx => h1 ?_⟩
    · show M.rot N x = j
      rw [hx]; exact hi
    · show M.rot N x = i
      rw [hx]; exact hj
  · intro hx
    exact rot_survivor_closed hM hN ⟨x, hx⟩

/-- The rotation restricted to the identified pair has one orbit. -/
theorem orbitCount_pair [Fintype α] [DecidableEq α]
    (h : Alternating M N) {i j : α}
    (hM : M.edge i = j) (hN : N.edge i = j) :
    orbitCount ((M.rotPerm N h).subtypePerm
      (p := fun x => ¬ (x ≠ i ∧ x ≠ j))
      (fun x => (rot_surviving_iff h hM hN x).not)) = 1 := by
  classical
  obtain ⟨hi, hj⟩ := rot_closed hM hN
  set π := (M.rotPerm N h).subtypePerm
    (p := fun x => ¬ (x ≠ i ∧ x ≠ j))
    (fun x => (rot_surviving_iff h hM hN x).not) with hπ
  have hiMem : ¬ ((i : α) ≠ i ∧ (i : α) ≠ j) := fun hc => hc.1 rfl
  rw [orbitCount_eq_card_orbits]
  refine Fintype.card_eq_one_iff.mpr
    ⟨Quotient.mk (Equiv.Perm.SameCycle.setoid π) ⟨i, hiMem⟩, ?_⟩
  refine Quotient.ind (fun z => ?_)
  refine orbit_eq_iff.mpr ?_
  have hz : z.val = i ∨ z.val = j := by
    by_contra hc
    exact z.prop ⟨fun hx => hc (Or.inl hx), fun hx => hc (Or.inr hx)⟩
  rcases hz with hz | hz
  · exact (Equiv.Perm.SameCycle.refl π z).trans
      (by rw [show z = ⟨i, hiMem⟩ from Subtype.ext hz])
  · refine ⟨1, ?_⟩
    rw [zpow_one]
    refine Subtype.ext ?_
    show M.rot N z.val = i
    rw [hz]
    exact hj

/-- **A closed glue step closes exactly one circuit.** -/
theorem orbitCount_restrict_closed [Fintype α] [DecidableEq α]
    (h : Alternating M N) {i j : α}
    (hM : M.edge i = j) (hN : N.edge i = j) :
    orbitCount ((M.restrict hM).rotPerm (N.restrict hN)
        (fun z => h z.val)) + 1
      = orbitCount (M.rotPerm N h) := by
  classical
  have hsplit := orbitCount_eq_add (M.rotPerm N h)
    (fun x => x ≠ i ∧ x ≠ j) (fun x => rot_surviving_iff h hM hN x)
  have hpair := orbitCount_pair h hM hN
  have hrest : (M.rotPerm N h).subtypePerm
      (fun x => rot_surviving_iff h hM hN x)
      = (M.restrict hM).rotPerm (N.restrict hN)
        (fun z => h z.val) :=
    Equiv.ext (fun z => Subtype.ext
      (rotPerm_restrict h hM hN z).symm)
  rw [hsplit, hrest, hpair]

/-! ### The component count ignores the directions

The rotation depends on which arc leaves each point, but its orbits
do not: one step of either rotation crosses one of the two arcs at a
point, and both arcs are visible to the other rotation as well.  So
the number of components of the union is a function of the two
pairings alone.

This is what lets a matching be transported across a construction
that changes the directions — a glue, say, which can turn a label
into a through-label and so flip the convention that fixes its
direction — as long as the pairings correspond.
-/

/-- **The number of components does not depend on the
directions.** -/
theorem orbitCount_rotPerm_congr [Fintype α] [DecidableEq α]
    {M₁ N₁ M₂ N₂ : DirMatching α} (h₁ : Alternating M₁ N₁)
    (h₂ : Alternating M₂ N₂) (heM : M₁.edge = M₂.edge)
    (heN : N₁.edge = N₂.edge) :
    orbitCount (M₁.rotPerm N₁ h₁) = orbitCount (M₂.rotPerm N₂ h₂) := by
  have hstep : ∀ (P₁ Q₁ P₂ Q₂ : DirMatching α)
      (k₁ : Alternating P₁ Q₁) (k₂ : Alternating P₂ Q₂),
      P₁.edge = P₂.edge → Q₁.edge = Q₂.edge →
      ∀ a, (P₂.rotPerm Q₂ k₂).SameCycle a (P₁.rot Q₁ a) := by
    intro P₁ Q₁ P₂ Q₂ _ k₂ hP hQ a
    unfold rot
    by_cases ha : P₁.tail a = true
    · rw [if_pos ha, show P₁.edge a = P₂.edge a from by rw [hP]]
      exact sameCycle_rot_edge k₂ a
    · rw [if_neg ha, show Q₁.edge a = Q₂.edge a from by rw [hQ]]
      exact sameCycle_rot_edge' k₂ a
  refine orbitCount_eq_of_orbitsEquiv ?_
  refine
    { toFun := Quotient.lift
        (fun a => Quotient.mk (Equiv.Perm.SameCycle.setoid
          (M₂.rotPerm N₂ h₂)) a)
        (fun _ _ hab => orbit_eq_iff.mpr
          (sameCycle_of_step id (hstep M₁ N₁ M₂ N₂ h₁ h₂ heM heN) hab))
      invFun := Quotient.lift
        (fun a => Quotient.mk (Equiv.Perm.SameCycle.setoid
          (M₁.rotPerm N₁ h₁)) a)
        (fun _ _ hab => orbit_eq_iff.mpr
          (sameCycle_of_step id
            (hstep M₂ N₂ M₁ N₁ h₂ h₁ heM.symm heN.symm) hab))
      left_inv := ?_
      right_inv := ?_ }
  · exact Quotient.ind (fun _ => rfl)
  · exact Quotient.ind (fun _ => rfl)

/-! ### The glue steps, stated on the pairings alone

The transport from a fragment supplies matchings whose pairings are
the contraction's but whose directions come from whatever convention
the glued object uses.  Since the component count ignores the
directions, the two steps can be stated that way, and the transport
then has only the pairings to check.
-/

/-- **An open glue step, with arbitrary directions.** -/
theorem orbitCount_contract_congr [Fintype α] [DecidableEq α]
    {M N : DirMatching α} (h : Alternating M N) {i j : α}
    (hij : i ≠ j) (hN : N.edge i = j) (hopen : M.edge i ≠ j)
    {M' N' : DirMatching (Surviving i j)} (h' : Alternating M' N')
    (heM : M'.edge
      = (M.contract hij hopen (tail_ne_of_alternating h hN)).edge)
    (heN : N'.edge = (N.restrict hN).edge) :
    orbitCount (M'.rotPerm N' h') = orbitCount (M.rotPerm N h) := by
  rw [orbitCount_rotPerm_congr h'
    (alternating_contract h hij hN hopen) heM heN]
  exact orbitCount_contract h hij hN hopen

/-- **A closed glue step, with arbitrary directions.** -/
theorem orbitCount_restrict_closed_congr [Fintype α] [DecidableEq α]
    {M N : DirMatching α} (h : Alternating M N) {i j : α}
    (hM : M.edge i = j) (hN : N.edge i = j)
    {M' N' : DirMatching (Surviving i j)} (h' : Alternating M' N')
    (heM : M'.edge = (M.restrict hM).edge)
    (heN : N'.edge = (N.restrict hN).edge) :
    orbitCount (M'.rotPerm N' h') + 1
      = orbitCount (M.rotPerm N h) := by
  rw [orbitCount_rotPerm_congr h' (fun z => h z.val) heM heN]
  exact orbitCount_restrict_closed h hM hN

/-- **Transporting a pair of matchings along a bijection conjugates
the rotation**, so the component count is unchanged. -/
theorem orbitCount_map [Fintype α] [DecidableEq α] {β : Type}
    [Fintype β] [DecidableEq β] (e : α ≃ β) {M N : DirMatching α}
    (h : Alternating M N) (h' : Alternating (M.map e) (N.map e)) :
    orbitCount ((M.map e).rotPerm (N.map e) h')
      = orbitCount (M.rotPerm N h) := by
  have hconj : (M.map e).rotPerm (N.map e) h'
      = e.permCongr (M.rotPerm N h) := by
    refine Equiv.ext (fun b => ?_)
    show (M.map e).rot (N.map e) b = e (M.rot N (e.symm b))
    unfold rot map
    by_cases hb : M.tail (e.symm b) = true
    · rw [if_pos hb, if_pos hb]
    · rw [if_neg hb, if_neg hb]
  rw [hconj, orbitCount_permCongr]

/-- The transported matching's partner map, conjugated by the
equivalence. -/
theorem map_edge {β : Type} (e : α ≃ β) (M : DirMatching α) (b : β) :
    (M.map e).edge b = e (M.edge (e.symm b)) := rfl

/-- Transported matchings have the same pairing when the originals
do. -/
theorem map_edge_congr {β : Type} (e : α ≃ β) {M M' : DirMatching α}
    (h : M'.edge = M.edge) : (M'.map e).edge = (M.map e).edge :=
  funext (fun b => congrArg e (congrFun h (e.symm b)))

/-- Transporting a pair of matchings preserves the Eulerian
condition. -/
theorem alternating_map {β : Type} (e : α ≃ β) {M N : DirMatching α}
    (h : Alternating M N) : Alternating (M.map e) (N.map e) :=
  fun b => h (e.symm b)

/-- **At a closed pair the contraction is the plain restriction**:
no surviving point has either identified label as its partner. -/
theorem contractEdge_of_closed [DecidableEq α] (M : DirMatching α)
    {i j : α} (hM : M.edge i = j) (x : α) (hx : x ≠ i)
    (hx' : x ≠ j) : M.contractEdge i j x = M.edge x := by
  have hMj : M.edge j = i := by rw [← hM, M.edge_invol]
  unfold contractEdge
  rw [if_neg (fun hc => hx' (((M.edge_invol x).symm.trans
      (congrArg M.edge hc)).trans hM)),
    if_neg (fun hc => hx (((M.edge_invol x).symm.trans
      (congrArg M.edge hc)).trans hMj))]

/-! ### The component count of a union

RS21's `c(M ∪ N)` is the number of connected components of the union
of two directed matchings, and the union has those components
whatever the directions are: the repair to Eulerian position exists
and the count does not depend on which one is taken.  Naming the
count that way removes the Eulerian position from every statement
that only reads it — and that is most of them, the position mattering
only where the *signs* do.
-/

/-- **The number of components of the union of two matchings** —
RS21's `c(M ∪ N)`, read at any repair to Eulerian position.  It
carries no decidability instance: on a sum type the ambient one is
the sum's own, which is not the one a linear order supplies, and the
two would not match where the recursion compares them. -/
noncomputable def unionCount [Fintype α] (M N : DirMatching α) : ℕ :=
  letI := Classical.decEq α
  orbitCount ((exists_alternating_repair M N).choose.rotPerm
    (exists_alternating_repair M N).choose_spec.choose
    (exists_alternating_repair M N).choose_spec.choose_spec.2.2)

/-- **The count is what any Eulerian pair with the same pairings
counts.** -/
theorem unionCount_eq_orbitCount [Fintype α] [DecidableEq α]
    {M N M' N' : DirMatching α} (h' : Alternating M' N')
    (heM : M'.edge = M.edge) (heN : N'.edge = N.edge) :
    unionCount M N = orbitCount (M'.rotPerm N' h') := by
  show (letI := Classical.decEq α; orbitCount _) = _
  rw [orbitCount_congr_decEq (Classical.decEq α) (inferInstance)]
  refine orbitCount_rotPerm_congr _ h' ?_ ?_
  · rw [(exists_alternating_repair M N).choose_spec.choose_spec.1,
      heM]
  · rw [(exists_alternating_repair M N).choose_spec.choose_spec.2.1,
      heN]

/-- **The count depends on the pairings alone.** -/
theorem unionCount_congr [Fintype α] {M₁ N₁ M₂ N₂ : DirMatching α}
    (heM : M₁.edge = M₂.edge) (heN : N₁.edge = N₂.edge) :
    unionCount M₁ N₁ = unionCount M₂ N₂ := by
  classical
  refine (unionCount_eq_orbitCount
    (M := M₁) (N := N₁)
    (exists_alternating_repair M₂ N₂).choose_spec.choose_spec.2.2
    ?_ ?_).trans
    (unionCount_eq_orbitCount (M := M₂) (N := N₂)
      (exists_alternating_repair M₂ N₂).choose_spec.choose_spec.2.2
      (exists_alternating_repair M₂ N₂).choose_spec.choose_spec.1
      (exists_alternating_repair M₂
        N₂).choose_spec.choose_spec.2.1).symm
  · rw [(exists_alternating_repair M₂ N₂).choose_spec.choose_spec.1,
      heM]
  · rw [(exists_alternating_repair M₂ N₂).choose_spec.choose_spec.2.1,
      heN]

/-- **An empty ground set has no components.** -/
theorem unionCount_of_isEmpty [Fintype α] [IsEmpty α]
    (M N : DirMatching α) : unionCount M N = 0 := by
  classical
  rw [unionCount_eq_orbitCount
      (exists_alternating_repair M N).choose_spec.choose_spec.2.2
      (exists_alternating_repair M N).choose_spec.choose_spec.1
      (exists_alternating_repair M N).choose_spec.choose_spec.2.1,
    orbitCount_eq_card_orbits]
  refine Fintype.card_eq_zero_iff.mpr ⟨fun o => ?_⟩
  exact Quotient.inductionOn o (fun x => isEmptyElim x)

/-- **The count survives a relabelling of the ground set.** -/
theorem unionCount_map [Fintype α] {β : Type} [Fintype β]
    (e : α ≃ β) (M N : DirMatching α) :
    unionCount (M.map e) (N.map e) = unionCount M N := by
  classical
  set A := (exists_alternating_repair M N).choose with hA
  set B := (exists_alternating_repair M N).choose_spec.choose with hB
  have hspec := (exists_alternating_repair M N).choose_spec.choose_spec
  have hAB : Alternating A B := hspec.2.2
  rw [unionCount_eq_orbitCount (M := M.map e) (N := N.map e)
      (alternating_map e hAB)
      (by funext b; exact congrArg e (congrFun hspec.1 (e.symm b)))
      (by funext b; exact congrArg e (congrFun hspec.2.1 (e.symm b))),
    unionCount_eq_orbitCount (M := M) (N := N) hAB hspec.1 hspec.2.1,
    orbitCount_map e hAB (alternating_map e hAB)]

/-- **Lemma 11 across an identification**: two matchings whose
directions are opposite along an order isomorphism have signs
multiplying to `(-1)` to the number of components of their union. -/
theorem sgnRel_mul_sgnRel_of_alternating {γ δ : Type} [LinearOrder γ]
    [LinearOrder δ] [Fintype γ] [Fintype δ] (E : γ ≃o δ) {m : ℕ}
    (hc : Fintype.card γ = 2 * m) (hc' : Fintype.card δ = 2 * m)
    (M : DirMatching γ) (N : DirMatching δ)
    (halt : ∀ a : γ, N.tail (E a) = !M.tail a) :
    ((sgnRel (stdMatching hc) M : ℤ) : ℂ)
        * ((sgnRel (stdMatching hc') N : ℤ) : ℂ)
      = (-1 : ℂ) ^ unionCount M (N.map E.symm.toEquiv) := by
  classical
  have halt' : Alternating M (N.map E.symm.toEquiv) := fun a => halt a
  rw [unionCount_eq_orbitCount halt' rfl rfl]
  have hs := sgnRel_mul_sgnRel_map_alternating E hc hc' M N halt'
  push_cast at hs ⊢
  exact hs

/-! ### The union read across a two-sided interface

RS21 reads `M(ω₁,κ₁) ∪ M(ω₂,κ₂)` on one copy of the label set `S`,
the two fragments' arcs sharing their ends.  The flag model keeps the
two fragments' labels apart, so the same union is read on the sum:
the two chord matchings side by side, against the matching that
identifies the two copies.  The two readings count the same
components — one step of the one-copy rotation is one or three steps
of the two-copy one, and the two copies of a label always lie on a
common component.
-/

/-- **Two matchings, side by side.** -/
def sumMatching {γ δ : Type} (M : DirMatching γ) (N : DirMatching δ) :
    DirMatching (γ ⊕ δ) where
  edge := Sum.map M.edge N.edge
  edge_invol x := by
    rcases x with a | b
    · exact congrArg Sum.inl (M.edge_invol a)
    · exact congrArg Sum.inr (N.edge_invol b)
  edge_ne x := by
    rcases x with a | b
    · exact fun h => M.edge_ne a (Sum.inl.inj h)
    · exact fun h => N.edge_ne b (Sum.inr.inj h)
  tail := Sum.elim M.tail N.tail
  tail_flip x := by
    rcases x with a | b
    · exact M.tail_flip a
    · exact N.tail_flip b

/-- **The interface matching across an identification** of the two
sides' labels. -/
def interfaceEquivMatching {γ δ : Type} (e : γ ≃ δ) :
    DirMatching (γ ⊕ δ) where
  edge := Sum.elim (fun a => Sum.inr (e a)) (fun b => Sum.inl (e.symm b))
  edge_invol x := by
    rcases x with a | b
    · exact congrArg Sum.inl (e.symm_apply_apply a)
    · exact congrArg Sum.inr (e.apply_symm_apply b)
  edge_ne x := by
    rcases x with a | b
    · exact fun h => Sum.inr_ne_inl h
    · exact fun h => Sum.inl_ne_inr h
  tail := Sum.isLeft
  tail_flip x := by rcases x with a | b <;> rfl

section TwoSided

variable {γ δ : Type}

/-- The two-copy repair built from a one-copy one. -/
private def sumRepair (e : γ ≃ δ)
    {A₁ B₁ : DirMatching γ}
    (_h : Alternating A₁ B₁) : DirMatching (γ ⊕ δ) :=
  sumMatching A₁ (B₁.map e)

/-- The interface half of the two-copy repair. -/
private def interfaceRepair (e : γ ≃ δ)
    {A₁ B₁ : DirMatching γ}
    (h : Alternating A₁ B₁) : DirMatching (γ ⊕ δ) where
  edge := Sum.elim (fun a => Sum.inr (e a)) (fun b => Sum.inl (e.symm b))
  edge_invol x := (interfaceEquivMatching e).edge_invol x
  edge_ne x := (interfaceEquivMatching e).edge_ne x
  tail := Sum.elim (fun a => !A₁.tail a) (fun b => !B₁.tail (e.symm b))
  tail_flip x := by
    rcases x with a | b
    · show (!B₁.tail (e.symm (e a))) = !(!A₁.tail a)
      rw [e.symm_apply_apply, h a, Bool.not_not]
    · show (!A₁.tail (e.symm b)) = !(!B₁.tail (e.symm b))
      rw [h (e.symm b), Bool.not_not]

private theorem alternating_sumRepair (e : γ ≃ δ)
    {A₁ B₁ : DirMatching γ}
    (h : Alternating A₁ B₁) :
    Alternating (sumRepair (δ := δ) e h) (interfaceRepair e h) := by
  rintro (a | b)
  · rfl
  · rfl

/-- One step of the one-copy rotation is a walk of the two-copy
one. -/
private theorem sameCycle_inl (e : γ ≃ δ)
    {A₁ B₁ : DirMatching γ}
    (h : Alternating A₁ B₁) (a : γ) :
    ((sumRepair (δ := δ) e h).rotPerm (interfaceRepair e h)
        (alternating_sumRepair e h)).SameCycle (Sum.inl a)
      (Sum.inl (A₁.rot B₁ a)) := by
  set π := (sumRepair (δ := δ) e h).rotPerm (interfaceRepair e h)
    (alternating_sumRepair e h) with hπ
  have hstep : ∀ x, π x = (sumRepair (δ := δ) e h).rot
      (interfaceRepair e h) x := fun _ => rfl
  by_cases ha : A₁.tail a = true
  · refine ⟨1, ?_⟩
    rw [zpow_one, hstep, show A₁.rot B₁ a = A₁.edge a from by
      rw [rot, if_pos ha]]
    show (if A₁.tail a = true then (Sum.inl (A₁.edge a) : γ ⊕ δ)
      else Sum.inr (e a)) = Sum.inl (A₁.edge a)
    rw [if_pos ha]
  · have ha' : A₁.tail a = false := by
      cases hb : A₁.tail a
      · rfl
      · exact absurd hb ha
    have hb : B₁.tail a = true := by rw [h a, ha']; rfl
    have hb2 : B₁.tail (B₁.edge a) = false := by
      rw [B₁.tail_flip a, hb]; rfl
    refine ⟨3, ?_⟩
    have h1 : π (Sum.inl a) = Sum.inr (e a) := by
      rw [hstep]
      show (if A₁.tail a = true then (Sum.inl (A₁.edge a) : γ ⊕ δ)
        else Sum.inr (e a)) = Sum.inr (e a)
      rw [if_neg ha]
    have h2 : π (Sum.inr (e a)) = Sum.inr (e (B₁.edge a)) := by
      rw [hstep]
      show (if B₁.tail (e.symm (e a)) = true then
          (Sum.inr (e (B₁.edge (e.symm (e a)))) : γ ⊕ δ)
        else Sum.inl (e.symm (e a))) = Sum.inr (e (B₁.edge a))
      rw [e.symm_apply_apply, if_pos hb]
    have h3 : π (Sum.inr (e (B₁.edge a))) = Sum.inl (B₁.edge a) := by
      rw [hstep]
      show (if B₁.tail (e.symm (e (B₁.edge a))) = true then
          (Sum.inr (e (B₁.edge (e.symm (e (B₁.edge a)))))
            : γ ⊕ δ)
        else Sum.inl (e.symm (e (B₁.edge a))))
        = Sum.inl (B₁.edge a)
      rw [e.symm_apply_apply, if_neg (by rw [hb2]; exact Bool.noConfusion)]
    have : (π ^ (3 : ℕ)) (Sum.inl a) = Sum.inl (B₁.edge a) := by
      show π (π (π (Sum.inl a))) = Sum.inl (B₁.edge a)
      rw [h1, h2, h3]
    rw [show ((3 : ℤ)) = ((3 : ℕ) : ℤ) from rfl, zpow_natCast, this,
      rot, if_neg ha]

/-- The two-copy rotation projects to the one-copy one. -/
private theorem sameCycle_proj (e : γ ≃ δ)
    {A₁ B₁ : DirMatching γ}
    (h : Alternating A₁ B₁) (x : γ ⊕ δ) :
    (A₁.rotPerm B₁ h).SameCycle (Sum.elim id (fun b => e.symm b) x)
      (Sum.elim id (fun b => e.symm b)
        (((sumRepair (δ := δ) e h).rotPerm (interfaceRepair e h)
          (alternating_sumRepair e h)) x)) := by
  have hstep : ∀ y, ((sumRepair (δ := δ) e h).rotPerm
      (interfaceRepair e h) (alternating_sumRepair e h)) y
      = (sumRepair (δ := δ) e h).rot (interfaceRepair e h) y :=
    fun _ => rfl
  rcases x with a | b
  · by_cases ha : A₁.tail a = true
    · refine ⟨1, ?_⟩
      rw [zpow_one, hstep]
      show A₁.rot B₁ a = Sum.elim id (fun b => e.symm b)
        (if A₁.tail a = true then (Sum.inl (A₁.edge a) : γ ⊕ δ)
          else Sum.inr (e a))
      rw [if_pos ha, rot, if_pos ha]
      rfl
    · refine ⟨0, ?_⟩
      rw [zpow_zero, hstep]
      show a = Sum.elim id (fun b => e.symm b)
        (if A₁.tail a = true then (Sum.inl (A₁.edge a) : γ ⊕ δ)
          else Sum.inr (e a))
      rw [if_neg ha]
      exact (e.symm_apply_apply a).symm
  · by_cases hb : B₁.tail (e.symm b) = true
    · have ha : A₁.tail (e.symm b) ≠ true := by
        have := h (e.symm b)
        rw [hb] at this
        rw [show A₁.tail (e.symm b) = false from by
          cases hc : A₁.tail (e.symm b)
          · rfl
          · rw [hc] at this; exact absurd this.symm (by decide)]
        exact Bool.noConfusion
      refine ⟨1, ?_⟩
      rw [zpow_one, hstep]
      show A₁.rot B₁ (e.symm b) = Sum.elim id (fun c => e.symm c)
        (if B₁.tail (e.symm b) = true then
            (Sum.inr (e (B₁.edge (e.symm b))) : γ ⊕ δ)
          else Sum.inl (e.symm b))
      rw [if_pos hb, rot, if_neg ha]
      exact (e.symm_apply_apply _).symm
    · refine ⟨0, ?_⟩
      rw [zpow_zero, hstep]
      show e.symm b = Sum.elim id (fun c => e.symm c)
        (if B₁.tail (e.symm b) = true then
            (Sum.inr (e (B₁.edge (e.symm b))) : γ ⊕ δ)
          else Sum.inl (e.symm b))
      rw [if_neg hb]
      rfl

/-- The two copies of a label lie on a common component. -/
private theorem sameCycle_inl_proj (e : γ ≃ δ)
    {A₁ B₁ : DirMatching γ}
    (h : Alternating A₁ B₁) (x : γ ⊕ δ) :
    ((sumRepair (δ := δ) e h).rotPerm (interfaceRepair e h)
        (alternating_sumRepair e h)).SameCycle
      (Sum.inl (Sum.elim id (fun b => e.symm b) x)) x := by
  have hstep : ∀ y, ((sumRepair (δ := δ) e h).rotPerm
      (interfaceRepair e h) (alternating_sumRepair e h)) y
      = (sumRepair (δ := δ) e h).rot (interfaceRepair e h) y :=
    fun _ => rfl
  rcases x with a | b
  · exact ⟨0, rfl⟩
  · by_cases ha : A₁.tail (e.symm b) = true
    · have hkey : ((sumRepair (δ := δ) e h).rotPerm
          (interfaceRepair e h) (alternating_sumRepair e h))
          (Sum.inr b) = Sum.inl (e.symm b) := by
        rw [hstep]
        show (if B₁.tail (e.symm b) = true then
            (Sum.inr (e (B₁.edge (e.symm b))) : γ ⊕ δ)
          else Sum.inl (e.symm b)) = Sum.inl (e.symm b)
        rw [if_neg (show ¬ (B₁.tail (e.symm b) = true) from by
          rw [h (e.symm b), ha]; decide)]
      refine Equiv.Perm.SameCycle.symm ?_
      exact ⟨1, by rw [zpow_one]; exact hkey⟩
    · refine ⟨1, ?_⟩
      rw [zpow_one, hstep]
      show (if A₁.tail (e.symm b) = true then
          (Sum.inl (A₁.edge (e.symm b)) : γ ⊕ δ)
        else Sum.inr (e (e.symm b))) = Sum.inr b
      rw [if_neg ha, e.apply_symm_apply]

/-- **The union on two copies counts what the union on one copy
counts.** -/
theorem unionCount_sumMatching
    [Fintype γ] [DecidableEq γ] [Fintype δ] [DecidableEq δ] (e : γ ≃ δ)
    (M₁ : DirMatching γ)
    (M₂ : DirMatching δ) :
    unionCount (sumMatching M₁ M₂) (interfaceEquivMatching e)
      = unionCount M₁ (M₂.map e.symm) := by
  classical
  obtain ⟨A₁, B₁, hAe, hBe, hAB⟩ :=
    exists_alternating_repair M₁ (M₂.map e.symm)
  have hsum : (sumRepair (δ := δ) e hAB).edge
      = (sumMatching M₁ M₂).edge := by
    funext x
    rcases x with a | b
    · exact congrArg Sum.inl (congrFun hAe a)
    · refine congrArg Sum.inr ?_
      show e (B₁.edge (e.symm b)) = M₂.edge b
      rw [congrFun hBe (e.symm b)]
      show e (e.symm (M₂.edge (e (e.symm b)))) = M₂.edge b
      rw [e.apply_symm_apply, e.apply_symm_apply]
  rw [unionCount_eq_orbitCount (M := sumMatching M₁ M₂)
      (N := interfaceEquivMatching e)
      (alternating_sumRepair e hAB) hsum rfl,
    unionCount_eq_orbitCount (M := M₁) (N := M₂.map e.symm) hAB hAe
      hBe]
  refine (orbitCount_eq_of_orbitsEquiv (π := (sumRepair (δ := δ) e hAB).rotPerm
    (interfaceRepair e hAB) (alternating_sumRepair e hAB))
    (ρ := A₁.rotPerm B₁ hAB) ?_)
  refine
    { toFun := Quotient.lift
        (fun x => Quotient.mk _ (Sum.elim id (fun b => e.symm b) x))
        (fun _ _ hab => Quotient.sound
          (sameCycle_of_step (Sum.elim id (fun b => e.symm b))
            (sameCycle_proj e hAB) hab))
      invFun := Quotient.lift (fun a => Quotient.mk _ (Sum.inl a))
        (fun _ _ hab => Quotient.sound
          (sameCycle_of_step Sum.inl (sameCycle_inl e hAB) hab))
      left_inv := ?_
      right_inv := ?_ }
  · exact Quotient.ind (fun x => Quotient.sound
      (sameCycle_inl_proj e hAB x))
  · exact Quotient.ind (fun _ => rfl)

end TwoSided

end DirMatching

end RS
