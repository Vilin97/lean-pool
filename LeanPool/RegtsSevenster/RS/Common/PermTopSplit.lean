/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

module

public import LeanPool.RegtsSevenster.RS.Common.MathlibDeps

/-!
# Splitting a permutation at the top slot

A permutation of `Fin (n + 1)` is determined by where it sends the
top slot, `Fin.last n`, together with the permutation it induces on
the remaining slots once both sides are compressed
order-preservingly.  This is the decomposition the symmetric-group
action on a tensor power recurses on.

`Equiv.Perm.decomposeFin` is the analogous splitting at slot `0`, but
it compresses by `swap 0 p` rather than order-preservingly, so its
induced permutation is not the one a tensor power's factors see.  The
compression here is `finSuccAboveEquiv`.
-/

@[expose] public section

namespace RS

open Equiv

variable {n : ℕ}

/-- Where a permutation sends the top slot. -/
def topImage (σ : Perm (Fin (n + 1))) : Fin (n + 1) := σ (Fin.last n)

/-- The identity leaves the top slot alone. -/
@[simp]
theorem topImage_one : topImage (1 : Perm (Fin (n + 1))) = Fin.last n := rfl

/-- A non-top slot has a non-top image, and conversely. -/
private theorem ne_last_iff (σ : Perm (Fin (n + 1))) (x : Fin (n + 1)) :
    x ≠ Fin.last n ↔ σ x ≠ topImage σ := by
  simp [topImage, σ.injective.eq_iff]

/-- **The induced permutation of the remaining slots.**  Both the
source slots other than the top one and the target slots other than
`topImage σ` are compressed to `Fin n` order-preservingly, and `σ`
carries one to the other. -/
def restPerm (σ : Perm (Fin (n + 1))) : Perm (Fin n) :=
  (finSuccAboveEquiv (Fin.last n)).trans
    ((Equiv.subtypeEquiv σ
      (show ∀ x, x ≠ Fin.last n ↔ σ x ≠ topImage σ from by exact ne_last_iff σ)).trans
      (finSuccAboveEquiv (topImage σ)).symm)

/-- The defining property of `restPerm`: reinserting the compressed
image at `topImage σ` recovers the action of `σ`. -/
theorem succAbove_restPerm (σ : Perm (Fin (n + 1))) (j : Fin n) :
    (topImage σ).succAbove (restPerm σ j) = σ j.castSucc := by
  have h : ((finSuccAboveEquiv (topImage σ)).symm
      ⟨σ ((Fin.last n).succAbove j), (ne_last_iff σ _).1
        (Fin.succAbove_ne _ j)⟩ : Fin n) = restPerm σ j := rfl
  have h2 := congrArg Subtype.val
    ((finSuccAboveEquiv (topImage σ)).apply_symm_apply
      ⟨σ ((Fin.last n).succAbove j), (ne_last_iff σ _).1
        (Fin.succAbove_ne _ j)⟩)
  rw [finSuccAboveEquiv_apply] at h2
  rw [h] at h2
  simpa [Fin.succAbove_last] using h2

/-- The identity induces the identity on the lower slots. -/
@[simp]
theorem restPerm_one : restPerm (1 : Perm (Fin (n + 1))) = 1 := by
  ext j
  have h := succAbove_restPerm (1 : Perm (Fin (n + 1))) j
  rw [topImage_one, Fin.succAbove_last] at h
  simpa using congrArg Fin.val h

/-! ## Permutations fixing the top slot

The standard embedding `S_n ↪ S_{n+1}`, extending by the identity on
the top slot.  It is the embedding `symCast` uses, so the tower's
compatibility field sees exactly these permutations.
-/

/-- A permutation of the lower slots, extended by fixing the top
slot. -/
noncomputable def extPerm (τ : Perm (Fin n)) : Perm (Fin (n + 1)) :=
  τ.viaEmbedding Fin.castSuccEmb

/-- On a lower slot the extension acts by `τ`. -/
@[simp]
theorem extPerm_castSucc (τ : Perm (Fin n)) (j : Fin n) :
    extPerm τ j.castSucc = (τ j).castSucc :=
  Equiv.Perm.viaEmbedding_apply τ Fin.castSuccEmb j

/-- The extension fixes the top slot. -/
@[simp]
theorem extPerm_last (τ : Perm (Fin n)) :
    extPerm τ (Fin.last n) = Fin.last n := by
  refine Equiv.Perm.viaEmbedding_apply_of_notMem τ Fin.castSuccEmb _ ?_
  rintro ⟨j, hj⟩
  exact absurd hj (Fin.castSucc_lt_last j).ne

/-- Extending by the top slot is a monoid map. -/
@[simp]
theorem extPerm_mul (τ ρ : Perm (Fin n)) :
    extPerm (τ * ρ) = extPerm τ * extPerm ρ :=
  (Equiv.Perm.viaEmbeddingHom Fin.castSuccEmb).map_mul τ ρ

/-- Extending the identity gives the identity. -/
@[simp]
theorem extPerm_one : extPerm (1 : Perm (Fin n)) = 1 :=
  (Equiv.Perm.viaEmbeddingHom Fin.castSuccEmb).map_one

/-- Precomposing with a permutation of the lower slots leaves the top
slot's image alone. -/
@[simp]
theorem topImage_mul_extPerm (σ : Perm (Fin (n + 1))) (τ : Perm (Fin n)) :
    topImage (σ * extPerm τ) = topImage σ := by
  change σ (extPerm τ (Fin.last n)) = σ (Fin.last n)
  rw [extPerm_last]

/-- **Precomposing with a permutation of the lower slots** acts on
the induced permutation by precomposition, with no interaction with
the top slot. -/
theorem restPerm_mul_extPerm (σ : Perm (Fin (n + 1))) (τ : Perm (Fin n)) :
    restPerm (σ * extPerm τ) = restPerm σ * τ := by
  ext j
  have h1 := succAbove_restPerm (σ * extPerm τ) j
  rw [topImage_mul_extPerm] at h1
  have h2 : (σ * extPerm τ) j.castSucc = σ (τ j).castSucc := by
    change σ (extPerm τ j.castSucc) = σ (τ j).castSucc
    rw [extPerm_castSucc]
  rw [h2, ← succAbove_restPerm σ (τ j)] at h1
  exact congrArg Fin.val (Fin.succAbove_right_injective h1)

/-- A top-fixing permutation fixes the top slot. -/
@[simp]
theorem topImage_extPerm (τ : Perm (Fin n)) :
    topImage (extPerm τ) = Fin.last n := extPerm_last τ

/-- A top-fixing permutation induces itself on the lower slots. -/
@[simp]
theorem restPerm_extPerm (τ : Perm (Fin n)) : restPerm (extPerm τ) = τ := by
  have h := restPerm_mul_extPerm (1 : Perm (Fin (n + 1))) τ
  rwa [one_mul, restPerm_one, one_mul] at h

/-! ## Iterating the standard embedding

The tower's compatibility field extends a permutation of `Fin m` all
the way to `Fin n` in one step, along `Fin.castLEEmb`.  The action
recurses one slot at a time, so the two descriptions have to be
identified: extending along `Fin.castLEEmb` is iterated `extPerm`.
-/

/-- **Composing embeddings composes the extensions**: extending a
permutation along `ι` and then along `κ` extends it along the
composite. -/
theorem viaEmbedding_viaEmbedding {α β γ : Type*} (σ : Perm α)
    (ι : α ↪ β) (κ : β ↪ γ) :
    (σ.viaEmbedding ι).viaEmbedding κ = σ.viaEmbedding (ι.trans κ) := by
  ext x
  by_cases hx : x ∈ Set.range κ
  · obtain ⟨b, rfl⟩ := hx
    rw [Perm.viaEmbedding_apply]
    by_cases hb : b ∈ Set.range ι
    · obtain ⟨a, rfl⟩ := hb
      rw [Perm.viaEmbedding_apply]
      exact (Perm.viaEmbedding_apply σ (ι.trans κ) a).symm
    · have hbκ : κ b ∉ Set.range (ι.trans κ) := by
        rintro ⟨a, ha⟩
        exact hb ⟨a, κ.injective ha⟩
      rw [Perm.viaEmbedding_apply_of_notMem _ _ _ hb,
        Perm.viaEmbedding_apply_of_notMem _ _ _ hbκ]
  · have hxκ : x ∉ Set.range (ι.trans κ) := fun ⟨a, ha⟩ => hx ⟨ι a, ha⟩
    rw [Perm.viaEmbedding_apply_of_notMem _ _ _ hx,
      Perm.viaEmbedding_apply_of_notMem _ _ _ hxκ]

/-- **One step of the standard embedding**: extending a permutation
of `Fin m` to `Fin (m + k + 1)` is extending it to `Fin (m + k)` and
then fixing the new top slot. -/
theorem viaEmbedding_castLEEmb_succ {m k : ℕ} (σ : Perm (Fin m)) :
    σ.viaEmbedding (Fin.castLEEmb (Nat.le_add_right m (k + 1))) =
      extPerm (σ.viaEmbedding (Fin.castLEEmb (Nat.le_add_right m k))) := by
  have h : (Fin.castLEEmb (Nat.le_add_right m k)).trans Fin.castSuccEmb =
      Fin.castLEEmb (Nat.le_add_right m (k + 1)) :=
    Function.Embedding.ext fun i => Fin.ext rfl
  rw [extPerm, viaEmbedding_viaEmbedding, h]

/-! ## Reassembling a permutation from its split

A target for the top slot together with a permutation of the rest
determines a permutation.  The cycle carrying the top slot to `p`
is the case of trivial induced permutation, and the action's
functoriality is proved along the factorisation into such a cycle
after a top-fixing permutation.
-/

/-- The permutation sending the top slot to `p` and inducing `τ` on
the rest. -/
noncomputable def ofSplit (p : Fin (n + 1)) (τ : Perm (Fin n)) :
    Perm (Fin (n + 1)) :=
  (finSuccEquiv' (Fin.last n)).trans
    ((Equiv.optionCongr τ).trans (finSuccEquiv' p).symm)

/-- The reassembled permutation sends the top slot to `p`. -/
@[simp]
theorem ofSplit_last (p : Fin (n + 1)) (τ : Perm (Fin n)) :
    ofSplit p τ (Fin.last n) = p := by
  change (finSuccEquiv' p).symm ((Equiv.optionCongr τ)
    ((finSuccEquiv' (Fin.last n)) (Fin.last n))) = p
  rw [finSuccEquiv'_at]
  simp

/-- On a lower slot the reassembled permutation acts by `τ`,
reinserted above `p`. -/
@[simp]
theorem ofSplit_castSucc (p : Fin (n + 1)) (τ : Perm (Fin n)) (j : Fin n) :
    ofSplit p τ j.castSucc = p.succAbove (τ j) := by
  change (finSuccEquiv' p).symm ((Equiv.optionCongr τ)
    ((finSuccEquiv' (Fin.last n)) j.castSucc)) = p.succAbove (τ j)
  rw [finSuccEquiv'_last_apply_castSucc]
  simp

/-- The reassembled permutation has `p` as its top image. -/
@[simp]
theorem topImage_ofSplit (p : Fin (n + 1)) (τ : Perm (Fin n)) :
    topImage (ofSplit p τ) = p := ofSplit_last p τ

/-- The reassembled permutation induces `τ` on the lower slots. -/
@[simp]
theorem restPerm_ofSplit (p : Fin (n + 1)) (τ : Perm (Fin n)) :
    restPerm (ofSplit p τ) = τ := by
  ext j
  have h := succAbove_restPerm (ofSplit p τ) j
  rw [topImage_ofSplit, ofSplit_castSucc] at h
  exact congrArg Fin.val (Fin.succAbove_right_injective h)

/-- The cycle carrying the top slot down to `p`, shifting the slots
at or above `p` up by one. -/
noncomputable def topCycle (p : Fin (n + 1)) : Perm (Fin (n + 1)) :=
  ofSplit p 1

/-- The cycle carries the top slot to `p`. -/
@[simp]
theorem topImage_topCycle (p : Fin (n + 1)) :
    topImage (topCycle p) = p := topImage_ofSplit p 1

/-- The cycle induces the identity on the lower slots. -/
@[simp]
theorem restPerm_topCycle (p : Fin (n + 1)) :
    restPerm (topCycle p) = 1 := restPerm_ofSplit p 1

/-- **The cycle carrying the top slot to the bottom** is Mathlib's
rotation: both send each lower slot one place up and the top slot
to `0`. -/
theorem topCycle_zero :
    topCycle (0 : Fin (n + 1)) = finRotate (n + 1) := by
  refine Equiv.ext fun i => ?_
  induction i using Fin.lastCases with
  | last =>
    rw [show topCycle (0 : Fin (n + 1)) (Fin.last n) = 0 from
      ofSplit_last 0 1, finRotate_last]
  | cast j =>
    have h : topCycle (0 : Fin (n + 1)) j.castSucc = j.succ := by
      change ofSplit (0 : Fin (n + 1)) 1 j.castSucc = j.succ
      simp
    refine Fin.ext ?_
    rw [h, coe_finRotate_of_ne_last (Fin.castSucc_lt_last j).ne]
    rfl

/-! ## The adjacent transpositions

`Equiv.Perm.mclosure_swap_castSucc_succ` generates `Perm (Fin (n+1))`
as a submonoid from the transpositions of adjacent slots.  Each of
them is either top-fixing — and so an `extPerm` of an adjacent
transposition one arity down — or the transposition of the top two
slots, which is the cycle at the second-highest slot.
-/

/-- Extending a transposition of the lower slots. -/
theorem extPerm_swap (a b : Fin n) :
    extPerm (Equiv.swap a b) =
      Equiv.swap a.castSucc b.castSucc :=
  Equiv.ext fun x => by
    refine Fin.lastCases ?_ (fun j => ?_) x
    · rw [extPerm_last, Equiv.swap_apply_of_ne_of_ne
        (Fin.castSucc_lt_last a).ne' (Fin.castSucc_lt_last b).ne']
    · rw [extPerm_castSucc]
      rcases eq_or_ne j a with rfl | hja
      · rw [Equiv.swap_apply_left, Equiv.swap_apply_left]
      · rcases eq_or_ne j b with rfl | hjb
        · rw [Equiv.swap_apply_right, Equiv.swap_apply_right]
        · rw [Equiv.swap_apply_of_ne_of_ne hja hjb,
            Equiv.swap_apply_of_ne_of_ne
              (fun h => hja (Fin.castSucc_injective _ h))
              (fun h => hjb (Fin.castSucc_injective _ h))]

/-- An adjacent transposition below the top is top-fixing. -/
theorem swap_castSucc_succ_castSucc (i : Fin n) :
    Equiv.swap (Fin.castSucc (Fin.castSucc i)) (Fin.castSucc i).succ =
      extPerm (Equiv.swap i.castSucc i.succ) := by
  rw [extPerm_swap, Fin.succ_castSucc]

/-- The transposition of the top two slots is the cycle at the
second-highest slot. -/
theorem topCycle_castSucc_last :
    topCycle (Fin.castSucc (Fin.last n)) =
      Equiv.swap (Fin.castSucc (Fin.last n)) (Fin.last (n + 1)) :=
  Equiv.ext fun x => by
    refine Fin.lastCases ?_ (fun j => ?_) x
    · rw [topCycle, ofSplit_last, Equiv.swap_apply_right]
    · rw [topCycle, ofSplit_castSucc, Equiv.Perm.one_apply]
      rcases eq_or_ne j (Fin.last n) with rfl | hj
      · rw [Fin.succAbove_of_le_castSucc _ _ le_rfl,
          Equiv.swap_apply_left, Fin.succ_last]
      · have hlt : j.castSucc < Fin.castSucc (Fin.last n) :=
          Fin.castSucc_lt_castSucc_iff.2
            (lt_of_le_of_ne (Fin.le_last j) hj)
        rw [Fin.succAbove_of_castSucc_lt _ _ hlt,
          Equiv.swap_apply_of_ne_of_ne hlt.ne
            (Fin.castSucc_lt_last _).ne]

/-! ## Precomposing with the top transposition

The transposition of the top two slots exchanges the two source slots
the action's recursion peels off first, so it exchanges the two
targets they consume.  Everything below them is untouched.
-/

/-- The transposition of the top two slots. -/
noncomputable def topSwap : Perm (Fin (n + 2)) :=
  Equiv.swap (Fin.castSucc (Fin.last n)) (Fin.last (n + 1))

/-- The top transposition is the cycle at the second-highest
slot. -/
theorem topSwap_eq_topCycle :
    (topSwap : Perm (Fin (n + 2))) = topCycle (Fin.castSucc (Fin.last n)) :=
  topCycle_castSucc_last.symm

/-- The top transposition carries the top slot one place down. -/
@[simp]
theorem topSwap_last : (topSwap : Perm (Fin (n + 2))) (Fin.last (n + 1)) =
    Fin.castSucc (Fin.last n) := Equiv.swap_apply_right _ _

/-- The top transposition carries the slot below the top one
place up. -/
@[simp]
theorem topSwap_castSucc_last :
    (topSwap : Perm (Fin (n + 2))) (Fin.castSucc (Fin.last n)) =
      Fin.last (n + 1) := Equiv.swap_apply_left _ _

/-- The top transposition fixes every slot below the top two. -/
@[simp]
theorem topSwap_castSucc_castSucc (j : Fin n) :
    (topSwap : Perm (Fin (n + 2))) (Fin.castSucc (Fin.castSucc j)) =
      Fin.castSucc (Fin.castSucc j) := by
  refine Equiv.swap_apply_of_ne_of_ne (fun h => ?_) (fun h => ?_)
  · exact absurd (Fin.castSucc_injective _ h) (Fin.castSucc_lt_last j).ne
  · exact absurd h (Fin.castSucc_lt_last _).ne

/-- **The top slot's new image**: precomposing with the top
transposition sends the top slot where the slot below it went. -/
theorem topImage_mul_topSwap (σ : Perm (Fin (n + 2))) :
    topImage (σ * topSwap) =
      (topImage σ).succAbove (topImage (restPerm σ)) := by
  change σ (topSwap (Fin.last (n + 1))) = _
  rw [topSwap_last, ← succAbove_restPerm σ (Fin.last n)]
  rfl

/-- **The two consumed targets are exchanged**: reinserting the new
second target recovers the old first one. -/
theorem succAbove_topImage_restPerm_mul_topSwap (σ : Perm (Fin (n + 2))) :
    (topImage (σ * topSwap)).succAbove (topImage (restPerm (σ * topSwap)))
      = topImage σ := by
  have h := succAbove_restPerm (σ * topSwap) (Fin.last n)
  rw [show restPerm (σ * topSwap) (Fin.last n)
      = topImage (restPerm (σ * topSwap)) from rfl] at h
  rw [h]
  change σ (topSwap (Fin.castSucc (Fin.last n))) = σ (Fin.last (n + 1))
  rw [topSwap_castSucc_last]

/-- **The new second target** is the old first one, compressed.  This
is the `Fin` simplicial identity: reinserting `m.predAbove p` at
`p.succAbove m` recovers `p`. -/
theorem topImage_restPerm_mul_topSwap (σ : Perm (Fin (n + 2))) :
    topImage (restPerm (σ * topSwap)) =
      (topImage (restPerm σ)).predAbove (topImage σ) := by
  have h1 := succAbove_topImage_restPerm_mul_topSwap σ
  have h2 := Fin.succAbove_succAbove_predAbove (topImage σ)
    (topImage (restPerm σ))
  rw [topImage_mul_topSwap σ] at h1
  exact Fin.succAbove_right_injective (h1.trans h2.symm)

/-- **Nothing below the top two slots moves.**  Precomposing with the
top transposition exchanges the two targets the top two source slots
consume, but the order-preserving embedding of the remaining slots
into their complement is the same either way, so the twice-restricted
permutation is unchanged. -/
theorem restPerm_restPerm_mul_topSwap (σ : Perm (Fin (n + 2))) :
    restPerm (restPerm (σ * topSwap)) = restPerm (restPerm σ) := by
  ext x
  have key : ∀ ρ : Perm (Fin (n + 2)),
      (topImage ρ).succAbove ((topImage (restPerm ρ)).succAbove
        (restPerm (restPerm ρ) x)) = ρ (Fin.castSucc (Fin.castSucc x)) := by
    intro ρ
    rw [succAbove_restPerm (restPerm ρ) x, succAbove_restPerm ρ x.castSucc]
  have hL := key (σ * topSwap)
  have hR := key σ
  rw [topImage_mul_topSwap σ, topImage_restPerm_mul_topSwap σ,
    Fin.succAbove_succAbove_succAbove_predAbove] at hL
  have hswap : (σ * topSwap : Perm (Fin (n + 2)))
      (Fin.castSucc (Fin.castSucc x)) =
      σ (Fin.castSucc (Fin.castSucc x)) := by
    rw [Equiv.Perm.mul_apply, topSwap_castSucc_castSucc]
  rw [hswap, ← hR] at hL
  exact congrArg Fin.val
    (Fin.succAbove_right_injective (Fin.succAbove_right_injective hL))

/-! ### The two consumed targets, by value

The bubbling distances the action's recursion uses are `n` minus
these values, so the braid identity is fed them in numeric form.  The
two cases are whether the top slot's image lies above or below the
image of the slot beneath it.
-/

/-- Above the threshold, the top slot's new image is the old inner
one. -/
theorem topImage_mul_topSwap_val_of_lt (σ : Perm (Fin (n + 2)))
    (h : (topImage (restPerm σ)).castSucc < topImage σ) :
    ((topImage (σ * topSwap) : Fin (n + 2)) : ℕ)
      = ((topImage (restPerm σ) : Fin (n + 1)) : ℕ) := by
  rw [topImage_mul_topSwap, Fin.succAbove_of_castSucc_lt _ _ h]
  rfl

/-- Above the threshold, the new inner image is the old top one,
lowered by one. -/
theorem topImage_restPerm_mul_topSwap_val_of_lt (σ : Perm (Fin (n + 2)))
    (h : (topImage (restPerm σ)).castSucc < topImage σ) :
    ((topImage (restPerm (σ * topSwap)) : Fin (n + 1)) : ℕ)
      = ((topImage σ : Fin (n + 2)) : ℕ) - 1 := by
  rw [topImage_restPerm_mul_topSwap, Fin.predAbove_of_castSucc_lt _ _ h]
  rfl

/-- Below the threshold, the top slot's new image is the old inner
one, raised by one. -/
theorem topImage_mul_topSwap_val_of_le (σ : Perm (Fin (n + 2)))
    (h : topImage σ ≤ (topImage (restPerm σ)).castSucc) :
    ((topImage (σ * topSwap) : Fin (n + 2)) : ℕ)
      = ((topImage (restPerm σ) : Fin (n + 1)) : ℕ) + 1 := by
  rw [topImage_mul_topSwap, Fin.succAbove_of_le_castSucc _ _ h]
  rfl

/-- Below the threshold, the new inner image is the old top one. -/
theorem topImage_restPerm_mul_topSwap_val_of_le (σ : Perm (Fin (n + 2)))
    (h : topImage σ ≤ (topImage (restPerm σ)).castSucc) :
    ((topImage (restPerm (σ * topSwap)) : Fin (n + 1)) : ℕ)
      = ((topImage σ : Fin (n + 2)) : ℕ) := by
  rw [topImage_restPerm_mul_topSwap, Fin.predAbove_of_le_castSucc _ _ h]
  rfl

end RS
