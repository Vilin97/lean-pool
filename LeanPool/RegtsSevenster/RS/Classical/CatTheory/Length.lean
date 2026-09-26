/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

module

public import LeanPool.RegtsSevenster.RS.Definitions

/-!
# Bounded length for objects of an abelian category

A lightweight, bound-shaped notion of composition length
(`LengthLE`, defined with the subquotient relation
`IsSubquotientOf` in `RS/Definitions.lean`): an object `Y`
satisfies `LengthLE Y k` when its subobject order admits no
strictly increasing chain of `k + 2` terms — exactly the predicate
needed to state growth hypotheses, without committing to a
composition-series formalism.

The elementary API, proved here: the bound is monotone, the predicate transfers
along isomorphisms of the ambient object, zero objects have length
at most `0`, simple objects have length at most `1`, and the bound
is subadditive over binary biproducts.
-/

@[expose] public section

namespace RS

open CategoryTheory CategoryTheory.Limits

universe v u

variable {C : Type u}

/-- The length bound is monotone: a bound at `k` is a bound at any
`k' ≥ k`. -/
theorem LengthLE.mono [Category.{v} C]
    {Y : C} {k k' : ℕ} (h : LengthLE Y k)
    (hk : k ≤ k') : LengthLE Y k' := by
  intro f hf
  exact h (f ∘ Fin.castLE (by omega))
    (hf.comp (Fin.strictMono_castLE (by omega)))

/-- The length bound transfers along an isomorphism of the ambient
object, via the induced order isomorphism of subobject lattices. -/
theorem LengthLE.of_iso [Category.{v} C]
    {Y Z : C} (e : Y ≅ Z) {k : ℕ}
    (h : LengthLE Y k) : LengthLE Z k := by
  intro f hf
  exact h (fun i => (Subobject.mapIsoToOrderIso e).symm (f i))
    ((Subobject.mapIsoToOrderIso e).symm.strictMono.comp hf)

/-- A zero object has length at most `0`: its subobject order is a
singleton, so it carries no strictly increasing pair. -/
theorem lengthLE_of_isZero [Category.{v} C]
    {Y : C} (hY : IsZero Y) : LengthLE Y 0 := by
  intro f hf
  have := Subobject.subsingleton_of_isZero hY
  exact (hf (show (0 : Fin 2) < 1 by decide)).ne
    (Subsingleton.elim (f 0) (f 1))

/-- A simple object has length at most `1`: its subobjects are only
`⊥` and `⊤`, so no chain has three distinct terms. -/
theorem lengthLE_of_simple [Category.{v} C] [Abelian C]
    {Y : C} [Simple Y] : LengthLE Y 1 := by
  intro f hf
  have h01 : f 0 < f 1 := hf (show (0 : Fin 3) < 1 by decide)
  have h12 : f 1 < f 2 := hf (show (1 : Fin 3) < 2 by decide)
  rcases eq_bot_or_eq_top (f 1) with h | h
  · exact not_lt_bot (h ▸ h01)
  · exact not_top_lt (h ▸ h12)

/-! ### Splitting strict chains in a product order -/

section Chains

/-- Appending a strictly larger element to a strict chain. -/
private lemma strictMono_snoc {A : Type*} [PartialOrder A]
    {p : ℕ} {g : Fin (p + 1) → A} {y : A}
    (hg : StrictMono g) (hy : g (Fin.last p) < y) :
    StrictMono (Fin.snoc g y : Fin (p + 2) → A) := by
  rw [Fin.strictMono_iff_lt_succ]
  intro i
  induction i using Fin.lastCases with
  | last => simpa using hy
  | cast j =>
    rw [Fin.succ_castSucc, Fin.snoc_castSucc, Fin.snoc_castSucc]
    exact hg Fin.castSucc_lt_succ

/-- A strict chain in a product of partial orders splits into strict
chains in the two factors whose numbers of steps sum to at least the
number of steps of the original chain. -/
private lemma pair_chains
    {A : Type*} {B : Type*} [PartialOrder A] [PartialOrder B]
    {n : ℕ} :
    ∀ w : Fin (n + 1) → A × B, StrictMono w →
      ∃ p q, n ≤ p + q ∧
        (∃ g : Fin (p + 1) → A, StrictMono g ∧
          g (Fin.last p) = (w (Fin.last n)).1) ∧
        (∃ g : Fin (q + 1) → B, StrictMono g ∧
          g (Fin.last q) = (w (Fin.last n)).2) := by
  induction n with
  | zero =>
    intro w _
    have : Subsingleton (Fin (0 + 1)) :=
      ⟨fun a b => Fin.ext (by have := a.isLt; have := b.isLt; omega)⟩
    exact ⟨0, 0, Nat.zero_le _,
      ⟨fun _ => (w (Fin.last 0)).1, Subsingleton.strictMono _, rfl⟩,
      ⟨fun _ => (w (Fin.last 0)).2, Subsingleton.strictMono _, rfl⟩⟩
  | succ n ih =>
    intro w hw
    obtain ⟨p, q, hpq, ⟨g1, hg1, he1⟩, ⟨g2, hg2, he2⟩⟩ :=
      ih (w ∘ Fin.castSucc) (hw.comp Fin.strictMono_castSucc)
    simp only [Function.comp_apply] at he1 he2
    have hlt : w ((Fin.last n).castSucc) < w (Fin.last (n + 1)) :=
      hw (Fin.castSucc_lt_last _)
    rcases Prod.lt_iff.mp hlt with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rcases h2.eq_or_lt with h2 | h2
      · exact ⟨p + 1, q, by omega,
          ⟨Fin.snoc g1 (w (Fin.last (n + 1))).1,
            strictMono_snoc hg1 (he1.trans_lt h1), by simp⟩,
          ⟨g2, hg2, he2.trans h2⟩⟩
      · exact ⟨p + 1, q + 1, by omega,
          ⟨Fin.snoc g1 (w (Fin.last (n + 1))).1,
            strictMono_snoc hg1 (he1.trans_lt h1), by simp⟩,
          ⟨Fin.snoc g2 (w (Fin.last (n + 1))).2,
            strictMono_snoc hg2 (he2.trans_lt h2), by simp⟩⟩
    · rcases h1.eq_or_lt with h1 | h1
      · exact ⟨p, q + 1, by omega,
          ⟨g1, hg1, he1.trans h1⟩,
          ⟨Fin.snoc g2 (w (Fin.last (n + 1))).2,
            strictMono_snoc hg2 (he2.trans_lt h2), by simp⟩⟩
      · exact ⟨p + 1, q + 1, by omega,
          ⟨Fin.snoc g1 (w (Fin.last (n + 1))).1,
            strictMono_snoc hg1 (he1.trans_lt h1), by simp⟩,
          ⟨Fin.snoc g2 (w (Fin.last (n + 1))).2,
            strictMono_snoc hg2 (he2.trans_lt h2), by simp⟩⟩

end Chains

/-! ### Subadditivity over a binary biproduct -/

/-- A morphism into a binary biproduct that vanishes on the second
projection factors through the first inclusion. -/
private lemma comp_fst_inl [Category.{v} C] [Abelian C]
    {Y Z T : C} (g : T ⟶ Y ⊞ Z)
    (hg : g ≫ biprod.snd = 0) :
    (g ≫ biprod.fst) ≫ biprod.inl = g := by
  conv_rhs => rw [← Category.comp_id g, ← biprod.total]
  rw [Preadditive.comp_add, ← Category.assoc, ← Category.assoc, hg,
    zero_comp, add_zero]

/-- The part of a subobject of `Y ⊞ Z` lying over `Y`: the pullback
of the subobject along the first inclusion. -/
private noncomputable def kerPart [Category.{v} C] [Abelian C]
    {Y Z : C} (P : Subobject (Y ⊞ Z)) :
    Subobject Y :=
  Subobject.mk (pullback.fst (biprod.inl : Y ⟶ Y ⊞ Z) P.arrow)

/-- The image of a subobject of `Y ⊞ Z` under the second
projection. -/
private noncomputable def imgPart [Category.{v} C] [Abelian C]
    {Y Z : C} (P : Subobject (Y ⊞ Z)) :
    Subobject Z :=
  Subobject.mk (image.ι (P.arrow ≫ biprod.snd))

/-- The `Y`-part is monotone in the subobject. -/
private lemma kerPart_mono [Category.{v} C] [Abelian C]
    {Y Z : C} {P Q : Subobject (Y ⊞ Z)}
    (h : P ≤ Q) : kerPart P ≤ kerPart Q := by
  unfold kerPart
  refine Subobject.mk_le_mk_of_comm
    (pullback.lift (pullback.fst biprod.inl P.arrow)
      (pullback.snd biprod.inl P.arrow ≫ Subobject.ofLE P Q h) ?_)
    (pullback.lift_fst _ _ _)
  rw [Category.assoc, Subobject.ofLE_arrow, pullback.condition]

/-- The `Z`-image is monotone in the subobject. -/
private lemma imgPart_mono [Category.{v} C] [Abelian C]
    {Y Z : C} {P Q : Subobject (Y ⊞ Z)}
    (h : P ≤ Q) : imgPart P ≤ imgPart Q := by
  unfold imgPart
  refine Subobject.mk_le_mk_of_comm
    (image.lift
      { I := image (Q.arrow ≫ biprod.snd)
        m := image.ι (Q.arrow ≫ biprod.snd)
        e := Subobject.ofLE P Q h ≫
          factorThruImage (Q.arrow ≫ biprod.snd)
        fac := ?_ }) (image.lift_fac _)
  rw [Category.assoc, image.fac, ← Category.assoc, Subobject.ofLE_arrow]

/-- Nested subobjects of a binary biproduct with the same part over
`Y` and the same image in `Z` coincide. -/
private lemma eq_of_parts [Category.{v} C] [Abelian C]
    {Y Z : C} {P Q : Subobject (Y ⊞ Z)}
    (hPQ : P ≤ Q) (hker : kerPart P = kerPart Q)
    (himg : imgPart P = imgPart Q) : P = Q := by
  unfold kerPart at hker
  unfold imgPart at himg
  have ht : Subobject.ofLE P Q hPQ ≫ Q.arrow = P.arrow :=
    Subobject.ofLE_arrow hPQ
  -- The kernel of `biprod.snd` restricted to `Q` factors through `P`.
  have hy : (kernel.ι (Q.arrow ≫ biprod.snd) ≫ Q.arrow ≫ biprod.fst)
      ≫ biprod.inl = kernel.ι (Q.arrow ≫ biprod.snd) ≫ Q.arrow := by
    rw [← Category.assoc]
    exact comp_fst_inl _
      (by rw [Category.assoc]; exact kernel.condition _)
  have hfac : ∃ χ : (kernel (Q.arrow ≫ biprod.snd) : C) ⟶ (P : C),
      χ ≫ P.arrow = kernel.ι (Q.arrow ≫ biprod.snd) ≫ Q.arrow := by
    refine ⟨pullback.lift
        (kernel.ι (Q.arrow ≫ biprod.snd) ≫ Q.arrow ≫ biprod.fst)
        (kernel.ι (Q.arrow ≫ biprod.snd)) hy ≫
      Subobject.ofMkLEMk _ _ hker.ge ≫ pullback.snd biprod.inl P.arrow,
      ?_⟩
    have hv : Subobject.ofMkLEMk _ _ hker.ge ≫
        pullback.fst biprod.inl P.arrow =
        pullback.fst biprod.inl Q.arrow :=
      Subobject.ofMkLEMk_comp hker.ge
    simp only [Category.assoc]
    rw [← pullback.condition,
      ← Category.assoc (Subobject.ofMkLEMk _ _ hker.ge), hv,
      ← Category.assoc, pullback.lift_fst]
    exact hy
  obtain ⟨χ, hχ⟩ := hfac
  have hχt : χ ≫ Subobject.ofLE P Q hPQ =
      kernel.ι (Q.arrow ≫ biprod.snd) := by
    rw [← cancel_mono Q.arrow, Category.assoc, ht, hχ]
  -- The cokernel of the inclusion vanishes on the kernel of the
  -- restriction of `biprod.snd` to `Q`.
  have hkc : kernel.ι (Q.arrow ≫ biprod.snd) ≫
      cokernel.π (Subobject.ofLE P Q hPQ) = 0 := by
    rw [← hχt, Category.assoc, cokernel.condition, comp_zero]
  have h3 : kernel.ι (factorThruImage (Q.arrow ≫ biprod.snd)) ≫
      (Q.arrow ≫ biprod.snd) = 0 := by
    calc kernel.ι (factorThruImage (Q.arrow ≫ biprod.snd)) ≫
          (Q.arrow ≫ biprod.snd)
        = kernel.ι (factorThruImage (Q.arrow ≫ biprod.snd)) ≫
          (factorThruImage (Q.arrow ≫ biprod.snd) ≫
            image.ι (Q.arrow ≫ biprod.snd)) := by rw [image.fac]
      _ = (kernel.ι (factorThruImage (Q.arrow ≫ biprod.snd)) ≫
          factorThruImage (Q.arrow ≫ biprod.snd)) ≫
            image.ι (Q.arrow ≫ biprod.snd) := by
          rw [Category.assoc]
      _ = 0 := by rw [kernel.condition, zero_comp]
  have hk2 : kernel.ι (factorThruImage (Q.arrow ≫ biprod.snd)) ≫
      cokernel.π (Subobject.ofLE P Q hPQ) = 0 := by
    rw [← kernel.lift_ι (Q.arrow ≫ biprod.snd)
        (kernel.ι (factorThruImage (Q.arrow ≫ biprod.snd))) h3,
      Category.assoc, hkc, comp_zero]
  -- Compare the two images and kill the cokernel.
  have hρ : Subobject.ofMkLEMk _ _ himg.le ≫
      image.ι (Q.arrow ≫ biprod.snd) =
      image.ι (P.arrow ≫ biprod.snd) :=
    Subobject.ofMkLEMk_comp himg.le
  have hρ' : Subobject.ofMkLEMk _ _ himg.ge ≫
      image.ι (P.arrow ≫ biprod.snd) =
      image.ι (Q.arrow ≫ biprod.snd) :=
    Subobject.ofMkLEMk_comp himg.ge
  have hsq : factorThruImage (P.arrow ≫ biprod.snd) ≫
      Subobject.ofMkLEMk _ _ himg.le =
      Subobject.ofLE P Q hPQ ≫
        factorThruImage (Q.arrow ≫ biprod.snd) := by
    rw [← cancel_mono (image.ι (Q.arrow ≫ biprod.snd)),
      Category.assoc, hρ, image.fac, Category.assoc, image.fac,
      ← Category.assoc, ht]
  have hd : factorThruImage (Q.arrow ≫ biprod.snd) ≫
      Abelian.epiDesc (factorThruImage (Q.arrow ≫ biprod.snd))
        (cokernel.π (Subobject.ofLE P Q hPQ)) hk2 =
      cokernel.π (Subobject.ofLE P Q hPQ) :=
    Abelian.comp_epiDesc _ _ _
  have h5 : Subobject.ofMkLEMk _ _ himg.le ≫
      Abelian.epiDesc (factorThruImage (Q.arrow ≫ biprod.snd))
        (cokernel.π (Subobject.ofLE P Q hPQ)) hk2 = 0 := by
    rw [← cancel_epi (factorThruImage (P.arrow ≫ biprod.snd)),
      ← Category.assoc, hsq, Category.assoc, hd, cokernel.condition,
      comp_zero]
  have h6 : Subobject.ofMkLEMk _ _ himg.ge ≫
      Subobject.ofMkLEMk _ _ himg.le = 𝟙 _ := by
    rw [← cancel_mono (image.ι (Q.arrow ≫ biprod.snd)),
      Category.assoc, hρ, hρ', Category.id_comp]
  have h7 : Abelian.epiDesc (factorThruImage (Q.arrow ≫ biprod.snd))
      (cokernel.π (Subobject.ofLE P Q hPQ)) hk2 = 0 := by
    rw [← Category.id_comp (Abelian.epiDesc
        (factorThruImage (Q.arrow ≫ biprod.snd))
        (cokernel.π (Subobject.ofLE P Q hPQ)) hk2),
      ← h6, Category.assoc, h5, comp_zero]
  have hcz : cokernel.π (Subobject.ofLE P Q hPQ) = 0 := by
    rw [← hd, h7, comp_zero]
  have : Epi (Subobject.ofLE P Q hPQ) :=
    Preadditive.epi_of_cokernel_zero hcz
  have : IsIso (Subobject.ofLE P Q hPQ) :=
    isIso_of_mono_of_epi _
  exact le_antisymm hPQ (Subobject.le_of_comm
    (inv (Subobject.ofLE P Q hPQ)) (by rw [IsIso.inv_comp_eq, ht]))

/-- Subadditivity of the length bound over a binary biproduct: a
strict chain of subobjects of `Y ⊞ Z` is traced by its parts over
`Y` and its images in `Z`, and each strict step moves at least one
of the two. -/
theorem LengthLE.biprod [Category.{v} C] [Abelian C]
    {Y Z : C} {j k : ℕ} (hY : LengthLE Y j)
    (hZ : LengthLE Z k) : LengthLE (Y ⊞ Z) (j + k) := by
  intro f hf
  have hwmono : StrictMono (fun i : Fin (j + k + 1 + 1) =>
      (kerPart (f i), imgPart (f i))) := by
    intro a b hab
    refine lt_of_le_of_ne
      ⟨kerPart_mono (hf hab).le, imgPart_mono (hf hab).le⟩
      (fun hEq => ?_)
    exact (hf hab).ne (eq_of_parts (hf hab).le
      (congrArg Prod.fst hEq) (congrArg Prod.snd hEq))
  obtain ⟨p, q, hpq, ⟨g1, hg1, -⟩, ⟨g2, hg2, -⟩⟩ :=
    pair_chains _ hwmono
  have hp : p ≤ j := by
    by_contra hp
    exact hY (g1 ∘ Fin.castLE (by omega))
      (hg1.comp (Fin.strictMono_castLE (by omega)))
  have hq : q ≤ k := by
    by_contra hq
    exact hZ (g2 ∘ Fin.castLE (by omega))
      (hg2.comp (Fin.strictMono_castLE (by omega)))
  omega

end RS
