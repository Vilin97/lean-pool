/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import LeanPool.InfinitaryLogic.Methods.LocalEMEquivariance
import Mathlib.ModelTheory.Encoding

/-!
# Skeleton compression: finite-support term codes

The generic compression layer of the countably-many-types project (issue #11 unit 3a),
independent of the local EM quotient: a closed `Λ[[J]]`-term supported in a finite `S : Finset J`
is coded by replacing each skeleton constant with its RANK in the increasing enumeration of `S`
(`locJCompress`), forgetting the actual `J`-values while retaining the term shape and the
equality/order pattern of the support. The inverse is expansion along any increasing embedding
(`locJExpand`). The round trips:

* `locJExpand_compress` — expanding along `S`'s own enumeration recovers the term;
* `locJCompress_expand` — compressing an expansion recovers the code;
* `locJRename_expand` — if `e ∘ s = t` pointwise then renaming along `e` carries the
  `s`-expansion to the `t`-expansion (the lemma the orbit theorem consumes);
* `locJSupport_locJExpand` — the support of an expansion is the image of the code's support.

The tuple-code type `LocalEMTupleCode Λ n` (`Σ k, Fin n → Λ[[Fin k]].Term Empty`) is COUNTABLE
for a countable base language (`countable_localEMTupleCode`) — the quotient-tuple coding and
the orbit theorem are unit 3b (`LocalEMTupleOrbit.lean`).
-/

namespace FirstOrder

namespace Language

variable (Λ : Language.{0, 0}) (J : Type) [LinearOrder J]

/-- **Skeleton compression**: replace each skeleton constant of an `S`-supported closed term by
its rank in the increasing enumeration of `S`. -/
def locJCompress (S : Finset J) :
    (t : Λ[[J]].Term Empty) → locJSupport Λ J t ⊆ S → Λ[[Fin S.card]].Term Empty
  | .var e, _ => e.elim
  | @Term.func _ _ _ (Sum.inl f') ts, h =>
      Term.func (Sum.inl f') fun i =>
        locJCompress S (ts i) ((locJSupport_subterm Λ J (Sum.inl f') ts i).trans h)
  | @Term.func _ _ 0 (Sum.inr j) _, h =>
      Term.func (show Λ[[Fin S.card]].Functions 0 from Sum.inr (⟨deepRank J S j,
        deepRank_lt_card J (h (Finset.mem_union_right _ (Finset.mem_singleton_self j)))⟩ :
          Fin S.card)) Fin.elim0
  | @Term.func _ _ (_ + 1) (Sum.inr c) _, _ => c.elim

/-- **Skeleton expansion** along an increasing embedding: interpret the `Fin k` constants by the
embedded skeleton points. -/
def locJExpand {k : ℕ} (s : Fin k ↪o J) {α : Type} (u : Λ[[Fin k]].Term α) :
    Λ[[J]].Term α :=
  (Λ.lhomWithConstantsMap (s : Fin k → J)).onTerm u

private theorem locJExpand_func_inl {k : ℕ} (s : Fin k ↪o J) {α : Type} {l : ℕ}
    (f' : Λ.Functions l) (ts : Fin l → Λ[[Fin k]].Term α) :
    locJExpand Λ J s (Term.func (Sum.inl f' : Λ[[Fin k]].Functions l) ts)
      = Term.func (Sum.inl f' : Λ[[J]].Functions l) (fun i => locJExpand Λ J s (ts i)) :=
  rfl

private theorem locJExpand_func_inr {k : ℕ} (s : Fin k ↪o J) {α : Type} (i₀ : Fin k)
    (ts : Fin 0 → Λ[[Fin k]].Term α) :
    locJExpand Λ J s (Term.func (Sum.inr i₀ : Λ[[Fin k]].Functions 0) ts)
      = Term.func (Sum.inr (s i₀) : Λ[[J]].Functions 0) (fun i => locJExpand Λ J s (ts i)) :=
  rfl



/-- The support of an expansion is the image of the code's support. -/
private theorem locJSupport_locJExpand {k : ℕ} (s : Fin k ↪o J) {α : Type}
    (u : Λ[[Fin k]].Term α) :
    locJSupport Λ J (locJExpand Λ J s u) = (locJSupport Λ (Fin k) u).image s := by
  induction u with
  | var x => simp [locJExpand, LHom.onTerm, locJSupport]
  | @func l f ts ih =>
    show locJSupport Λ J (Term.func ((Λ.lhomWithConstantsMap (s : Fin k → J)).onFunction f)
      fun i => locJExpand Λ J s (ts i)) = _
    rw [locJSupport, locJSupport, Finset.image_union]
    congr 1
    · ext x
      simp only [Finset.mem_biUnion, Finset.mem_image, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨i, hx⟩
        rw [ih i] at hx
        obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
        exact ⟨y, ⟨i, hy⟩, rfl⟩
      · rintro ⟨y, ⟨i, hy⟩, rfl⟩
        exact ⟨i, by rw [ih i]; exact Finset.mem_image_of_mem _ hy⟩
    · rcases l with _ | l
      · rcases f with f' | j
        · rfl
        · simp only [locJConstOf]
          rfl
      · rcases f with f' | c
        · rfl
        · exact c.elim

/-- **Round trip 1**: expanding along `S`'s own increasing enumeration recovers the term. -/
theorem locJExpand_compress (S : Finset J) (t : Λ[[J]].Term Empty)
    (h : locJSupport Λ J t ⊆ S) :
    locJExpand Λ J (S.orderEmbOfFin rfl) (locJCompress Λ J S t h) = t := by
  induction t with
  | var x => exact x.elim
  | @func l f ts ih =>
    rcases l with _ | l
    · rcases f with f' | j
      · simp only [locJCompress]
        rw [locJExpand_func_inl]
        exact congrArg _ (funext fun i => i.elim0)
      · have hj : j ∈ S := h (Finset.mem_union_right _ (Finset.mem_singleton_self j))
        simp only [locJCompress]
        rw [locJExpand_func_inr, orderEmbOfFin_deepRank J S rfl hj]
        exact congrArg _ (funext fun i => i.elim0)
    · rcases f with f' | c
      · simp only [locJCompress]
        rw [locJExpand_func_inl]
        exact congrArg _ (funext fun i => ih i _)
      · exact c.elim

/-- **Round trip 2**: compressing an expansion along `S`'s enumeration recovers the code. -/
private theorem locJCompress_expand (S : Finset J) (u : Λ[[Fin S.card]].Term Empty)
    (h : locJSupport Λ J (locJExpand Λ J (S.orderEmbOfFin rfl) u) ⊆ S) :
    locJCompress Λ J S (locJExpand Λ J (S.orderEmbOfFin rfl) u) h = u := by
  induction u with
  | var x => exact x.elim
  | @func l f ts ih =>
    rcases l with _ | l
    · rcases f with f' | i₀
      · show locJCompress Λ J S (Term.func (Sum.inl f' : Λ[[J]].Functions 0)
            (fun i => locJExpand Λ J (S.orderEmbOfFin rfl) (ts i))) h
          = Term.func (Sum.inl f') ts
        simp only [locJCompress]
        exact congrArg _ (funext fun i => i.elim0)
      · have hrank := deepRank_orderEmbOfFin J S rfl i₀
        show locJCompress Λ J S (Term.func
            (Sum.inr (S.orderEmbOfFin rfl i₀) : Λ[[J]].Functions 0)
            (fun i => locJExpand Λ J (S.orderEmbOfFin rfl) (ts i))) h
          = Term.func (Sum.inr i₀) ts
        simp only [locJCompress]
        refine congrArg₂ (fun (c : Fin S.card) args => Term.func
          (show Λ[[Fin S.card]].Functions 0 from Sum.inr c) args)
          (Fin.ext hrank) (funext fun i => i.elim0)
    · rcases f with f' | c
      · show locJCompress Λ J S (Term.func (Sum.inl f' : Λ[[J]].Functions (l + 1))
            (fun i => locJExpand Λ J (S.orderEmbOfFin rfl) (ts i))) h
          = Term.func (Sum.inl f') ts
        simp only [locJCompress]
        exact congrArg _ (funext fun i => ih i _)
      · exact c.elim

/-- **Round trip 3** (the orbit-theorem workhorse): if `e` carries the embedding `s` pointwise
to `t`, then renaming along `e` carries the `s`-expansion to the `t`-expansion. -/
theorem locJRename_expand (e : J ≃o J) {k : ℕ} (s t : Fin k ↪o J)
    (hst : ∀ i, e (s i) = t i) {α : Type} (u : Λ[[Fin k]].Term α) :
    locJRename Λ J e (locJExpand Λ J s u) = locJExpand Λ J t u := by
  induction u with
  | var x => rfl
  | @func l f ts ih =>
    have harg : (fun i => locJRename Λ J e (locJExpand Λ J s (ts i)))
        = fun i => locJExpand Λ J t (ts i) := funext ih
    rcases l with _ | l
    · rcases f with f' | i₀
      · exact congrArg _ harg
      · exact congrArg₂ (fun j (g : Fin 0 → Λ[[J]].Term α) =>
          Term.func (Sum.inr j : Λ[[J]].Functions 0) g) (hst i₀) harg
    · rcases f with f' | c
      · exact congrArg _ harg
      · exact c.elim

/-! ## The countable tuple-code type -/

/-- The code of an `n`-tuple: a compression arity `k` together with `n` closed terms over the
compressed skeleton `Fin k`. -/
def LocalEMTupleCode (Λ : Language.{0, 0}) (n : ℕ) : Type :=
  Σ k : ℕ, Fin n → Λ[[Fin k]].Term Empty

/-- Symbol countability passes to the constant expansion by a compressed skeleton. -/
theorem countable_sigma_functions_withFin (k : ℕ)
    [Countable (Σ l, Λ.Functions l)] : Countable (Σ l, Λ[[Fin k]].Functions l) := by
  have : ∀ l, Countable ((constantsOn (Fin k)).Functions l) := fun l =>
    match l with
    | 0 => inferInstanceAs (Countable (Fin k))
    | _ + 1 => inferInstanceAs (Countable PEmpty)
  exact Countable.of_equiv _ (Equiv.sigmaSumDistrib _ _).symm

/-- **Countability of the code type**: for a countable base language, there are only countably
many tuple codes at each arity. -/
theorem countable_localEMTupleCode (n : ℕ)
    [Countable (Σ l, Λ.Functions l)] : Countable (LocalEMTupleCode Λ n) := by
  have : ∀ k, Countable (Σ l, Λ[[Fin k]].Functions l) := fun k =>
    countable_sigma_functions_withFin Λ k
  have : ∀ k, Countable (Λ[[Fin k]].Term Empty) := fun k => inferInstance
  exact inferInstanceAs (Countable (Σ k : ℕ, Fin n → Λ[[Fin k]].Term Empty))

end Language

end FirstOrder
