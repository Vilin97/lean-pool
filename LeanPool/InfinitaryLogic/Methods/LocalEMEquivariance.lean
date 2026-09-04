/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import LeanPool.InfinitaryLogic.Methods.LocalEMContext
/-!
# Equivariance of the local EM quotient (the issue #11 spike)

An order automorphism `e : J ≃o J` acts on `Λ[[J]]`-terms by renaming skeleton constants
(`locJRename`, via Mathlib's `lhomWithConstantsMap`). The spike question for the
countably-many-types project: does the DEFINING semantic equivalence `LocalEMEq` of the local
EM quotient commute with this action? The three test lemmas, in the order of risk:

* `locJSupport_locJRename` — the finite skeleton support maps by `Finset.image e`;
* `deepRank_image_orderIso` — the support's internal rank enumeration is invariant: an order
  automorphism preserves each element's rank in a finite support;
* `locDeepInterp_locJRename` — the deep interpretation of the renamed term over the renamed
  support EQUALS (not merely relates to) that of the original — pointwise in the depth `d`.

Consequently `LocalEMEq_locJRename_iff`: the setoid is preserved AND reflected by renaming —
the two `∀ᶠ` propositions are pointwise equal, so the critical gate of the spike holds with no
reconstruction of semantic truth outside the quotient's defining fragment. The verdict is that
the existing quotient (`LocalEMContext.Carrier`) is the correct vehicle for the induced
automorphisms.

The packaging (issue #11 step 3) follows in the same file: functoriality of the renaming action
(`locJRename_refl`/`_trans`/inverses), the descended carrier equivalence
(`LocalEMContext.carrierEquiv`, computing on classes and sending `[c_j]` to `[c_{e j}]`), the
targeted expanded-language equivariance (`carrierEquiv_funMap` under the renamed symbol,
`carrierEquiv_relMap` for base relations), the acceptance theorem
`LocalEMContext.baseAutomorphism : Carrier ≃[Λ] Carrier` over the base reduct
`structureBase`, and the semantic endpoint `realize_carrierEquiv`: every base-language
infinitary formula is invariant under the induced automorphism.
-/

namespace FirstOrder

namespace Language

variable (Λ : Language.{0, 0}) (J : Type) [LinearOrder J]

/-- The skeleton-constant renaming action of an order automorphism on closed `Λ[[J]]`-terms. -/
def locJRename (e : J ≃o J) {α : Type} (t : Λ[[J]].Term α) : Λ[[J]].Term α :=
  (Λ.lhomWithConstantsMap (e : J → J)).onTerm t

/-- Renaming carries each function symbol's skeleton constant by `Finset.image e`. -/
private theorem locJConstOf_lhomWithConstantsMap (e : J ≃o J) {n : ℕ} (f : Λ[[J]].Functions n) :
    locJConstOf Λ J ((Λ.lhomWithConstantsMap (e : J → J)).onFunction f)
      = (locJConstOf Λ J f).image e := by
  rcases n with _ | n
  · rcases f with f' | j
    · rfl
    · simp only [locJConstOf]
      rfl
  · rcases f with f' | c
    · rfl
    · exact c.elim

/-- **Test lemma 1**: the skeleton support of the renamed term is the image of the support. -/
private theorem locJSupport_locJRename (e : J ≃o J) {α : Type} (t : Λ[[J]].Term α) :
    locJSupport Λ J (locJRename Λ J e t) = (locJSupport Λ J t).image e := by
  induction t with
  | var x => simp [locJRename, LHom.onTerm, locJSupport]
  | @func l f ts ih =>
    show locJSupport Λ J (Term.func ((Λ.lhomWithConstantsMap (e : J → J)).onFunction f)
      fun i => locJRename Λ J e (ts i)) = _
    rw [locJSupport, locJSupport, Finset.image_union, locJConstOf_lhomWithConstantsMap]
    congr 1
    ext x
    simp only [Finset.mem_biUnion, Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨i, hx⟩
      rw [ih i] at hx
      obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
      exact ⟨y, ⟨i, hy⟩, rfl⟩
    · rintro ⟨y, ⟨i, hy⟩, rfl⟩
      exact ⟨i, by rw [ih i]; exact Finset.mem_image_of_mem _ hy⟩

/-- **Test lemma 2**: an order automorphism preserves the internal rank enumeration of a finite
support: the rank of `e j` in `S.image e` is the rank of `j` in `S`. -/
private theorem deepRank_image_orderIso (e : J ≃o J) (S : Finset J) (j : J) :
    deepRank J (S.image e) (e j) = deepRank J S j := by
  unfold deepRank
  rw [Finset.filter_image]
  have hpred : (S.filter fun x => (e x : J) < e j) = S.filter (· < j) :=
    Finset.filter_congr fun x _ => e.lt_iff_lt
  rw [hpred]
  exact Finset.card_image_of_injective _ e.injective

/-- De-substitution intertwines skeleton renaming with variable relabeling: the
`constantsToVars` of the renamed term is the relabel of the original's along `Sum.map e id`. -/
private theorem constantsToVars_locJRename (e : J ≃o J) {α : Type} (t : Λ[[J]].Term α) :
    (locJRename Λ J e t).constantsToVars
      = t.constantsToVars.relabel (Sum.map e id) := by
  induction t with
  | var x => rfl
  | @func l f ts ih =>
    rcases l with _ | l
    · rcases f with f' | j
      · show Term.func f' (fun i => (locJRename Λ J e (ts i)).constantsToVars)
          = Term.relabel _ (Term.func f' fun i => (ts i).constantsToVars)
        rw [Term.relabel]
        congr 1
        exact funext fun i => ih i
      · rfl
    · rcases f with f' | c
      · show Term.func f' (fun i => (locJRename Λ J e (ts i)).constantsToVars)
          = Term.relabel _ (Term.func f' fun i => (ts i).constantsToVars)
        rw [Term.relabel]
        congr 1
        exact funext fun i => ih i
      · exact c.elim

/-- **Test lemma 3**: the deep interpretation of the renamed term over the image support equals
that of the original term over the original support — pointwise in the depth `d`, not merely
eventually. -/
private theorem locDeepInterp_locJRename {M : Type} [Λ.Structure M] (a : ℕ → M) (e : J ≃o J)
    (d : ℕ) (S : Finset J) (t : Λ[[J]].Term Empty) :
    locDeepInterp Λ J a d (S.image e) (locJRename Λ J e t) = locDeepInterp Λ J a d S t := by
  rw [locDeepInterp_eq_realize, locDeepInterp_eq_realize, constantsToVars_locJRename,
    Term.realize_relabel]
  congr 1
  funext x
  rcases x with j | ee
  · show a (d + deepRank J (S.image e) (e j)) = a (d + deepRank J S j)
    rw [deepRank_image_orderIso]
  · exact ee.elim

/-- **The critical gate**: the defining semantic equivalence of the local EM quotient is
preserved AND reflected by skeleton renaming — the two eventual equalities are pointwise
equivalent propositions. The existing quotient is equivariant. -/
private theorem LocalEMEq_locJRename_iff {M : Type} [Λ.Structure M] (a : ℕ → M) (e : J ≃o J)
    (t u : Λ[[J]].Term Empty) :
    LocalEMEq Λ J a (locJRename Λ J e t) (locJRename Λ J e u) ↔ LocalEMEq Λ J a t u := by
  unfold LocalEMEq
  rw [locJSupport_locJRename, locJSupport_locJRename, ← Finset.image_union]
  exact Filter.eventually_congr (Filter.Eventually.of_forall fun d => by
    rw [locDeepInterp_locJRename, locDeepInterp_locJRename])

/-- The setoid form of the gate, for a full local EM context: renamed representatives are
related exactly when the originals are. -/
private theorem LocalEMContext.setoid_locJRename_iff {M : Type} [Λ.Structure M]
    (ctx : LocalEMContext Λ J (M := M)) (e : J ≃o J) (t u : Λ[[J]].Term Empty) :
    ctx.setoid.r (locJRename Λ J e t) (locJRename Λ J e u) ↔ ctx.setoid.r t u :=
  LocalEMEq_locJRename_iff Λ J ctx.a e t u

variable {Λ} {J}

/-! ## Functoriality of the renaming action -/

private theorem locJRename_refl {α : Type} (t : Λ[[J]].Term α) :
    locJRename Λ J (OrderIso.refl J) t = t := by
  induction t with
  | var x => rfl
  | @func l f ts ih =>
    have harg : (fun i => locJRename Λ J (OrderIso.refl J) (ts i)) = ts := funext ih
    rcases l with _ | l
    · rcases f with f' | j
      · exact congrArg _ harg
      · exact congrArg _ harg
    · rcases f with f' | c
      · exact congrArg _ harg
      · exact c.elim

private theorem locJRename_trans (e₁ e₂ : J ≃o J) {α : Type} (t : Λ[[J]].Term α) :
    locJRename Λ J e₂ (locJRename Λ J e₁ t) = locJRename Λ J (e₁.trans e₂) t := by
  induction t with
  | var x => rfl
  | @func l f ts ih =>
    have harg : (fun i => locJRename Λ J e₂ (locJRename Λ J e₁ (ts i)))
        = fun i => locJRename Λ J (e₁.trans e₂) (ts i) := funext ih
    rcases l with _ | l
    · rcases f with f' | j
      · exact congrArg _ harg
      · exact congrArg _ harg
    · rcases f with f' | c
      · exact congrArg _ harg
      · exact c.elim

private theorem locJRename_symm_locJRename (e : J ≃o J) {α : Type} (t : Λ[[J]].Term α) :
    locJRename Λ J e.symm (locJRename Λ J e t) = t := by
  rw [locJRename_trans, OrderIso.self_trans_symm]
  exact locJRename_refl t

private theorem locJRename_locJRename_symm (e : J ≃o J) {α : Type} (t : Λ[[J]].Term α) :
    locJRename Λ J e (locJRename Λ J e.symm t) = t := by
  rw [locJRename_trans, OrderIso.symm_trans_self]
  exact locJRename_refl t

/-- The renaming action as an equivalence of closed terms. -/
private def locJRenameEquiv (e : J ≃o J) : Λ[[J]].Term Empty ≃ Λ[[J]].Term Empty where
  toFun := locJRename Λ J e
  invFun := locJRename Λ J e.symm
  left_inv t := locJRename_symm_locJRename e t
  right_inv t := locJRename_locJRename_symm e t

/-! ## The descended automorphism of the local EM quotient -/

variable {M : Type} [Λ.Structure M]

/-- **The descended carrier equivalence**: an order automorphism of the skeleton acts on the
local EM quotient by renaming representatives — well-defined by the equivariance gate. -/
noncomputable def LocalEMContext.carrierEquiv (ctx : LocalEMContext Λ J (M := M))
    (e : J ≃o J) : ctx.Carrier ≃ ctx.Carrier :=
  Quotient.congr (locJRenameEquiv e) fun t u =>
    (LocalEMContext.setoid_locJRename_iff Λ J ctx e t u).symm

theorem LocalEMContext.carrierEquiv_mkClass (ctx : LocalEMContext Λ J (M := M))
    (e : J ≃o J) (t : Λ[[J]].Term Empty) :
    ctx.carrierEquiv e (ctx.mkClass (t := t)) = ctx.mkClass (t := locJRename Λ J e t) :=
  rfl

/-- **The skeleton-class equation**: the descended automorphism sends the class of the skeleton
constant `c_j` to the class of `c_{e j}`. -/
private theorem LocalEMContext.carrierEquiv_const (ctx : LocalEMContext Λ J (M := M))
    (e : J ≃o J) (j : J) :
    ctx.carrierEquiv e
        (ctx.mkClass (t := Term.func (Sum.inr j : Λ[[J]].Functions 0) Fin.elim0))
      = ctx.mkClass (t := Term.func (Sum.inr (e j) : Λ[[J]].Functions 0) Fin.elim0) := by
  rw [ctx.carrierEquiv_mkClass]
  exact congrArg (fun t => ctx.mkClass (t := t)) (congrArg _ (funext fun i => i.elim0))

/-- Equivariance of function interpretation under the language renaming induced by `e`: the
targeted expanded-language fact (the base-reduct automorphism consumes its `Sum.inl` case). -/
private theorem LocalEMContext.carrierEquiv_funMap (ctx : LocalEMContext Λ J (M := M))
    (e : J ≃o J) {n : ℕ} (f : Λ[[J]].Functions n) (xs : Fin n → ctx.Carrier) :
    ctx.carrierEquiv e (@Structure.funMap (Λ[[J]]) ctx.Carrier ctx.structure n f xs)
      = @Structure.funMap (Λ[[J]]) ctx.Carrier ctx.structure n
          ((Λ.lhomWithConstantsMap (e : J → J)).onFunction f)
          (fun i => ctx.carrierEquiv e (xs i)) := by
  have hxs : xs = fun i => ctx.mkClass (t := Quotient.out (xs i)) :=
    funext fun i => (Quotient.out_eq (xs i)).symm
  rw [hxs, ctx.funMap_mkClass, ctx.carrierEquiv_mkClass,
    show (fun i => ctx.carrierEquiv e (ctx.mkClass (t := Quotient.out (xs i))))
        = fun i => ctx.mkClass (t := locJRename Λ J e (Quotient.out (xs i))) from
      funext fun i => ctx.carrierEquiv_mkClass e (Quotient.out (xs i)),
    ctx.funMap_mkClass]
  rfl

/-- Equivariance of base-relation interpretation: the descended map preserves and reflects
every base relation — via the pointwise deep-interpretation equality over the image support. -/
private theorem LocalEMContext.carrierEquiv_relMap (ctx : LocalEMContext Λ J (M := M))
    (e : J ≃o J) {n : ℕ} (R : Λ.Relations n) (xs : Fin n → ctx.Carrier) :
    (@Structure.RelMap (Λ[[J]]) ctx.Carrier ctx.structure n (Sum.inl R)
        (fun i => ctx.carrierEquiv e (xs i))
      ↔ @Structure.RelMap (Λ[[J]]) ctx.Carrier ctx.structure n (Sum.inl R) xs) := by
  set rep : Fin n → Λ[[J]].Term Empty := fun i => Quotient.out (xs i) with hrep
  set S : Finset J := Finset.univ.biUnion fun i => locJSupport Λ J (rep i) with hS
  have hxs : xs = fun i => ctx.mkClass (t := rep i) :=
    funext fun i => (Quotient.out_eq (xs i)).symm
  have hFxs : (fun i => ctx.carrierEquiv e (xs i))
      = fun i => ctx.mkClass (t := locJRename Λ J e (rep i)) := by
    funext i
    rw [hxs]
    exact ctx.carrierEquiv_mkClass e (rep i)
  have hsubS : (Finset.univ.biUnion fun i => locJSupport Λ J (rep i)) ⊆ S := subset_refl S
  have hsubS' : (Finset.univ.biUnion fun i => locJSupport Λ J (locJRename Λ J e (rep i)))
      ⊆ S.image e := by
    refine Finset.biUnion_subset.mpr fun i _ => ?_
    rw [locJSupport_locJRename]
    exact Finset.image_subset_image
      (Finset.subset_biUnion_of_mem (fun i => locJSupport Λ J (rep i)) (Finset.mem_univ i))
  rw [hFxs, hxs,
    LocalEMContext.relMap_mkClass_iff Λ J ctx R rep hsubS,
    LocalEMContext.relMap_mkClass_iff Λ J ctx R (fun i => locJRename Λ J e (rep i)) hsubS']
  exact Filter.eventually_congr (Filter.Eventually.of_forall fun d => Iff.of_eq (congrArg _
    (funext fun i => locDeepInterp_locJRename Λ J ctx.a e d S (rep i))))

/-- **The acceptance theorem**: the descended equivalence is a genuine automorphism of the
base-language (`Λ`-reduct) structure on the local EM carrier — every order automorphism of the
skeleton induces a structure automorphism sending `[c_j]` to `[c_{e j}]`
(`carrierEquiv_const`). -/
private noncomputable def LocalEMContext.baseAutomorphism (ctx : LocalEMContext Λ J (M := M))
    (e : J ≃o J) :
    letI := ctx.structureBase
    ctx.Carrier ≃[Λ] ctx.Carrier :=
  letI := ctx.structureBase
  { toEquiv := ctx.carrierEquiv e
    map_fun' := fun f xs => ctx.carrierEquiv_funMap e (Sum.inl f) xs
    map_rel' := fun R xs => ctx.carrierEquiv_relMap e R xs }

/-- **The semantic endpoint of the packaging**: every base-language infinitary formula is
invariant under the induced automorphism. -/
theorem LocalEMContext.realize_carrierEquiv (ctx : LocalEMContext Λ J (M := M))
    (e : J ≃o J) {α : Type} {n : ℕ} (φ : Λ.BoundedFormulaω α n)
    (v : α → ctx.Carrier) (xs : Fin n → ctx.Carrier) :
    letI := ctx.structureBase
    (φ.Realize v xs ↔ φ.Realize (ctx.carrierEquiv e ∘ v) (ctx.carrierEquiv e ∘ xs)) := by
  let := ctx.structureBase
  exact BoundedFormulaω.realize_equiv (ctx.baseAutomorphism e) φ v xs

end Language

end FirstOrder
