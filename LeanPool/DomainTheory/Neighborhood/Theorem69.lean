/-
Copyright (c) 2026 Catskills Research Company. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Catskills Research Company
-/

import LeanPool.DomainTheory.Neighborhood.Definition68
import LeanPool.DomainTheory.Neighborhood.Theorem41

/-!
# Lecture VI — Theorem 6.9 (Scott 1981, PRG-19): homomorphisms out of a fixed
point

> **THEOREM 6.9.** If the functor `T` is *continuous on maps* (Definition 6.8) and
if `D ≅ T(D)`, so
> in particular `D` is a `T`-algebra, then for any `T`-algebra `k : T(E) → E`
there is a homomorphism
> `h : D → E`.

Scott's proof. Let `i : T(D) → D` be the isomorphism making `D` a `T`-algebra and
`j : D → T(D)` its
inverse. A homomorphism `h : D → E` must satisfy `h ∘ i = k ∘ T(h)`, equivalently
the **fixed-point
equation**

`h = k ∘ T(h) ∘ j`.

The operator `λh. k ∘ T(h) ∘ j` on the **strict** function space `(D →⊥ E)` is
approximable: the
inner `λh. T(h)` is approximable *precisely by Definition 6.8*
(`ContinuousOnMaps`), and post- and
pre-composition with the fixed maps `k`, `j` is approximable too. Hence by the
Lecture IV fixed-point
theory (Theorem 4.1, `fixElement`) it has a least fixed point `h`, the desired
homomorphism.

## What the formalization does

We work over Scott's **strict** function space `(D →⊥ E) = strictFun D.sys E.sys`
(Exercise 5.10),
exactly matching Definition 6.8.

* **`homOpComp`** — the strict composite `g ↦ k ∘ g ∘ j` as a `StrictMap`.
Strictness of the composite
  uses that `j` is strict (any isomorphism of domains preserves `⊥`,
  `isStrict_of_comp_eq_id`) and `k`
  is strict (a morphism of Scott's *strict* category; carried as a hypothesis), so
  `T(h) ∘ j` and then
  `k ∘ (T(h) ∘ j)` stay strict.
* **`homOp`** — the post/pre-composition map `(T(D) →⊥ T(E)) → (D →⊥ E)`, `g ↦ k ∘
g ∘ j`, built by
  Exercise 2.8's `ofMono`. Its decisive **action lemma** `homOp_apply_filter` says
  `homOp(f̂) = (k ∘ f ∘ j)^` for every strict `f`; it is proved by reducing
  (through the strict
  representation `strictFunEquiv`) to single step neighbourhoods `[X, Z]`, where
  the "finite factoring"
  is just `N := [Y₁, Y₂]`.
* The operator is `Op = homOp ∘ Φ`, where `Φ` is Definition 6.8's witness that
`λf. T(f)` is
  approximable. Its `fixElement` represents the strict map `h`; the fixed-point
  equation
  (`toElementMap_fixElement`) unwinds — via `Φ`'s defining property and
  `homOp_apply_filter` — to
  `h = k ∘ T(h) ∘ j`, which rearranges (using `j ∘ i = I`) to the homomorphism
  square
  `h ∘ i = k ∘ T(h)`.

The conclusion is `Nonempty {g : AlgHom ⟨D, i⟩ B // IsStrict g.hom}` — Scott's
*existence* statement,
recording that the homomorphism is itself a strict map (it is `toStrictMap` of the
fixed point), which
the uniqueness half of Theorem 6.14 consumes. Extracting `Φ` from the
`Prop`-valued `ContinuousOnMaps`
is done by `Exists.elim` while proving a `Prop`, so it stays **choice-free**
(`#print axioms ⊆ {propext, Quot.sound}`).
-/

namespace Domain.Neighborhood

open NeighborhoodSystem ApproximableMap Domain.Neighborhood.Exercise510

universe u

variable {α β γ : Type*}
  {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β} {V₂ : NeighborhoodSystem γ}

/-! ### General helper lemmas (strictness and monotonicity of composition). -/

/-- The composite of strict maps is strict: `(a ∘ b)(⊥) = a(b(⊥)) = a(⊥) = ⊥`. -/
theorem isStrict_comp {a : ApproximableMap V₁ V₂} {b : ApproximableMap V₀ V₁}
    (ha : IsStrict a) (hb : IsStrict b) : IsStrict (a.comp b) := by
  rw [isStrict_iff_apply_bot, toElementMap_comp, isStrict_iff_apply_bot.mp hb,
    isStrict_iff_apply_bot.mp ha]

/-- If `a ∘ b = I` then `a` is strict: any (split) iso preserves `⊥`. -/
theorem isStrict_of_comp_eq_id {a : ApproximableMap V₁ V₀} {b : ApproximableMap V₀ V₁}
    (h : a.comp b = idMap V₀) : IsStrict a := by
  rw [isStrict_iff_apply_bot]
  refine le_antisymm ?_ (V₀.bot_le _)
  calc a.toElementMap V₁.bot
      ≤ a.toElementMap (b.toElementMap V₀.bot) := toElementMap_mono a (V₁.bot_le _)
    _ = (a.comp b).toElementMap V₀.bot := (toElementMap_comp a b V₀.bot).symm
    _ = V₀.bot := by rw [h, toElementMap_idMap]

/-- Composition is monotone in both arguments (general arities). -/
theorem comp_mono_gen {a a' : ApproximableMap V₁ V₂} {b b' : ApproximableMap V₀ V₁}
    (ha : a ≤ a') (hb : b ≤ b') : a.comp b ≤ a'.comp b' := by
  intro X Z h
  obtain ⟨Y, hXY, hYZ⟩ := h
  exact ⟨Y, hb _ _ hXY, ha _ _ hYZ⟩

/-- `toStrictMap` is monotone. -/
theorem toStrictMap_mono {φ φ' : (strictFun V₀ V₁).Element} (h : φ ≤ φ') :
    toStrictMap φ ≤ toStrictMap φ' := by
  intro X Y hrel
  rw [toStrictMap_rel] at hrel ⊢
  exact h _ hrel

/-- `toStrictFilter` is monotone. -/
theorem toStrictFilter_mono {f f' : StrictMap V₀ V₁} (h : f ≤ f') :
    toStrictFilter f ≤ toStrictFilter f' := by
  intro W hW
  rw [mem_toStrictFilter] at hW ⊢
  exact ⟨hW.1, strictFun_mem_up_closed hW.1 hW.2 h⟩

/-- `toStrictFilter ∘ toStrictMap = id` (the left inverse of the
strict-function-space
representation; the mirror of `toStrictMap_toStrictFilter`). -/
theorem toStrictFilter_toStrictMap (φ : (strictFun V₀ V₁).Element) :
    toStrictFilter (toStrictMap φ) = φ := by
  apply Element.ext
  intro W
  constructor
  · rintro ⟨hWmem, hfW⟩
    obtain ⟨⟨L, hL, rfl⟩, _⟩ := hWmem
    exact (mem_sstepFun_iff φ hL).mpr (fun p hp => hfW p hp)
  · intro hW
    refine ⟨φ.sub hW, ?_⟩
    obtain ⟨⟨L, hL, rfl⟩, _⟩ := φ.sub hW
    intro p hp
    exact (mem_sstepFun_iff φ hL).mp hW p hp

/-! ### The post/pre-composition operator on strict function spaces. -/

section HomOp

variable (T : Endofunctor DomainObj) (D E : DomainObj)
  (j : ApproximableMap D.sys (T.obj D).sys)
  (k : ApproximableMap (T.obj E).sys E.sys)
  (hj : IsStrict j) (hk : IsStrict k)

/-- The strict composite `g ↦ k ∘ g ∘ j : (T(D) →⊥ T(E)) → (D →⊥ E)`. -/
def homOpComp (g : StrictMap (T.obj D).sys (T.obj E).sys) : StrictMap D.sys E.sys :=
  ⟨k.comp (g.1.comp j), isStrict_comp hk (isStrict_comp g.2 hj)⟩

theorem homOpComp_mono {g g' : StrictMap (T.obj D).sys (T.obj E).sys} (hgg : g ≤ g') :
    homOpComp T D E j k hj hk g ≤ homOpComp T D E j k hj hk g' := by
  change k.comp (g.1.comp j) ≤ k.comp (g'.1.comp j)
  exact comp_mono_gen le_rfl (comp_mono_gen (Subtype.coe_le_coe.mpr hgg) le_rfl)

/-- **The operator `λg. k ∘ g ∘ j`** as an approximable map between the strict
function spaces,
built
by Exercise 2.8 (`ofMono`) from its values on finite elements. -/
def homOp : ApproximableMap (strictFun (T.obj D).sys (T.obj E).sys) (strictFun D.sys E.sys) :=
  ofMono
    (fun N hN => toStrictFilter (homOpComp T D E j k hj hk
      (toStrictMap ((strictFun (T.obj D).sys (T.obj E).sys).principal hN))))
    (by
      intro N N' hN hN' hN'N
      apply toStrictFilter_mono
      apply homOpComp_mono
      apply toStrictMap_mono
      exact ((strictFun (T.obj D).sys (T.obj E).sys).principal_le_iff hN hN').mpr hN'N)

theorem homOp_rel {N : Set (StrictMap (T.obj D).sys (T.obj E).sys)}
    {M : Set (StrictMap D.sys E.sys)} :
    (homOp T D E j k hj hk).rel N M ↔
      ∃ hN : (strictFun (T.obj D).sys (T.obj E).sys).mem N,
        (toStrictFilter (homOpComp T D E j k hj hk
          (toStrictMap ((strictFun (T.obj D).sys (T.obj E).sys).principal hN)))).mem M :=
  Iff.rfl

/-- **Action lemma.** `homOp` realizes the composite `g ↦ k ∘ g ∘ j` on filters of
strict maps:
`homOp(ĝ) = (k ∘ g ∘ j)^`. Proved by reducing to single step neighbourhoods
through the strict
representation. -/
theorem homOp_apply_filter (g : StrictMap (T.obj D).sys (T.obj E).sys) :
    (homOp T D E j k hj hk).toElementMap (toStrictFilter g)
      = toStrictFilter (homOpComp T D E j k hj hk g) := by
  have key : ∀ X Z,
      ((homOp T D E j k hj hk).toElementMap (toStrictFilter g)).mem (sstep X Z)
        ↔ (homOpComp T D E j k hj hk g).1.rel X Z := by
    intro X Z
    constructor
    · rintro ⟨N, hgN, hrel⟩
      rw [homOp_rel] at hrel
      obtain ⟨hN, hmem⟩ := hrel
      rw [mem_toStrictFilter] at hmem
      obtain ⟨_, hsstep⟩ := hmem
      rw [mem_sstep] at hsstep
      obtain ⟨Y2, ⟨Y1, hXY1, hY1Y2⟩, hY2Z⟩ := hsstep
      rw [toStrictMap_rel, mem_principal] at hY1Y2
      obtain ⟨_, hNsub⟩ := hY1Y2
      exact ⟨Y2, ⟨Y1, hXY1, hNsub (mem_toStrictFilter.mp hgN).2⟩, hY2Z⟩
    · intro hrel
      obtain ⟨Y2, ⟨Y1, hXY1, hgY1Y2⟩, hY2Z⟩ := hrel
      refine ⟨sstep Y1 Y2, ?_, ?_⟩
      · rw [mem_toStrictFilter]
        exact ⟨sstep_mem_of_mem (g := g) hgY1Y2, hgY1Y2⟩
      · rw [homOp_rel]
        refine ⟨sstep_mem_of_mem (g := g) hgY1Y2, ?_⟩
        rw [mem_toStrictFilter]
        refine ⟨sstep_mem_of_mem (g := homOpComp T D E j k hj hk g)
          ⟨Y2, ⟨Y1, hXY1, hgY1Y2⟩, hY2Z⟩, ?_⟩
        rw [mem_sstep]
        refine ⟨Y2, ⟨Y1, hXY1, ?_⟩, hY2Z⟩
        rw [toStrictMap_rel, mem_principal]
        exact ⟨sstep_mem_of_mem (g := g) hgY1Y2, subset_rfl⟩
  have hmap : toStrictMap ((homOp T D E j k hj hk).toElementMap (toStrictFilter g))
      = homOpComp T D E j k hj hk g := by
    apply Subtype.ext
    apply ApproximableMap.ext
    intro X Z
    rw [toStrictMap_rel]
    exact key X Z
  have hL := toStrictFilter_toStrictMap
    ((homOp T D E j k hj hk).toElementMap (toStrictFilter g))
  rw [hmap] at hL
  exact hL.symm

end HomOp

/-! ### Theorem 6.9. -/

/-- **Theorem 6.9 (Scott 1981, PRG-19).** If `T` is continuous on maps and `D ≅
T(D)` (so `D` is a
`T`-algebra via `i : T(D) → D`), then for any `T`-algebra `B = (E, k)` with `k`
strict there is a
homomorphism `D → E`. The homomorphism is the least fixed point of `λh. k ∘ T(h) ∘
j`. -/
theorem nonempty_algHom_of_continuousOnMaps
    (T : Endofunctor DomainObj) (hT : ContinuousOnMaps T)
    {D : DomainObj} (iso : Iso (T.obj D) D)
    (B : TAlgebra T) (hk : IsStrict B.str) :
    Nonempty {g : AlgHom (⟨D, iso.hom⟩ : TAlgebra T) B // IsStrict g.hom} := by
  -- `j = i⁻¹` is strict (it is an isomorphism of domains).
  have hji : iso.inv.comp iso.hom = idMap (T.obj D).sys := iso.hom_inv_id
  have hj : IsStrict iso.inv := isStrict_of_comp_eq_id hji
  -- Definition 6.8's witness that `λf. T(f)` is approximable.
  obtain ⟨Φ, hΦ⟩ := hT D B.carrier
  -- the operator `Op = (k ∘ · ∘ j) ∘ T` and its least fixed point.
  set Op := (homOp T D B.carrier iso.inv B.str hj hk).comp Φ with hOp
  set x := Op.fixElement with hx
  set h := toStrictMap x with hh
  let Tg : StrictMap (T.obj D).sys (T.obj B.carrier).sys :=
    ⟨T.map (X := D) (Y := B.carrier) h.1, hT.isStrict_map (D := D) (E := B.carrier) h⟩
  have hfix : Op.toElementMap x = x := toElementMap_fixElement Op
  have hxh : toStrictFilter h = x := toStrictFilter_toStrictMap x
  -- `Φ` sends `h` to the filter of `T(h)`.
  have hTg : toStrictMap (Φ.toElementMap (toStrictFilter h)) = Tg := Subtype.ext (hΦ h)
  have hφ : Φ.toElementMap (toStrictFilter h) = toStrictFilter Tg := by
    rw [← hTg]; exact (toStrictFilter_toStrictMap _).symm
  -- evaluate the operator at the fixed point.
  have hOpx : Op.toElementMap x
      = toStrictFilter (homOpComp T D B.carrier iso.inv B.str hj hk Tg) := by
    rw [hOp, toElementMap_comp, ← hxh, hφ, homOp_apply_filter]
  have hcompeq : toStrictFilter (homOpComp T D B.carrier iso.inv B.str hj hk Tg)
      = toStrictFilter h := by
    rw [← hOpx, hfix, hxh]
  have hh' : homOpComp T D B.carrier iso.inv B.str hj hk Tg = h := by
    have h2 := congrArg toStrictMap hcompeq
    rwa [toStrictMap_toStrictFilter, toStrictMap_toStrictFilter] at h2
  -- the fixed-point equation `h = k ∘ T(h) ∘ j`.
  have hcore : B.str.comp ((T.map (X := D) (Y := B.carrier) h.1).comp iso.inv) = h.1 :=
    congrArg Subtype.val hh'
  -- rearrange to the homomorphism square `h ∘ i = k ∘ T(h)`.
  refine ⟨⟨{ hom := h.1, comm := ?_ }, h.2⟩⟩
  change h.1.comp iso.hom = B.str.comp (T.map (X := D) (Y := B.carrier) h.1)
  conv_lhs => rw [← hcore]
  rw [comp_assoc, comp_assoc, hji, comp_idMap]

end Domain.Neighborhood
