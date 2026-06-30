/-
Copyright (c) 2026 Catskills Research Company. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Catskills Research Company
-/

import LeanPool.DomainTheory.Neighborhood.Theorem69
import LeanPool.DomainTheory.Neighborhood.Proposition67
import LeanPool.DomainTheory.Neighborhood.Lemma615
import LeanPool.DomainTheory.Neighborhood.Exercise408

/-!
# Lecture VI — Theorem 6.16 (Scott 1981, PRG-19): an initial algebra embeds in
every solution

> **THEOREM 6.16.** If on the category of domains and strict approximable maps the
functor `T` is
> continuous on maps, and if `D` is an initial `T`-algebra, then for any system `E
≅ T(E)` we have
> `D ⊴ E`.

Scott's proof. By Theorem 6.9 there is a homomorphism `h : D → E` and (running 6.9
the other way) a
homomorphism `g : E → D`. The composite `g ∘ h : D → D` is a homomorphism of the
*initial* algebra
`D`, hence equals `I_D` by uniqueness. By Lemma 6.15 it remains to show `h ∘ g ⊑
I_E`.

Writing `i : T(D) → D`, `j : D → T(D)` for `D`'s isomorphism (Lambek, Proposition
6.7) and
`u : T(E) → E`, `v : E → T(E)` for `E`'s, the proof of 6.9 produces `h` and `g` as
the least fixed
points of
`h = u ∘ T(h) ∘ j` and `g = i ∘ T(g) ∘ v`.
Setting `h₀ = ⊥`, `g₀ = ⊥` and `hₙ₊₁ = u ∘ T(hₙ) ∘ j`, `gₙ₊₁ = i ∘ T(gₙ) ∘ v`, one
computes
`hₙ₊₁ ∘ gₙ₊₁ = u ∘ T(hₙ ∘ gₙ) ∘ v` (using `j ∘ i = I_{T(D)}`), so `kₙ := hₙ ∘ gₙ`
is the approximant
chain of the operator `k ↦ u ∘ T(k) ∘ v`. Therefore `h ∘ g = ⊔ₙ (hₙ ∘ gₙ)` is its
*least* fixed
point, and since `I_E` is a fixed point of that operator, `h ∘ g ⊑ I_E`.

## What the formalization does

Everything reuses Theorem 6.9's operator `(homOp T D E j k) ∘ Φ` on Scott's
**strict** function
space `(D →⊥ E)` (Exercise 5.10). The per-step computation is isolated as
`opStep`. The three
approximant chains `H`, `G`, `K` (for `h`, `g`, `k`) and the ladder identity `H n
∘ G n = K n` give
`h ∘ g = k` (the least fixed point of `u ∘ T(·) ∘ v`), which is `⊑ I_E` because
`I_E` is a fixed
point. Lemma 6.15 (`trianglelefteq_of_projectionPair`) then closes `D ⊴ E`.
-/

namespace Domain.Neighborhood

open NeighborhoodSystem ApproximableMap Domain.Neighborhood.Exercise510

universe w

/-! ### General helpers. -/

/-- **The per-step computation of Theorem 6.9's operator.** For the operator `Op =
(k ∘ · ∘ j) ∘ Φ`
on the strict function space, `Op(x)` is the strict map `k ∘ T(toStrictMap x) ∘
j`. This is the
content of `homOp_apply_filter` plus the defining property `hΦ` of the Definition
6.8 witness `Φ`. -/
theorem opStep (T : Endofunctor DomainObj.{w}) (D E : DomainObj.{w})
    (j : ApproximableMap D.sys (T.obj D).sys) (k : ApproximableMap (T.obj E).sys E.sys)
    (hj : IsStrict j) (hk : IsStrict k)
    (Φ : ApproximableMap (strictFun D.sys E.sys) (strictFun (T.obj D).sys (T.obj E).sys))
    (hΦ : ∀ f : StrictMap D.sys E.sys,
      (toStrictMap (Φ.toElementMap (toStrictFilter f))).1 = T.map (X := D) (Y := E) f.1)
    (x : (strictFun D.sys E.sys).Element) :
    (toStrictMap (((homOp T D E j k hj hk).comp Φ).toElementMap x)).1
      = k.comp ((T.map (X := D) (Y := E) (toStrictMap x).1).comp j) := by
  set h := toStrictMap x with hh
  have hx : toStrictFilter h = x := toStrictFilter_toStrictMap x
  have hφ : Φ.toElementMap x
      = toStrictFilter (toStrictMap (Φ.toElementMap (toStrictFilter h))) := by
    rw [← hx]; exact (toStrictFilter_toStrictMap _).symm
  rw [toElementMap_comp, hφ, homOp_apply_filter, toStrictMap_toStrictFilter]
  change k.comp ((toStrictMap (Φ.toElementMap (toStrictFilter h))).1.comp j)
      = k.comp ((T.map (X := D) (Y := E) h.1).comp j)
  rw [hΦ h]

/-- The strict map represented by `⊥` of the strict function space relates `X` to
`Y` exactly when
`X` is a neighbourhood and `Y` is the master output: it is the constant-`⊥`
(least) strict map. -/
theorem botStrict_rel {α β : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}
    {X : Set α} {Y : Set β} :
    (toStrictMap (strictFun V₀ V₁).bot).1.rel X Y ↔ V₀.mem X ∧ Y = V₁.master := by
  rw [toStrictMap_rel, NeighborhoodSystem.mem_bot, strictFun_master]
  constructor
  · intro h
    have hcb : (⟨constMap V₀ V₁.bot, isStrict_constBot⟩ : StrictMap V₀ V₁) ∈ sstep X Y := by
      rw [h]; exact Set.mem_univ _
    rw [mem_sstep, constMap_rel, NeighborhoodSystem.mem_bot] at hcb
    exact hcb
  · rintro ⟨hX, rfl⟩
    exact sstep_cod_master hX

/-! ### Theorem 6.16. -/

/-- **Theorem 6.16 (Scott 1981, PRG-19).** If `T` is continuous on maps and `D` is
an initial
`T`-algebra, then for any system `E ≅ T(E)` we have `D ⊴ E`: the initial algebra
embeds as a
subdomain of every solution of the domain equation. -/
theorem trianglelefteq_of_isInitial
    (T : Endofunctor DomainObj.{w}) (hT : ContinuousOnMaps T)
    (Dalg : TAlgebra T) (hinit : IsInitial Dalg)
    (E : DomainObj.{w}) (isoE : Iso (T.obj E) E) :
    Dalg.carrier.sys ⊴ E.sys := by
  -- Lambek (Proposition 6.7): the structure map of `D` is an isomorphism `i :
  -- T(D) ≅ D`.
  let isoD : Iso (T.obj Dalg.carrier) Dalg.carrier := lambek Dalg hinit
  -- strictness of the four structure maps (each is a split iso, hence preserves
  -- `⊥`).
  have hi : IsStrict isoD.hom := isStrict_of_comp_eq_id isoD.inv_hom_id
  have hj : IsStrict isoD.inv := isStrict_of_comp_eq_id isoD.hom_inv_id
  have hu : IsStrict isoE.hom := isStrict_of_comp_eq_id isoE.inv_hom_id
  have hv : IsStrict isoE.inv := isStrict_of_comp_eq_id isoE.hom_inv_id
  -- the iso laws in `.comp` form.
  have hji : isoD.inv.comp isoD.hom = idMap (T.obj Dalg.carrier).sys := isoD.hom_inv_id
  have hvu : isoE.inv.comp isoE.hom = idMap (T.obj E).sys := isoE.hom_inv_id
  have huv : isoE.hom.comp isoE.inv = idMap E.sys := isoE.inv_hom_id
  -- Definition 6.8 witnesses that `λf. T(f)` is approximable on each strict
  -- function space.
  obtain ⟨ΦDE, hΦDE⟩ := hT Dalg.carrier E
  obtain ⟨ΦED, hΦED⟩ := hT E Dalg.carrier
  obtain ⟨ΦEE, hΦEE⟩ := hT E E
  -- the three operators (Theorem 6.9's `λf. k ∘ T(f) ∘ j`) for `h`, `g`, `k`.
  let Oph := (homOp T Dalg.carrier E isoD.inv isoE.hom hj hu).comp ΦDE
  let Opg := (homOp T E Dalg.carrier isoE.inv isoD.hom hv hi).comp ΦED
  let Opk := (homOp T E E isoE.inv isoE.hom hv hu).comp ΦEE
  -- the approximant chains.
  let H : ℕ → ApproximableMap Dalg.carrier.sys E.sys := fun n => (toStrictMap (Oph.iterElem n)).1
  let G : ℕ → ApproximableMap E.sys Dalg.carrier.sys := fun n => (toStrictMap (Opg.iterElem n)).1
  let K : ℕ → ApproximableMap E.sys E.sys := fun n => (toStrictMap (Opk.iterElem n)).1
  -- `iterElem 0 = ⊥`.
  have iterElem_zero : ∀ {γ : Type w} {V : NeighborhoodSystem γ} (f : ApproximableMap V V),
      f.iterElem 0 = V.bot := by
    intro γ V f
    change (f.iterMap 0).toElementMap V.bot = V.bot
    rw [iterMap_zero, toElementMap_idMap]
  -- the recursion equations `hₙ₊₁ = u ∘ T(hₙ) ∘ j`, etc.
  have H_succ : ∀ n, H (n + 1)
      = isoE.hom.comp ((T.map (X := Dalg.carrier) (Y := E) (H n)).comp isoD.inv) := by
    intro n
    change (toStrictMap (Oph.iterElem (n + 1))).1 = _
    rw [iterElem_succ]
    exact opStep T Dalg.carrier E isoD.inv isoE.hom hj hu ΦDE hΦDE (Oph.iterElem n)
  have G_succ : ∀ n, G (n + 1)
      = isoD.hom.comp ((T.map (X := E) (Y := Dalg.carrier) (G n)).comp isoE.inv) := by
    intro n
    change (toStrictMap (Opg.iterElem (n + 1))).1 = _
    rw [iterElem_succ]
    exact opStep T E Dalg.carrier isoE.inv isoD.hom hv hi ΦED hΦED (Opg.iterElem n)
  have K_succ : ∀ n, K (n + 1)
      = isoE.hom.comp ((T.map (X := E) (Y := E) (K n)).comp isoE.inv) := by
    intro n
    change (toStrictMap (Opk.iterElem (n + 1))).1 = _
    rw [iterElem_succ]
    exact opStep T E E isoE.inv isoE.hom hv hu ΦEE hΦEE (Opk.iterElem n)
  -- monotonicity of the chains.
  have H_mono : ∀ {n m : ℕ}, n ≤ m → H n ≤ H m := fun hnm =>
    toStrictMap_mono (iterElem_mono Oph hnm)
  have G_mono : ∀ {n m : ℕ}, n ≤ m → G n ≤ G m := fun hnm =>
    toStrictMap_mono (iterElem_mono Opg hnm)
  -- the algebraic core: `(u ∘ a ∘ j) ∘ (i ∘ b ∘ v) = u ∘ (a ∘ b) ∘ v` (uses `j ∘
  -- i = I`).
  have key : ∀ (a : ApproximableMap (T.obj Dalg.carrier).sys (T.obj E).sys)
      (b : ApproximableMap (T.obj E).sys (T.obj Dalg.carrier).sys),
      (isoE.hom.comp (a.comp isoD.inv)).comp (isoD.hom.comp (b.comp isoE.inv))
        = isoE.hom.comp ((a.comp b).comp isoE.inv) := by
    intro a b
    rw [comp_assoc isoE.hom (a.comp isoD.inv) (isoD.hom.comp (b.comp isoE.inv)),
        comp_assoc a isoD.inv (isoD.hom.comp (b.comp isoE.inv)),
        ← comp_assoc isoD.inv isoD.hom (b.comp isoE.inv), hji, idMap_comp,
        ← comp_assoc a b isoE.inv]
  -- functoriality `T(p) ∘ T(q) = T(p ∘ q)` in `.comp` form.
  have hTcomp : ∀ (p : ApproximableMap Dalg.carrier.sys E.sys)
      (q : ApproximableMap E.sys Dalg.carrier.sys),
      (T.map (X := Dalg.carrier) (Y := E) p).comp (T.map (X := E) (Y := Dalg.carrier) q)
        = T.map (X := E) (Y := E) (p.comp q) :=
    fun p q => (T.map_comp (X := E) (Y := Dalg.carrier) (Z := E) p q).symm
  -- **the ladder**: `hₙ ∘ gₙ = kₙ`.
  have ladder : ∀ n, (H n).comp (G n) = K n := by
    intro n
    induction n with
    | zero =>
      apply ApproximableMap.ext
      intro X Z
      have hH0 : ∀ {P Q}, (H 0).rel P Q ↔ Dalg.carrier.sys.mem P ∧ Q = E.sys.master := by
        intro P Q
        change (toStrictMap (Oph.iterElem 0)).1.rel P Q ↔ _
        rw [iterElem_zero]; exact botStrict_rel
      have hG0 : ∀ {P Q}, (G 0).rel P Q ↔ E.sys.mem P ∧ Q = Dalg.carrier.sys.master := by
        intro P Q
        change (toStrictMap (Opg.iterElem 0)).1.rel P Q ↔ _
        rw [iterElem_zero]; exact botStrict_rel
      have hK0 : ∀ {P Q}, (K 0).rel P Q ↔ E.sys.mem P ∧ Q = E.sys.master := by
        intro P Q
        change (toStrictMap (Opk.iterElem 0)).1.rel P Q ↔ _
        rw [iterElem_zero]; exact botStrict_rel
      constructor
      · rintro ⟨Y, hG, hHr⟩
        rw [hG0] at hG; rw [hH0] at hHr
        obtain ⟨hEX, rfl⟩ := hG
        obtain ⟨_, rfl⟩ := hHr
        rw [hK0]; exact ⟨hEX, rfl⟩
      · intro hK
        rw [hK0] at hK
        obtain ⟨hEX, rfl⟩ := hK
        exact ⟨Dalg.carrier.sys.master,
          (hG0).mpr ⟨hEX, rfl⟩, (hH0).mpr ⟨Dalg.carrier.sys.master_mem, rfl⟩⟩
    | succ n ih =>
      rw [H_succ n, G_succ n, key, K_succ n, hTcomp (H n) (G n), ih]
  -- the fixed-point maps and their `⊔`-decomposition.
  let hh := (toStrictMap Oph.fixElement).1
  let gg := (toStrictMap Opg.fixElement).1
  let kk := (toStrictMap Opk.fixElement).1
  have H_fix_rel : ∀ X Y, hh.rel X Y ↔ ∃ n, (H n).rel X Y := by
    intro X Y
    change (toStrictMap Oph.fixElement).1.rel X Y ↔ _
    rw [toStrictMap_rel, Oph.fixElement_eq_iSupDirected, NeighborhoodSystem.mem_iSupDirected]
    constructor
    · rintro ⟨n, hn⟩; exact ⟨n, hn⟩
    · rintro ⟨n, hn⟩; exact ⟨n, hn⟩
  have G_fix_rel : ∀ X Y, gg.rel X Y ↔ ∃ n, (G n).rel X Y := by
    intro X Y
    change (toStrictMap Opg.fixElement).1.rel X Y ↔ _
    rw [toStrictMap_rel, Opg.fixElement_eq_iSupDirected, NeighborhoodSystem.mem_iSupDirected]
    constructor
    · rintro ⟨n, hn⟩; exact ⟨n, hn⟩
    · rintro ⟨n, hn⟩; exact ⟨n, hn⟩
  have K_fix_rel : ∀ X Y, kk.rel X Y ↔ ∃ n, (K n).rel X Y := by
    intro X Y
    change (toStrictMap Opk.fixElement).1.rel X Y ↔ _
    rw [toStrictMap_rel, Opk.fixElement_eq_iSupDirected, NeighborhoodSystem.mem_iSupDirected]
    constructor
    · rintro ⟨n, hn⟩; exact ⟨n, hn⟩
    · rintro ⟨n, hn⟩; exact ⟨n, hn⟩
  -- `h ∘ g = k` (the diagonal of the doubly-indexed directed family, via the
  -- ladder).
  have hgk : hh.comp gg = kk := by
    apply ApproximableMap.ext
    intro X Z
    constructor
    · rintro ⟨Y, hgXY, hhYZ⟩
      rw [G_fix_rel] at hgXY
      rw [H_fix_rel] at hhYZ
      obtain ⟨m, hm⟩ := hgXY
      obtain ⟨n, hn⟩ := hhYZ
      rw [K_fix_rel]
      refine ⟨max m n, ?_⟩
      rw [← ladder (max m n)]
      exact ⟨Y, G_mono (le_max_left m n) X Y hm, H_mono (le_max_right m n) Y Z hn⟩
    · intro hk
      rw [K_fix_rel] at hk
      obtain ⟨p, hp⟩ := hk
      rw [← ladder p] at hp
      obtain ⟨Y, hG, hHr⟩ := hp
      exact ⟨Y, (G_fix_rel X Y).mpr ⟨p, hG⟩, (H_fix_rel Y Z).mpr ⟨p, hHr⟩⟩
  -- `k ⊑ I_E`, because `I_E` is a fixed point of `k ↦ u ∘ T(k) ∘ v`.
  have hk_le : kk ≤ idMap E.sys := by
    have hstepeq : (toStrictMap (Opk.toElementMap
        (toStrictFilter (⟨idMap E.sys, isStrict_idMap⟩ : StrictMap E.sys E.sys)))).1
          = idMap E.sys := by
      have hs := opStep T E E isoE.inv isoE.hom hv hu ΦEE hΦEE
        (toStrictFilter (⟨idMap E.sys, isStrict_idMap⟩ : StrictMap E.sys E.sys))
      have hmapid : T.map (X := E) (Y := E) (idMap E.sys) = idMap (T.obj E).sys := T.map_id E
      rw [hs, show (toStrictMap (toStrictFilter
          (⟨idMap E.sys, isStrict_idMap⟩ : StrictMap E.sys E.sys))).1 = idMap E.sys from
          congrArg Subtype.val (toStrictMap_toStrictFilter _),
        hmapid, idMap_comp, huv]
    have hfp : Opk.toElementMap (toStrictFilter (⟨idMap E.sys,
      isStrict_idMap⟩ : StrictMap E.sys E.sys))
        = toStrictFilter (⟨idMap E.sys, isStrict_idMap⟩ : StrictMap E.sys E.sys) := by
      calc Opk.toElementMap (toStrictFilter ⟨idMap E.sys, isStrict_idMap⟩)
          = toStrictFilter (toStrictMap (Opk.toElementMap
              (toStrictFilter ⟨idMap E.sys, isStrict_idMap⟩))) :=
            (toStrictFilter_toStrictMap _).symm
        _ = toStrictFilter (⟨idMap E.sys, isStrict_idMap⟩ : StrictMap E.sys E.sys) := by
            congr 1
            apply Subtype.ext
            rw [hstepeq]
        _ = toStrictFilter ⟨idMap E.sys, isStrict_idMap⟩ := rfl
    have hle : Opk.fixElement ≤
      toStrictFilter (⟨idMap E.sys, isStrict_idMap⟩ : StrictMap E.sys E.sys) :=
      fixElement_le_of_toElementMap_le Opk (le_of_eq hfp)
    have hmono := toStrictMap_mono hle
    change (toStrictMap Opk.fixElement).1 ≤ idMap E.sys
    refine le_of_le_of_eq hmono ?_
    exact congrArg Subtype.val (toStrictMap_toStrictFilter _)
  -- `h` and `g` are algebra homomorphisms.
  let Balg : TAlgebra T := ⟨E, isoE.hom⟩
  have h_fixeq : hh = isoE.hom.comp ((T.map (X := Dalg.carrier) (Y := E) hh).comp isoD.inv) := by
    have hs := opStep T Dalg.carrier E isoD.inv isoE.hom hj hu ΦDE hΦDE Oph.fixElement
    rw [toElementMap_fixElement] at hs
    exact hs
  have h_comm : hh.comp isoD.hom = isoE.hom.comp (T.map (X := Dalg.carrier) (Y := E) hh) := by
    conv_lhs => rw [h_fixeq]
    rw [comp_assoc, comp_assoc, hji, comp_idMap]
  let h_alg : AlgHom Dalg Balg := { hom := hh, comm := h_comm }
  have g_fixeq : gg = isoD.hom.comp ((T.map (X := E) (Y := Dalg.carrier) gg).comp isoE.inv) := by
    have hs := opStep T E Dalg.carrier isoE.inv isoD.hom hv hi ΦED hΦED Opg.fixElement
    rw [toElementMap_fixElement] at hs
    exact hs
  have g_comm : gg.comp isoE.hom = isoD.hom.comp (T.map (X := E) (Y := Dalg.carrier) gg) := by
    conv_lhs => rw [g_fixeq]
    rw [comp_assoc, comp_assoc, hvu, comp_idMap]
  let g_alg : AlgHom Balg Dalg := { hom := gg, comm := g_comm }
  -- `g ∘ h = I_D` by initiality of `D`.
  have hgh_id : gg.comp hh = idMap Dalg.carrier.sys := by
    have huniq : g_alg.comp h_alg = AlgHom.id Dalg := by
      rw [hinit.uniq Dalg (g_alg.comp h_alg), hinit.uniq Dalg (AlgHom.id Dalg)]
    have hh2 := congrArg AlgHom.hom huniq
    exact hh2
  -- conclude via Lemma 6.15.
  exact trianglelefteq_of_projectionPair hh gg hgh_id (le_of_eq_of_le hgk hk_le)

end Domain.Neighborhood
