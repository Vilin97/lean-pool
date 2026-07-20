/-
Copyright (c) 2026 Catskills Research Company. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Catskills Research Company
-/

import LeanPool.DomainTheory.Neighborhood.Definition71
import LeanPool.DomainTheory.Neighborhood.Approximable

/-!
# Definition 7.2 (Scott 1981, PRG-19, §7) — computable maps and computable
elements

Following Dana Scott, *Lectures on a Mathematical Theory of Computation*, PRG-19,
Lecture VII,
*Computability in effectively given domains*.

> **Definition 7.2.** Given two recursively presented domains `𝒟 = {Xₙ ∣ n ∈ ℕ}`
and
> `ℰ = {Yₘ ∣ m ∈ ℕ}`, an approximable mapping `f : 𝒟 → ℰ` is said to be
*computable* iff the
> relation `Xₙ f Yₘ` is **recursively enumerable** in `n` and `m`.

Why r.e. (and not recursive)? Scott answers by degenerating `𝒟` to the one-point
domain `{Δ}`: then
`f` is just a single element `y = f({Δ}) ∈ |ℰ|`, and the condition reduces to the
index set
`{m ∣ Yₘ ∈ y}` being r.e. A *finite* element has a recursive index set, but an
infinite element can
only be approximated "a little at a time" — its approximations can be *listed*
(r.e.) but membership
need not be decidable. So 7.2 already incorporates the notion of a **computable
element**
(`IsComputableElement`).

We model `IsComputableMap` as `REPred₂ (fun n m ↦ Xₙ f Yₘ)` over the choice-free
recursion theory of
`Recursive.lean` (`REPred` = projection of a recursively decidable relation; see
that file for why we
roll our own and reject Mathlib's classical recursion theory).

**Proposition 7.3** is then formalized in full:

* `idMap_isComputable` — the identity map is computable, because `Xₙ I Xₘ ↔ Xₙ ⊆
Xₘ`
  (`ComputablePresentation.incl_computable`) is recursively *decidable*, hence
  r.e.
* `comp_isComputable` — the composition of computable maps is computable: `Xₙ
(g∘f) Zₖ` is
  `∃ Yₗ, Xₙ f Yₗ ∧ Yₗ g Zₖ` (surjectivity of the middle presentation lets `Y`
  range over indices
  `l`), which is r.e. by the closure lemmas
  `REPred.comp`/`REPred.and`/`REPred.proj`.
* `apply_isComputableElement` — Scott's stated consequence: a computable map
applied to a computable
  element gives a computable element (`f(x) = {Yₘ ∣ ∃ Xₙ ∈ x, Xₙ f Yₘ}`, again
  r.e. by the closure
  lemmas).

Two further faithful facts:

* `principal_isComputableElement` — every **finite** (principal) element `↑Xₙ` is
computable, since
  its index set `{m ∣ Xₙ ⊆ Xₘ}` is a recursive slice of `incl_computable` (Scott's
  remark that
  finite elements have recursive index sets).

Everything here is `⊆ {propext, Quot.sound}` (choice-free): it is built only from
the choice-free
deciders of Definition 7.1 and the choice-free r.e. layer of `Recursive.lean`.
-/

namespace Domain.Neighborhood

open NeighborhoodSystem Domain.Recursive ApproximableMap

variable {α β γ : Type*}

/-- **Definition 7.2 (Scott 1981, PRG-19) — computable map.** Relative to
computable presentations
`P` of `V` and `Q` of `W`, an approximable map `f : V → W` is *computable* iff its
neighbourhood
relation `Xₙ f Yₘ`, transported to the integer indices, is recursively enumerable. -/
def IsComputableMap {V : NeighborhoodSystem α} {W : NeighborhoodSystem β}
    (P : ComputablePresentation V) (Q : ComputablePresentation W) (f : ApproximableMap V W) :
      Prop :=
  REPred₂ (fun n m => f.rel (P.X n) (Q.X m))

/-- **Definition 7.2 (Scott 1981, PRG-19) — computable element.** Specializing to
`f : 𝟙 → W`, the
condition becomes: the index set `{m ∣ Yₘ ∈ y}` of the element `y ∈ |W|` is
recursively enumerable.
We take this as the definition of a *computable element*. -/
def IsComputableElement {W : NeighborhoodSystem β} (Q : ComputablePresentation W)
    (y : W.Element) : Prop :=
  REPred (fun m => y.mem (Q.X m))

variable {V : NeighborhoodSystem α} {W : NeighborhoodSystem β}

/-- **The identity map is computable** (the identity half of Proposition 7.3). The
relation
`Xₙ I Xₘ` is `Xₙ ⊆ Xₘ` (`incl_computable`), which is recursively *decidable*,
hence recursively
enumerable. -/
theorem idMap_isComputable (P : ComputablePresentation V) :
    IsComputableMap P P (idMap V) :=
  (RecDecidable.of_iff (fun t => by
    simp only [idMap_rel]
    exact ⟨fun h => h.2.2, fun h => ⟨P.mem_X _, P.mem_X _, h⟩⟩)
    P.incl_computable).re

/-- **Proposition 7.3 (Scott 1981, PRG-19) — composition of computable maps is
computable.** For
`X (g∘f) Z ↔ ∃ Y, X f Y ∧ Y g Z`, surjectivity of the middle presentation `Q` lets
the witness `Y`
range over indices `l` (`Y = Yₗ`); the resulting `∃ l, Xₙ f Yₗ ∧ Yₗ g Zₖ` is
recursively enumerable
by reindexing (`REPred.comp`), conjunction (`REPred.and`), and existential
projection
(`REPred.proj`). -/
theorem comp_isComputable {U : NeighborhoodSystem γ}
    {P : ComputablePresentation V} {Q : ComputablePresentation W} {R : ComputablePresentation U}
    {f : ApproximableMap V W} {g : ApproximableMap W U}
    (hf : IsComputableMap P Q f) (hg : IsComputableMap Q R g) :
    IsComputableMap P R (g.comp f) := by
  have hf' : REPred (fun s => f.rel (P.X s.unpair.1) (Q.X s.unpair.2)) := hf
  have hg' : REPred (fun s => g.rel (Q.X s.unpair.1) (R.X s.unpair.2)) := hg
  have hgf : Nat.Primrec (fun u => Nat.pair u.unpair.2.unpair.1 u.unpair.1) :=
    Nat.Primrec.pair (Nat.Primrec.left.comp Nat.Primrec.right) Nat.Primrec.left
  have hgg : Nat.Primrec (fun u => Nat.pair u.unpair.1 u.unpair.2.unpair.2) :=
    Nat.Primrec.pair Nat.Primrec.left (Nat.Primrec.right.comp Nat.Primrec.right)
  refine REPred.of_iff (fun t => ?_) ((hf'.comp hgf).and (hg'.comp hgg)).proj
  simp only [comp_rel, unpair_pair_fst, unpair_pair_snd]
  constructor
  · rintro ⟨Y, hfY, hgY⟩
    obtain ⟨l, rfl⟩ := Q.surj (g.rel_dom hgY)
    exact ⟨l, hfY, hgY⟩
  · rintro ⟨l, hfl, hgl⟩
    exact ⟨Q.X l, hfl, hgl⟩

/-- **Proposition 7.3 (consequence) (Scott 1981, PRG-19).** "If `f : 𝒟 → ℰ` is
computable and
`x ∈ |𝒟|` is computable, then `f(x) ∈ |ℰ|` is also computable." Here `f(x) = {Yₘ ∣
∃ Xₙ ∈ x, Xₙ f Yₘ}`
(`toElementMap`); surjectivity of `P` lets the witness `X` range over indices `n`,
and the resulting
`∃ n, Xₙ ∈ x ∧ Xₙ f Yₘ` is r.e. by `REPred.and`/`REPred.proj`. -/
theorem apply_isComputableElement {P : ComputablePresentation V} {Q : ComputablePresentation W}
    {f : ApproximableMap V W} (hf : IsComputableMap P Q f) {x : V.Element}
    (hx : IsComputableElement P x) : IsComputableElement Q (f.toElementMap x) := by
  have hf' : REPred (fun s => f.rel (P.X s.unpair.1) (Q.X s.unpair.2)) := hf
  have hx' : REPred (fun n => x.mem (P.X n)) := hx
  refine REPred.of_iff (fun m => ?_) ((hx'.comp Nat.Primrec.left).and hf').proj
  simp only [mem_toElementMap, unpair_pair_fst, unpair_pair_snd]
  constructor
  · rintro ⟨X, hX, hfX⟩
    obtain ⟨n, rfl⟩ := P.surj (x.sub hX)
    exact ⟨n, hX, hfX⟩
  · rintro ⟨n, hxn, hfn⟩
    exact ⟨P.X n, hxn, hfn⟩

/-- **Every finite (principal) element is computable** (Scott's remark after 7.2:
"If `y` were
finite, the set of indices would be recursive"). For the finite element `↑Xₙ`, the
index set
`{m ∣ Xₙ ⊆ Xₘ}` is a recursive slice of `incl_computable` (fix the first index to
`n` by the
primitive-recursive reindex `m ↦ ⟨n, m⟩`), hence r.e. -/
theorem principal_isComputableElement (P : ComputablePresentation V) (n : ℕ) :
    IsComputableElement P (V.principal (P.mem_X n)) := by
  have hg : Nat.Primrec (fun m => Nat.pair n m) :=
    ((Nat.Primrec.const n).pair primrec_id).of_eq (fun _ => rfl)
  have hrec : RecDecidable (fun m => P.X n ⊆ P.X m) :=
    RecDecidable.of_iff (fun m => by simp only [unpair_pair_fst, unpair_pair_snd])
      (P.incl_computable.comp hg)
  refine (RecDecidable.of_iff (fun m => ?_) hrec).re
  simp only [mem_principal]
  exact ⟨fun h => h.2, fun h => ⟨P.mem_X m, h⟩⟩

end Domain.Neighborhood
