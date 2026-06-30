/-
Copyright (c) 2026 Catskills Research Company. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Catskills Research Company
-/

import LeanPool.DomainTheory.Neighborhood.Example24
import LeanPool.DomainTheory.Neighborhood.ApproximableExercises

/-!
# Exercise 2.18 (Scott 1981, PRG-19, §2) — the "spacing" map `h : 𝔹 → 𝔹`

> **EXERCISE 2.18.** What is the meaning in words of the approximable mapping `h :
𝔹 → 𝔹`, where
> `h(0x) = 00 h(x)` and `h(1x) = 10 h(x)` for all `x ∈ |𝔹|`? Is `h` an
isomorphism? Does there exist
> a map `k : 𝔹 → 𝔹` where `k ∘ h = I_𝔹`, and is `k` one-one?

**Meaning in words.** `h` *spaces the sequence out*: it copies each input symbol
`b` and inserts a
`0` immediately after it. So the input bit `b` becomes the block `b0`, and `h`
doubles the length of
every sequence, planting a `0` in every odd position (0-indexed positions `1, 3,
5, …`).

We follow the `Example24.runMap` template: a guaranteed-output function on finite
prefixes drives the
neighbourhood relation `X h Y ↔ ∃ σ, X = σΣ* ∧ Y ∈ 𝔹 ∧ (hOut σ)Σ* ⊆ Y`.

* `hOut σ` — the doubling of `σ` (each `b ↦ b0`); `hMap : ApproximableMap B B`.
* `kOut τ` — the left inverse on prefixes: keep the first bit of every *complete*
pair, drop the
  inserted `0`; `kMap : ApproximableMap B B`. Key identity: `kOut (hOut σ) = σ`.
* `kMap_comp_hMap` — **`k ∘ h = I_𝔹`** (so the required `k` exists).
* `kMap_not_injective` — **`k` is *not* one-one**: `↑(0Σ*)` and `↑(1Σ*)` both map
to `⊥` (the first
  bit of a length-1 prefix is an incomplete pair, hence dropped).
* `hMap_not_surjective` — **`h` is *not* an isomorphism**: it is not surjective
(e.g. `↑(01Σ*)` is
  not in the range, since `h` only produces sequences with `0` in every odd
  position). `h` *is*
  injective (it has the left inverse `k`), so it is injective-but-not-surjective.

Choice-free (`#print axioms ⊆ {propext, Quot.sound}`): everything is decidable
list surgery. -/

namespace Domain.Neighborhood.Exercise218

open Domain.Neighborhood NeighborhoodSystem ExampleB ApproximableMap

/-! ### The doubling output `hOut` and its monotonicity. -/

/-- The guaranteed output of `h` on a finite prefix: each symbol `b` becomes the
block `b0`. -/
def hOut : Str → Str
  | [] => []
  | b :: t => b :: false :: hOut t

@[simp] theorem hOut_nil : hOut [] = [] := rfl
@[simp] theorem hOut_cons (b : Bool) (t : Str) : hOut (b :: t) = b :: false :: hOut t := rfl

/-- `hOut` grows under extension: `hOut σ <+: hOut (σ ++ t)`. -/
theorem hOut_append (σ t : Str) : hOut σ <+: hOut (σ ++ t) := by
  induction σ with
  | nil => simp
  | cons b s ih =>
    simp only [List.cons_append, hOut_cons]
    obtain ⟨u, hu⟩ := ih
    exact ⟨u, by rw [List.cons_append, List.cons_append, hu]⟩

/-- **Prefix-monotonicity of `hOut`.** `σ <+: σ' → hOut σ <+: hOut σ'`. -/
theorem hOut_mono {σ σ' : Str} (h : σ <+: σ') : hOut σ <+: hOut σ' := by
  obtain ⟨t, rfl⟩ := h
  exact hOut_append σ t

/-! ### The inverse output `kOut` and its monotonicity. -/

/-- The guaranteed output of `k` on a finite prefix: keep the first bit of every
*complete* pair,
discard the inserted `0`. A trailing odd bit is an incomplete pair, hence dropped. -/
def kOut : Str → Str
  | [] => []
  | [_] => []
  | b :: _ :: t => b :: kOut t

@[simp] theorem kOut_nil : kOut [] = [] := rfl
@[simp] theorem kOut_single (b : Bool) : kOut [b] = [] := rfl
@[simp] theorem kOut_cons (b c : Bool) (t : Str) : kOut (b :: c :: t) = b :: kOut t := rfl

/-- **`k` inverts `h` on prefixes.** `kOut (hOut σ) = σ`. -/
theorem kOut_hOut (σ : Str) : kOut (hOut σ) = σ := by
  induction σ with
  | nil => rfl
  | cons b t ih => simp only [hOut_cons, kOut_cons, ih]

/-- `kOut` grows under extension: `kOut σ <+: kOut (σ ++ t)`. -/
theorem kOut_append (σ t : Str) : kOut σ <+: kOut (σ ++ t) := by
  induction σ using kOut.induct with
  | case1 => simp
  | case2 _ => simp
  | case3 b c t' ih =>
    simp only [List.cons_append, kOut_cons]
    obtain ⟨u, hu⟩ := ih
    exact ⟨u, by rw [List.cons_append, hu]⟩

/-- **Prefix-monotonicity of `kOut`.** `σ <+: σ' → kOut σ <+: kOut σ'`. -/
theorem kOut_mono {σ σ' : Str} (h : σ <+: σ') : kOut σ <+: kOut σ' := by
  obtain ⟨t, rfl⟩ := h
  exact kOut_append σ t

/-! ### The approximable maps `hMap` and `kMap`. -/

/-- **Exercise 2.18 — the spacing map `h : 𝔹 → 𝔹`.** `X h Y ↔ ∃ σ, X = σΣ* ∧ Y ∈ 𝔹
∧ (hOut σ)Σ*
⊆ Y`.
Same shape as `Example24.runMap`, with the doubling `hOut` (`hOut_mono` gives
Definition 2.1(iii)). -/
def hMap : ApproximableMap B B where
  rel X Y := ∃ σ, X = cone σ ∧ B.mem Y ∧ cone (hOut σ) ⊆ Y
  rel_dom := fun ⟨σ, hX, _, _⟩ => ⟨σ, hX⟩
  rel_cod := fun ⟨_, _, hYmem, _⟩ => hYmem
  master_rel := by
    refine ⟨[], (B_master).trans cone_nil.symm, B.master_mem, ?_⟩
    rw [hOut_nil, B_master, cone_nil]
  inter_right := by
    rintro X Y Y' ⟨σ, hX, hYmem, hYsub⟩ ⟨σ', hX', hY'mem, hY'sub⟩
    have hσ : σ = σ' := cone_injective (hX ▸ hX')
    subst hσ
    have hsub : cone (hOut σ) ⊆ Y ∩ Y' := Set.subset_inter hYsub hY'sub
    exact ⟨σ, hX, B.inter_mem hYmem hY'mem (memB_cone (hOut σ)) hsub, hsub⟩
  mono := by
    rintro X X' Y Y' ⟨σ, hX, _, hYsub⟩ hX'X hYY' hX'mem hY'mem
    obtain ⟨σ', hX'cone⟩ := hX'mem
    have hpre : σ <+: σ' := by
      apply cone_subset_cone.mp; rw [← hX'cone, ← hX]; exact hX'X
    have hcone : cone (hOut σ') ⊆ cone (hOut σ) := cone_subset_cone.mpr (hOut_mono hpre)
    exact ⟨σ', hX'cone, hY'mem, (hcone.trans hYsub).trans hYY'⟩

/-- **Exercise 2.18 — the left inverse `k : 𝔹 → 𝔹`.** `X k Y ↔ ∃ σ, X = σΣ* ∧ Y ∈
𝔹 ∧ (kOut σ)Σ*
⊆ Y`. -/
def kMap : ApproximableMap B B where
  rel X Y := ∃ σ, X = cone σ ∧ B.mem Y ∧ cone (kOut σ) ⊆ Y
  rel_dom := fun ⟨σ, hX, _, _⟩ => ⟨σ, hX⟩
  rel_cod := fun ⟨_, _, hYmem, _⟩ => hYmem
  master_rel := by
    refine ⟨[], (B_master).trans cone_nil.symm, B.master_mem, ?_⟩
    rw [kOut_nil, B_master, cone_nil]
  inter_right := by
    rintro X Y Y' ⟨σ, hX, hYmem, hYsub⟩ ⟨σ', hX', hY'mem, hY'sub⟩
    have hσ : σ = σ' := cone_injective (hX ▸ hX')
    subst hσ
    have hsub : cone (kOut σ) ⊆ Y ∩ Y' := Set.subset_inter hYsub hY'sub
    exact ⟨σ, hX, B.inter_mem hYmem hY'mem (memB_cone (kOut σ)) hsub, hsub⟩
  mono := by
    rintro X X' Y Y' ⟨σ, hX, _, hYsub⟩ hX'X hYY' hX'mem hY'mem
    obtain ⟨σ', hX'cone⟩ := hX'mem
    have hpre : σ <+: σ' := by
      apply cone_subset_cone.mp; rw [← hX'cone, ← hX]; exact hX'X
    have hcone : cone (kOut σ') ⊆ cone (kOut σ) := cone_subset_cone.mpr (kOut_mono hpre)
    exact ⟨σ', hX'cone, hY'mem, (hcone.trans hYsub).trans hYY'⟩

/-- The elementwise value of `hMap` on the finite element `↑(σΣ*)` is `↑((hOut
σ)Σ*)`. -/
theorem toElementMap_hMap_cone (σ : Str) :
    hMap.toElementMap (B.principal (memB_cone σ)) = B.principal (memB_cone (hOut σ)) := by
  apply Element.ext
  intro Y
  rw [← hMap.rel_iff_mem_principal (memB_cone σ), mem_principal]
  constructor
  · rintro ⟨ρ, hcone, hYmem, hsub⟩
    have : σ = ρ := cone_injective hcone
    subst this
    exact ⟨hYmem, hsub⟩
  · rintro ⟨hYmem, hsub⟩
    exact ⟨σ, rfl, hYmem, hsub⟩

/-- The elementwise value of `kMap` on the finite element `↑(σΣ*)` is `↑((kOut
σ)Σ*)`. -/
theorem toElementMap_kMap_cone (σ : Str) :
    kMap.toElementMap (B.principal (memB_cone σ)) = B.principal (memB_cone (kOut σ)) := by
  apply Element.ext
  intro Y
  rw [← kMap.rel_iff_mem_principal (memB_cone σ), mem_principal]
  constructor
  · rintro ⟨ρ, hcone, hYmem, hsub⟩
    have : σ = ρ := cone_injective hcone
    subst this
    exact ⟨hYmem, hsub⟩
  · rintro ⟨hYmem, hsub⟩
    exact ⟨σ, rfl, hYmem, hsub⟩

/-! ### `k ∘ h = I`, `k` not injective, `h` not surjective. -/

/-- **Exercise 2.18 — `k ∘ h = I_𝔹`.** The composite recovers the identity:
reading `kOut (hOut
σ) = σ`
through the cone relations. -/
theorem kMap_comp_hMap : kMap.comp hMap = idMap B := by
  apply ApproximableMap.ext
  intro X Z
  rw [comp_rel, idMap_rel]
  constructor
  · rintro ⟨Y, ⟨σ, hXcone, _, hYsub⟩, τ, hYcone, hZmem, hZsub⟩
    refine ⟨⟨σ, hXcone⟩, hZmem, ?_⟩
    have hτ : τ <+: hOut σ := cone_subset_cone.mp (hYcone ▸ hYsub)
    have hτσ : kOut τ <+: σ := by have := kOut_mono hτ; rwa [kOut_hOut] at this
    calc X = cone σ := hXcone
      _ ⊆ cone (kOut τ) := cone_subset_cone.mpr hτσ
      _ ⊆ Z := hZsub
  · rintro ⟨⟨σ, hXcone⟩, hZmem, hXZ⟩
    refine ⟨cone (hOut σ), ⟨σ, hXcone, memB_cone (hOut σ), subset_rfl⟩, hOut σ, rfl, hZmem, ?_⟩
    rw [kOut_hOut, hXcone] at *
    exact hXZ

/-- **Exercise 2.18 — `k` is not one-one.** `↑(0Σ*)` and `↑(1Σ*)` are distinct
finite elements that
`k` collapses to `⊥` (a length-1 prefix is an incomplete pair, so its bit is
dropped). -/
theorem kMap_not_injective : ¬ Function.Injective kMap.toElementMap := by
  intro hinj
  have h1 : kMap.toElementMap (B.principal (memB_cone [false]))
      = kMap.toElementMap (B.principal (memB_cone [true])) := by
    rw [toElementMap_kMap_cone, toElementMap_kMap_cone]; rfl
  have h2 := hinj h1
  have hcone := cone_injective (B.principal_injective (memB_cone _) (memB_cone _) h2)
  simp at hcone

/-- **Exercise 2.18 — `h` is not an isomorphism.** It is not surjective: `↑(01Σ*)`
is not in the
range (any preimage `x` satisfies `x = k(h(x))`, forcing `h(x) = ↑(00Σ*) ≠
↑(01Σ*)`). -/
theorem hMap_not_surjective : ¬ Function.Surjective hMap.toElementMap := by
  intro hsurj
  obtain ⟨x, hx⟩ := hsurj (B.principal (memB_cone [false, true]))
  have hkhx : kMap.toElementMap (hMap.toElementMap x) = x := by
    rw [← toElementMap_comp, kMap_comp_hMap, toElementMap_idMap]
  rw [hx, toElementMap_kMap_cone] at hkhx
  rw [← hkhx, toElementMap_hMap_cone] at hx
  have hcone := cone_injective (B.principal_injective (memB_cone _) (memB_cone _) hx)
  simp at hcone

end Domain.Neighborhood.Exercise218
