/-
Copyright (c) 2026 Catskills Research Company. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Catskills Research Company
-/

import LeanPool.DomainTheory.Neighborhood.Basic

/-!
# Theorem 1.10 (Scott 1981, PRG-19, §1) — the element-token system `{[X]}`

Given any neighbourhood system `𝒟`, Scott replaces the tokens `Δ` by the
*elements* `|𝒟|`
themselves: for `X ∈ 𝒟` put

`[X] = {x ∈ |𝒟| ∣ X ∈ x}`,

the set of elements that contain `X`. The family `{[X] ∣ X ∈ 𝒟}` is a
neighbourhood system over
`|𝒟|`, and it determines a domain *isomorphic* to `|𝒟|` (Definition 1.9). "The
rôle of the tokens
is simply to keep the inclusions (and intersections) of neighbourhoods sorted
out."

We prove Scott's four facts:

* (1) `[Δ] = |𝒟|`                              — `bracket_master`;
* (2) `X, Y` consistent in `𝒟` iff `[X]∩[Y] ≠ ∅` — `bracket_inter_nonempty_iff`;
* (3) `[X] ∩ [Y] = [X ∩ Y]` (for `X, Y ∈ 𝒟`)   — `bracket_inter`;
* (4) `↑X ∈ [X]`                               — `principal_mem_bracket`;

together with the one-one (`bracket_injective`), inclusion-preserving
(`bracket_subset_iff`)
correspondence `X ↦ [X]`, and finally the induced order-isomorphism `tokenIso :
|𝒟| ≃o |{[X]}|`,
giving `𝒟 ≅ᴰ tokenSystem` (`isomorphic_tokenSystem`).

Everything is constructive (`[propext, Quot.sound]`): `[X]`-membership is just
`x.mem X`, and the
filter laws mirror the constructive proofs for `principal`.
-/

namespace Domain.Neighborhood

namespace NeighborhoodSystem

variable {α : Type*} (V : NeighborhoodSystem α)

/-- Scott's `[X] = {x ∈ |𝒟| ∣ X ∈ x}`: the elements of `|𝒟|` that contain the
neighbourhood `X`.
(This is the `basicOpen X` of Exercise 1.22, repeated here to avoid the topology
dependency.) -/
def bracket (X : Set α) : Set V.Element := {x | x.mem X}

@[simp] theorem mem_bracket {X : Set α} {x : V.Element} : x ∈ V.bracket X ↔ x.mem X := Iff.rfl

/-- **Theorem 1.10 (1).** `[Δ] = |𝒟|`: every element contains the master
neighbourhood. -/
@[simp] theorem bracket_master : V.bracket V.master = Set.univ := by
  ext x; simp only [mem_bracket, Set.mem_univ, iff_true]; exact x.master_mem

/-- **Theorem 1.10 (4).** `↑X ∈ [X]`: the principal filter of `X` contains `X`. -/
theorem principal_mem_bracket {X : Set α} (hX : V.mem X) : V.principal hX ∈ V.bracket X :=
  ⟨hX, subset_rfl⟩

/-- **Theorem 1.10 (3).** `[X] ∩ [Y] = [X ∩ Y]` for `X, Y ∈ 𝒟`. (`⊆` is filter
closure under `∩`;
`⊇` is upward closure along `X ∩ Y ⊆ X`, `X ∩ Y ⊆ Y`.) -/
theorem bracket_inter {X Y : Set α} (hX : V.mem X) (hY : V.mem Y) :
    V.bracket X ∩ V.bracket Y = V.bracket (X ∩ Y) := by
  ext x
  simp only [Set.mem_inter_iff, mem_bracket]
  constructor
  · rintro ⟨hx, hy⟩
    exact x.inter_mem hx hy
  · intro hxy
    exact ⟨x.up_mem hxy hX Set.inter_subset_left, x.up_mem hxy hY Set.inter_subset_right⟩

/-- **The correspondence `X ↦ [X]` is inclusion-preserving.** `[X] ⊆ [Y] ↔ X ⊆ Y`
(for `X,Y ∈ 𝒟`).
`→` tests at `↑X ∈ [X]`, reading `X ⊆ Y` off `↑X ∈ [Y]`; `←` is upward closure. -/
theorem bracket_subset_iff {X Y : Set α} (hX : V.mem X) (hY : V.mem Y) :
    V.bracket X ⊆ V.bracket Y ↔ X ⊆ Y := by
  constructor
  · intro h
    exact (h (V.principal_mem_bracket hX)).2
  · intro hXY x hx
    exact x.up_mem hx hY hXY

/-- **The correspondence `X ↦ [X]` is one-one.** `[X] = [Y] ⟹ X = Y` (for `X,Y ∈
𝒟`). -/
theorem bracket_injective {X Y : Set α} (hX : V.mem X) (hY : V.mem Y)
    (h : V.bracket X = V.bracket Y) : X = Y :=
  Set.Subset.antisymm ((V.bracket_subset_iff hX hY).mp h.subset)
    ((V.bracket_subset_iff hY hX).mp h.superset)

/-- **Theorem 1.10 (2).** `X, Y` are consistent in `𝒟` (have a common lower bound
`Z ∈ 𝒟`,
`Z ⊆ X ∩ Y`) iff `[X] ∩ [Y] ≠ ∅`. `→` uses `↑Z` (which lies in both `[X]` and
`[Y]`); `←` reads a
witness off any common element. -/
theorem bracket_inter_nonempty_iff {X Y : Set α} (hX : V.mem X) (hY : V.mem Y) :
    (V.bracket X ∩ V.bracket Y).Nonempty ↔ ∃ Z, V.mem Z ∧ Z ⊆ X ∩ Y := by
  constructor
  · rintro ⟨x, hxX, hxY⟩
    exact ⟨X ∩ Y, x.sub (x.inter_mem hxX hxY), subset_rfl⟩
  · rintro ⟨Z, hZ, hZsub⟩
    refine ⟨V.principal hZ, ?_, ?_⟩
    · exact ⟨hX, hZsub.trans Set.inter_subset_left⟩
    · exact ⟨hY, hZsub.trans Set.inter_subset_right⟩

/-! ### The token system `{[X]}` and the isomorphism. -/

/-- **Theorem 1.10.** The *element-token system* `{[X] ∣ X ∈ 𝒟}` over the tokens
`|𝒟|`. The two
laws reduce to facts about `[·]`: the master `[Δ] = |𝒟|` is the whole space; the
consistency
witness `[W]` for `[X] ∩ [Y]` yields `W ⊆ X ∩ Y` (via `↑W`), so `X ∩ Y ∈ 𝒟` and
`[X] ∩ [Y] = [X ∩ Y]`. -/
def tokenSystem : NeighborhoodSystem V.Element where
  mem S := ∃ X, V.mem X ∧ S = V.bracket X
  master := Set.univ
  master_mem := ⟨V.master, V.master_mem, V.bracket_master.symm⟩
  inter_mem := by
    rintro S T W ⟨X, hX, rfl⟩ ⟨Y, hY, rfl⟩ ⟨Z, hZ, rfl⟩ hWsub
    have hpz := hWsub (V.principal_mem_bracket hZ)
    obtain ⟨hzX, hzY⟩ := hpz
    have hXY : V.mem (X ∩ Y) := V.inter_mem hX hY hZ (Set.subset_inter hzX.2 hzY.2)
    exact ⟨X ∩ Y, hXY, V.bracket_inter hX hY⟩
  sub_master := fun _ => Set.subset_univ _

@[simp] theorem tokenSystem_mem {S : Set V.Element} :
    V.tokenSystem.mem S ↔ ∃ X, V.mem X ∧ S = V.bracket X := Iff.rfl

/-- The element of `|{[X]}|` corresponding to `x ∈ |𝒟|`: the filter `{[X] ∣ X ∈
x}`. -/
def toToken (x : V.Element) : V.tokenSystem.Element where
  mem S := ∃ X, x.mem X ∧ S = V.bracket X
  sub := by rintro S ⟨X, hX, rfl⟩; exact ⟨X, x.sub hX, rfl⟩
  master_mem := ⟨V.master, x.master_mem, V.bracket_master.symm⟩
  inter_mem := by
    rintro S T ⟨X, hX, rfl⟩ ⟨Y, hY, rfl⟩
    exact ⟨X ∩ Y, x.inter_mem hX hY, V.bracket_inter (x.sub hX) (x.sub hY)⟩
  up_mem := by
    rintro S T ⟨X, hX, rfl⟩ hT hsub
    obtain ⟨Y, hYmem, rfl⟩ := hT
    exact ⟨Y, x.up_mem hX hYmem ((V.bracket_subset_iff (x.sub hX) hYmem).mp hsub), rfl⟩

/-- The element of `|𝒟|` corresponding to `y ∈ |{[X]}|`: the filter `{X ∣ [X] ∈
y}`. -/
def ofToken (y : V.tokenSystem.Element) : V.Element where
  mem X := V.mem X ∧ y.mem (V.bracket X)
  sub h := h.1
  master_mem := ⟨V.master_mem, by rw [V.bracket_master]; exact y.master_mem⟩
  inter_mem := by
    rintro X Y ⟨hX, hyX⟩ ⟨hY, hyY⟩
    have hyInter : y.mem (V.bracket X ∩ V.bracket Y) := y.inter_mem hyX hyY
    obtain ⟨W, hW, hWeq⟩ := y.sub hyInter
    have hpw := V.principal_mem_bracket hW
    rw [← hWeq] at hpw
    obtain ⟨hwX, hwY⟩ := hpw
    have hXY : V.mem (X ∩ Y) := V.inter_mem hX hY hW (Set.subset_inter hwX.2 hwY.2)
    refine ⟨hXY, ?_⟩
    rw [← V.bracket_inter hX hY]
    exact hyInter
  up_mem := by
    rintro X Y ⟨hX, hyX⟩ hY hXY
    exact ⟨hY, y.up_mem hyX ⟨Y, hY, rfl⟩ ((V.bracket_subset_iff hX hY).mpr hXY)⟩

/-- **Theorem 1.10 (the isomorphism).** `X ↦ [X]` induces an order-isomorphism
`|𝒟| ≃o |{[X]}|`:
`toToken` and `ofToken` are mutually inverse and preserve/reflect `⊑`. -/
def tokenIso : V.Element ≃o V.tokenSystem.Element where
  toFun := V.toToken
  invFun := V.ofToken
  left_inv := by
    intro x
    apply Element.ext
    intro X
    constructor
    · rintro ⟨hX, X', hX', heq⟩
      rw [V.bracket_injective hX (x.sub hX') heq]; exact hX'
    · intro hx
      exact ⟨x.sub hx, X, hx, rfl⟩
  right_inv := by
    intro y
    apply Element.ext
    intro S
    constructor
    · rintro ⟨X, ⟨_, hyX⟩, rfl⟩
      exact hyX
    · intro hyS
      obtain ⟨X, hX, rfl⟩ := y.sub hyS
      exact ⟨X, ⟨hX, hyS⟩, rfl⟩
  map_rel_iff' := by
    intro x x'
    constructor
    · intro h X hx
      have hmem : (V.toToken x).mem (V.bracket X) := ⟨X, hx, rfl⟩
      obtain ⟨X', hX', heq⟩ := h (V.bracket X) hmem
      rw [V.bracket_injective (x.sub hx) (x'.sub hX') heq]; exact hX'
    · intro h S hS
      obtain ⟨X, hX, rfl⟩ := hS
      exact ⟨X, h X hX, rfl⟩

/-- **Theorem 1.10 (statement).** Any neighbourhood system is isomorphic to its
element-token
system: `𝒟 ≅ᴰ {[X]}`. -/
theorem isomorphic_tokenSystem : V ≅ᴰ V.tokenSystem := ⟨V.tokenIso⟩

end NeighborhoodSystem

end Domain.Neighborhood
