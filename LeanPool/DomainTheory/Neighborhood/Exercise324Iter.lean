/-
Copyright (c) 2026 Catskills Research Company. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Catskills Research Company
-/

import LeanPool.DomainTheory.Neighborhood.Exercise316
import LeanPool.DomainTheory.Neighborhood.FunctionSpace

/-!
# Exercise 3.24(ii) (Scott 1981, PRG-19, §3) — `(𝒟₀ → 𝒟₁^∞) ≅ (𝒟₀ → 𝒟₁)^∞`

Using the infinite iterate `𝒟^∞` of Exercise 3.16 and the function space `(𝒟₀ →
𝒟₁)` of
Definition 3.8 / Theorem 3.10, we establish Scott's isomorphism (ii):

`(𝒟₀ → 𝒟₁^∞) ≅ (𝒟₀ → 𝒟₁)^∞`.

The crux is the order-isomorphism *on approximable maps*

`funIterEquiv : Hom(𝒟₀, 𝒟₁^∞) ≃o (ℕ → Hom(𝒟₀, 𝒟₁))`,

`f ↦ (n ↦ projₙ ∘ f)` with inverse the "infinite pairing" `g ↦ mapOfSeq g`, whose
value is the
sequence `mapOfSeq g (x) = ⟨gₙ(x)⟩ₙ`. Transporting through Theorem 3.10's
`funSpaceEquiv` (twice,
the second time pointwise via `OrderIso.piCongrRight`) and Exercise 3.16's
`iterSeqEquiv` yields the
domain isomorphism.

Everything is **choice-free in spirit**; the only classical input is inherited
from `Element.ext`,
`funSpaceEquiv` and the `choose` in the `∃/∀`-swap lemma, exactly as elsewhere in
§3.
-/

namespace Domain.Neighborhood

open NeighborhoodSystem ApproximableMap

variable {α β : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}

/-- The "infinite pairing" map `𝒟₀ → 𝒟₁^∞` of a sequence `g : ℕ → Hom(𝒟₀, 𝒟₁)`:
`X (mapOfSeq g) W ↔ X ∈ 𝒟₀, W ∈ 𝒟₁^∞, and X gᵢ (fiber W i) for all i`. -/
def mapOfSeq (g : ℕ → ApproximableMap V₀ V₁) : ApproximableMap V₀ (iterSys V₁) where
  rel X W := V₀.mem X ∧ (iterSys V₁).mem W ∧ ∀ i, (g i).rel X (fiber W i)
  rel_dom h := h.1
  rel_cod h := h.2.1
  master_rel := ⟨V₀.master_mem, (iterSys V₁).master_mem, fun i => by
    rw [fiber_iterSys_master]; exact (g i).master_rel⟩
  inter_right := by
    rintro X W W' ⟨hX, hW, hrel⟩ ⟨_, hW', hrel'⟩
    refine ⟨hX, ⟨fun i => (g i).rel_cod ((g i).inter_right (hrel i) (hrel' i)), ?_⟩,
      fun i => (g i).inter_right (hrel i) (hrel' i)⟩
    obtain ⟨NW, hNW⟩ := hW.2
    obtain ⟨NW', hNW'⟩ := hW'.2
    refine ⟨max NW NW', fun i hi => ?_⟩
    rw [fiber_inter, hNW i (le_trans (le_max_left _ _) hi),
      hNW' i (le_trans (le_max_right _ _) hi), Set.inter_self]
  mono := by
    rintro X X' W W' ⟨_, _, hrel⟩ hX'X hWW' hX' hW'
    exact ⟨hX', hW', fun i => (g i).mono (hrel i) hX'X (fiber_mono hWW' i) hX' (hW'.1 i)⟩

/-- The `∃/∀`-swap behind `mapOfSeq`: a single input neighbourhood `X ∈ x` works
for all coordinates
iff each coordinate has its own (intersect the finitely many non-trivial ones). -/
theorem exists_forall_swap {x : V₀.Element} {W : Set (ℕ × β)}
    {g : ℕ → ApproximableMap V₀ V₁} (hW : (iterSys V₁).mem W) :
    (∃ X, x.mem X ∧ ∀ i, (g i).rel X (fiber W i)) ↔
      (∀ i, ∃ X, x.mem X ∧ (g i).rel X (fiber W i)) := by
  constructor
  · rintro ⟨X, hXx, hall⟩ i; exact ⟨X, hXx, hall i⟩
  · intro hall
    obtain ⟨N, hN⟩ := hW.2
    choose Xs hXx hXrel using hall
    have hbase : x.mem (V₀.interUpTo Xs N) := x.mem_interUpTo Xs (n := N) (fun i _ => hXx i)
    refine ⟨V₀.interUpTo Xs N, hbase, fun i => ?_⟩
    by_cases h : i < N
    · exact (g i).mono (hXrel i) (V₀.interUpTo_subset Xs h) subset_rfl (x.sub hbase)
        ((g i).rel_cod (hXrel i))
    · rw [hN i (not_lt.mp h)]; exact (g i).rel_master (x.sub hbase)

/-- The value of `mapOfSeq g` is the sequence of values `⟨gᵢ(x)⟩`. -/
theorem toElementMap_mapOfSeq (g : ℕ → ApproximableMap V₀ V₁) (x : V₀.Element) :
    (mapOfSeq g).toElementMap x = ofSeq (fun i => (g i).toElementMap x) := by
  apply Element.ext
  intro W
  constructor
  · rintro ⟨X, hXx, _, hW, hrel⟩
    exact ⟨hW, fun i => ⟨X, hXx, hrel i⟩⟩
  · rintro ⟨hW, hfib⟩
    obtain ⟨X, hXx, hrel⟩ := (exists_forall_swap hW).mpr (fun i => hfib i)
    exact ⟨X, hXx, x.sub hXx, hW, hrel⟩

/-- `projₙ ∘ f` is monotone in `f`. -/
theorem projComp_mono {f f' : ApproximableMap V₀ (iterSys V₁)} (h : f ≤ f') (n : ℕ) :
    (projN V₁ n).comp f ≤ (projN V₁ n).comp f' := by
  rintro X Y ⟨W, hfXW, hWY⟩
  exact ⟨W, h X W hfXW, hWY⟩

/-- A map `𝒟₀ → 𝒟₁^∞` is detected coordinate-wise: `f ⊑ f'` iff `projₙ ∘ f ⊑ projₙ
∘ f'` for all
`n`. -/
theorem le_of_projComp_le {f f' : ApproximableMap V₀ (iterSys V₁)}
    (h : ∀ n, (projN V₁ n).comp f ≤ (projN V₁ n).comp f') : f ≤ f' := by
  rw [le_iff_toElementMap_le]
  intro x
  apply le_of_component_le
  intro n
  have hx := (le_iff_toElementMap_le.mp (h n)) x
  rwa [toElementMap_comp, toElementMap_comp, toElementMap_projN, toElementMap_projN] at hx

/-- **Exercise 3.24(ii) (Scott 1981, PRG-19).** The order-isomorphism on
approximable maps
`Hom(𝒟₀, 𝒟₁^∞) ≃o (ℕ → Hom(𝒟₀, 𝒟₁))`, `f ↦ (n ↦ projₙ ∘ f)`. -/
def funIterEquiv (V₀ : NeighborhoodSystem α) (V₁ : NeighborhoodSystem β) :
    ApproximableMap V₀ (iterSys V₁) ≃o (∀ _ : ℕ, ApproximableMap V₀ V₁) where
  toFun f := fun n => (projN V₁ n).comp f
  invFun g := mapOfSeq g
  left_inv f := by
    apply ext_of_toElementMap
    intro x
    rw [toElementMap_mapOfSeq]
    have hfun : (fun i => ((projN V₁ i).comp f).toElementMap x)
        = (fun i => component (f.toElementMap x) i) := by
      funext i; rw [toElementMap_comp, toElementMap_projN]
    rw [hfun, ofSeq_component]
  right_inv g := by
    funext n
    apply ext_of_toElementMap
    intro x
    rw [toElementMap_comp, toElementMap_mapOfSeq, toElementMap_projN, component_ofSeq]
  map_rel_iff' := by
    intro f f'
    constructor
    · intro h; exact le_of_projComp_le (fun n => h n)
    · intro h n; exact projComp_mono h n

/-- A pointwise family of order-isomorphisms induces one on the dependent product. -/
def piCongrOrderIso {ι : Type*} {A B : ι → Type*} [∀ i, Preorder (A i)] [∀ i, Preorder (B i)]
    (e : ∀ i, A i ≃o B i) : (∀ i, A i) ≃o (∀ i, B i) where
  toFun f := fun i => e i (f i)
  invFun g := fun i => (e i).symm (g i)
  left_inv f := by funext i; simp
  right_inv g := by funext i; simp
  map_rel_iff' := by
    intro f g
    exact ⟨fun h i => (e i).le_iff_le.mp (h i), fun h i => (e i).le_iff_le.mpr (h i)⟩

/-- **Exercise 3.24(ii) (Scott 1981, PRG-19).** The domain isomorphism
`|𝒟₀ → 𝒟₁^∞| ≃o |(𝒟₀ → 𝒟₁)^∞|`. -/
def funIterIso (V₀ : NeighborhoodSystem α) (V₁ : NeighborhoodSystem β) :
    (funSpace V₀ (iterSys V₁)).Element ≃o (iterSys (funSpace V₀ V₁)).Element :=
  (funSpaceEquiv V₀ (iterSys V₁)).trans <|
    (funIterEquiv V₀ V₁).trans <|
      (piCongrOrderIso (fun _ : ℕ => (funSpaceEquiv V₀ V₁).symm)).trans
        (iterSeqEquiv (funSpace V₀ V₁)).symm

/-- **Exercise 3.24(ii).** `(𝒟₀ → 𝒟₁^∞) ≅ (𝒟₀ → 𝒟₁)^∞`. -/
theorem funIter_isomorphic : funSpace V₀ (iterSys V₁) ≅ᴰ iterSys (funSpace V₀ V₁) :=
  ⟨funIterIso V₀ V₁⟩

end Domain.Neighborhood
