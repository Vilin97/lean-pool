/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/
module

public import LeanPool.JacobianDiffgeo.Cech.Colimit
public import LeanPool.JacobianDiffgeo.Cech.Injectivity
import LeanPool.JacobianDiffgeo.Dbar.DiskAcyclic
import LeanPool.JacobianDiffgeo.Meromorphic.Gluing
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.MeasureTheory.Covering.Besicovitch

/-!
# Leray's theorem and the cocycle-trade lemma (`Jacobian/DolbeaultComparison/Leray.lean`)

Unit: dolbeault-comparison (`docs/design/dolbeault-comparison.md` §5). This is the FIRST file of
the unit and the gate for `finiteness-and-chi` (§0.1 of the design): everything here uses only
cech's cover/cochain/colimit machinery, mero's gluing sheaf axioms, and dbar's disk acyclicity
(`subsingleton_h1Cover_of_isChartDisk`, general-`D`, added to `Jacobian/Dbar/DiskAcyclic.lean`
under this unit's authorization) as black boxes — no `Form01`, no PoU, no dbar-solving.

* `FinCover.induced 𝒱 V : FinCover V`: the induced cover of a member `V` of `⊤`'s cover `𝒱`.
* `exists_goodCover`: good covers exist (3-line corollary of cech's `exists_good_refinement`).
* `exists_trade` (Forster 14.6(a), qualitative): cocycles on any refinement of a good cover are,
  up to coboundary, restrictions of cocycles on the good cover — the Schwartz surjectivity input
  for finiteness-and-chi.
* `resH1_surjective_of_isGood` / `toH1_surjective_of_isGood` (Leray 12.8 surjectivity;
  injectivity is cech's `toH1_injective`, ALREADY on disk) / `h1CoverEquiv`.
-/

public section

open scoped ContDiff Manifold
open Set TopologicalSpace RS.Cech

namespace RS.Cech

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

/-! ### A reusable lattice fact -/

omit [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ, ℂ) ω X] in
theorem inf_inf_inf_le (a b c : Opens X) : (a ⊓ b) ⊓ (a ⊓ c) ≤ b ⊓ c :=
  le_inf (inf_le_left.trans inf_le_right) (inf_le_right.trans inf_le_right)

/-! ### The induced cover of a member -/

/-- The induced cover of a member: `(V ⊓ 𝒱.U α)_α : FinCover V` for `V ≤ ⊤`. -/
@[expose] def FinCover.induced (𝒱 : FinCover (⊤ : Opens X)) (V : Opens X) : FinCover V where
  n := 𝒱.n
  U := fun α => V ⊓ 𝒱.U α
  le_base := fun _ => inf_le_left
  covers := fun x hx => by
    obtain ⟨α, hα⟩ := 𝒱.covers x trivial
    exact ⟨α, hx, hα⟩

omit [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ, ℂ) ω X] in
@[simp] theorem FinCover.induced_n (𝒱 : FinCover (⊤ : Opens X)) (V : Opens X) :
    (𝒱.induced V).n = 𝒱.n := rfl

omit [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ, ℂ) ω X] in
@[simp] theorem FinCover.induced_U (𝒱 : FinCover (⊤ : Opens X)) (V : Opens X) (α : Fin 𝒱.n) :
    (𝒱.induced V).U α = V ⊓ 𝒱.U α := rfl

omit [IsManifold 𝓘(ℂ, ℂ) ω X] in
/-- Good covers exist (§6.3 of cech-cohomology, applied to the trivial cover). -/
theorem exists_goodCover [CompactSpace X] :
    ∃ 𝒰 : FinCover (⊤ : Opens X), 𝒰.IsGood := by
  obtain ⟨𝒲, -, hgood⟩ := exists_good_refinement (FinCover.single (⊤ : Opens X))
  exact ⟨𝒲, hgood⟩

/-! ### §5 step 1: the induced cocycle -/

variable {𝒰 𝒱 : FinCover (⊤ : Opens X)} (D : RS.Divisor X)

/-- The induced cocycle on `𝒱.induced (𝒰.U i)` (§5 step 1): componentwise restriction of `f`
along the "drop the `𝒰.U i` factor" lattice map. -/
noncomputable def indCocycle (i : Fin 𝒰.n) (f : C1 D 𝒱) : C1 D (𝒱.induced (𝒰.U i)) :=
  fun p => LinSysOn.restrictL D (inf_inf_inf_le (𝒰.U i) (𝒱.U p.1) (𝒱.U p.2)) (f p)

omit [IsManifold 𝓘(ℂ, ℂ) ω X] in
theorem indCocycle_mem_Z1 (i : Fin 𝒰.n) {f : C1 D 𝒱} (hf : f ∈ Z1 D 𝒱) :
    indCocycle D i f ∈ Z1 D (𝒱.induced (𝒰.U i)) := by
  rw [mem_Z1_iff]
  rintro ⟨α, β, γ⟩
  have hβγ𝒱ᵢ : (𝒱.induced (𝒰.U i)).U α ⊓ (𝒱.induced (𝒰.U i)).U β ⊓ (𝒱.induced (𝒰.U i)).U γ ≤
      (𝒱.induced (𝒰.U i)).U β ⊓ (𝒱.induced (𝒰.U i)).U γ :=
    le_inf (inf_le_left.trans inf_le_right) inf_le_right
  have hαγ𝒱ᵢ : (𝒱.induced (𝒰.U i)).U α ⊓ (𝒱.induced (𝒰.U i)).U β ⊓ (𝒱.induced (𝒰.U i)).U γ ≤
      (𝒱.induced (𝒰.U i)).U α ⊓ (𝒱.induced (𝒰.U i)).U γ :=
    le_inf (inf_le_left.trans inf_le_left) inf_le_right
  have hαβ𝒱ᵢ : (𝒱.induced (𝒰.U i)).U α ⊓ (𝒱.induced (𝒰.U i)).U β ⊓ (𝒱.induced (𝒰.U i)).U γ ≤
      (𝒱.induced (𝒰.U i)).U α ⊓ (𝒱.induced (𝒰.U i)).U β := inf_le_left
  have hβγ : (𝒱.induced (𝒰.U i)).U α ⊓ (𝒱.induced (𝒰.U i)).U β ⊓ (𝒱.induced (𝒰.U i)).U γ ≤
      𝒱.U β ⊓ 𝒱.U γ := hβγ𝒱ᵢ.trans (inf_inf_inf_le (𝒰.U i) (𝒱.U β) (𝒱.U γ))
  have hαγ : (𝒱.induced (𝒰.U i)).U α ⊓ (𝒱.induced (𝒰.U i)).U β ⊓ (𝒱.induced (𝒰.U i)).U γ ≤
      𝒱.U α ⊓ 𝒱.U γ := hαγ𝒱ᵢ.trans (inf_inf_inf_le (𝒰.U i) (𝒱.U α) (𝒱.U γ))
  have hαβ : (𝒱.induced (𝒰.U i)).U α ⊓ (𝒱.induced (𝒰.U i)).U β ⊓ (𝒱.induced (𝒰.U i)).U γ ≤
      𝒱.U α ⊓ 𝒱.U β := hαβ𝒱ᵢ.trans (inf_inf_inf_le (𝒰.U i) (𝒱.U α) (𝒱.U β))
  have hW : (𝒱.induced (𝒰.U i)).U α ⊓ (𝒱.induced (𝒰.U i)).U β ⊓ (𝒱.induced (𝒰.U i)).U γ ≤
      𝒱.U α ⊓ 𝒱.U β ⊓ 𝒱.U γ := le_inf hαβ (inf_le_right.trans inf_le_right)
  have key := Z1.rel_res D hf α β γ hW hβγ hαγ hαβ
  refine Eq.trans ?_ key
  exact congrArg₂ (· + ·)
    (congrArg₂ (· - ·)
      (restrictL_restrictL D _ hβγ𝒱ᵢ hβγ _)
      (restrictL_restrictL D _ hαγ𝒱ᵢ hαγ _))
    (restrictL_restrictL D _ hαβ𝒱ᵢ hαβ _)

/-! ### §5 step 2: member splitting via disk acyclicity -/

variable [T2Space X] [CompactSpace X]

/-- Step 2: each induced cocycle splits, since `𝒰.U i` is a chart disk (disk acyclicity). -/
theorem exists_splitting (h𝒰 : 𝒰.IsGood) {f : C1 D 𝒱} (hf : f ∈ Z1 D 𝒱) :
    ∃ gFam : ∀ i : Fin 𝒰.n, C0 D (𝒱.induced (𝒰.U i)),
      ∀ i, d0 D (𝒱.induced (𝒰.U i)) (gFam i) = indCocycle D i f := by
  choose gFam hgFam using fun i : Fin 𝒰.n =>
    ((subsingleton_h1Cover_iff D (𝒱.induced (𝒰.U i))).mp
      (subsingleton_h1Cover_of_isChartDisk (h𝒰 i) D (𝒱.induced (𝒰.U i)))) (indCocycle_mem_Z1 D i hf)
  exact ⟨gFam, hgFam⟩

omit [T2Space X] [CompactSpace X] [IsManifold 𝓘(ℂ, ℂ) ω X] in
/-- The pointwise splitting identity extracted from `exists_splitting`, at `LinSysOn`
(submodule) level (used both for the cross-glue compatibility and for the final comparison,
§5 steps 3/5). -/
theorem splitting_eq {f : C1 D 𝒱} {gFam : ∀ i : Fin 𝒰.n, C0 D (𝒱.induced (𝒰.U i))}
    (hgFam : ∀ i, d0 D (𝒱.induced (𝒰.U i)) (gFam i) = indCocycle D i f) (i : Fin 𝒰.n)
    (α β : Fin 𝒱.n) :
    LinSysOn.restrictL D
        (inf_le_right : (𝒱.induced (𝒰.U i)).U α ⊓ (𝒱.induced (𝒰.U i)).U β ≤
          (𝒱.induced (𝒰.U i)).U β) (gFam i β) -
      LinSysOn.restrictL D
        (inf_le_left : (𝒱.induced (𝒰.U i)).U α ⊓ (𝒱.induced (𝒰.U i)).U β ≤
          (𝒱.induced (𝒰.U i)).U α) (gFam i α) =
    indCocycle D i f (α, β) := congrFun (hgFam i) (α, β)

omit [T2Space X] [CompactSpace X] [IsManifold 𝓘(ℂ, ℂ) ω X] in
/-- Raw `MeroGermOn`-level form of `splitting_eq`. -/
theorem splitting_eq' {f : C1 D 𝒱} {gFam : ∀ i : Fin 𝒰.n, C0 D (𝒱.induced (𝒰.U i))}
    (hgFam : ∀ i, d0 D (𝒱.induced (𝒰.U i)) (gFam i) = indCocycle D i f) (i : Fin 𝒰.n)
    (α β : Fin 𝒱.n) :
    (RS.MeroGermOn.restrict
        (inf_le_right : (𝒱.induced (𝒰.U i)).U α ⊓ (𝒱.induced (𝒰.U i)).U β ≤
          (𝒱.induced (𝒰.U i)).U β)
        (gFam i β : RS.MeroGermOn X ((𝒱.induced (𝒰.U i)).U β : Set X)) -
      RS.MeroGermOn.restrict
        (inf_le_left : (𝒱.induced (𝒰.U i)).U α ⊓ (𝒱.induced (𝒰.U i)).U β ≤
          (𝒱.induced (𝒰.U i)).U α)
        (gFam i α : RS.MeroGermOn X ((𝒱.induced (𝒰.U i)).U α : Set X)) :
      RS.MeroGermOn X ((𝒱.induced (𝒰.U i)).U α ⊓ (𝒱.induced (𝒰.U i)).U β : Set X)) =
    RS.MeroGermOn.restrict (inf_inf_inf_le (𝒰.U i) (𝒱.U α) (𝒱.U β))
      (f (α, β) : RS.MeroGermOn X (𝒱.U α ⊓ 𝒱.U β : Set X)) := by
  exact congrArg Subtype.val (splitting_eq D hgFam i α β)

omit [T2Space X] [CompactSpace X] [IsManifold 𝓘(ℂ, ℂ) ω X] in
/-- `splitting_eq'`, restricted down to an arbitrary smaller open `W` (§5 step 3's workhorse:
lets us compare the splittings at TWO different good-cover members `i`, `j` on their common
overlap with a member of `𝒱`). -/
theorem splitting_eq_restrict {f : C1 D 𝒱} {gFam : ∀ i : Fin 𝒰.n, C0 D (𝒱.induced (𝒰.U i))}
    (hgFam : ∀ i, d0 D (𝒱.induced (𝒰.U i)) (gFam i) = indCocycle D i f) (i : Fin 𝒰.n)
    (α β : Fin 𝒱.n) {W : Opens X} (hWα : W ≤ (𝒱.induced (𝒰.U i)).U α)
    (hWβ : W ≤ (𝒱.induced (𝒰.U i)).U β) (hWαβ : W ≤ 𝒱.U α ⊓ 𝒱.U β) :
    RS.MeroGermOn.restrict hWβ (gFam i β : RS.MeroGermOn X ((𝒱.induced (𝒰.U i)).U β : Set X)) -
      RS.MeroGermOn.restrict hWα (gFam i α : RS.MeroGermOn X ((𝒱.induced (𝒰.U i)).U α : Set X)) =
    RS.MeroGermOn.restrict hWαβ (f (α, β) : RS.MeroGermOn X (𝒱.U α ⊓ 𝒱.U β : Set X)) := by
  have hWαβ' : W ≤ (𝒱.induced (𝒰.U i)).U α ⊓ (𝒱.induced (𝒰.U i)).U β := le_inf hWα hWβ
  have hcast := congrArg (RS.MeroGermOn.restrict hWαβ') (splitting_eq' D hgFam i α β)
  rw [map_sub] at hcast
  exact (congrArg₂ (· - ·)
    (RS.MeroGermOn.restrict_restrict inf_le_right hWαβ' _).symm
    (RS.MeroGermOn.restrict_restrict inf_le_left hWαβ' _).symm).trans
      (hcast.trans (RS.MeroGermOn.restrict_restrict (inf_inf_inf_le (𝒰.U i) (𝒱.U α) (𝒱.U β))
        hWαβ' _))

/-! ### §5 step 3: cross-glue -/

/-- The local candidate for the glued section on `𝒰.U i ⊓ 𝒰.U j` (§5 step 3). -/
noncomputable def patch (gFam : ∀ i : Fin 𝒰.n, C0 D (𝒱.induced (𝒰.U i))) (i j : Fin 𝒰.n)
    (α : Fin 𝒱.n) : RS.LinSysOn D (𝒰.U i ⊓ 𝒰.U j ⊓ 𝒱.U α : Set X) :=
  LinSysOn.restrictL D
      (le_inf (inf_le_left.trans inf_le_right) inf_le_right :
        𝒰.U i ⊓ 𝒰.U j ⊓ 𝒱.U α ≤ (𝒱.induced (𝒰.U j)).U α) (gFam j α) -
    LinSysOn.restrictL D
      (le_inf (inf_le_left.trans inf_le_left) inf_le_right :
        𝒰.U i ⊓ 𝒰.U j ⊓ 𝒱.U α ≤ (𝒱.induced (𝒰.U i)).U α) (gFam i α)

omit [IsManifold 𝓘(ℂ, ℂ) ω X] [T2Space X] [CompactSpace X] in
theorem patch_coe (gFam : ∀ i : Fin 𝒰.n, C0 D (𝒱.induced (𝒰.U i))) (i j : Fin 𝒰.n)
    (α : Fin 𝒱.n) :
    (patch D gFam i j α : RS.MeroGermOn X (𝒰.U i ⊓ 𝒰.U j ⊓ 𝒱.U α : Set X)) =
      (RS.MeroGermOn.restrict
          (le_inf (inf_le_left.trans inf_le_right) inf_le_right :
            𝒰.U i ⊓ 𝒰.U j ⊓ 𝒱.U α ≤ (𝒱.induced (𝒰.U j)).U α)
          (gFam j α : RS.MeroGermOn X ((𝒱.induced (𝒰.U j)).U α : Set X))) -
        (RS.MeroGermOn.restrict
          (le_inf (inf_le_left.trans inf_le_left) inf_le_right :
            𝒰.U i ⊓ 𝒰.U j ⊓ 𝒱.U α ≤ (𝒱.induced (𝒰.U i)).U α)
          (gFam i α : RS.MeroGermOn X ((𝒱.induced (𝒰.U i)).U α : Set X))) := rfl

omit [IsManifold 𝓘(ℂ, ℂ) ω X] [T2Space X] [CompactSpace X] in
/-- `patch`, restricted further down to an arbitrary open `W` (`LinSysOn`-level unfolding of
`patch_coe`, reused for both step 4's triple relation and step 5's final comparison). -/
theorem patch_restrict (gFam : ∀ i : Fin 𝒰.n, C0 D (𝒱.induced (𝒰.U i))) (i j : Fin 𝒰.n)
    (α : Fin 𝒱.n) {W : Opens X} (hWj : W ≤ (𝒱.induced (𝒰.U j)).U α)
    (hWi : W ≤ (𝒱.induced (𝒰.U i)).U α) (hWij : W ≤ 𝒰.U i ⊓ 𝒰.U j ⊓ 𝒱.U α) :
    RS.MeroGermOn.restrict hWij
        (patch D gFam i j α : RS.MeroGermOn X (𝒰.U i ⊓ 𝒰.U j ⊓ 𝒱.U α : Set X)) =
      RS.MeroGermOn.restrict hWj
          (gFam j α : RS.MeroGermOn X ((𝒱.induced (𝒰.U j)).U α : Set X)) -
        RS.MeroGermOn.restrict hWi
          (gFam i α : RS.MeroGermOn X ((𝒱.induced (𝒰.U i)).U α : Set X)) := by
  exact (map_sub (RS.MeroGermOn.restrict hWij) _ _).trans
    (congrArg₂ (· - ·) (RS.MeroGermOn.restrict_restrict _ hWij _)
      (RS.MeroGermOn.restrict_restrict _ hWij _))

omit [T2Space X] [CompactSpace X] [IsManifold 𝓘(ℂ, ℂ) ω X] in
/-- Compatibility of the patches on overlaps (§5 step 3). -/
theorem patch_compat {f : C1 D 𝒱} {gFam : ∀ i : Fin 𝒰.n, C0 D (𝒱.induced (𝒰.U i))}
    (hgFam : ∀ i, d0 D (𝒱.induced (𝒰.U i)) (gFam i) = indCocycle D i f) (i j : Fin 𝒰.n)
    (α β : Fin 𝒱.n) :
    RS.MeroGermOn.restrict
        (inf_le_left : 𝒰.U i ⊓ 𝒰.U j ⊓ 𝒱.U α ⊓ (𝒰.U i ⊓ 𝒰.U j ⊓ 𝒱.U β) ≤ 𝒰.U i ⊓ 𝒰.U j ⊓ 𝒱.U α)
        (patch D gFam i j α : RS.MeroGermOn X (𝒰.U i ⊓ 𝒰.U j ⊓ 𝒱.U α : Set X)) =
      RS.MeroGermOn.restrict
        (inf_le_right : 𝒰.U i ⊓ 𝒰.U j ⊓ 𝒱.U α ⊓ (𝒰.U i ⊓ 𝒰.U j ⊓ 𝒱.U β) ≤ 𝒰.U i ⊓ 𝒰.U j ⊓ 𝒱.U β)
        (patch D gFam i j β : RS.MeroGermOn X (𝒰.U i ⊓ 𝒰.U j ⊓ 𝒱.U β : Set X)) := by
  have hWα : 𝒰.U i ⊓ 𝒰.U j ⊓ 𝒱.U α ⊓ (𝒰.U i ⊓ 𝒰.U j ⊓ 𝒱.U β) ≤ 𝒰.U i ⊓ 𝒰.U j ⊓ 𝒱.U α := inf_le_left
  have hWβ : 𝒰.U i ⊓ 𝒰.U j ⊓ 𝒱.U α ⊓ (𝒰.U i ⊓ 𝒰.U j ⊓ 𝒱.U β) ≤ 𝒰.U i ⊓ 𝒰.U j ⊓ 𝒱.U β := inf_le_right
  have hWαj : 𝒰.U i ⊓ 𝒰.U j ⊓ 𝒱.U α ⊓ (𝒰.U i ⊓ 𝒰.U j ⊓ 𝒱.U β) ≤ (𝒱.induced (𝒰.U j)).U α :=
    hWα.trans (le_inf (inf_le_left.trans inf_le_right) inf_le_right)
  have hWαi : 𝒰.U i ⊓ 𝒰.U j ⊓ 𝒱.U α ⊓ (𝒰.U i ⊓ 𝒰.U j ⊓ 𝒱.U β) ≤ (𝒱.induced (𝒰.U i)).U α :=
    hWα.trans (le_inf (inf_le_left.trans inf_le_left) inf_le_right)
  have hWβj : 𝒰.U i ⊓ 𝒰.U j ⊓ 𝒱.U α ⊓ (𝒰.U i ⊓ 𝒰.U j ⊓ 𝒱.U β) ≤ (𝒱.induced (𝒰.U j)).U β :=
    hWβ.trans (le_inf (inf_le_left.trans inf_le_right) inf_le_right)
  have hWβi : 𝒰.U i ⊓ 𝒰.U j ⊓ 𝒱.U α ⊓ (𝒰.U i ⊓ 𝒰.U j ⊓ 𝒱.U β) ≤ (𝒱.induced (𝒰.U i)).U β :=
    hWβ.trans (le_inf (inf_le_left.trans inf_le_left) inf_le_right)
  have hWαβ𝒱 : 𝒰.U i ⊓ 𝒰.U j ⊓ 𝒱.U α ⊓ (𝒰.U i ⊓ 𝒰.U j ⊓ 𝒱.U β) ≤ 𝒱.U α ⊓ 𝒱.U β :=
    le_inf (hWα.trans inf_le_right) (hWβ.trans inf_le_right)
  have hj := splitting_eq_restrict D hgFam j α β hWαj hWβj hWαβ𝒱
  have hi := splitting_eq_restrict D hgFam i α β hWαi hWβi hWαβ𝒱
  rw [patch_restrict D gFam i j α hWαj hWαi hWα,
    patch_restrict D gFam i j β hWβj hWβi hWβ]
  apply sub_eq_sub_iff_sub_eq_sub.2
  simpa only [neg_sub] using congrArg Neg.neg (hj.trans hi.symm)

omit [T2Space X] [CompactSpace X] in
/-- The glued section `F_{ij}` on `𝒰.U i ⊓ 𝒰.U j`, restricting back to `patch` on each
`Uᵢ⊓Uⱼ⊓Vα` (§5 step 3). -/
theorem exists_crossGlue {f : C1 D 𝒱} (_hf : f ∈ Z1 D 𝒱)
    {gFam : ∀ i : Fin 𝒰.n, C0 D (𝒱.induced (𝒰.U i))}
    (hgFam : ∀ i, d0 D (𝒱.induced (𝒰.U i)) (gFam i) = indCocycle D i f) (i j : Fin 𝒰.n) :
    ∃ Φ : RS.MeroGermOn X (𝒰.U i ⊓ 𝒰.U j : Set X), ∀ α : Fin 𝒱.n,
      RS.MeroGermOn.restrict (inf_le_left : 𝒰.U i ⊓ 𝒰.U j ⊓ 𝒱.U α ≤ 𝒰.U i ⊓ 𝒰.U j) Φ =
        (patch D gFam i j α : RS.MeroGermOn X (𝒰.U i ⊓ 𝒰.U j ⊓ 𝒱.U α : Set X)) := by
  have hWopen : ∀ α : Fin 𝒱.n, IsOpen ((𝒰.U i ⊓ 𝒰.U j ⊓ 𝒱.U α : Opens X) : Set X) :=
    fun α => (𝒰.U i ⊓ 𝒰.U j ⊓ 𝒱.U α).2
  have hunion : (⋃ α : Fin 𝒱.n, ((𝒰.U i ⊓ 𝒰.U j ⊓ 𝒱.U α : Opens X) : Set X)) =
      (𝒰.U i ⊓ 𝒰.U j : Set X) := iUnion_inf_eq (𝒰.U i ⊓ 𝒰.U j) le_top
  obtain ⟨Ψ, hΨ⟩ := RS.MeroGermOn.exists_glue hWopen
    (fun α => (patch D gFam i j α : RS.MeroGermOn X (𝒰.U i ⊓ 𝒰.U j ⊓ 𝒱.U α : Set X)))
    (fun α β => patch_compat D hgFam i j α β)
  refine ⟨MeroGermOn.congrSet hunion Ψ, fun α => ?_⟩
  have hstep : RS.MeroGermOn.restrict
      (inf_le_left : 𝒰.U i ⊓ 𝒰.U j ⊓ 𝒱.U α ≤ 𝒰.U i ⊓ 𝒰.U j)
      (RS.MeroGermOn.restrict hunion.ge Ψ) =
      RS.MeroGermOn.restrict
        (Set.subset_iUnion (fun α => ((𝒰.U i ⊓ 𝒰.U j ⊓ 𝒱.U α : Opens X) : Set X)) α) Ψ :=
    RS.MeroGermOn.restrict_restrict hunion.ge inf_le_left Ψ
  change RS.MeroGermOn.restrict (inf_le_left : 𝒰.U i ⊓ 𝒰.U j ⊓ 𝒱.U α ≤ 𝒰.U i ⊓ 𝒰.U j)
      (MeroGermOn.congrSet hunion Ψ) =
      (patch D gFam i j α : RS.MeroGermOn X (𝒰.U i ⊓ 𝒰.U j ⊓ 𝒱.U α : Set X))
  exact hstep.trans (hΨ α)

omit [T2Space X] [CompactSpace X] in
/-- The glued section, packaged as a `LinSysOn` element (§5 step 3, `LinSysOn`-level): the
`crossGlue` witness restricts back to `patch` on each `Uᵢ⊓Uⱼ⊓Vα`. -/
theorem exists_crossGlueLinSysOn {f : C1 D 𝒱} (hf : f ∈ Z1 D 𝒱)
    {gFam : ∀ i : Fin 𝒰.n, C0 D (𝒱.induced (𝒰.U i))}
    (hgFam : ∀ i, d0 D (𝒱.induced (𝒰.U i)) (gFam i) = indCocycle D i f) (i j : Fin 𝒰.n) :
    ∃ Φ : RS.LinSysOn D (𝒰.U i ⊓ 𝒰.U j : Set X), ∀ α : Fin 𝒱.n,
      LinSysOn.restrictL D (inf_le_left : 𝒰.U i ⊓ 𝒰.U j ⊓ 𝒱.U α ≤ 𝒰.U i ⊓ 𝒰.U j) Φ =
        patch D gFam i j α := by
  obtain ⟨Ψ, hΨ⟩ := exists_crossGlue D hf hgFam i j
  have hmem : Ψ ∈ RS.LinSysOn D (𝒰.U i ⊓ 𝒰.U j : Set X) := by
    refine (RS.mem_linSysOn_iff_of_isOpen (𝒰.U i ⊓ 𝒰.U j).isOpen).2 ?_
    intro x hx
    obtain ⟨α, hα⟩ := 𝒱.covers x trivial
    have hxmem : x ∈ (𝒰.U i ⊓ 𝒰.U j ⊓ 𝒱.U α : Opens X) := ⟨hx, hα⟩
    have hord := RS.MeroGermOn.ord_restrict
      (inf_le_left : 𝒰.U i ⊓ 𝒰.U j ⊓ 𝒱.U α ≤ 𝒰.U i ⊓ 𝒰.U j)
      (𝒰.U i ⊓ 𝒰.U j ⊓ 𝒱.U α).isOpen (𝒰.U i ⊓ 𝒰.U j).isOpen hxmem Ψ
    rw [hΨ α] at hord
    rw [← hord]
    exact (RS.mem_linSysOn_iff_of_isOpen (𝒰.U i ⊓ 𝒰.U j ⊓ 𝒱.U α).isOpen).1
      (patch D gFam i j α).2 x hxmem
  refine ⟨⟨Ψ, hmem⟩, fun α => ?_⟩
  apply Subtype.ext
  rw [restrictL_apply_coe]
  exact hΨ α

omit [T2Space X] [CompactSpace X] in
/-- The glued sections `F_{ij}`, packaged as a full `1`-cochain on `𝒰` (§5 step 3, `LinSysOn`
level): a choice of `crossGlue`-witness for every pair. -/
theorem exists_crossGlueFam {f : C1 D 𝒱} (hf : f ∈ Z1 D 𝒱)
    {gFam : ∀ i : Fin 𝒰.n, C0 D (𝒱.induced (𝒰.U i))}
    (hgFam : ∀ i, d0 D (𝒱.induced (𝒰.U i)) (gFam i) = indCocycle D i f) :
    ∃ F : C1 D 𝒰, ∀ (i j : Fin 𝒰.n) (α : Fin 𝒱.n),
      LinSysOn.restrictL D (inf_le_left : 𝒰.U i ⊓ 𝒰.U j ⊓ 𝒱.U α ≤ 𝒰.U i ⊓ 𝒰.U j) (F (i, j)) =
        patch D gFam i j α := by
  choose Φ hΦ using fun p : Fin 𝒰.n × Fin 𝒰.n =>
    exists_crossGlueLinSysOn D hf hgFam p.1 p.2
  exact ⟨Φ, fun i j α => hΦ (i, j) α⟩

omit [T2Space X] [CompactSpace X] [IsManifold 𝓘(ℂ, ℂ) ω X] in
private theorem crossGlueFam_restrict {F : C1 D 𝒰}
    {gFam : ∀ i : Fin 𝒰.n, C0 D (𝒱.induced (𝒰.U i))}
    (hF : ∀ (i j : Fin 𝒰.n) (α : Fin 𝒱.n),
      LinSysOn.restrictL D (inf_le_left : 𝒰.U i ⊓ 𝒰.U j ⊓ 𝒱.U α ≤ 𝒰.U i ⊓ 𝒰.U j) (F (i, j)) =
        patch D gFam i j α)
    (i j : Fin 𝒰.n) (α : Fin 𝒱.n) {W : Opens X}
    (hWj : W ≤ (𝒱.induced (𝒰.U j)).U α) (hWi : W ≤ (𝒱.induced (𝒰.U i)).U α)
    (hWij : W ≤ 𝒰.U i ⊓ 𝒰.U j ⊓ 𝒱.U α) :
    RS.MeroGermOn.restrict (hWij.trans inf_le_left)
        (F (i, j) : RS.MeroGermOn X (𝒰.U i ⊓ 𝒰.U j : Set X)) =
      RS.MeroGermOn.restrict hWj
          (gFam j α : RS.MeroGermOn X ((𝒱.induced (𝒰.U j)).U α : Set X)) -
        RS.MeroGermOn.restrict hWi
          (gFam i α : RS.MeroGermOn X ((𝒱.induced (𝒰.U i)).U α : Set X)) := by
  exact (RS.MeroGermOn.restrict_restrict inf_le_left hWij _).symm.trans
    ((congrArg (RS.MeroGermOn.restrict hWij) (congrArg Subtype.val (hF i j α))).trans
      (patch_restrict D gFam i j α hWj hWi hWij))

/-! ### §5 step 4: `F ∈ Z1 D 𝒰` -/

omit [T2Space X] [CompactSpace X] in
/-- Step 4: the glued family is a genuine cocycle on `𝒰` (the triple relation telescopes
term-by-term from the `patch` definition — pure algebra, no further analytic input). -/
theorem crossGlueFam_mem_Z1 {F : C1 D 𝒰} {gFam : ∀ i : Fin 𝒰.n, C0 D (𝒱.induced (𝒰.U i))}
    (hF : ∀ (i j : Fin 𝒰.n) (α : Fin 𝒱.n),
      LinSysOn.restrictL D (inf_le_left : 𝒰.U i ⊓ 𝒰.U j ⊓ 𝒱.U α ≤ 𝒰.U i ⊓ 𝒰.U j) (F (i, j)) =
        patch D gFam i j α) :
    F ∈ Z1 D 𝒰 := by
  rw [mem_Z1_iff]
  rintro ⟨i, j, k⟩
  let A : Opens X := 𝒰.U i ⊓ 𝒰.U j ⊓ 𝒰.U k
  let W : Fin 𝒱.n → Set X := fun α => ((A ⊓ 𝒱.U α : Opens X) : Set X)
  have hWopen : ∀ α, IsOpen (W α) := fun α => (A ⊓ 𝒱.U α).isOpen
  have hunion : (⋃ α, W α) = (A : Set X) := iUnion_inf_eq A le_top
  let e := MeroGermOn.congrSet hunion.symm
  have hrewrite : ∀ (Z : RS.MeroGermOn X (A : Set X)) (α : Fin 𝒱.n),
      RS.MeroGermOn.restrict (Set.subset_iUnion W α) (e Z) =
        RS.MeroGermOn.restrict (inf_le_left : A ⊓ 𝒱.U α ≤ A) Z := by
    intro Z α
    exact RS.MeroGermOn.restrict_restrict _ _ Z
  have hi : A ≤ 𝒰.U i := inf_le_left.trans inf_le_left
  have hj : A ≤ 𝒰.U j := inf_le_left.trans inf_le_right
  have hk : A ≤ 𝒰.U k := inf_le_right
  have hjk : A ≤ 𝒰.U j ⊓ 𝒰.U k := le_inf (inf_le_left.trans inf_le_right) inf_le_right
  have hik : A ≤ 𝒰.U i ⊓ 𝒰.U k := le_inf (inf_le_left.trans inf_le_left) inf_le_right
  have hij : A ≤ 𝒰.U i ⊓ 𝒰.U j := inf_le_left
  have hcore : ∀ α : Fin 𝒱.n,
      RS.MeroGermOn.restrict (inf_le_left : A ⊓ 𝒱.U α ≤ A)
          (d1 D 𝒰 F (i, j, k) : RS.MeroGermOn X (A : Set X)) =
        RS.MeroGermOn.restrict (inf_le_left : A ⊓ 𝒱.U α ≤ A)
          ((0 : RS.LinSysOn D (A : Set X)) : RS.MeroGermOn X (A : Set X)) := by
    intro α
    let Wα : Opens X := A ⊓ 𝒱.U α
    have hWA : Wα ≤ A := inf_le_left
    have hWα' : Wα ≤ 𝒱.U α := inf_le_right
    have hWjk : Wα ≤ 𝒰.U j ⊓ 𝒰.U k := hWA.trans hjk
    have hWik : Wα ≤ 𝒰.U i ⊓ 𝒰.U k := hWA.trans hik
    have hWij : Wα ≤ 𝒰.U i ⊓ 𝒰.U j := hWA.trans hij
    have hWjkα : Wα ≤ 𝒰.U j ⊓ 𝒰.U k ⊓ 𝒱.U α := le_inf hWjk hWα'
    have hWikα : Wα ≤ 𝒰.U i ⊓ 𝒰.U k ⊓ 𝒱.U α := le_inf hWik hWα'
    have hWijα : Wα ≤ 𝒰.U i ⊓ 𝒰.U j ⊓ 𝒱.U α := le_inf hWij hWα'
    have hWjα : Wα ≤ (𝒱.induced (𝒰.U j)).U α := le_inf (hWA.trans hj) hWα'
    have hWiα : Wα ≤ (𝒱.induced (𝒰.U i)).U α := le_inf (hWA.trans hi) hWα'
    have hWkα : Wα ≤ (𝒱.induced (𝒰.U k)).U α := le_inf (hWA.trans hk) hWα'
    have step_jk := crossGlueFam_restrict D hF j k α hWkα hWjα hWjkα
    have step_ik := crossGlueFam_restrict D hF i k α hWkα hWiα hWikα
    have step_ij := crossGlueFam_restrict D hF i j α hWjα hWiα hWijα
    change RS.MeroGermOn.restrict hWA
        (RS.MeroGermOn.restrict hjk (F (j, k) : RS.MeroGermOn X (𝒰.U j ⊓ 𝒰.U k : Set X)) -
          RS.MeroGermOn.restrict hik (F (i, k) : RS.MeroGermOn X (𝒰.U i ⊓ 𝒰.U k : Set X)) +
          RS.MeroGermOn.restrict hij (F (i, j) : RS.MeroGermOn X (𝒰.U i ⊓ 𝒰.U j : Set X))) =
        RS.MeroGermOn.restrict hWA 0
    rw [map_add, map_sub]
    have g1 := RS.MeroGermOn.restrict_restrict
      (le_inf (inf_le_left.trans inf_le_right) inf_le_right : A ≤ 𝒰.U j ⊓ 𝒰.U k) hWA
      (F (j, k) : RS.MeroGermOn X (𝒰.U j ⊓ 𝒰.U k : Set X))
    have g2 := RS.MeroGermOn.restrict_restrict
      (le_inf (inf_le_left.trans inf_le_left) inf_le_right : A ≤ 𝒰.U i ⊓ 𝒰.U k) hWA
      (F (i, k) : RS.MeroGermOn X (𝒰.U i ⊓ 𝒰.U k : Set X))
    have g3 := RS.MeroGermOn.restrict_restrict
      (inf_le_left : A ≤ 𝒰.U i ⊓ 𝒰.U j) hWA
      (F (i, j) : RS.MeroGermOn X (𝒰.U i ⊓ 𝒰.U j : Set X))
    rw [g1, g2, g3, step_jk, step_ik, step_ij, map_zero]
    abel
  have hglu : e ((d1 D 𝒰 F (i, j, k) : RS.MeroGermOn X (A : Set X))) =
      e (((0 : RS.LinSysOn D (A : Set X)) : RS.MeroGermOn X (A : Set X))) := by
    apply RS.MeroGermOn.glue_unique hWopen
    intro α
    rw [hrewrite _ α, hrewrite _ α]
    exact hcore α
  exact Subtype.ext (e.injective hglu)

/-! ### §5 step 5: the comparison on `𝒱` -/

variable (τ : Fin 𝒱.n → Fin 𝒰.n) (hτ : IsRefIdx 𝒰 𝒱 τ)

/-- The `0`-cochain `h` of §5 step 5: `h_α := restrict g^{τα}_α`. -/
noncomputable def tradeH0 (gFam : ∀ i : Fin 𝒰.n, C0 D (𝒱.induced (𝒰.U i))) : C0 D 𝒱 :=
  fun α => LinSysOn.restrictL D
    (le_inf (hτ α) le_rfl : 𝒱.U α ≤ 𝒰.U (τ α) ⊓ 𝒱.U α) (gFam (τ α) α)

omit [T2Space X] [CompactSpace X] [IsManifold 𝓘(ℂ, ℂ) ω X] in
/-- Step 5's frozen conclusion: `resC1 F + f = d0 h`. -/
theorem resC1_crossGlueFam_add_eq {f : C1 D 𝒱} (_hf : f ∈ Z1 D 𝒱)
    {gFam : ∀ i : Fin 𝒰.n, C0 D (𝒱.induced (𝒰.U i))}
    (hgFam : ∀ i, d0 D (𝒱.induced (𝒰.U i)) (gFam i) = indCocycle D i f) {F : C1 D 𝒰}
    (hF : ∀ (i j : Fin 𝒰.n) (α : Fin 𝒱.n),
      LinSysOn.restrictL D (inf_le_left : 𝒰.U i ⊓ 𝒰.U j ⊓ 𝒱.U α ≤ 𝒰.U i ⊓ 𝒰.U j) (F (i, j)) =
        patch D gFam i j α) :
    resC1 D τ hτ F + f = d0 D 𝒱 (tradeH0 D τ hτ gFam) := by
  funext p
  obtain ⟨α, β⟩ := p
  apply Subtype.ext
  let W : Opens X := 𝒱.U α ⊓ 𝒱.U β
  have hWτα : W ≤ 𝒰.U (τ α) := inf_le_left.trans (hτ α)
  have hWτβ : W ≤ 𝒰.U (τ β) := inf_le_right.trans (hτ β)
  have hWα : W ≤ 𝒱.U α := inf_le_left
  have hWβ : W ≤ 𝒱.U β := inf_le_right
  have hWij : W ≤ 𝒰.U (τ α) ⊓ 𝒰.U (τ β) := inf_le_inf (hτ α) (hτ β)
  have hWijα : W ≤ 𝒰.U (τ α) ⊓ 𝒰.U (τ β) ⊓ 𝒱.U α := le_inf hWij hWα
  have hWτβα : W ≤ (𝒱.induced (𝒰.U (τ β))).U α := le_inf hWτβ hWα
  have hWτβ' : W ≤ (𝒱.induced (𝒰.U (τ β))).U β := le_inf hWτβ hWβ
  have hWτα' : W ≤ (𝒱.induced (𝒰.U (τ α))).U α := le_inf hWτα hWα
  -- LHS term 1: `resC1 F (α, β)`, unfolded via `hF (τα) (τβ) α`
  have step1 : RS.MeroGermOn.restrict hWij
      (F (τ α, τ β) : RS.MeroGermOn X (𝒰.U (τ α) ⊓ 𝒰.U (τ β) : Set X)) =
      RS.MeroGermOn.restrict hWτβα
          (gFam (τ β) α : RS.MeroGermOn X ((𝒱.induced (𝒰.U (τ β))).U α : Set X)) -
        RS.MeroGermOn.restrict hWτα'
          (gFam (τ α) α : RS.MeroGermOn X ((𝒱.induced (𝒰.U (τ α))).U α : Set X)) :=
    crossGlueFam_restrict D hF (τ α) (τ β) α hWτβα hWτα' hWijα
  -- LHS term 2: `f (α, β)`, unfolded via `splitting_eq_restrict` at `i := τ β`
  have step2 :
      RS.MeroGermOn.restrict hWτβ'
          (gFam (τ β) β : RS.MeroGermOn X ((𝒱.induced (𝒰.U (τ β))).U β : Set X)) -
        RS.MeroGermOn.restrict hWτβα
          (gFam (τ β) α : RS.MeroGermOn X ((𝒱.induced (𝒰.U (τ β))).U α : Set X)) =
      (f (α, β) : RS.MeroGermOn X (𝒱.U α ⊓ 𝒱.U β : Set X)) := by
    have h0 := splitting_eq_restrict D hgFam (τ β) α β hWτβα hWτβ' (le_refl (𝒱.U α ⊓ 𝒱.U β))
    rwa [RS.MeroGermOn.restrict_id] at h0
  -- RHS: `d0 h (α, β)`, unfolded via `tradeH0`'s definition
  have step3 :
      RS.MeroGermOn.restrict hWβ ((tradeH0 D τ hτ gFam β : RS.LinSysOn D (𝒱.U β : Set X)) :
          RS.MeroGermOn X (𝒱.U β : Set X)) -
        RS.MeroGermOn.restrict hWα ((tradeH0 D τ hτ gFam α : RS.LinSysOn D (𝒱.U α : Set X)) :
          RS.MeroGermOn X (𝒱.U α : Set X)) =
      RS.MeroGermOn.restrict hWτβ'
          (gFam (τ β) β : RS.MeroGermOn X ((𝒱.induced (𝒰.U (τ β))).U β : Set X)) -
        RS.MeroGermOn.restrict hWτα'
          (gFam (τ α) α : RS.MeroGermOn X ((𝒱.induced (𝒰.U (τ α))).U α : Set X)) := by
    have hβ := RS.MeroGermOn.restrict_restrict
      (le_inf (hτ β) le_rfl : 𝒱.U β ≤ 𝒰.U (τ β) ⊓ 𝒱.U β) hWβ
      (gFam (τ β) β : RS.MeroGermOn X ((𝒱.induced (𝒰.U (τ β))).U β : Set X))
    have hα := RS.MeroGermOn.restrict_restrict
      (le_inf (hτ α) le_rfl : 𝒱.U α ≤ 𝒰.U (τ α) ⊓ 𝒱.U α) hWα
      (gFam (τ α) α : RS.MeroGermOn X ((𝒱.induced (𝒰.U (τ α))).U α : Set X))
    exact congrArg₂ (· - ·) hβ hα
  exact ((congrArg₂ (· + ·) step1 step2.symm).trans
    ((add_comm _ _).trans (sub_add_sub_cancel _ _ _))).trans step3.symm

/-! ### §5 steps 6-7: `exists_trade`, Leray's theorem, `h1CoverEquiv` -/

/-- Forster 14.6(a), qualitative (all `D`): cocycles on any refinement of a good cover are, up to
coboundary, restrictions of cocycles on the good cover. THE Schwartz surjectivity input for
finiteness-and-chi. -/
theorem exists_trade (h𝒰 : 𝒰.IsGood) (τ : Fin 𝒱.n → Fin 𝒰.n) (hτ : IsRefIdx 𝒰 𝒱 τ)
    (f : Z1 D 𝒱) :
    ∃ (F : Z1 D 𝒰) (g : C0 D 𝒱),
      (resZ1 D τ hτ F : C1 D 𝒱) = (f : C1 D 𝒱) + d0 D 𝒱 g := by
  obtain ⟨gFam, hgFam⟩ := exists_splitting D h𝒰 f.2
  obtain ⟨F₀, hF₀⟩ := exists_crossGlueFam D f.2 hgFam
  have hF₀mem : F₀ ∈ Z1 D 𝒰 := crossGlueFam_mem_Z1 D hF₀
  have hadd := resC1_crossGlueFam_add_eq D τ hτ f.2 hgFam hF₀
  refine ⟨-(⟨F₀, hF₀mem⟩ : Z1 D 𝒰), -(tradeH0 D τ hτ gFam), ?_⟩
  have hneg : -(resC1 D τ hτ F₀) = (f : C1 D 𝒱) - d0 D 𝒱 (tradeH0 D τ hτ gFam) :=
    neg_eq_iff_add_eq_zero.2 ((add_sub_assoc _ _ _).symm.trans (sub_eq_zero.mpr hadd))
  exact (map_neg (resC1 D τ hτ) F₀).trans
    (hneg.trans ((sub_eq_add_neg _ _).trans
      (congrArg ((f : C1 D 𝒱) + ·) (map_neg (d0 D 𝒱) _).symm)))

/-- Forster 14.6(a) at `H1Cover`-level: the qualitative trade. -/
theorem resH1_surjective_of_isGood (h𝒰 : 𝒰.IsGood) (τ : Fin 𝒱.n → Fin 𝒰.n)
    (hτ : IsRefIdx 𝒰 𝒱 τ) : Function.Surjective (resH1 D τ hτ) := by
  intro ξ
  obtain ⟨f, rfl⟩ := H1Cover.mk_surjective D 𝒱 ξ
  obtain ⟨F, g, hFg⟩ := exists_trade D h𝒰 τ hτ f
  refine ⟨H1Cover.mk D 𝒰 F, (resH1_mk D τ hτ F).trans ?_⟩
  apply (Submodule.Quotient.eq _).2
  exact ⟨g, (eq_sub_iff_add_eq).2 ((add_comm _ _).trans hFg.symm)⟩

/-- **LERAY** (Forster 12.8 surjectivity half; injectivity is cech's `toH1_injective`,
already on disk). Discharges the interface recorded in cech's `Colimit.lean`. -/
theorem toH1_surjective_of_isGood (h𝒰 : 𝒰.IsGood) : Function.Surjective (toH1 D 𝒰) := by
  intro ξ
  obtain ⟨𝒲, c, hc⟩ := exists_rep D ξ
  obtain ⟨c', hc'⟩ := resH1_surjective_of_isGood D h𝒰 (chosenRefIdx (le_meet_left 𝒰 𝒲))
    (chosenRefIdx_spec (le_meet_left 𝒰 𝒲)) (resH1' D (le_meet_right 𝒰 𝒲) c)
  refine ⟨c', (toH1_resH1 D (chosenRefIdx (le_meet_left 𝒰 𝒲))
    (chosenRefIdx_spec (le_meet_left 𝒰 𝒲)) c').symm.trans ?_⟩
  exact (congrArg (toH1 D (FinCover.meet 𝒰 𝒲)) hc').trans
    ((toH1_resH1' D (le_meet_right 𝒰 𝒲) c).trans hc)

/-- Cover-level `H¹` computes the colimit on good covers — finiteness transfers dimensions
through this. -/
noncomputable def h1CoverEquiv (h𝒰 : 𝒰.IsGood) : H1Cover D 𝒰 ≃ₗ[ℂ] H1 D :=
  LinearEquiv.ofBijective (toH1 D 𝒰) ⟨toH1_injective D 𝒰, toH1_surjective_of_isGood D h𝒰⟩

@[simp] theorem h1CoverEquiv_apply (h𝒰 : 𝒰.IsGood) (c : H1Cover D 𝒰) :
    h1CoverEquiv D h𝒰 c = toH1 D 𝒰 c := by rfl

end RS.Cech
