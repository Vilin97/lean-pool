/-
Copyright (c) 2026 Christopher Albert. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Albert
-/

import LeanPool.Stafford38.AlgebraicAnalysis.Module.RankTorsion
import Mathlib.LinearAlgebra.Dimension.DivisionRing

/-!
# Rank additivity for split sequences

Packet 2 cannot currently assert that noncommutative Ore localization is flat:
the pinned Mathlib has no such theorem.  This file therefore proves the exact
additivity statements that require only an explicit linear equivalence after
localization.  In particular, whenever a localized short exact sequence is
known to split, its localized middle term is equivalent to a product and the
rank is additive.  No flatness or exactness interface is postulated here.
-/

namespace AlgebraicAnalysis
namespace RankExact

open OreLocalization
open nonZeroDivisors

universe u v

section DivisionRing

variable {Q : Type u} [DivisionRing Q]
variable {V W : Type v} [AddCommGroup V] [Module Q V]
variable [AddCommGroup W] [Module Q W]

theorem rank_prod_add :
    Module.rank Q (V × W) = Module.rank Q V + Module.rank Q W := by
  exact rank_prod'

theorem rank_add_of_linearEquiv_prod {U : Type v}
    [AddCommGroup U] [Module Q U]
    (e : U ≃ₗ[Q] V × W) :
    Module.rank Q U = Module.rank Q V + Module.rank Q W := by
  rw [e.rank_eq, rank_prod_add]

theorem rank_add_of_split_exact
    {U : Type v} [AddCommGroup U] [Module Q U]
    (i : V →ₗ[Q] U) (p : U →ₗ[Q] W)
    (r : U →ₗ[Q] V) (s : W →ₗ[Q] U)
    (hri : r.comp i = LinearMap.id)
    (hps : p.comp s = LinearMap.id)
    (hpi : p.comp i = 0)
    (hrs : r.comp s = 0)
    (hdecomp : i.comp r + s.comp p = LinearMap.id) :
    Module.rank Q U = Module.rank Q V + Module.rank Q W := by
  let f : U →ₗ[Q] V × W := LinearMap.prod r p
  let g : V × W →ₗ[Q] U := LinearMap.coprod i s
  have hgf : g.comp f = LinearMap.id := by
    ext u
    change i (r u) + s (p u) = u
    exact LinearMap.congr_fun hdecomp u
  have hfg : f.comp g = LinearMap.id := by
    apply LinearMap.ext
    intro z
    rcases z with ⟨v, w⟩
    apply Prod.ext
    · change r (i v + s w) = v
      rw [map_add]
      have hri' : r (i v) = v := by
        simpa only [LinearMap.comp_apply, LinearMap.id_apply] using
          LinearMap.congr_fun hri v
      have hrs' : r (s w) = 0 := by
        simpa only [LinearMap.comp_apply, LinearMap.zero_apply] using
          LinearMap.congr_fun hrs w
      rw [hri', hrs', add_zero]
    · change p (i v + s w) = w
      rw [map_add]
      have hpi' : p (i v) = 0 := by
        simpa only [LinearMap.comp_apply, LinearMap.zero_apply] using
          LinearMap.congr_fun hpi v
      have hps' : p (s w) = w := by
        simpa only [LinearMap.comp_apply, LinearMap.id_apply] using
          LinearMap.congr_fun hps w
      rw [hpi', hps', zero_add]
  have hf : Function.Bijective f := by
    constructor
    · intro u₁ u₂ h
      have hgfu (u : U) : g (f u) = u := by
        simpa only [LinearMap.comp_apply, LinearMap.id_apply] using
          LinearMap.congr_fun hgf u
      calc
        u₁ = g (f u₁) := (hgfu u₁).symm
        _ = g (f u₂) := congrArg g h
        _ = u₂ := hgfu u₂
    · intro z
      have hfgz (z : V × W) : f (g z) = z := by
        simpa only [LinearMap.comp_apply, LinearMap.id_apply] using
          LinearMap.congr_fun hfg z
      exact ⟨g z, hfgz z⟩
  exact rank_add_of_linearEquiv_prod (LinearEquiv.ofBijective f hf)

theorem finrank_prod_add [Module.Finite Q V] [Module.Finite Q W] :
    Module.finrank Q (V × W) = Module.finrank Q V + Module.finrank Q W := by
  exact Module.finrank_prod

@[nolint unusedArguments]
theorem finrank_add_of_linearEquiv_prod {U : Type v}
    [AddCommGroup U] [Module Q U] [Module.Finite Q U]
    [Module.Finite Q V] [Module.Finite Q W]
    (e : U ≃ₗ[Q] V × W) :
    Module.finrank Q U = Module.finrank Q V + Module.finrank Q W := by
  rw [e.finrank_eq, finrank_prod_add]

end DivisionRing

section LocalizedOre

variable {R : Type u} [Ring R] [Nontrivial R] [NoZeroDivisors R]
variable [OreLocalization.OreSet (Rᵐᵒᵖ)⁰]
variable {M N P : Type v}
variable [AddCommGroup M] [Module Rᵐᵒᵖ M]
variable [AddCommGroup N] [Module Rᵐᵒᵖ N]
variable [AddCommGroup P] [Module Rᵐᵒᵖ P]

open AlgebraicAnalysis.RankTorsion

theorem oreRank_add_of_localized_prod_equiv
    (e : LocalizedRightModule R M ≃ₗ[FractionRingOp R]
      (LocalizedRightModule R N × LocalizedRightModule R P)) :
    oreRank (R := R) M = oreRank (R := R) N + oreRank (R := R) P := by
  rw [oreRank_eq_rank_localized, e.rank_eq, rank_prod_add,
    oreRank_eq_rank_localized, oreRank_eq_rank_localized]

end LocalizedOre


end RankExact
end AlgebraicAnalysis
