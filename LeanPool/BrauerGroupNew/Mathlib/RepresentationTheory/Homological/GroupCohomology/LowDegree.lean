/-
Copyright (c) 2026 Yunzhou Xie and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yunzhou Xie, Yichen Feng, Jujian Zhang, Yael Dillies
-/

import Mathlib.RepresentationTheory.Homological.GroupCohomology.LowDegree

/-!
# Low-degree group cohomology compatibility

This file restores upstream aliases and multiplicative cocycle closure lemmas.
-/

variable {G M : Type*} [Group G] [CommGroup M] [MulDistribMulAction G M] {f g : G × G → M}

alias groupCohomology.IsMulCocycle₂.of_mem_cocycles₂ :=
  groupCohomology.isMulCocycle₂_of_mem_cocycles₂

lemma groupCohomology.IsMulCocycle₂.mul
    (hf : groupCohomology.IsMulCocycle₂ f) (hg : groupCohomology.IsMulCocycle₂ g) :
    groupCohomology.IsMulCocycle₂ (f * g) :=
  fun a b c ↦ by simp [hf a, hg a, smul_mul', mul_mul_mul_comm]

instance [Fact <| groupCohomology.IsMulCocycle₂ f] [Fact <| groupCohomology.IsMulCocycle₂ g] :
    Fact <| groupCohomology.IsMulCocycle₂ (f * g) :=
  ⟨groupCohomology.IsMulCocycle₂.mul Fact.out Fact.out⟩
