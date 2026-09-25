/-
Copyright (c) 2026 Dmitrii Zakharov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dmitrii Zakharov
-/
module


public import LeanPool.ErdosGinzburgZiv.EGZ.Decomposition.Levels
public import LeanPool.ErdosGinzburgZiv.EGZ.Decomposition.ModularRank

/-!
# Injective coordinate transport at equal levels

If a new represented space is contained in an old one and an integral
coordinate map factors the old representation through the new one, equal
levels force equal spaces and equal ranks. The factor is then bijective
modulo the prime, injective on integer lattices, and bijective over the reals.
-/

@[expose] public section

namespace EGZ.FpRepresentation

variable {p d : ℕ} [Fact p.Prime] {F G : ConvexFlag}

/-- At equal levels, any affine factor between the coordinate spaces is
injective over the represented field. -/
theorem factor_modp_injective_of_level_eq (R : FpRepresentation p d F)
    (T : FpRepresentation p d G) (x : F.Node) (y : G.Node)
    (A : FpCoord p (G.rank y) →ᵃ[ZMod p] FpCoord p (F.rank x))
    (hspace : T.space y ≤ R.space x)
    (hfactor : ∀ v ∈ T.space y, R.map x v = A (T.map y v))
    (hlevel : R.level x = T.level y) : Function.Injective A := by
  obtain ⟨hcodim, hrank⟩ := R.codimension_eq_and_rank_eq_of_level_eq T x y hlevel
  have hs := R.space_eq_of_codimension_eq_of_le T x y hspace hcodim
  have hsurj := R.factor_surjective_of_space_eq T x y A hs hfactor
  apply A.linear_injective_iff.mp
  apply (LinearMap.injective_iff_surjective_of_finrank_eq_finrank ?_).mpr
    (A.linear_surjective_iff.mpr hsurj)
  simpa using hrank.symm

theorem factor_real_injective_of_level_eq (R : FpRepresentation p d F)
    (T : FpRepresentation p d G) (x : F.Node) (y : G.Node)
    (A : IntegralAffineMap (G.rank y) (F.rank x))
    (hspace : T.space y ≤ R.space x)
    (hfactor : ∀ v ∈ T.space y, R.map x v = A.modp p (T.map y v))
    (hlevel : R.level x = T.level y) : Function.Injective A.real :=
  A.real_injective_of_modp_of_rank_eq
    (R.codimension_eq_and_rank_eq_of_level_eq T x y hlevel).2.symm
    (R.factor_modp_injective_of_level_eq T x y (A.modp p) hspace hfactor hlevel)

theorem factor_integer_injective_of_level_eq (R : FpRepresentation p d F)
    (T : FpRepresentation p d G) (x : F.Node) (y : G.Node)
    (A : IntegralAffineMap (G.rank y) (F.rank x))
    (hspace : T.space y ≤ R.space x)
    (hfactor : ∀ v ∈ T.space y, R.map x v = A.modp p (T.map y v))
    (hlevel : R.level x = T.level y) : Function.Injective A.integer :=
  A.integer_injective_of_modp_of_rank_eq
    (R.codimension_eq_and_rank_eq_of_level_eq T x y hlevel).2.symm
    (R.factor_modp_injective_of_level_eq T x y (A.modp p) hspace hfactor hlevel)

/-- Real coordinate transport at an unchanged level is an affine
isomorphism; lattice indices need not be one. -/
theorem factor_real_bijective_of_level_eq (R : FpRepresentation p d F)
    (T : FpRepresentation p d G) (x : F.Node) (y : G.Node)
    (A : IntegralAffineMap (G.rank y) (F.rank x))
    (hspace : T.space y ≤ R.space x)
    (hfactor : ∀ v ∈ T.space y, R.map x v = A.modp p (T.map y v))
    (hlevel : R.level x = T.level y) : Function.Bijective A.real := by
  have hi := R.factor_real_injective_of_level_eq T x y A hspace hfactor hlevel
  refine ⟨hi, A.real.linear_surjective_iff.mp ?_⟩
  apply (LinearMap.injective_iff_surjective_of_finrank_eq_finrank ?_).mp
    (A.real.linear_injective_iff.mpr hi)
  simpa using (R.codimension_eq_and_rank_eq_of_level_eq T x y hlevel).2.symm

theorem transition_real_injective_of_level_eq (R : FpRepresentation p d F)
    {y x : F.Node} (h : y ≤ x) (heq : R.level y = R.level x) :
    Function.Injective (F.transition h).real :=
  R.factor_real_injective_of_level_eq R x y (F.transition h) (R.space_mono h)
    (fun _ hv ↦ R.compatible h hv) heq.symm

theorem transition_integer_injective_of_level_eq (R : FpRepresentation p d F)
    {y x : F.Node} (h : y ≤ x) (heq : R.level y = R.level x) :
    Function.Injective (F.transition h).integer :=
  R.factor_integer_injective_of_level_eq R x y (F.transition h) (R.space_mono h)
    (fun _ hv ↦ R.compatible h hv) heq.symm

end EGZ.FpRepresentation
