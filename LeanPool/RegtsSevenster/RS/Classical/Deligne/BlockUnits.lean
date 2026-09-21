/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

import LeanPool.RegtsSevenster.RS.Classical.SchurTheory.NativeFaithful
import LeanPool.RegtsSevenster.RS.Classical.Interfaces.SchurPackage

/-!
# Matrix units inside a block

Inside each block of the symmetric-group algebra the central
idempotent `P.e μ` of a `SchurPackage` splits as a sum of `P.dim μ`
orthogonal nonzero idempotents (`SchurPackage.exists_block_units`).

The route is through a simple submodule of the regular module lying
inside the block, which exists because the group algebra is
semisimple and the idempotent is nonzero
(`exists_simple_of_central_idem`).  The native action on such a
carrier sends the idempotent to the identity, is surjective onto
the endomorphisms of the carrier (`nPsi_surjective`, from
`mPsiLin_surjective`), and is injective on the block
(`block_faithful`); comparing dimensions against `block_rank`
identifies the dimension of the carrier with `P.dim μ`, and the
rank-one projections attached to a basis of the carrier
(`basisProj`) pull back to the required family of units.
-/

namespace RS

open Module

universe u

/-- The rank-one idempotent attached to a basis vector: the
projection onto the `i`-th coordinate line of the basis `b`. -/
noncomputable def basisProj {V : Type*} [AddCommGroup V]
    [Module ℂ V] {d : ℕ} (b : Basis (Fin d) ℂ V) (i : Fin d) :
    Module.End ℂ V :=
  (b.coord i).smulRight (b i)

variable {V : Type*}

/-- The projection scales the `i`-th coordinate back onto the
`i`-th basis vector. -/
theorem basisProj_apply [AddCommGroup V] [Module ℂ V] {d : ℕ}
    (b : Basis (Fin d) ℂ V) (i : Fin d)
    (m : V) : basisProj b i m = b.repr m i • b i := by
  unfold basisProj
  rw [LinearMap.smulRight_apply, Basis.coord_apply]

/-- Each basis projection is idempotent. -/
theorem basisProj_mul_self [AddCommGroup V] [Module ℂ V] {d : ℕ}
    (b : Basis (Fin d) ℂ V) (i : Fin d) :
    basisProj b i * basisProj b i = basisProj b i := by
  apply LinearMap.ext
  intro m
  simp only [Module.End.mul_apply, basisProj_apply, map_smul,
    Basis.repr_self, Finsupp.single_eq_same, one_smul]

/-- Distinct basis projections are orthogonal. -/
theorem basisProj_mul_ne [AddCommGroup V] [Module ℂ V] {d : ℕ}
    (b : Basis (Fin d) ℂ V) {i j : Fin d}
    (hij : i ≠ j) : basisProj b i * basisProj b j = 0 := by
  apply LinearMap.ext
  intro m
  simp only [Module.End.mul_apply, basisProj_apply, map_smul,
    Basis.repr_self, LinearMap.zero_apply]
  rw [Finsupp.single_eq_of_ne hij, zero_smul, smul_zero]

/-- The basis projections sum to the identity. -/
theorem sum_basisProj [AddCommGroup V] [Module ℂ V] {d : ℕ}
    (b : Basis (Fin d) ℂ V) :
    ∑ i, basisProj b i = 1 := by
  apply LinearMap.ext
  intro m
  simp only [LinearMap.sum_apply, basisProj_apply,
    Module.End.one_apply]
  exact b.sum_repr m

/-- Each basis projection is nonzero. -/
theorem basisProj_ne_zero [AddCommGroup V] [Module ℂ V] {d : ℕ}
    (b : Basis (Fin d) ℂ V) (i : Fin d) :
    basisProj b i ≠ 0 := by
  intro h0
  have h1 := LinearMap.congr_fun h0 (b i)
  rw [basisProj_apply, Basis.repr_self, Finsupp.single_eq_same,
    one_smul, LinearMap.zero_apply] at h1
  exact b.ne_zero i h1

/-- Every nonzero central idempotent of a complex group algebra
has a simple submodule of the regular module inside its block: a
simple submodule on which it multiplies as the identity. -/
theorem exists_simple_of_central_idem {G : Type*} [Group G]
    [Fintype G] (e : MonoidAlgebra ℂ G) (hidem : e * e = e)
    (hcentral : ∀ x : MonoidAlgebra ℂ G, e * x = x * e)
    (hne : e ≠ 0) :
    ∃ S : Submodule (MonoidAlgebra ℂ G) (MonoidAlgebra ℂ G),
      IsSimpleModule (MonoidAlgebra ℂ G) S ∧
        ∀ s ∈ S, e * s = s := by
  classical
  have hex : ∃ T : Submodule (MonoidAlgebra ℂ G)
      (MonoidAlgebra ℂ G),
      IsSimpleModule (MonoidAlgebra ℂ G) T ∧
        ∃ t ∈ T, e * t ≠ 0 := by
    by_contra hno
    push Not at hno
    exact hne (eq_zero_of_kills_simples e fun T hT t ht =>
      hno T hT t ht)
  obtain ⟨T, hT, t, ht, het⟩ := hex
  haveI := hT
  let g : T →ₗ[MonoidAlgebra ℂ G] MonoidAlgebra ℂ G :=
    { toFun := fun s => e * (s : MonoidAlgebra ℂ G)
      map_add' := fun a b => by
        rw [Submodule.coe_add, mul_add]
      map_smul' := fun a s => by
        show e * ((a • s : T) : MonoidAlgebra ℂ G) =
          a • (e * (s : MonoidAlgebra ℂ G))
        rw [Submodule.coe_smul, smul_eq_mul, smul_eq_mul,
          ← mul_assoc, hcentral a, mul_assoc] }
  have hg : ∀ s : T, g s = e * (s : MonoidAlgebra ℂ G) :=
    fun s => rfl
  have hker : LinearMap.ker g = ⊥ := by
    rcases hT.eq_bot_or_eq_top (LinearMap.ker g) with hb | htop
    · exact hb
    · exfalso
      apply het
      have hmem : (⟨t, ht⟩ : T) ∈ LinearMap.ker g := by
        rw [htop]
        trivial
      have h1 := LinearMap.mem_ker.mp hmem
      rw [hg] at h1
      exact h1
  have hinj : Function.Injective g := LinearMap.ker_eq_bot.mp hker
  refine ⟨LinearMap.range g, ?_, ?_⟩
  · exact IsSimpleModule.congr (LinearEquiv.ofInjective g hinj).symm
  · intro s hs
    obtain ⟨w, hw⟩ := LinearMap.mem_range.mp hs
    rw [← hw, hg, ← mul_assoc, hidem]

/-- An element multiplying a submodule of the regular module as
the identity acts as the identity endomorphism of its carrier. -/
theorem nPsi_eq_one_of_forall_eq {G : Type*} [Group G]
    (S : Submodule (MonoidAlgebra ℂ G) (MonoidAlgebra ℂ G))
    (e : MonoidAlgebra ℂ G) (he : ∀ s ∈ S, e * s = s) :
    nPsi S e = 1 := by
  apply LinearMap.ext
  intro m
  rw [show (nPsi S e) m = e • m from
    rhoS_asAlgebraHom_apply S e m]
  apply Subtype.ext
  rw [show ((e • m : subCarrier S) : MonoidAlgebra ℂ G) =
    e * (m : MonoidAlgebra ℂ G) from rfl]
  rw [he _ m.2]
  rfl

/-- The native action of a simple submodule of the regular module
is surjective onto the endomorphisms of its carrier. -/
theorem nPsi_surjective {G : Type*} [Group G] [Fintype G]
    [DecidableEq G]
    (S : Submodule (MonoidAlgebra ℂ G) (MonoidAlgebra ℂ G))
    (hS : IsSimpleModule (MonoidAlgebra ℂ G) S) :
    Function.Surjective (nPsi S) := by
  intro T
  obtain ⟨y, hy⟩ := mPsiLin_surjective S hS
    ((stdEquiv S).toLinearMap ∘ₗ T ∘ₗ
      (stdEquiv S).symm.toLinearMap)
  refine ⟨(y : MonoidAlgebra ℂ G), ?_⟩
  apply LinearMap.ext
  intro m
  have h2 : mPsi S (y : MonoidAlgebra ℂ G) (stdEquiv S m) =
      ((stdEquiv S).toLinearMap ∘ₗ T ∘ₗ
        (stdEquiv S).symm.toLinearMap) (stdEquiv S m) :=
    LinearMap.congr_fun hy (stdEquiv S m)
  rw [mPsi_apply, (stdEquiv S).symm_apply_apply] at h2
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearEquiv.symm_apply_apply] at h2
  exact (stdEquiv S).injective h2

/-- **Block units**: inside each block of the symmetric-group
algebra, the central idempotent `P.e μ` splits as a sum of
`P.dim μ` orthogonal nonzero idempotents of the block. -/
theorem SchurPackage.exists_block_units (P : SchurPackage.{u})
    (μ : YoungDiagram) :
    ∃ u : Fin (P.dim μ) → SymGroupAlgebra μ.card,
      (∀ i, u i * u i = u i) ∧
      (∀ i j, i ≠ j → u i * u j = 0) ∧
      (∀ i, P.e μ * u i = u i) ∧
      (∀ i, u i * P.e μ = u i) ∧
      (∑ i, u i = P.e μ) ∧
      (∀ i, u i ≠ 0) := by
  classical
  have hidem : P.e μ * P.e μ = P.e μ := P.idem μ
  have hcentral : ∀ y : SymGroupAlgebra μ.card,
      P.e μ * y = y * P.e μ := P.central μ
  have hrank : Module.finrank ℂ
      (LinearMap.range (LinearMap.mulLeft ℂ (P.e μ))) =
      P.dim μ ^ 2 := P.block_rank μ
  -- The central idempotent is nonzero, its block having positive
  -- dimension.
  have hne : P.e μ ≠ 0 := by
    intro h0
    rw [h0, LinearMap.mulLeft_zero_eq_zero, LinearMap.range_zero,
      finrank_bot] at hrank
    exact Nat.pos_iff_ne_zero.mp (pow_pos (P.dim_pos μ) 2)
      hrank.symm
  -- A simple submodule inside the block.
  obtain ⟨S, hS, hSb⟩ :=
    exists_simple_of_central_idem (P.e μ) hidem hcentral hne
  haveI := hS
  haveI := IsSimpleModule.nontrivial
    (MonoidAlgebra ℂ (Equiv.Perm (Fin μ.card))) S
  haveI : Nontrivial (subCarrier S) :=
    inferInstanceAs (Nontrivial S)
  have hone : nPsi S (P.e μ) = 1 :=
    nPsi_eq_one_of_forall_eq S (P.e μ) hSb
  have hone_ne : (1 : Module.End ℂ (subCarrier S)) ≠ 0 := by
    intro h1
    obtain ⟨m, hm⟩ := exists_ne (0 : subCarrier S)
    apply hm
    have h2 := LinearMap.congr_fun h1 m
    rwa [Module.End.one_apply, LinearMap.zero_apply] at h2
  -- The kill criterion on the block, through `block_faithful`.
  have hkill : ∀ x : SymGroupAlgebra μ.card,
      nPsi S (P.e μ * x) = 0 → P.e μ * x = 0 := by
    intro x hx0
    have hφ : ((ULift.algEquiv (R := ℂ)).symm.toAlgHom.comp
        (nPsi S) : SymGroupAlgebra μ.card →ₐ[ℂ]
          ULift.{u} (Module.End ℂ (subCarrier S)))
        (P.e μ) ≠ 0 := by
      intro hz
      apply hone_ne
      have h1 : (ULift.algEquiv (R := ℂ)).symm
          (nPsi S (P.e μ)) =
          (0 : ULift.{u} (Module.End ℂ (subCarrier S))) := hz
      rw [hone] at h1
      have h2 := congrArg (ULift.algEquiv (R := ℂ)) h1
      rw [AlgEquiv.apply_symm_apply, map_zero] at h2
      exact h2
    have h0' : ((ULift.algEquiv (R := ℂ)).symm.toAlgHom.comp
        (nPsi S) : SymGroupAlgebra μ.card →ₐ[ℂ]
          ULift.{u} (Module.End ℂ (subCarrier S)))
        (P.e μ * x) = 0 := by
      show (ULift.algEquiv (R := ℂ)).symm
        (nPsi S (P.e μ * x)) = 0
      rw [hx0, map_zero]
    exact P.block_faithful μ
      (ULift.{u} (Module.End ℂ (subCarrier S)))
      ((ULift.algEquiv (R := ℂ)).symm.toAlgHom.comp (nPsi S))
      hφ x h0'
  have hsurj := nPsi_surjective S hS
  -- The block maps bijectively onto the endomorphism algebra of
  -- the carrier, identifying the carrier dimension with `dim μ`.
  let ψ : LinearMap.range (LinearMap.mulLeft ℂ (P.e μ)) →ₗ[ℂ]
      Module.End ℂ (subCarrier S) :=
    (nPsi S).toLinearMap.comp
      (LinearMap.range (LinearMap.mulLeft ℂ (P.e μ))).subtype
  have hψinj : Function.Injective ψ := by
    intro a b hab
    have hd : ψ (a - b) = 0 := by
      rw [map_sub, hab, sub_self]
    obtain ⟨w, hw⟩ := (a - b).2
    have h1 : nPsi S (P.e μ * w) = 0 := by
      rw [show P.e μ * w = ((a - b :
        LinearMap.range (LinearMap.mulLeft ℂ (P.e μ))) :
          SymGroupAlgebra μ.card) from hw]
      exact hd
    have h2 := hkill w h1
    have h3 : a - b = 0 := by
      apply Subtype.ext
      rw [← hw]
      exact h2
    exact sub_eq_zero.mp h3
  have hψsurj : Function.Surjective ψ := by
    intro T
    obtain ⟨x, hx⟩ := hsurj T
    have hmem : P.e μ * x ∈
        LinearMap.range (LinearMap.mulLeft ℂ (P.e μ)) :=
      LinearMap.mem_range.mpr ⟨x, rfl⟩
    refine ⟨⟨P.e μ * x, hmem⟩, ?_⟩
    show nPsi S (P.e μ * x) = T
    rw [map_mul, hone, one_mul, hx]
  have hdim : P.dim μ = nDim S := by
    have hfr := LinearEquiv.finrank_eq
      (LinearEquiv.ofBijective ψ ⟨hψinj, hψsurj⟩)
    rw [hrank] at hfr
    have hEnd : Module.finrank ℂ
        (Module.End ℂ (subCarrier S)) = nDim S * nDim S :=
      Module.finrank_linearMap ℂ ℂ (subCarrier S) (subCarrier S)
    rw [hEnd, ← pow_two] at hfr
    exact Nat.pow_left_injective (by decide) hfr
  -- The units: preimages of the basis projections of the carrier.
  have hfrk : Module.finrank ℂ (subCarrier S) = P.dim μ :=
    hdim.symm
  let b : Basis (Fin (P.dim μ)) ℂ (subCarrier S) :=
    Module.finBasisOfFinrankEq ℂ (subCarrier S) hfrk
  choose x hx using fun i : Fin (P.dim μ) =>
    hsurj (basisProj b i)
  have hval : ∀ i, nPsi S (P.e μ * x i) = basisProj b i := by
    intro i
    rw [map_mul, hone, one_mul, hx i]
  have hmul_self : ∀ i,
      P.e μ * x i * (P.e μ * x i) = P.e μ * x i := by
    intro i
    have hz : nPsi S
        (P.e μ * (x i * (P.e μ * x i) - x i)) = 0 := by
      rw [mul_sub, ← mul_assoc, map_sub, map_mul, hval i,
        basisProj_mul_self, sub_self]
    have h4 := hkill _ hz
    rw [mul_sub, ← mul_assoc] at h4
    exact sub_eq_zero.mp h4
  have hmul_ne : ∀ i j, i ≠ j →
      P.e μ * x i * (P.e μ * x j) = 0 := by
    intro i j hij
    have hz : nPsi S
        (P.e μ * (x i * (P.e μ * x j))) = 0 := by
      rw [← mul_assoc, map_mul, hval i, hval j,
        basisProj_mul_ne b hij]
    have h4 := hkill _ hz
    rw [← mul_assoc] at h4
    exact h4
  have hleft : ∀ i, P.e μ * (P.e μ * x i) = P.e μ * x i := by
    intro i
    rw [← mul_assoc, hidem]
  have hright : ∀ i, P.e μ * x i * P.e μ = P.e μ * x i := by
    intro i
    rw [← hcentral (P.e μ * x i)]
    exact hleft i
  have hsum : ∑ i, P.e μ * x i = P.e μ := by
    have hz : nPsi S (P.e μ * ((∑ i, x i) - 1)) = 0 := by
      rw [mul_sub, mul_one, map_sub, map_mul, hone, one_mul,
        map_sum]
      simp only [hx]
      rw [sum_basisProj b, sub_self]
    have h4 := hkill _ hz
    rw [mul_sub, mul_one, Finset.mul_sum] at h4
    exact sub_eq_zero.mp h4
  have hnz : ∀ i, P.e μ * x i ≠ 0 := by
    intro i h0
    apply basisProj_ne_zero b i
    rw [← hval i, h0, map_zero]
  exact ⟨fun i => P.e μ * x i, hmul_self, hmul_ne, hleft,
    hright, hsum, hnz⟩

end RS
