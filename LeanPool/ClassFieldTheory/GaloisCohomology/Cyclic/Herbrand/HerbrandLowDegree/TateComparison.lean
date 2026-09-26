/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.GaloisCohomology.Cyclic.Herbrand.HerbrandLowDegree.Basic
public import LeanPool.ClassFieldTheory.GaloisCohomology.Cyclic.TateComparison
/-! Comparisons between arithmetic Herbrand quotient presentations and mathlib Tate cohomology. -/

@[expose] public section

open CategoryTheory

namespace CyclicCohomology.ProfiniteCohomology.Herbrand

noncomputable
section

universe u w

private theorem repExact_of_hom_exact {k G : Type u} [CommRing k] [Group G]
    (S : ShortComplex (Rep.{w} k G))
    (h : ∀ b : S.X₂, S.g.hom b = 0 → ∃ a : S.X₁, S.f.hom a = b) :
    S.Exact :=
  (forget₂ (Rep.{w} k G) (ModuleCat.{w} k)).reflects_exact_of_faithful _ <|
    (ShortComplex.moduleCat_exact_iff _).2 h

variable {G A B C : Type}
variable [Group G] [Fintype G] [CommGroup A] [CommGroup B] [CommGroup C]
variable [MulDistribMulAction G A] [MulDistribMulAction G B]
  [MulDistribMulAction G C]

/-- An equivariant homomorphism of multiplicative `G`-modules, regarded as
the corresponding morphism between mathlib's additive `ℤ`-representations. -/
def equivariantRepHom (f : A →* B)
    (hf : ∀ (g : G) (a : A), f (g • a) = g • f a) :
    Rep.ofMulDistribMulAction G A ⟶ Rep.ofMulDistribMulAction G B :=
  Rep.ofHom <|
    (MonoidHom.toAdditive f).toIntLinearMap.intertwiningMap_of_isIntertwiningMap
      (Rep.ofMulDistribMulAction G A).ρ
      (Rep.ofMulDistribMulAction G B).ρ <| by
      intro g a
      apply Additive.ofMul.injective
      exact hf g a.toMul

omit [Fintype G] in
@[simp]
theorem equivariantRepHom_apply (f : A →* B)
    (hf : ∀ (g : G) (a : A), f (g • a) = g • f a) (a : Additive A) :
    equivariantRepHom f hf a = Additive.ofMul (f a.toMul) :=
  rfl

/-- The short complex of mathlib representations associated to two
equivariant multiplicative homomorphisms whose composite is trivial. -/
def equivariantShortComplex
    (i : A →* B) (j : B →* C)
    (hi : ∀ (g : G) (a : A), i (g • a) = g • i a)
    (hj : ∀ (g : G) (b : B), j (g • b) = g • j b)
    (hker : ∀ b : B, j b = 1 ↔ ∃ a : A, i a = b) :
    ShortComplex (Rep ℤ G) :=
  ShortComplex.mk (equivariantRepHom i hi) (equivariantRepHom j hj) <| by
    apply Rep.hom_ext
    ext a
    change Additive.ofMul (j (i a.toMul)) = 0
    apply Additive.ofMul.injective
    exact (hker (i a.toMul)).2 ⟨a.toMul, rfl⟩

omit [Fintype G] in
theorem equivariantShortComplex_shortExact
    (i : A →* B) (j : B →* C)
    (hi : ∀ (g : G) (a : A), i (g • a) = g • i a)
    (hj : ∀ (g : G) (b : B), j (g • b) = g • j b)
    (hker : ∀ b : B, j b = 1 ↔ ∃ a : A, i a = b)
    (hinj : Function.Injective i) (hsurj : Function.Surjective j) :
    (equivariantShortComplex i j hi hj hker).ShortExact := by
  refine
    { exact := repExact_of_hom_exact _ ?_
      mono_f := (Rep.mono_iff_injective _).2 ?_
      epi_g := (Rep.epi_iff_surjective _).2 ?_ }
  · intro b hb
    change Additive.ofMul (j b.toMul) = 0 at hb
    have hb' : j b.toMul = 1 := Additive.ofMul.injective hb
    rcases (hker b.toMul).1 hb' with ⟨a, ha⟩
    refine ⟨Additive.ofMul a, ?_⟩
    change Additive.ofMul (i a) = b
    apply Additive.toMul.injective
    exact ha
  · intro a a' h
    change Additive.ofMul (i a.toMul) = Additive.ofMul (i a'.toMul) at h
    apply Additive.toMul.injective
    apply hinj
    exact Additive.ofMul.injective h
  · intro c
    rcases hsurj c.toMul with ⟨b, hb⟩
    refine ⟨Additive.ofMul b, ?_⟩
    change Additive.ofMul (j b) = c
    apply Additive.toMul.injective
    exact hb

private theorem repNorm_toMul (a : Additive A) :
    Additive.toMul
        ((Rep.ofMulDistribMulAction G A).ρ.norm a) =
      tateNorm G A a.toMul := by
  unfold Rep.ofMulDistribMulAction
  change Additive.toMul
      ((Representation.ofMulDistribMulAction G A).norm a) =
    ∏ g : G, g • a.toMul
  exact Representation.norm_ofMulDistribMulAction_eq a

private theorem repSigmaMinusOne_toMul
    {G A : Type} [CommGroup G] [CommGroup A]
    [MulDistribMulAction G A] (σ : G) (a : Additive A) :
    Additive.toMul
        ((Rep.toAdditive (M := G) (G := A))
          (((Rep.ofMulDistribMulAction G A).applyAsHom σ -
            𝟙 (Rep.ofMulDistribMulAction G A)).hom a)) =
      sigmaMinusOne G A σ a.toMul := by
  unfold Rep.toAdditive
  unfold Rep.ofMulDistribMulAction
  rw [Rep.sub_hom]
  rw [show
    (Rep.Hom.hom
        ((Rep.of (Representation.ofMulDistribMulAction G A)).applyAsHom σ) -
      Rep.Hom.hom
        (𝟙 (Rep.of (Representation.ofMulDistribMulAction G A)))) a =
        Rep.Hom.hom
            ((Rep.of (Representation.ofMulDistribMulAction G A)).applyAsHom σ) a -
          Rep.Hom.hom
            (𝟙 (Rep.of (Representation.ofMulDistribMulAction G A))) a by
    rfl]
  rw [Rep.applyAsHom_apply]
  rw [show
    Rep.Hom.hom
        (𝟙 (Rep.of (Representation.ofMulDistribMulAction G A))) a = a by
    rfl]
  unfold sigmaMinusOne
  rw [show
    ((Rep.of (Representation.ofMulDistribMulAction G A)).ρ σ) a =
      Additive.ofMul (σ • a.toMul) by
    rfl]
  change Additive.toMul
      (Additive.ofMul (σ • a.toMul) - a) =
    σ • a.toMul * (a.toMul)⁻¹
  rw [toMul_sub]
  exact div_eq_mul_inv _ _

/-- Identify degree-zero cohomological cycles with the additive form of the fixed subgroup. -/
def fixedCyclesAddEquiv :
    LinearMap.ker
        (groupCohomology.d₀₁ (Rep.ofMulDistribMulAction G A)).hom ≃+
      Additive (fixedSubgroup G A) where
  toFun x :=
    Additive.ofMul
      ⟨x.1.toMul, by
        have hx : x.1 ∈ (Rep.ofMulDistribMulAction G A).ρ.invariants := by
          rw [← groupCohomology.d₀₁_ker_eq_invariants]
          exact x.2
        intro g
        apply Additive.ofMul.injective
        exact hx g⟩
  invFun x :=
    ⟨Additive.ofMul x.toMul.1, by
      rw [groupCohomology.d₀₁_ker_eq_invariants]
      intro g
      apply Additive.ofMul.injective
      exact x.toMul.2 g⟩
  left_inv x := by
    apply Subtype.ext
    rfl
  right_inv x := by
    apply Additive.ofMul.injective
    apply Subtype.ext
    rfl
  map_add' x y := by
    apply Additive.ofMul.injective
    apply Subtype.ext
    rfl

omit [Fintype G] in
private theorem fixedCyclesAddEquiv_coe
    (x : LinearMap.ker (groupCohomology.d₀₁ (Rep.ofMulDistribMulAction G A)).hom) :
    (fixedCyclesAddEquiv (G := G) (A := A) x).toMul.val = x.val.toMul := rfl

/-- Mathlib's degree-zero Tate cohomology is the arithmetic fixed-point
quotient by the norm image used by `HerbrandH0`. -/
noncomputable def tateH0IsoHerbrandH0 :
    tateCohomology (Rep.ofMulDistribMulAction G A) 0 ≅
      ModuleCat.of ℤ (Additive (HerbrandH0 G A)) := by
  let M := Rep.ofMulDistribMulAction G A
  let S : ShortComplex (ModuleCat ℤ) :=
    ShortComplex.mk M.norm.toModuleCatHom (groupCohomology.d₀₁ M)
      (Rep.norm_comp_d_eq_zero M)
  let eKOwner :
      S.moduleCatLeftHomologyData.K ≅
        ModuleCat.of ℤ
          (LinearMap.ker
            (groupCohomology.d₀₁ (Rep.ofMulDistribMulAction G A)).hom) :=
    eqToIso (by rfl)
  let eK :=
    (eKOwner ≪≫
      ((fixedCyclesAddEquiv (G := G) (A := A)).toIntLinearEquiv
        (modM := inferInstance) (modM₂ := inferInstance)).toModuleIso).toLinearEquiv
  let q : Additive (fixedSubgroup G A) →+ Additive (HerbrandH0 G A) :=
    MonoidHom.toAdditive (HerbrandH0.mk (G := G) (A := A))
  have hboundary :
      (LinearMap.range S.moduleCatToCycles).map eK.toLinearMap =
        q.ker.toIntSubmodule := by
    ext x
    constructor
    · rintro ⟨y, ⟨a, ha⟩, rfl⟩
      subst y
      change Additive A at a
      change q (eK (S.moduleCatToCycles a)) = 0
      apply Additive.ofMul.injective
      change HerbrandH0.mk _ = 1
      apply (HerbrandH0.mk_eq_one_iff _).2
      refine ⟨a.toMul, ?_⟩
      dsimp [eK, fixedCyclesAddEquiv, S, M]
      exact (by exact (repNorm_toMul (G := G) (A := A) a).symm)
    · intro hx
      change q x = 0 at hx
      have hx' : HerbrandH0.mk x.toMul = 1 := by
        apply Additive.ofMul.injective
        exact hx
      rcases (HerbrandH0.mk_eq_one_iff x.toMul).1 hx' with ⟨a, ha⟩
      refine ⟨eK.symm x, ?_, eK.apply_symm_apply x⟩
      refine ⟨Additive.ofMul a, ?_⟩
      apply eK.injective
      rw [eK.apply_symm_apply]
      apply Additive.toMul.injective
      apply Subtype.ext
      have hnorm :
          Additive.toMul
              ((Representation.ofMulDistribMulAction G A).norm
                (Additive.ofMul a)) =
            x.toMul.1 :=
        (Representation.norm_ofMulDistribMulAction_eq
          (G := G) (M := A) (Additive.ofMul a)).trans <| by
            rw [show Additive.toMul (Additive.ofMul a) = a by rfl]
            simpa only [tateNormHom_apply, tateNorm] using ha
      dsimp [eK, fixedCyclesAddEquiv, S, M]
      unfold Rep.ofMulDistribMulAction
      exact hnorm
  let eQ :=
    (Submodule.Quotient.equiv (LinearMap.range S.moduleCatToCycles)
      q.ker.toIntSubmodule eK hboundary).trans
      ((QuotientAddGroup.quotientKerEquivOfSurjective q
        (HerbrandH0.mk_surjective (G := G) (A := A))).toIntLinearEquiv
          (modM₂ := inferInstance))
  exact TateCohomology.isoZeroBoundary M ≪≫
    S.moduleCatHomologyIso ≪≫ eQ.toModuleIso

/-- Identify norm-kernel cycles with the additive form of the multiplicative norm kernel. -/
def normKernelCyclesAddEquiv :
    LinearMap.ker
        (Rep.ofMulDistribMulAction G A).norm.toModuleCatHom.hom ≃+
      Additive (normKernelSubgroup G A) where
  toFun x :=
    let a : Additive A := x.1
    Additive.ofMul
      ⟨a.toMul, by
        change tateNorm G A a.toMul = 1
        have hx := x.2
        change (Rep.ofMulDistribMulAction G A).ρ.norm a = 0 at hx
        exact (by
          exact (repNorm_toMul (G := G) (A := A) a).symm.trans <| by
            rw [hx]
            rfl)⟩
  invFun x :=
    let a : Additive A := Additive.ofMul x.toMul.1
    ⟨a, by
      have hx0 := x.toMul.2
      change tateNorm G A x.toMul.1 = 1 at hx0
      have hx : tateNorm G A a.toMul = 1 := hx0
      change (Rep.ofMulDistribMulAction G A).ρ.norm a = 0
      unfold Rep.ofMulDistribMulAction
      apply Additive.toMul.injective
      change Additive.toMul
          ((Representation.ofMulDistribMulAction G A).norm a) = (1 : A)
      exact
        (Representation.norm_ofMulDistribMulAction_eq
          (G := G) (M := A) a).trans <| by
            simpa [tateNorm] using hx⟩
  left_inv x := by
    apply Subtype.ext
    rfl
  right_inv x := by
    apply Additive.ofMul.injective
    apply Subtype.ext
    rfl
  map_add' x y := by
    apply Additive.ofMul.injective
    apply Subtype.ext
    rfl

private theorem normKernelCyclesAddEquiv_coe
    (x : LinearMap.ker (Rep.ofMulDistribMulAction G A).norm.toModuleCatHom.hom) :
    (normKernelCyclesAddEquiv (G := G) (A := A) x).toMul.val = x.val.toMul := rfl

/-- Identify degree-minus-one Tate cohomology with the Herbrand quotient
for a commutative cyclic group. -/
noncomputable def tateHMinusOneIsoHerbrandHMinusOneOfCommGroup
    {G A : Type} [CommGroup G] [Fintype G] [CommGroup A]
    [MulDistribMulAction G A]
    (σ : G) (hgen : ∀ g : G, g ∈ Subgroup.zpowers σ) :
    tateCohomology (Rep.ofMulDistribMulAction G A) (-1) ≅
      ModuleCat.of ℤ (Additive (HerbrandHMinusOne G A σ)) := by
  let M := Rep.ofMulDistribMulAction G A
  let S := Rep.FiniteCyclicGroup.subCompNormHom M σ
  let eKOwner :
      S.moduleCatLeftHomologyData.K ≅
        ModuleCat.of ℤ
          (LinearMap.ker
            (Rep.ofMulDistribMulAction G A).norm.toModuleCatHom.hom) :=
    eqToIso (by rfl)
  let eK :=
    (eKOwner ≪≫
      ((normKernelCyclesAddEquiv (G := G) (A := A)).toIntLinearEquiv
        (modM := inferInstance) (modM₂ := inferInstance)).toModuleIso).toLinearEquiv
  let q : Additive (normKernelSubgroup G A) →+
      Additive (HerbrandHMinusOne G A σ) :=
    MonoidHom.toAdditive (HerbrandHMinusOne.mk (G := G) (A := A) σ)
  have hboundary :
      (LinearMap.range S.moduleCatToCycles).map eK.toLinearMap =
        q.ker.toIntSubmodule := by
    ext x
    constructor
    · rintro ⟨y, ⟨a, ha⟩, rfl⟩
      subst y
      change Additive A at a
      change q (eK (S.moduleCatToCycles a)) = 0
      apply Additive.ofMul.injective
      change HerbrandHMinusOne.mk σ _ = 1
      apply (HerbrandHMinusOne.mk_eq_one_iff σ _).2
      refine ⟨a.toMul, ?_⟩
      dsimp [eK, normKernelCyclesAddEquiv, S, M]
      exact (by exact (repSigmaMinusOne_toMul (G := G) (A := A) σ a).symm)
    · intro hx
      change q x = 0 at hx
      have hx' : HerbrandHMinusOne.mk σ x.toMul = 1 := by
        apply Additive.ofMul.injective
        exact hx
      rcases (HerbrandHMinusOne.mk_eq_one_iff σ x.toMul).1 hx' with ⟨a, ha⟩
      refine ⟨eK.symm x, ?_, eK.apply_symm_apply x⟩
      refine ⟨Additive.ofMul a, ?_⟩
      apply eK.injective
      rw [eK.apply_symm_apply]
      apply Additive.toMul.injective
      apply Subtype.ext
      dsimp [eK, normKernelCyclesAddEquiv, S, M]
      exact (by
        have hσ := repSigmaMinusOne_toMul (G := G) (A := A) σ (Additive.ofMul a)
        rw [show Additive.toMul (Additive.ofMul a) = a by rfl] at hσ
        exact hσ.trans ha)
  let eQ :=
    (Submodule.Quotient.equiv (LinearMap.range S.moduleCatToCycles)
      q.ker.toIntSubmodule eK hboundary).trans
      ((QuotientAddGroup.quotientKerEquivOfSurjective q
        (HerbrandHMinusOne.mk_surjective (G := G) (A := A) σ)).toIntLinearEquiv
          (modM₂ := inferInstance))
  exact TateCohomology.isoFiniteCyclicNegOne M σ hgen ≪≫
    S.moduleCatHomologyIso ≪≫ eQ.toModuleIso

/-- For a chosen generator `σ`, mathlib's degree-minus-one Tate cohomology is
the arithmetic quotient `ker N / im (σ - 1)` used by `HerbrandHMinusOne`. -/
noncomputable def tateHMinusOneIsoHerbrandHMinusOne
    (σ : G) (hgen : ∀ g : G, g ∈ Subgroup.zpowers σ) :
    tateCohomology (Rep.ofMulDistribMulAction G A) (-1) ≅
      ModuleCat.of ℤ (Additive (HerbrandHMinusOne G A σ)) := by
  letI : IsCyclic G := ⟨⟨σ, hgen⟩⟩
  letI : CommGroup G := IsCyclic.commGroup
  exact tateHMinusOneIsoHerbrandHMinusOneOfCommGroup σ hgen

end

end CyclicCohomology.ProfiniteCohomology.Herbrand
