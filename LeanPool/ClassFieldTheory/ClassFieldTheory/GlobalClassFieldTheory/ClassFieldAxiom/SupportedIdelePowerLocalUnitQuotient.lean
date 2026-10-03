/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.ClassFieldAxiom.IdelePowerLocalUnitSubgroup
public import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.RayClass.Approximation
/-!
# Supported idele power-local-unit quotient

This module restricts the power-local-unit subgroup to ideles supported at
the prescribed finite places and identifies the resulting quotient with the
product of its archimedean and finite local power-class groups.
-/

@[expose] public section

open scoped NumberField NNReal IsMulCommutative
open NumberField IsDedekindDomain
open KummerTheory

noncomputable
section

namespace GlobalClassFieldTheory.ClassFieldAxiom

variable {K : Type*} [Field K] [NumberField K]

open scoped Classical in
/-- A surjective homomorphism identifies the quotient by its specified kernel with the target. -/
noncomputable def quotientEquivOfSurjectiveWithKernel
    {G H : Type*} [Group G] [Group H]
    (f : G →* H)
    (N : Subgroup G) [N.Normal]
    (hf : Function.Surjective f)
    (hker : f.ker = N) :
    G ⧸ N ≃* H :=
  (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective f hf)

open scoped Classical in
/-- The power/local-unit subgroup `h(S,T)`, regarded inside
`I_K^{S ∪ T}`. -/
def supportedIdelePowerLocalUnitSubgroup
    (n : ℕ+)
    (S T : Finset (HeightOneSpectrum (𝓞 K))) :
    Subgroup
      (IdeleGroup.supportedAt
        (K := K) (S ∪ T : Set (HeightOneSpectrum (𝓞 K)))) :=
  (idelePowerLocalUnitSubgroup (K := K) n S T).comap
    (IdeleGroup.supportedAt
      (K := K) (S ∪ T : Set (HeightOneSpectrum (𝓞 K)))).subtype

open scoped Classical in
/-- Membership in `h(S,T)` automatically supplies the restricted-product
condition defining `I_K^{S ∪ T}`. -/
theorem idelePowerLocalUnitSubgroup_le_supportedAt
    (n : ℕ+)
    (S T : Finset (HeightOneSpectrum (𝓞 K))) :
    idelePowerLocalUnitSubgroup (K := K) n S T ≤
      IdeleGroup.supportedAt
        (K := K) (S ∪ T : Set (HeightOneSpectrum (𝓞 K))) := by
  intro a ha
  rw [IdeleGroup.mem_supportedAt_iff]
  intro v hv
  apply
    ((mem_idelePowerLocalUnitSubgroup_iff
      (K := K) n S T a).mp ha).2.2 v
  simpa using hv

open scoped Classical in
/-- Reduction modulo local `n`-th powers at all infinite places and at the
finite places in `S`.  The coordinates in `T` and the integral coordinates
away from `S ∪ T` disappear in the supported-idele index calculation. -/
def supportedIdelePowerClassMap
    (n : ℕ+)
    (S T : Finset (HeightOneSpectrum (𝓞 K))) :
    IdeleGroup.supportedAt
        (K := K) (S ∪ T : Set (HeightOneSpectrum (𝓞 K))) →*
      ((
        ∀ w : InfinitePlace K,
          w.Completionˣ ⧸
            (powMonoidHom (n : ℕ) :
              w.Completionˣ →* w.Completionˣ).range) ×
        (∀ v : ↥S,
          (v.1.adicCompletion K)ˣ ⧸
            (powMonoidHom (n : ℕ) :
              (v.1.adicCompletion K)ˣ →*
                (v.1.adicCompletion K)ˣ).range)) where
  toFun a :=
    (fun w =>
      QuotientGroup.mk'
        (powMonoidHom (n : ℕ) :
          w.Completionˣ →* w.Completionˣ).range
        (IdeleGroup.infiniteComponent w a.1),
     fun v =>
      QuotientGroup.mk'
        (powMonoidHom (n : ℕ) :
          (v.1.adicCompletion K)ˣ →*
            (v.1.adicCompletion K)ˣ).range
        (IdeleGroup.finiteComponent v.1 a.1))
  map_one' := by
    apply Prod.ext
    · funext w
      apply (QuotientGroup.eq_one_iff _).mpr
      apply
        (MonoidHom.mem_range
          (G := w.Completionˣ)).mpr
      refine ⟨1, ?_⟩
      rw [powMonoidHom_apply, one_pow]
      exact (IdeleGroup.infiniteComponent w).map_one.symm
    · funext v
      simp
  map_mul' a b := by
    apply Prod.ext
    · funext w
      change
        QuotientGroup.mk'
            (powMonoidHom (n : ℕ) :
              w.Completionˣ →* w.Completionˣ).range
            (IdeleGroup.infiniteComponent w (a.1 * b.1)) =
          QuotientGroup.mk'
              (powMonoidHom (n : ℕ) :
                w.Completionˣ →* w.Completionˣ).range
              (IdeleGroup.infiniteComponent w a.1) *
            QuotientGroup.mk'
              (powMonoidHom (n : ℕ) :
                w.Completionˣ →* w.Completionˣ).range
              (IdeleGroup.infiniteComponent w b.1)
      rw [map_mul, map_mul]
    · funext v
      simp

open scoped Classical in
/-- The kernel of the local-power class map is precisely `h(S,T)` inside
`I_K^{S ∪ T}`. -/
theorem supportedIdelePowerClassMap_ker
    (n : ℕ+)
    (S T : Finset (HeightOneSpectrum (𝓞 K))) :
    (supportedIdelePowerClassMap (K := K) n S T).ker =
      supportedIdelePowerLocalUnitSubgroup (K := K) n S T := by
  ext a
  rw [MonoidHom.mem_ker]
  constructor
  · intro ha
    rw [supportedIdelePowerLocalUnitSubgroup,
      Subgroup.mem_comap,
      mem_idelePowerLocalUnitSubgroup_iff]
    refine ⟨?_, ?_, ?_⟩
    · intro w
      have hw := congrArg (fun q => q.1 w) ha
      rw [Prod.fst_one, Pi.one_apply] at hw
      exact (QuotientGroup.eq_one_iff _).mp hw
    · intro v hv
      let vS : ↥S := ⟨v, hv⟩
      have hvq := congrArg (fun q => q.2 vS) ha
      rw [Prod.snd_one, Pi.one_apply] at hvq
      exact (QuotientGroup.eq_one_iff _).mp hvq
    · intro v hv
      have hv' :
          v ∉ (S ∪ T : Set (HeightOneSpectrum (𝓞 K))) := by
        simpa using hv
      exact
        (IdeleGroup.mem_supportedAt_iff
          (K := K)
          (S ∪ T : Set (HeightOneSpectrum (𝓞 K))) a.1).mp
            a.2 v hv'
  · intro ha
    rw [supportedIdelePowerLocalUnitSubgroup,
      Subgroup.mem_comap,
      mem_idelePowerLocalUnitSubgroup_iff] at ha
    apply Prod.ext
    · funext w
      exact (QuotientGroup.eq_one_iff _).mpr (ha.1 w)
    · funext v
      exact (QuotientGroup.eq_one_iff _).mpr
        (ha.2.1 v.1 v.2)

open scoped Classical in
/-- The local-power class map is onto: choose representatives independently
at the finitely many constrained finite places and at all archimedean
places, then extend the finite family by `1`. -/
theorem supportedIdelePowerClassMap_surjective
    (n : ℕ+)
    (S T : Finset (HeightOneSpectrum (𝓞 K))) :
    Function.Surjective
      (supportedIdelePowerClassMap (K := K) n S T) := by
  intro q
  choose aInf hInf using fun w : InfinitePlace K =>
    QuotientGroup.mk_surjective (q.1 w)
  choose aS hS using fun v : ↥S =>
    QuotientGroup.mk_surjective (q.2 v)
  let alpha : IdeleGroup K :=
    (ContinuousMulEquiv.piUnits.symm aInf,
      IdeleGroup.finiteIdeleOfFinset S aS)
  have hAlpha :
      alpha ∈
        IdeleGroup.supportedAt
          (K := K) (S ∪ T : Set (HeightOneSpectrum (𝓞 K))) := by
    rw [IdeleGroup.mem_supportedAt_iff]
    intro v hv
    have hvS : v ∉ S := by
      intro hvS
      apply hv
      exact Or.inl hvS
    change
      IdeleGroup.finiteIdeleOfFinset S aS v ∈
        (v.adicCompletionIntegers K).units
    rw [IdeleGroup.finiteIdeleOfFinset_apply_notMem S aS v hvS]
    exact Subgroup.one_mem _
  refine ⟨⟨alpha, hAlpha⟩, ?_⟩
  apply Prod.ext
  · funext w
    calc
      QuotientGroup.mk'
          (powMonoidHom (n : ℕ) :
            w.Completionˣ →* w.Completionˣ).range
          (IdeleGroup.infiniteComponent w alpha) =
          QuotientGroup.mk'
            (powMonoidHom (n : ℕ) :
              w.Completionˣ →* w.Completionˣ).range
            (aInf w) := by
        apply congrArg
        change
          ContinuousMulEquiv.piUnits
              (ContinuousMulEquiv.piUnits.symm aInf) w =
            aInf w
        exact congrFun
          (ContinuousMulEquiv.piUnits.apply_symm_apply aInf) w
      _ = q.1 w := hInf w
  · funext v
    calc
      QuotientGroup.mk'
          (powMonoidHom (n : ℕ) :
            (v.1.adicCompletion K)ˣ →*
              (v.1.adicCompletion K)ˣ).range
          (IdeleGroup.finiteComponent v.1 alpha) =
          QuotientGroup.mk'
            (powMonoidHom (n : ℕ) :
              (v.1.adicCompletion K)ˣ →*
                (v.1.adicCompletion K)ˣ).range
            (aS v) := by
        apply congrArg
        exact IdeleGroup.finiteIdeleOfFinset_apply_mem S aS v
      _ = q.2 v := hS v

open scoped Classical in
/-- The algebraic supported-idele index decomposition:

`I_K^{S ∪ T} / h(S,T)` is the product of the local `n`-power class
groups at all infinite places and at the finite places in `S`. -/
noncomputable def supportedIdeleQuotientEquivLocalPowerClasses
    (n : ℕ+)
    (S T : Finset (HeightOneSpectrum (𝓞 K))) :
    IdeleGroup.supportedAt
          (K := K) (S ∪ T : Set (HeightOneSpectrum (𝓞 K))) ⧸
        supportedIdelePowerLocalUnitSubgroup (K := K) n S T ≃*
      ((
        ∀ w : InfinitePlace K,
          w.Completionˣ ⧸
            (powMonoidHom (n : ℕ) :
              w.Completionˣ →* w.Completionˣ).range) ×
        (∀ v : ↥S,
          (v.1.adicCompletion K)ˣ ⧸
            (powMonoidHom (n : ℕ) :
              (v.1.adicCompletion K)ˣ →*
                (v.1.adicCompletion K)ˣ).range)) :=
  quotientEquivOfSurjectiveWithKernel
    (H :=
      ((
        ∀ w : InfinitePlace K,
          w.Completionˣ ⧸
            (powMonoidHom (n : ℕ) :
              w.Completionˣ →* w.Completionˣ).range) ×
        (∀ v : ↥S,
          (v.1.adicCompletion K)ˣ ⧸
            (powMonoidHom (n : ℕ) :
              (v.1.adicCompletion K)ˣ →*
                (v.1.adicCompletion K)ˣ).range)))
    (supportedIdelePowerClassMap (K := K) n S T)
    (supportedIdelePowerLocalUnitSubgroup (K := K) n S T)
    (supportedIdelePowerClassMap_surjective (K := K) n S T)
    (supportedIdelePowerClassMap_ker (K := K) n S T)

open scoped Classical in
/-- Cardinal form of the supported-idele index decomposition.  The subsequent
local power-index and product-formula calculation evaluates the right-hand
side. -/
theorem card_supportedIdeleQuotient_eq_localPowerClasses
    (n : ℕ+)
    (S T : Finset (HeightOneSpectrum (𝓞 K))) :
    Nat.card
        (IdeleGroup.supportedAt
              (K := K) (S ∪ T : Set (HeightOneSpectrum (𝓞 K))) ⧸
          supportedIdelePowerLocalUnitSubgroup (K := K) n S T) =
      Nat.card
        ((
          ∀ w : InfinitePlace K,
            w.Completionˣ ⧸
              (powMonoidHom (n : ℕ) :
                w.Completionˣ →* w.Completionˣ).range) ×
          (∀ v : ↥S,
            (v.1.adicCompletion K)ˣ ⧸
              (powMonoidHom (n : ℕ) :
                (v.1.adicCompletion K)ˣ →*
                  (v.1.adicCompletion K)ˣ).range)) :=
  Nat.card_congr
    (supportedIdeleQuotientEquivLocalPowerClasses
      (K := K) n S T).toEquiv


end GlobalClassFieldTheory.ClassFieldAxiom
