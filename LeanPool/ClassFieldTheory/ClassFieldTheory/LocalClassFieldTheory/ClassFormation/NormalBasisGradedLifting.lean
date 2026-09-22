/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.ClassFieldTheory.LocalClassFieldTheory.ClassFormation.NormalBasis
import LeanPool.ClassFieldTheory.ClassFieldTheory.LocalClassFieldTheory.ClassFormation.PrincipalUnitGraded
import LeanPool.ClassFieldTheory.ClassFieldTheory.LocalClassFieldTheory.ClassFormation.NormalBasisGaloisAction
import LeanPool.ClassFieldTheory.GaloisCohomology.Cyclic.Herbrand.HerbrandLowDegree.Basic
/-! Provides the public declarations in the
  `LocalClassFieldTheory.ClassFormation.NormalBasisGradedLifting` Lean module. -/

namespace LocalClassFieldTheory

open LocalFieldTheory

open CyclicCohomology

noncomputable section

universe u

open scoped BigOperators ValuativeRel
open IsNonarchimedeanLocalField
open CyclicCohomology.ProfiniteCohomology.Herbrand

variable (K L : Type u) [Field K] [Field L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [ValuativeRel L]
  [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
  [IsIntegralClosure 𝒪[L] 𝒪[K] L]

/-- The class `u - 1` in the normal-basis lattice graded piece is equivariant
for the actual Galois action on integer units and the transported action on
the lattice quotient. -/
theorem chosenNormalBasisPrincipalUnitLatticeClass_galoisGroup
    (n : Nat) (sigma : Gal(L/K)) (u : 𝒪[L]ˣ)
    (hu : u ∈ chosenNormalBasisPrincipalUnitSet K L n) :
    letI := galoisGroupIntegerUnitsMulDistribMulActionOfIsIntegralClosure K L
    letI := galoisGroupChosenNormalBasisLatticeSuccQuotDistribMulAction K L n
    chosenNormalBasisPrincipalUnitLatticeClass K L n (sigma • u)
        (galoisGroup_smul_mem_chosenNormalBasisPrincipalUnitSet
          (K := K) (L := L) n sigma hu) =
      sigma • chosenNormalBasisPrincipalUnitLatticeClass K L n u hu := by
  let := galoisGroupIntegerUnitsMulDistribMulActionOfIsIntegralClosure K L
  let := galoisGroupChosenNormalBasisLatticeSuccQuotDistribMulAction K L n
  let y : chosenBaseUniformizerPowSubmodule K L n
      (chosenNormalBasisIntegerLattice K L) :=
    ⟨((((u : 𝒪[L]ˣ) : 𝒪[L]) - 1 : 𝒪[L]) : L), hu⟩
  let x : chosenNormalBasisIntegerLattice K L :=
    (chosenNormalBasisIntegerLatticeMulPowLinearEquiv K L n).symm y
  have hxy : chosenNormalBasisIntegerLatticeMulPowLinearEquiv K L n x = y :=
    (chosenNormalBasisIntegerLatticeMulPowLinearEquiv K L n).apply_symm_apply y
  rw [chosenNormalBasisPrincipalUnitLatticeClass,
    chosenNormalBasisPrincipalUnitLatticeClass]
  change chosenNormalBasisLatticeSuccQuotMk K L n _ =
    sigma • chosenNormalBasisLatticeSuccQuotMk K L n y
  rw [← hxy,
    galoisGroupChosenNormalBasisLatticeSuccQuotDistribMulAction_smul_mk_mulPow]
  apply congrArg (chosenNormalBasisLatticeSuccQuotMk K L n)
  apply Subtype.ext
  have hfield := chosenNormalBasisIntegerLatticeMulPowLinearEquiv_galoisGroup_apply_coe
    K L n sigma x
  rw [hxy] at hfield
  simpa [y, galoisGroupIntegerUnitsMulDistribMulActionOfIsIntegralClosure_smul,
    map_sub, map_one] using hfield.symm

/-- The actual action on `V^n` descends to the successive quotient
`V^n / V^(n+1)`. -/
@[implicit_reducible]
def chosenNormalBasisPrincipalUnitSuccQuotMulDistribMulAction
    (n : Nat) {Vn Vsucc : Subgroup 𝒪[L]ˣ} (hV : Vsucc ≤ Vn)
    (hVn : (Vn : Set 𝒪[L]ˣ) = chosenNormalBasisPrincipalUnitSet K L n)
    (hVsucc : (Vsucc : Set 𝒪[L]ˣ) =
      chosenNormalBasisPrincipalUnitSet K L (n + 1)) :
    MulDistribMulAction (Gal(L / K))
      (chosenNormalBasisPrincipalUnitSuccQuot (L := L) hV) := by
  letI := galoisGroupIntegerUnitsMulDistribMulActionOfIsIntegralClosure K L
  letI := chosenNormalBasisPrincipalUnitSubgroupMulDistribMulAction
    K L n Vn hVn
  change MulDistribMulAction (Gal(L / K))
    (Vn ⧸ chosenNormalBasisPrincipalUnitSuccSubgroup (L := L) hV)
  exact quotientMulDistribMulActionOfSubgroupStable
    (Gal(L / K)) Vn
    (chosenNormalBasisPrincipalUnitSuccSubgroup (L := L) hV) (by
      intro sigma a ha
      apply (mem_chosenNormalBasisPrincipalUnitSuccSubgroup_iff
        (L := L) hV (sigma • a)).2
      change (sigma • (a : 𝒪[L]ˣ)) ∈ (Vsucc : Set 𝒪[L]ˣ)
      rw [hVsucc]
      apply galoisGroup_smul_mem_chosenNormalBasisPrincipalUnitSet
        (K := K) (L := L) (n + 1) sigma
      rw [← hVsucc]
      exact (mem_chosenNormalBasisPrincipalUnitSuccSubgroup_iff
        (L := L) hV a).1 ha)

/-- States the theorem `chosenNormalBasisPrincipalUnitSuccQuotMulDistribMulAction_smul_mk`. -/
@[simp]
theorem chosenNormalBasisPrincipalUnitSuccQuotMulDistribMulAction_smul_mk
    (n : Nat) {Vn Vsucc : Subgroup 𝒪[L]ˣ} (hV : Vsucc ≤ Vn)
    (hVn : (Vn : Set 𝒪[L]ˣ) = chosenNormalBasisPrincipalUnitSet K L n)
    (hVsucc : (Vsucc : Set 𝒪[L]ˣ) =
      chosenNormalBasisPrincipalUnitSet K L (n + 1))
    (sigma : Gal(L/K)) (u : Vn) :
    letI := chosenNormalBasisPrincipalUnitSubgroupMulDistribMulAction
      K L n Vn hVn
    letI := chosenNormalBasisPrincipalUnitSuccQuotMulDistribMulAction
      K L n hV hVn hVsucc
    sigma • chosenNormalBasisPrincipalUnitSuccQuotMk (L := L) hV u =
      chosenNormalBasisPrincipalUnitSuccQuotMk (L := L) hV (sigma • u) :=
  rfl

/-- Any graded-piece equivalence whose value on representatives is `u - 1`
is equivariant for the actual quotient action and the lattice action. -/
theorem chosenNormalBasisPrincipalUnitSuccQuotMulEquiv_galoisGroup
    (n : Nat) {Vn Vsucc : Subgroup 𝒪[L]ˣ} (hV : Vsucc ≤ Vn)
    (hVn : (Vn : Set 𝒪[L]ˣ) = chosenNormalBasisPrincipalUnitSet K L n)
    (hVsucc : (Vsucc : Set 𝒪[L]ˣ) =
      chosenNormalBasisPrincipalUnitSet K L (n + 1))
    (Phi : chosenNormalBasisPrincipalUnitSuccQuot (L := L) hV ≃*
      Multiplicative (chosenNormalBasisLatticeSuccQuot K L n))
    (hPhi : ∀ u : Vn,
      Phi (chosenNormalBasisPrincipalUnitSuccQuotMk (L := L) hV u) =
        Multiplicative.ofAdd
          (chosenNormalBasisPrincipalUnitLatticeClass K L n (u : 𝒪[L]ˣ)
            (by exact hVn ▸ u.2)))
    (sigma : Gal(L / K))
    (q : chosenNormalBasisPrincipalUnitSuccQuot (L := L) hV) :
    letI := chosenNormalBasisPrincipalUnitSubgroupMulDistribMulAction
      K L n Vn hVn
    letI := chosenNormalBasisPrincipalUnitSuccQuotMulDistribMulAction
      K L n hV hVn hVsucc
    letI := galoisGroupChosenNormalBasisLatticeSuccQuotDistribMulAction K L n
    letI := multiplicativeMulDistribMulActionOfDistribMulAction
      (Gal(L / K)) (chosenNormalBasisLatticeSuccQuot K L n)
    Phi (sigma • q) = sigma • Phi q := by
  let := galoisGroupIntegerUnitsMulDistribMulActionOfIsIntegralClosure K L
  let := chosenNormalBasisPrincipalUnitSubgroupMulDistribMulAction
    K L n Vn hVn
  let := chosenNormalBasisPrincipalUnitSuccQuotMulDistribMulAction
    K L n hV hVn hVsucc
  let := galoisGroupChosenNormalBasisLatticeSuccQuotDistribMulAction K L n
  let := multiplicativeMulDistribMulActionOfDistribMulAction
    (Gal(L / K)) (chosenNormalBasisLatticeSuccQuot K L n)
  refine
    chosenNormalBasisPrincipalUnitSuccQuot.inductionOn
      (L := L) hV
      (motive := fun q => Phi (sigma • q) = sigma • Phi q)
      q ?_
  intro u
  rw [chosenNormalBasisPrincipalUnitSuccQuotMulDistribMulAction_smul_mk,
    hPhi, hPhi]
  exact congrArg Multiplicative.ofAdd
    (chosenNormalBasisPrincipalUnitLatticeClass_galoisGroup
      (K := K) (L := L) n sigma (u : 𝒪[L]ˣ) (by exact hVn ▸ u.2))

/-- One-step `H⁰` lifting: sufficiently deep fixed units are
a norm from the same level times a fixed unit one level deeper. -/
theorem exists_chosenNormalBasisPrincipalUnit_h0_oneStep_lifting
    [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    [Module.Finite 𝒪[K] 𝒪[L]] :
    letI := galoisGroupIntegerUnitsMulDistribMulActionOfIsIntegralClosure K L
    ∃ c : Nat, ∀ k : Nat, c ≤ k → ∀ a : 𝒪[L]ˣ,
      a ∈ chosenNormalBasisPrincipalUnitSet K L k →
      (∀ sigma : Gal(L / K), sigma • a = a) →
      ∃ b a' : 𝒪[L]ˣ,
        b ∈ chosenNormalBasisPrincipalUnitSet K L k ∧
        a' ∈ chosenNormalBasisPrincipalUnitSet K L (k + 1) ∧
        (∀ sigma : Gal(L / K), sigma • a' = a') ∧
        a = tateNorm (Gal(L / K)) 𝒪[L]ˣ b * a' := by
  let := galoisGroupIntegerUnitsMulDistribMulActionOfIsIntegralClosure K L
  rcases exists_chosenNormalBasisPrincipalUnitSuccQuotMulEquivLatticeSuccQuot
      (K := K) (L := L) with ⟨c, hc⟩
  refine ⟨c, ?_⟩
  intro k hck a ha hfixed
  rcases hc k hck with
    ⟨Vn, Vsucc, hV, hVn, hVsucc, Phi, _hVnle, hPhi⟩
  let := chosenNormalBasisPrincipalUnitSubgroupMulDistribMulAction
    K L k Vn hVn
  let := chosenNormalBasisPrincipalUnitSuccQuotMulDistribMulAction
    K L k hV hVn hVsucc
  let := galoisGroupChosenNormalBasisLatticeSuccQuotDistribMulAction K L k
  let := multiplicativeMulDistribMulActionOfDistribMulAction
    (Gal(L / K)) (chosenNormalBasisLatticeSuccQuot K L k)
  let av : Vn := ⟨a, by
    change a ∈ (Vn : Set 𝒪[L]ˣ)
    rw [hVn]
    exact ha⟩
  let q : Multiplicative (chosenNormalBasisLatticeSuccQuot K L k) :=
    Phi (chosenNormalBasisPrincipalUnitSuccQuotMk (L := L) hV av)
  have hqfixed : ∀ sigma : Gal(L / K), sigma • q = q := by
    intro sigma
    dsimp [q]
    calc
      sigma • Phi (chosenNormalBasisPrincipalUnitSuccQuotMk (L := L) hV av) =
          Phi (sigma • chosenNormalBasisPrincipalUnitSuccQuotMk (L := L) hV av) :=
        (chosenNormalBasisPrincipalUnitSuccQuotMulEquiv_galoisGroup
          (K := K) (L := L) k hV hVn hVsucc Phi hPhi sigma _).symm
      _ = Phi (chosenNormalBasisPrincipalUnitSuccQuotMk (L := L) hV (sigma • av)) := by
        rw [chosenNormalBasisPrincipalUnitSuccQuotMulDistribMulAction_smul_mk]
      _ = Phi (chosenNormalBasisPrincipalUnitSuccQuotMk (L := L) hV av) := by
        congr 2
        apply Subtype.ext
        exact hfixed sigma
  let qfixed : fixedSubgroup (Gal(L / K))
      (Multiplicative (chosenNormalBasisLatticeSuccQuot K L k)) :=
    ⟨q, hqfixed⟩
  have hH0 := chosenNormalBasisLatticeSuccQuot_herbrandH0_subsingleton K L k
  have hqone :
      QuotientGroup.mk'
          ((tateNormSubgroup (Gal(L / K))
            (Multiplicative (chosenNormalBasisLatticeSuccQuot K L k))).subgroupOf
              (fixedSubgroup (Gal(L / K))
                (Multiplicative (chosenNormalBasisLatticeSuccQuot K L k))))
          qfixed = 1 :=
    @Subsingleton.elim _ hH0 _ _
  have hqmem : q ∈ tateNormSubgroup (Gal(L / K))
      (Multiplicative (chosenNormalBasisLatticeSuccQuot K L k)) := by
    have hm := (QuotientGroup.eq_one_iff _).1 hqone
    exact hm
  rcases hqmem with ⟨y, hy⟩
  rcases Phi.surjective y with ⟨qb, hqb⟩
  rcases chosenNormalBasisPrincipalUnitSuccQuotMk_surjective
      (L := L) hV qb with
    ⟨bv, hbvmk⟩
  change chosenNormalBasisPrincipalUnitSuccQuotMk (L := L) hV bv = qb at hbvmk
  have hPhiNorm :
      Phi (tateNorm (Gal(L / K))
        (chosenNormalBasisPrincipalUnitSuccQuot (L := L) hV)
        (chosenNormalBasisPrincipalUnitSuccQuotMk (L := L) hV bv)) = q := by
    calc
      Phi (tateNorm (Gal(L / K))
          (chosenNormalBasisPrincipalUnitSuccQuot (L := L) hV)
          (chosenNormalBasisPrincipalUnitSuccQuotMk (L := L) hV bv)) =
          tateNorm (Gal(L / K))
            (Multiplicative (chosenNormalBasisLatticeSuccQuot K L k))
            (Phi (chosenNormalBasisPrincipalUnitSuccQuotMk (L := L) hV bv)) :=
        map_tateNorm Phi.toMonoidHom
          (fun sigma z => chosenNormalBasisPrincipalUnitSuccQuotMulEquiv_galoisGroup
            (K := K) (L := L) k hV hVn hVsucc Phi hPhi sigma z) _
      _ = tateNorm (Gal(L / K))
          (Multiplicative (chosenNormalBasisLatticeSuccQuot K L k)) y := by
        rw [hbvmk, hqb]
      _ = q := hy
  have hquotNorm :
      tateNorm (Gal(L / K))
          (chosenNormalBasisPrincipalUnitSuccQuot (L := L) hV)
          (chosenNormalBasisPrincipalUnitSuccQuotMk (L := L) hV bv) =
        chosenNormalBasisPrincipalUnitSuccQuotMk (L := L) hV av := by
    apply Phi.injective
    simpa [q] using hPhiNorm
  let bn : Vn := tateNorm (Gal(L / K)) Vn bv
  have hmkbn : chosenNormalBasisPrincipalUnitSuccQuotMk (L := L) hV bn =
      chosenNormalBasisPrincipalUnitSuccQuotMk (L := L) hV av := by
    calc
      chosenNormalBasisPrincipalUnitSuccQuotMk (L := L) hV bn =
          tateNorm (Gal(L / K))
            (chosenNormalBasisPrincipalUnitSuccQuot (L := L) hV)
            (chosenNormalBasisPrincipalUnitSuccQuotMk (L := L) hV bv) := by
        exact map_tateNorm
          (chosenNormalBasisPrincipalUnitSuccQuotMk (L := L) hV)
          (fun sigma z =>
            (chosenNormalBasisPrincipalUnitSuccQuotMulDistribMulAction_smul_mk
              (K := K) (L := L) k hV hVn hVsucc sigma z).symm) bv
      _ = chosenNormalBasisPrincipalUnitSuccQuotMk (L := L) hV av := hquotNorm
  let aprimev : Vn := av / bn
  have haprimeSucc : (aprimev : 𝒪[L]ˣ) ∈ Vsucc := by
    apply (chosenNormalBasisPrincipalUnitSuccQuotMk_eq_one_iff
      (L := L) hV aprimev).1
    dsimp [aprimev]
    rw [map_div, hmkbn]
    simp
  have havfixed : ∀ sigma : Gal(L / K), sigma • av = av := by
    intro sigma
    apply Subtype.ext
    exact hfixed sigma
  have hbnfixed : ∀ sigma : Gal(L / K), sigma • bn = bn := by
    intro sigma
    exact smul_tateNorm_eq (G := Gal(L / K)) (A := Vn) sigma bv
  have haprimefixed : ∀ sigma : Gal(L / K), sigma • aprimev = aprimev := by
    intro sigma
    dsimp [aprimev]
    have ha' := havfixed sigma
    have hb' := hbnfixed sigma
    change (MulDistribMulAction.toMonoidHom Vn sigma) av = av at ha'
    change (MulDistribMulAction.toMonoidHom Vn sigma) bn = bn at hb'
    change (MulDistribMulAction.toMonoidHom Vn sigma) (av / bn) = av / bn
    rw [map_div, ha', hb']
  refine ⟨(bv : 𝒪[L]ˣ), (aprimev : 𝒪[L]ˣ), ?_, ?_, ?_, ?_⟩
  · exact hVn ▸ bv.2
  · exact hVsucc ▸ haprimeSucc
  · intro sigma
    exact congrArg (fun z : Vn => (z : 𝒪[L]ˣ)) (haprimefixed sigma)
  · have hbnval : (bn : 𝒪[L]ˣ) =
        tateNorm (Gal(L / K)) 𝒪[L]ˣ (bv : 𝒪[L]ˣ) := by
      exact map_tateNorm
        (chosenNormalBasisPrincipalUnitSubgroupInclusion (L := L) Vn)
        (fun sigma z => chosenNormalBasisPrincipalUnitSubgroupInclusion_equivariant
          (K := K) (L := L) k Vn hVn sigma z) bv
    change a = tateNorm (Gal(L / K)) 𝒪[L]ˣ (bv : 𝒪[L]ˣ) *
      (aprimev : 𝒪[L]ˣ)
    rw [← hbnval]
    dsimp [aprimev, av]
    simp

/-- One-step `H⁻¹` lifting: for a chosen generator, every
sufficiently deep norm-one unit is a coboundary from the same level times a
norm-one unit one level deeper. -/
theorem exists_chosenNormalBasisPrincipalUnit_hMinusOne_oneStep_lifting
    [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    [Module.Finite 𝒪[K] 𝒪[L]]
    (g : Gal(L / K)) (hgen : ∀ sigma : Gal(L / K),
      sigma ∈ Subgroup.zpowers g) :
    letI := galoisGroupIntegerUnitsMulDistribMulActionOfIsIntegralClosure K L
    ∃ c : Nat, ∀ k : Nat, c ≤ k → ∀ a : 𝒪[L]ˣ,
      a ∈ chosenNormalBasisPrincipalUnitSet K L k →
      tateNorm (Gal(L / K)) 𝒪[L]ˣ a = 1 →
      ∃ b a' : 𝒪[L]ˣ,
        b ∈ chosenNormalBasisPrincipalUnitSet K L k ∧
        a' ∈ chosenNormalBasisPrincipalUnitSet K L (k + 1) ∧
        tateNorm (Gal(L / K)) 𝒪[L]ˣ a' = 1 ∧
        a = sigmaMinusOne (Gal(L / K)) 𝒪[L]ˣ g b * a' := by
  let := galoisGroupIntegerUnitsMulDistribMulActionOfIsIntegralClosure K L
  rcases exists_chosenNormalBasisPrincipalUnitSuccQuotMulEquivLatticeSuccQuot
      (K := K) (L := L) with ⟨c, hc⟩
  refine ⟨c, ?_⟩
  intro k hck a ha hnorm
  rcases hc k hck with
    ⟨Vn, Vsucc, hV, hVn, hVsucc, Phi, _hVnle, hPhi⟩
  let := chosenNormalBasisPrincipalUnitSubgroupMulDistribMulAction
    K L k Vn hVn
  let := chosenNormalBasisPrincipalUnitSuccQuotMulDistribMulAction
    K L k hV hVn hVsucc
  let := galoisGroupChosenNormalBasisLatticeSuccQuotDistribMulAction K L k
  let := multiplicativeMulDistribMulActionOfDistribMulAction
    (Gal(L / K)) (chosenNormalBasisLatticeSuccQuot K L k)
  let av : Vn := ⟨a, by
    change a ∈ (Vn : Set 𝒪[L]ˣ)
    rw [hVn]
    exact ha⟩
  have hnormv : tateNorm (Gal(L / K)) Vn av = 1 := by
    apply Subtype.ext
    have hmap := map_tateNorm
      (chosenNormalBasisPrincipalUnitSubgroupInclusion (L := L) Vn)
      (fun sigma z => chosenNormalBasisPrincipalUnitSubgroupInclusion_equivariant
        (K := K) (L := L) k Vn hVn sigma z) av
    change ((chosenNormalBasisPrincipalUnitSubgroupInclusion (L := L) Vn)
      (tateNorm (Gal(L / K)) Vn av) : 𝒪[L]ˣ) =
        tateNorm (Gal(L / K)) 𝒪[L]ˣ a at hmap
    rw [hnorm] at hmap
    exact hmap
  let q : Multiplicative (chosenNormalBasisLatticeSuccQuot K L k) :=
    Phi (chosenNormalBasisPrincipalUnitSuccQuotMk (L := L) hV av)
  have hqnorm : tateNorm (Gal(L / K))
      (Multiplicative (chosenNormalBasisLatticeSuccQuot K L k)) q = 1 := by
    dsimp [q]
    calc
      tateNorm (Gal(L / K))
          (Multiplicative (chosenNormalBasisLatticeSuccQuot K L k))
          (Phi (chosenNormalBasisPrincipalUnitSuccQuotMk (L := L) hV av)) =
          Phi (tateNorm (Gal(L / K))
            (chosenNormalBasisPrincipalUnitSuccQuot (L := L) hV)
            (chosenNormalBasisPrincipalUnitSuccQuotMk (L := L) hV av)) :=
        (map_tateNorm Phi.toMonoidHom
          (fun sigma z => chosenNormalBasisPrincipalUnitSuccQuotMulEquiv_galoisGroup
            (K := K) (L := L) k hV hVn hVsucc Phi hPhi sigma z) _).symm
      _ = Phi (chosenNormalBasisPrincipalUnitSuccQuotMk (L := L) hV
          (tateNorm (Gal(L / K)) Vn av)) := by
        congr 1
        exact (map_tateNorm
          (chosenNormalBasisPrincipalUnitSuccQuotMk (L := L) hV)
          (fun sigma z =>
            (chosenNormalBasisPrincipalUnitSuccQuotMulDistribMulAction_smul_mk
              (K := K) (L := L) k hV hVn hVsucc sigma z).symm) av).symm
      _ = 1 := by rw [hnormv]; simp
  let qker : normKernelSubgroup (Gal(L / K))
      (Multiplicative (chosenNormalBasisLatticeSuccQuot K L k)) :=
    ⟨q, hqnorm⟩
  have hHm := chosenNormalBasisLatticeSuccQuot_herbrandHMinusOne_subsingleton
    K L k g hgen
  have hqone :
      QuotientGroup.mk'
          ((augmentationSubgroup (Gal(L / K))
            (Multiplicative (chosenNormalBasisLatticeSuccQuot K L k)) g).subgroupOf
              (normKernelSubgroup (Gal(L / K))
                (Multiplicative (chosenNormalBasisLatticeSuccQuot K L k))))
          qker = 1 :=
    @Subsingleton.elim _ hHm _ _
  have hqmem : q ∈ augmentationSubgroup (Gal(L / K))
      (Multiplicative (chosenNormalBasisLatticeSuccQuot K L k)) g := by
    have hm := (QuotientGroup.eq_one_iff _).1 hqone
    exact hm
  rcases hqmem with ⟨y, hy⟩
  rcases Phi.surjective y with ⟨qb, hqb⟩
  rcases chosenNormalBasisPrincipalUnitSuccQuotMk_surjective
      (L := L) hV qb with
    ⟨bv, hbvmk⟩
  change chosenNormalBasisPrincipalUnitSuccQuotMk (L := L) hV bv = qb at hbvmk
  have hPhiCoboundary :
      Phi (sigmaMinusOne (Gal(L / K))
        (chosenNormalBasisPrincipalUnitSuccQuot (L := L) hV) g
        (chosenNormalBasisPrincipalUnitSuccQuotMk (L := L) hV bv)) = q := by
    calc
      Phi (sigmaMinusOne (Gal(L / K))
          (chosenNormalBasisPrincipalUnitSuccQuot (L := L) hV) g
          (chosenNormalBasisPrincipalUnitSuccQuotMk (L := L) hV bv)) =
          sigmaMinusOne (Gal(L / K))
            (Multiplicative (chosenNormalBasisLatticeSuccQuot K L k)) g
            (Phi (chosenNormalBasisPrincipalUnitSuccQuotMk (L := L) hV bv)) :=
        map_sigmaMinusOne Phi.toMonoidHom
          (fun sigma z => chosenNormalBasisPrincipalUnitSuccQuotMulEquiv_galoisGroup
            (K := K) (L := L) k hV hVn hVsucc Phi hPhi sigma z) g _
      _ = sigmaMinusOne (Gal(L / K))
          (Multiplicative (chosenNormalBasisLatticeSuccQuot K L k)) g y := by
        rw [hbvmk, hqb]
      _ = q := hy
  have hquotCoboundary :
      sigmaMinusOne (Gal(L / K))
          (chosenNormalBasisPrincipalUnitSuccQuot (L := L) hV) g
          (chosenNormalBasisPrincipalUnitSuccQuotMk (L := L) hV bv) =
        chosenNormalBasisPrincipalUnitSuccQuotMk (L := L) hV av := by
    apply Phi.injective
    simpa [q] using hPhiCoboundary
  let cobv : Vn := sigmaMinusOne (Gal(L / K)) Vn g bv
  have hmkcob : chosenNormalBasisPrincipalUnitSuccQuotMk (L := L) hV cobv =
      chosenNormalBasisPrincipalUnitSuccQuotMk (L := L) hV av := by
    calc
      chosenNormalBasisPrincipalUnitSuccQuotMk (L := L) hV cobv =
          sigmaMinusOne (Gal(L / K))
            (chosenNormalBasisPrincipalUnitSuccQuot (L := L) hV) g
            (chosenNormalBasisPrincipalUnitSuccQuotMk (L := L) hV bv) := by
        exact map_sigmaMinusOne
          (chosenNormalBasisPrincipalUnitSuccQuotMk (L := L) hV)
          (fun sigma z =>
            (chosenNormalBasisPrincipalUnitSuccQuotMulDistribMulAction_smul_mk
              (K := K) (L := L) k hV hVn hVsucc sigma z).symm) g bv
      _ = chosenNormalBasisPrincipalUnitSuccQuotMk (L := L) hV av := hquotCoboundary
  let aprimev : Vn := av / cobv
  have haprimeSucc : (aprimev : 𝒪[L]ˣ) ∈ Vsucc := by
    apply (chosenNormalBasisPrincipalUnitSuccQuotMk_eq_one_iff
      (L := L) hV aprimev).1
    dsimp [aprimev]
    rw [map_div, hmkcob]
    simp
  have haprimeNormV : tateNorm (Gal(L / K)) Vn aprimev = 1 := by
    dsimp [aprimev, cobv]
    rw [div_eq_mul_inv, tateNorm_mul, tateNorm_inv, hnormv,
      tateNorm_sigmaMinusOne_eq_one]
    simp
  have haprimeNorm : tateNorm (Gal(L / K)) 𝒪[L]ˣ
      (aprimev : 𝒪[L]ˣ) = 1 := by
    have hmap := map_tateNorm
      (chosenNormalBasisPrincipalUnitSubgroupInclusion (L := L) Vn)
      (fun sigma z => chosenNormalBasisPrincipalUnitSubgroupInclusion_equivariant
        (K := K) (L := L) k Vn hVn sigma z) aprimev
    have hleft :
        chosenNormalBasisPrincipalUnitSubgroupInclusion (L := L) Vn
          (tateNorm (Gal(L / K)) Vn aprimev) = 1 :=
      (congrArg
        (chosenNormalBasisPrincipalUnitSubgroupInclusion (L := L) Vn)
        haprimeNormV).trans
          (chosenNormalBasisPrincipalUnitSubgroupInclusion (L := L) Vn).map_one
    exact (congrArg (tateNorm (Gal(L / K)) 𝒪[L]ˣ)
      (chosenNormalBasisPrincipalUnitSubgroupInclusion_apply
        (L := L) Vn aprimev)).symm.trans (hmap.symm.trans hleft)
  refine ⟨(bv : 𝒪[L]ˣ), (aprimev : 𝒪[L]ˣ), ?_, ?_, haprimeNorm, ?_⟩
  · exact hVn ▸ bv.2
  · exact hVsucc ▸ haprimeSucc
  · have hcobval : (cobv : 𝒪[L]ˣ) =
        sigmaMinusOne (Gal(L / K)) 𝒪[L]ˣ g (bv : 𝒪[L]ˣ) := by
      exact map_sigmaMinusOne
        (chosenNormalBasisPrincipalUnitSubgroupInclusion (L := L) Vn)
        (fun sigma z => chosenNormalBasisPrincipalUnitSubgroupInclusion_equivariant
          (K := K) (L := L) k Vn hVn sigma z) g bv
    change a = sigmaMinusOne (Gal(L / K)) 𝒪[L]ˣ g (bv : 𝒪[L]ˣ) *
      (aprimev : 𝒪[L]ˣ)
    rw [← hcobval]
    dsimp [aprimev, av]
    simp

end
end LocalClassFieldTheory
