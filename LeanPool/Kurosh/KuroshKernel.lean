/-
Copyright (c) 2026 Arthur Freitas Ramos et al. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/
import LeanPool.Kurosh.KuroshPathEndpoint

/-!
# Kurosh Kernel

Adapted for Lean Pool from Arthur742Ramos/KuroshSubgroupTheorem,
commit `911707126c8b9bb0c764bf853008fe1053c0aad9`: imports, API compatibility,
and proof organization were revised.
-/

open Set Function
open CategoryTheory
open scoped Pointwise
noncomputable section

/-- Classical equality used locally in this part of the Kurosh construction. -/
local instance GraphCoveringTheory.Kurosh.kuroshKernelDecidableEq
    (α : Type*) : DecidableEq α := Classical.decEq α

universe u v

namespace GraphCoveringTheory.Kurosh

theorem test_treeKuroshRootStabilizer_subsingleton {ι : Type v}
    (G : ι → Type u) [∀ i, Group (G i)] (H : Subgroup (FreeProduct G)) :
    ∀ x : treeVertexStabilizer G H (rawBassSerreOrbitRoot G H), x = 1 := by
  intro x
  apply Subtype.ext
  have hx : (x.1 : FreeProduct G) • rawTreeRepresentative G H
      (rawBassSerreOrbitRoot G H) =
      rawTreeRepresentative G H (rawBassSerreOrbitRoot G H) := x.property
  rw [test_rawTreeRepresentative_root G H] at hx
  have hx' : (x.1 : FreeProduct G) = 1 :=
    (rawBassSerre_central_fixed_iff G 1 (x.1 : FreeProduct G)).mp hx
  have hxH : x.1 = (1 : H) := Subtype.ext hx'
  change x.1 = (1 : treeVertexStabilizer G H
    (rawBassSerreOrbitRoot G H)).1
  exact hxH

theorem test_treeKuroshProductToH_kernel {ι : Type v}
    (G : ι → Type u) [∀ i, Group (G i)] (H : Subgroup (FreeProduct G))
    (z : CoverSource G H)
    (hz : treeKuroshProductToH G H z = 1) : z = 1 := by
  let root := rawBassSerreOrbitRoot G H
  let K := MonoidHom.range (treeKuroshVertexInclusion G H root)
  have hv := test_coverVertexMk_eq_root_of_treeKuroshProductToH_eq_one
    G H z hz
  have hcos : rightCosetMk K z = rightCosetMk K 1 := by
    change (⟨root, rightCosetMk K z⟩ : CoverVertex G H) =
      ⟨root, rightCosetMk K 1⟩ at hv
    exact eq_of_heq (Sigma.ext_iff.mp hv).2
  rcases (rightCosetMk_eq_iff K z 1).1 hcos with ⟨k, hk⟩
  rcases k.property with ⟨x, hx⟩
  have hx1 : x = 1 := by
    exact test_treeKuroshRootStabilizer_subsingleton G H x
  have hk1val : (k : CoverSource G H) = 1 := by
    calc
      (k : CoverSource G H) = treeKuroshVertexInclusion G H root x := hx.symm
      _ = treeKuroshVertexInclusion G H root 1 := by rw [hx1]
      _ = 1 := (treeKuroshVertexInclusion G H root).map_one
  have hk1 : k = 1 := Subtype.ext hk1val
  simpa [hk1] using hk

theorem test_treeDataGenerated_eq_top_for_kernel {ι : Type v}
    (G : ι → Type u) [∀ i, Group (G i)] (H : Subgroup (FreeProduct G)) :
    testTreeDataGenerated G H = ⊤ := by
  apply le_antisymm le_top
  intro h _
  let p := testRawTreePath G
    (h.1 • RawBassSerreVertex.central (G := G) 1)
  let a := testRawPathAlignmentGenerated G H p
  have horbit :
      actionOrbitMk H (RawBassSerreVertex G)
          (h.1 • RawBassSerreVertex.central (G := G) 1) =
        rawBassSerreOrbitRoot G H := by
    change actionOrbitMk H (RawBassSerreVertex G)
        (h.1 • RawBassSerreVertex.central (G := G) 1) =
      actionOrbitMk H (RawBassSerreVertex G)
        (RawBassSerreVertex.central (G := G) 1)
    exact actionOrbitMk_smul H (RawBassSerreVertex G) h
      (RawBassSerreVertex.central (G := G) 1)
  have hrep : rawTreeRepresentative G H
      (actionOrbitMk H (RawBassSerreVertex G)
        (h.1 • RawBassSerreVertex.central (G := G) 1)) =
      RawBassSerreVertex.central (G := G) 1 := by
    rw [horbit]
    exact test_rawTreeRepresentative_root G H
  have hpath : h.1 • RawBassSerreVertex.central (G := G) 1 =
      a.1 • RawBassSerreVertex.central (G := G) 1 := by
    calc
      h.1 • RawBassSerreVertex.central (G := G) 1 = a.1 •
          rawTreeRepresentative G H
            (actionOrbitMk H (RawBassSerreVertex G)
              (h.1 • RawBassSerreVertex.central (G := G) 1)) := a.2.1
      _ = a.1 • RawBassSerreVertex.central (G := G) 1 :=
        congrArg (fun z => (a.1 : FreeProduct G) • z) hrep
  have hval : h.1 = a.1 := by
    change RawBassSerreVertex.central (G := G) ((h.1 : FreeProduct G) * 1) =
      RawBassSerreVertex.central (G := G) ((a.1 : FreeProduct G) * 1) at hpath
    injection hpath with hmul
    simpa only [mul_one] using hmul
  have heq : h = a.1 := Subtype.ext hval
  exact heq ▸ a.2.2

theorem test_treeKuroshProductToH_surjective_for_kernel {ι : Type v}
    (G : ι → Type u) [∀ i, Group (G i)] (H : Subgroup (FreeProduct G)) :
    Function.Surjective (@treeKuroshProductToH.{u, v, 0} ι G _ H) := by
  have hgen : testTreeDataGenerated G H ≤
      MonoidHom.range (@treeKuroshProductToH.{u, v, 0} ι G _ H) := by
    change Subgroup.closure (testTreeDataGeneratorSet G H) ≤
      MonoidHom.range (@treeKuroshProductToH.{u, v, 0} ι G _ H)
    rw [Subgroup.closure_le]
    intro h hh
    rcases hh with ⟨a, ha⟩ | ⟨e, he⟩
    · refine ⟨treeKuroshVertexInclusion G H a ⟨h, ha⟩, ?_⟩
      exact treeKuroshProductToH_vertex G H a ⟨h, ha⟩
    · have hlabel : quotientEdgeLabel G H e.2.2 ∈
          MonoidHom.range (@treeKuroshProductToH.{u, v, 0} ι G _ H) := by
        refine ⟨treeKuroshFreeInclusion G H
          (quotientEdgeLoop G H e.2.2), ?_⟩
        rw [treeKuroshProductToH_free,
          kuroshFreePartHom_quotientEdgeLoop]
      exact he ▸ hlabel
  have hrange_top : MonoidHom.range
      (@treeKuroshProductToH.{u, v, 0} ι G _ H) = ⊤ := by
    apply le_antisymm le_top
    intro h _
    apply hgen
    rw [test_treeDataGenerated_eq_top_for_kernel G H]
    trivial
  intro h
  have hrange : h ∈ MonoidHom.range
      (@treeKuroshProductToH.{u, v, 0} ι G _ H) := by
    rw [hrange_top]
    trivial
  exact hrange

theorem test_treeKuroshProductToH_injective {ι : Type v}
    (G : ι → Type u) [∀ i, Group (G i)] (H : Subgroup (FreeProduct G)) :
    Function.Injective (@treeKuroshProductToH.{u, v, 0} ι G _ H) := by
  intro p q hpq
  have hker : @treeKuroshProductToH.{u, v, 0} ι G _ H
      (p * q⁻¹) = 1 := by
    rw [map_mul, map_inv, hpq]
    simp
  have hker' := test_treeKuroshProductToH_kernel G H (p * q⁻¹) hker
  calc
    p = (p * q⁻¹) * q := by simp [mul_assoc]
    _ = 1 * q := by rw [hker']
    _ = q := by simp

/-- The tree Kurosh decomposition, induced by the actual stabilizer inclusions. -/
noncomputable def treeKuroshProductMulEquivH {ι : Type v}
    (G : ι → Type u) [∀ i, Group (G i)] (H : Subgroup (FreeProduct G)) :
    @TreeKuroshProduct.{u, v, 0} ι G _ H ≃* H :=
  MulEquiv.ofBijective (@treeKuroshProductToH.{u, v, 0} ι G _ H)
    ⟨test_treeKuroshProductToH_injective G H,
      test_treeKuroshProductToH_surjective_for_kernel G H⟩

theorem test_treeVertexStabilizer_central_or_factor {ι : Type v}
    (G : ι → Type u) [∀ i, Group (G i)] (H : Subgroup (FreeProduct G))
    (a : RawBassSerreOrbitVertex G H) :
    (∃ g : FreeProduct G,
      rawTreeRepresentative G H a = RawBassSerreVertex.central g ∧
      treeVertexStabilizer G H a = ⊥) ∨
    (∃ (i : ι) (g : FreeProduct G),
      rawTreeRepresentative G H a =
        RawBassSerreVertex.factor i (factorCosetMk G i g) ∧
      treeVertexStabilizer G H a = intersectionFactorInH H i g) := by
  let r := rawTreeRepresentative G H a
  cases hr : r with
  | central g =>
      left
      refine ⟨g, hr, ?_⟩
      apply (Subgroup.eq_bot_iff_forall _).2
      intro x hx
      have hfix : (x.1 : FreeProduct G) • RawBassSerreVertex.central g =
          RawBassSerreVertex.central g := by
        change (x.1 : FreeProduct G) • r = r at hx
        rw [hr] at hx
        exact hx
      have hx' : (x.1 : FreeProduct G) = 1 :=
        (rawBassSerre_central_fixed_iff G g (x.1 : FreeProduct G)).mp hfix
      exact Subtype.ext hx'
  | factor i c =>
      right
      have hc : factorCosetMk G i (Quotient.out c) = c := by
        simp [factorCosetMk, rightCosetMk]
      have hrep : rawTreeRepresentative G H a =
          RawBassSerreVertex.factor i
            (factorCosetMk G i (Quotient.out c)) :=
        hr.trans (congrArg (RawBassSerreVertex.factor i) hc.symm)
      refine ⟨i, Quotient.out c, hrep, ?_⟩
      apply Subgroup.ext
      intro x
      constructor
      · intro hx
        change (x.1 : FreeProduct G) ∈ intersectionFactor H i
            (Quotient.out c)
        apply (rawBassSerre_factor_fixed_iff G H i (Quotient.out c) x).1
        change (x.1 : FreeProduct G) •
            rawTreeRepresentative G H a = rawTreeRepresentative G H a at hx
        simpa [hrep] using hx
      · intro hx
        change (x.1 : FreeProduct G) •
            rawTreeRepresentative G H a = rawTreeRepresentative G H a
        rw [hrep]
        apply (rawBassSerre_factor_fixed_iff G H i (Quotient.out c) x).2
        exact hx

end GraphCoveringTheory.Kurosh
