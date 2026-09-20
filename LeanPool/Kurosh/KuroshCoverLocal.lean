/-
Copyright (c) 2026 Arthur Freitas Ramos et al. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/
import LeanPool.Kurosh.KuroshCoverStar
import Mathlib.Combinatorics.Quiver.Covering

/-!
# Kurosh Cover Local

Adapted for Lean Pool from Arthur742Ramos/KuroshSubgroupTheorem,
commit `911707126c8b9bb0c764bf853008fe1053c0aad9`: imports, API compatibility,
and proof organization were revised.
-/

open Set Function
open CategoryTheory
open scoped Pointwise
noncomputable section

/-- Classical equality used locally in this part of the Kurosh construction. -/
local instance GraphCoveringTheory.Kurosh.kuroshCoverLocalDecidableEq
    (α : Type*) : DecidableEq α := Classical.decEq α

universe u v w

namespace GraphCoveringTheory.Kurosh

open Monoid.CoprodI

theorem Internal.rawCostar_eq_of_data_eq {ι : Type v}
    (G : ι → Type u) [∀ i, Group (G i)]
    {a b c : RawBassSerreVertex G}
    (f : @Quiver.Hom (RawBassSerreVertex G) (rawBassSerreQuiver G) b a)
    (g : @Quiver.Hom (RawBassSerreVertex G) (rawBassSerreQuiver G) c a)
    (hdata : rawBassSerreEdgeDataOf G f = rawBassSerreEdgeDataOf G g) :
    (⟨b, f⟩ : Quiver.Costar a) = ⟨c, g⟩ := by
  have hsrc : b = c := by
    calc
      b = rawBassSerreEdgeDataSource G (rawBassSerreEdgeDataOf G f) :=
        (rawBassSerreEdgeDataOf_source G f).symm
      _ = rawBassSerreEdgeDataSource G (rawBassSerreEdgeDataOf G g) :=
        congrArg (rawBassSerreEdgeDataSource G) hdata
      _ = c := rawBassSerreEdgeDataOf_source G g
  cases hsrc
  have hstar : (⟨a, f⟩ : Quiver.Star b) = ⟨a, g⟩ :=
    Internal.rawStar_eq_of_data_eq G f g hdata
  exact Sigma.ext rfl (Sigma.ext_iff.mp hstar).2

/-- Lift an incoming Bass-Serre edge ending at the image of a covering vertex. -/
noncomputable def coverCostarInv {ι : Type v}
    (G : ι → Type u) [∀ i, Group (G i)] (H : Subgroup (FreeProduct G))
    (x : CoverVertex G H) :
    Quiver.Costar (coverVertexMap G H x) → Quiver.Costar x := by
  cases x with
  | mk a c =>
      intro f
      cases f with
      | mk z f =>
          let q : CoverSource G H := Quotient.out c
          have hc : c = rightCosetMk
              (MonoidHom.range (treeKuroshVertexInclusion G H a)) q :=
            (Quotient.out_eq c).symm
          let e₀ : actionOrbitMk H (RawBassSerreVertex G) z ⟶
              actionOrbitMk H (RawBassSerreVertex G)
                (coverVertexMap G H ⟨a, c⟩) :=
            rawBassSerreOrbitEdgeMap G H f
          have ha : actionOrbitMk H (RawBassSerreVertex G)
                (coverVertexMap G H ⟨a, c⟩) = a :=
            Internal.coverVertexMap_orbit G H ⟨a, c⟩
          let e : actionOrbitMk H (RawBassSerreVertex G) z ⟶ a :=
            Quiver.Hom.cast rfl ha e₀
          let ce : CoverEdge G H := coverBaseEdge G H e
          let r : rawBassSerreEdgeData G := quotientEdgeRawData G H ce.2.2
          let fd : rawBassSerreEdgeData G := rawBassSerreEdgeDataOf G f
          have horbit : actionOrbitMk H (rawBassSerreEdgeData G) r =
                actionOrbitMk H (rawBassSerreEdgeData G) fd := by
            dsimp [r, ce]
            change actionOrbitMk H (rawBassSerreEdgeData G)
                (quotientEdgeRawData G H e) =
              actionOrbitMk H (rawBassSerreEdgeData G) fd
            rw [Internal.quotientEdgeRawData_cast G H rfl ha e₀]
            exact Internal.quotientEdgeRawData_orbit_of_raw G H f
          let t : H := rawEdgeAlign G H horbit
          let s : H := quotientEdgeCoherentSourceAlign G H ce.2.2
          let l : H := quotientEdgeLabel G H ce.2.2
          let m : H := l * s
          let h₀ : H := treeKuroshProductToH G H q * m
          have ht_target : t.1 • rawBassSerreEdgeDataTarget G r =
                rawBassSerreEdgeDataTarget G fd := by
            calc
              t.1 • rawBassSerreEdgeDataTarget G r =
                  rawBassSerreEdgeDataTarget G (t.1 • r) := by
                    rw [rawBassSerreEdgeData_target_action]
              _ = rawBassSerreEdgeDataTarget G fd := by
                rw [Internal.rawEdgeAlign_spec G H horbit]
          have hm_target : m.1 • rawBassSerreEdgeDataTarget G r =
                rawTreeRepresentative G H a := by
            dsimp [m]
            rw [mul_smul]
            exact quotientEdgeLabel_transport_coherent G H ce.2.2
          have h0_target : h₀.1 • rawBassSerreEdgeDataTarget G r =
                coverVertexMap G H ⟨a, c⟩ := by
            dsimp [h₀]
            rw [mul_smul, hm_target]
            rw [hc]
            exact (coverVertexMap_mk G H a q).symm
          have hu_target :
                (h₀⁻¹ * t).1 • rawBassSerreEdgeDataTarget G r =
                  rawBassSerreEdgeDataTarget G r := by
            have hcoe : (h₀⁻¹ * t).1 = h₀.1⁻¹ * t.1 := rfl
            rw [hcoe, mul_smul]
            rw [ht_target, rawBassSerreEdgeDataOf_target G f]
            rw [← h0_target]
            change (h₀⁻¹).1 • (h₀.1 • rawBassSerreEdgeDataTarget G r) = _
            rw [smul_smul]
            simp
          have hv :
                (m * (h₀⁻¹ * t) * m⁻¹).1 •
                    rawTreeRepresentative G H a =
                  rawTreeRepresentative G H a := by
            rw [← hm_target]
            have hcoe : (m * (h₀⁻¹ * t) * m⁻¹).1 =
                m.1 * (h₀⁻¹ * t).1 * (m⁻¹).1 := rfl
            rw [hcoe]
            calc
              (m.1 * (h₀⁻¹ * t).1 * (m⁻¹).1) •
                    (m.1 • rawBassSerreEdgeDataTarget G r) =
                  m.1 • ((h₀⁻¹ * t).1 •
                    ((m⁻¹).1 • (m.1 • rawBassSerreEdgeDataTarget G r))) := by
                      simp only [smul_smul, mul_assoc]
              _ = m.1 • ((h₀⁻¹ * t).1 •
                    rawBassSerreEdgeDataTarget G r) := by
                      simp
              _ = m.1 • rawBassSerreEdgeDataTarget G r := by
                      rw [hu_target]
          let k : treeVertexStabilizer G H a :=
            ⟨m * (h₀⁻¹ * t) * m⁻¹, hv⟩
          let L : CoverSource G H := coverEdgeLetter G H ce
          have hletter : treeKuroshProductToH G H L = l := by
            change treeKuroshProductToH G H
                (treeKuroshFreeInclusion G H (quotientEdgeLoop G H ce.2.2)) = l
            rw [treeKuroshProductToH_free]
            exact kuroshFreePartHom_quotientEdgeLoop G H ce.2.2
          let p : CoverSource G H :=
            q * treeKuroshVertexInclusion G H a k * L
          have htarget : coverEdgeTarget G H (p, ce) =
                (⟨a, c⟩ : CoverVertex G H) := by
            apply congrArg (Sigma.mk a)
            change rightCosetMk
                (MonoidHom.range (treeKuroshVertexInclusion G H a))
                (p * L⁻¹) = c
            rw [hc]
            let kk : MonoidHom.range
                (treeKuroshVertexInclusion G H a) :=
              ⟨treeKuroshVertexInclusion G H a k, ⟨k, rfl⟩⟩
            apply (rightCosetMk_eq_iff
              (MonoidHom.range (treeKuroshVertexInclusion G H a))
              (p * L⁻¹) q).2
            refine ⟨kk⁻¹, ?_⟩
            dsimp [p]
            calc
              (q * treeKuroshVertexInclusion G H a k * L) * L⁻¹ *
                    (↑kk : CoverSource G H)⁻¹ =
                  q * treeKuroshVertexInclusion G H a k *
                    (↑kk : CoverSource G H)⁻¹ := by
                      simp [mul_assoc]
              _ = q := by
                have hkk : (↑kk : CoverSource G H) =
                    treeKuroshVertexInclusion G H a k := by rfl
                rw [hkk]
                calc
                  q * treeKuroshVertexInclusion G H a k *
                        (treeKuroshVertexInclusion G H a k)⁻¹ =
                      q * (treeKuroshVertexInclusion G H a k *
                        (treeKuroshVertexInclusion G H a k)⁻¹) := by
                          rw [mul_assoc]
                  _ = q := by simp
          let y := coverEdgeSource G H (p, ce)
          exact ⟨y, ⟨(p, ce), rfl, htarget⟩⟩

theorem Internal.coverPrefunctor_costar_inv {ι : Type v}
    (G : ι → Type u) [∀ i, Group (G i)] (H : Subgroup (FreeProduct G))
    (x : CoverVertex G H) (f : Quiver.Costar (coverVertexMap G H x)) :
    (coverPrefunctor G H).costar x (coverCostarInv G H x f) = f := by
  cases x with
  | mk a c =>
      cases f with
      | mk z f =>
          dsimp [coverCostarInv, coverPrefunctor, Prefunctor.costar]
          apply Internal.rawCostar_eq_of_data_eq G
          rw [Internal.coverEdgeMap_data]
          simp only [mul_inv_rev, map_mul, treeKuroshProductToH_vertex,
            coverEdgeLetter, treeKuroshProductToH_free, kuroshFreePartHom_quotientEdgeLoop,
            mul_assoc, mul_inv_cancel_left, inv_mul_cancel, mul_one]
          exact Internal.rawEdgeAlign_spec G H _

theorem Internal.coverCostar_data_eq {ι : Type v}
    (G : ι → Type u) [∀ i, Group (G i)] (H : Subgroup (FreeProduct G))
    (x : CoverVertex G H)
    {y z : CoverVertex G H}
    (d : @Quiver.Hom (CoverVertex G H) (coverQuiver G H) y x)
    (e : @Quiver.Hom (CoverVertex G H) (coverQuiver G H) z x)
    (h : (coverPrefunctor G H).costar x
          (⟨y, d⟩ : Quiver.Costar x) =
        (coverPrefunctor G H).costar x
          (⟨z, e⟩ : Quiver.Costar x)) :
    rawBassSerreEdgeDataOf G (coverEdgeMap G H d) =
      rawBassSerreEdgeDataOf G (coverEdgeMap G H e) := by
  exact congrArg
    (fun F : Quiver.Costar (coverVertexMap G H x) =>
      rawBassSerreEdgeDataOf G F.2) h

theorem Internal.coverEdge_eq_of_target_val_eq {ι : Type v}
    (G : ι → Type u) [∀ i, Group (G i)] (H : Subgroup (FreeProduct G))
    {a b c d : RawBassSerreOrbitVertex G H}
    {e : @Quiver.Hom (RawBassSerreOrbitVertex G H)
      (rawBassSerreOrbitQuiver.inst G H) a b}
    {f : @Quiver.Hom (RawBassSerreOrbitVertex G H)
      (rawBassSerreOrbitQuiver.inst G H) c d}
    (h : b = d) (hv : e.1 = f.1) :
    (⟨a, b, e⟩ : CoverEdge G H) = ⟨c, d, f⟩ := by
  rcases e with ⟨e, he⟩
  rcases f with ⟨f, hf⟩
  dsimp at h hv
  have hac : a = c := he.1.symm.trans
    ((congrArg (rawBassSerreOrbitEdgeSource G H) hv).trans hf.1)
  apply Sigma.ext hac
  cases hac
  apply heq_of_eq
  apply Sigma.ext h
  cases h
  exact heq_of_eq (Subtype.ext hv)

theorem Internal.coverEdge_base_eq_of_map_data_eq_costar {ι : Type v}
    (G : ι → Type u) [∀ i, Group (G i)] (H : Subgroup (FreeProduct G))
    (x : CoverVertex G H)
    {y z : CoverVertex G H}
    (d : @Quiver.Hom (CoverVertex G H) (coverQuiver G H) y x)
    (e : @Quiver.Hom (CoverVertex G H) (coverQuiver G H) z x)
    (h : rawBassSerreEdgeDataOf G (coverEdgeMap G H d) =
      rawBassSerreEdgeDataOf G (coverEdgeMap G H e)) :
    d.1.2 = e.1.2 := by
  let rd : rawBassSerreEdgeData G :=
    quotientEdgeRawData G H d.1.2.2.2
  let re : rawBassSerreEdgeData G :=
    quotientEdgeRawData G H e.1.2.2.2
  let hd : H := treeKuroshProductToH G H d.1.1 *
    quotientEdgeCoherentSourceAlign G H d.1.2.2.2
  let he : H := treeKuroshProductToH G H e.1.1 *
    quotientEdgeCoherentSourceAlign G H e.1.2.2.2
  have hdata : hd.1 • rd = he.1 • re := by
    rw [Internal.coverEdgeMap_data G H d, Internal.coverEdgeMap_data G H e] at h
    simpa [hd, he, rd, re] using h
  have horbit : actionOrbitMk H (rawBassSerreEdgeData G) rd =
        actionOrbitMk H (rawBassSerreEdgeData G) re := by
    have hdo : actionOrbitMk H (rawBassSerreEdgeData G) (hd.1 • rd) =
          actionOrbitMk H (rawBassSerreEdgeData G) rd := by
      rw [← Subgroup.smul_def hd, actionOrbitMk_smul]
    have heo : actionOrbitMk H (rawBassSerreEdgeData G) (he.1 • re) =
          actionOrbitMk H (rawBassSerreEdgeData G) re := by
      rw [← Subgroup.smul_def he, actionOrbitMk_smul]
    calc
      actionOrbitMk H (rawBassSerreEdgeData G) rd =
          actionOrbitMk H (rawBassSerreEdgeData G) (hd.1 • rd) := hdo.symm
      _ = actionOrbitMk H (rawBassSerreEdgeData G) (he.1 • re) :=
        congrArg (actionOrbitMk H (rawBassSerreEdgeData G)) hdata
      _ = actionOrbitMk H (rawBassSerreEdgeData G) re := heo
  have hbase : d.1.2.2.2.1 = e.1.2.2.2.1 := by
    calc
      d.1.2.2.2.1 = rawBassSerreOrbitEdgeMk G H rd := by
        symm
        exact quotientEdgeRawData_mk G H d.1.2.2.2
      _ = rawBassSerreOrbitEdgeMk G H re := horbit
      _ = e.1.2.2.2.1 := quotientEdgeRawData_mk G H e.1.2.2.2
  have htarget : d.1.2.2.1 = e.1.2.2.1 := by
    have hd' := congrArg Sigma.fst d.2.2
    have he' := congrArg Sigma.fst e.2.2
    exact hd'.trans he'.symm
  exact Internal.coverEdge_eq_of_target_val_eq G H htarget hbase

theorem Internal.coverTarget_coset_eq_of_edge_eq {ι : Type v}
    (G : ι → Type u) [∀ i, Group (G i)] (H : Subgroup (FreeProduct G))
    {x : CoverVertex G H} {p q : CoverSource G H}
    {e f : CoverEdge G H}
    (hef : e = f)
    (he : coverEdgeTarget G H (p, e) = x)
    (hf : coverEdgeTarget G H (q, f) = x) :
    rightCosetMk (MonoidHom.range
      (treeKuroshVertexInclusion G H e.2.1))
      (p * (coverEdgeLetter G H e)⁻¹) =
    rightCosetMk (MonoidHom.range
      (treeKuroshVertexInclusion G H e.2.1))
      (q * (coverEdgeLetter G H e)⁻¹) := by
  cases hef
  have h := he.trans hf.symm
  change (⟨e.2.1, rightCosetMk (MonoidHom.range
      (treeKuroshVertexInclusion G H e.2.1))
      (p * (coverEdgeLetter G H e)⁻¹)⟩ : CoverVertex G H) =
    ⟨e.2.1, rightCosetMk (MonoidHom.range
      (treeKuroshVertexInclusion G H e.2.1))
      (q * (coverEdgeLetter G H e)⁻¹)⟩ at h
  exact eq_of_heq (Sigma.ext_iff.mp h).2

theorem Internal.coverEdge_pair_eq_of_map_data_eq_costar {ι : Type v}
    (G : ι → Type u) [∀ i, Group (G i)] (H : Subgroup (FreeProduct G))
    (x : CoverVertex G H)
    {y z : CoverVertex G H}
    (d : @Quiver.Hom (CoverVertex G H) (coverQuiver G H) y x)
    (e : @Quiver.Hom (CoverVertex G H) (coverQuiver G H) z x)
    (h : rawBassSerreEdgeDataOf G (coverEdgeMap G H d) =
      rawBassSerreEdgeDataOf G (coverEdgeMap G H e)) :
    d.1 = e.1 := by
  have hce : d.1.2 = e.1.2 :=
    Internal.coverEdge_base_eq_of_map_data_eq_costar G H x d e h
  have hr : quotientEdgeRawData G H d.1.2.2.2 =
        quotientEdgeRawData G H e.1.2.2.2 := by
    exact congrArg (fun ce : CoverEdge G H =>
      quotientEdgeRawData G H ce.2.2) hce
  have hsa : quotientEdgeCoherentSourceAlign G H d.1.2.2.2 =
        quotientEdgeCoherentSourceAlign G H e.1.2.2.2 := by
    exact congrArg (fun ce : CoverEdge G H =>
      quotientEdgeCoherentSourceAlign G H ce.2.2) hce
  let rd : rawBassSerreEdgeData G :=
    quotientEdgeRawData G H d.1.2.2.2
  let re : rawBassSerreEdgeData G :=
    quotientEdgeRawData G H e.1.2.2.2
  let hd : H := treeKuroshProductToH G H d.1.1 *
    quotientEdgeCoherentSourceAlign G H d.1.2.2.2
  let he : H := treeKuroshProductToH G H e.1.1 *
    quotientEdgeCoherentSourceAlign G H e.1.2.2.2
  have hdata : hd.1 • rd = he.1 • re := by
    rw [Internal.coverEdgeMap_data G H d, Internal.coverEdgeMap_data G H e] at h
    simpa [hd, he, rd, re] using h
  have hdata' : hd.1 • re = he.1 • re := by
    simpa [rd, re, hr] using hdata
  have hde : hd = he := Internal.rawBassSerreEdgeData_action_injective
    G H re hdata'
  have hphi : treeKuroshProductToH G H d.1.1 =
        treeKuroshProductToH G H e.1.1 := by
    have hcoe := congrArg Subtype.val hde
    change (treeKuroshProductToH G H d.1.1).1 *
          (quotientEdgeCoherentSourceAlign G H d.1.2.2.2).1 =
          (treeKuroshProductToH G H e.1.1).1 *
          (quotientEdgeCoherentSourceAlign G H e.1.2.2.2).1 at hcoe
    rw [hsa] at hcoe
    exact Subtype.ext (mul_right_cancel hcoe)
  have hcoset := Internal.coverTarget_coset_eq_of_edge_eq G H hce
    (he := d.2.2) (hf := e.2.2)
  rcases (rightCosetMk_eq_iff
    (MonoidHom.range (treeKuroshVertexInclusion G H d.1.2.2.1)) _ _).1
      hcoset with ⟨k, hpk⟩
  rcases k.property with ⟨kk, hkk⟩
  have hpk' : d.1.1 * (coverEdgeLetter G H d.1.2)⁻¹ *
        (k : CoverSource G H) = e.1.1 *
        (coverEdgeLetter G H d.1.2)⁻¹ := by
    simpa [hce] using hpk
  let L : CoverSource G H := coverEdgeLetter G H d.1.2
  have hprod : treeKuroshProductToH G H d.1.1 *
        (treeKuroshProductToH G H L)⁻¹ *
        treeKuroshProductToH G H (k : CoverSource G H) =
      treeKuroshProductToH G H e.1.1 *
        (treeKuroshProductToH G H L)⁻¹ := by
    simpa only [L, map_mul, map_inv] using congrArg
      (treeKuroshProductToH G H) hpk'
  have hkl : (treeKuroshProductToH G H L)⁻¹ *
        treeKuroshProductToH G H (k : CoverSource G H) =
      (treeKuroshProductToH G H L)⁻¹ := by
    have hprod' : treeKuroshProductToH G H d.1.1 *
          ((treeKuroshProductToH G H L)⁻¹ *
            treeKuroshProductToH G H (k : CoverSource G H)) =
        treeKuroshProductToH G H d.1.1 *
          (treeKuroshProductToH G H L)⁻¹ := by
      simpa [hphi, mul_assoc] using hprod
    exact mul_left_cancel hprod'
  have hkphi : treeKuroshProductToH G H (k : CoverSource G H) = 1 := by
    have h := congrArg (fun z =>
      treeKuroshProductToH G H L * z) hkl
    simpa [mul_assoc] using h
  have hkk1 : kk = 1 := by
    apply Subtype.ext
    calc
      (kk : H) = treeKuroshProductToH G H
          (treeKuroshVertexInclusion G H d.1.2.2.1 kk) :=
        (treeKuroshProductToH_vertex G H d.1.2.2.1 kk).symm
      _ = treeKuroshProductToH G H (k : CoverSource G H) := by rw [hkk]
      _ = 1 := hkphi
  have hk1 : (k : CoverSource G H) = 1 := by
    calc
      (k : CoverSource G H) = treeKuroshVertexInclusion G H d.1.2.2.1 kk := hkk.symm
      _ = treeKuroshVertexInclusion G H d.1.2.2.1 1 := by rw [hkk1]
      _ = 1 := by simp
  have hp : d.1.1 = e.1.1 := by
    have hpeq : d.1.1 * L⁻¹ = e.1.1 * L⁻¹ := by
      simpa [L, hk1] using hpk'
    exact mul_right_cancel hpeq
  exact Prod.ext hp hce

theorem Internal.coverCostar_eq_of_pair_eq {ι : Type v}
    (G : ι → Type u) [∀ i, Group (G i)] (H : Subgroup (FreeProduct G))
    {x y z : CoverVertex G H}
    (d : @Quiver.Hom (CoverVertex G H) (coverQuiver G H) y x)
    (e : @Quiver.Hom (CoverVertex G H) (coverQuiver G H) z x)
    (hp : d.1 = e.1) :
    (⟨y, d⟩ : Quiver.Costar x) = ⟨z, e⟩ := by
  have hyz : y = z := d.2.1.symm.trans
      ((congrArg (fun pe : CoverSource G H × CoverEdge G H =>
        coverEdgeSource G H pe) hp).trans e.2.1)
  apply Sigma.ext hyz
  cases hyz
  exact heq_of_eq (Subtype.ext hp)

theorem Internal.coverPrefunctor_costar_injective {ι : Type v}
    (G : ι → Type u) [∀ i, Group (G i)] (H : Subgroup (FreeProduct G))
    (x : CoverVertex G H) :
    Injective ((coverPrefunctor G H).costar x) := by
  intro f g h
  cases f with
  | mk y d =>
      cases g with
      | mk z e =>
          apply Internal.coverCostar_eq_of_pair_eq G H d e
          apply Internal.coverEdge_pair_eq_of_map_data_eq_costar G H x d e
          exact Internal.coverCostar_data_eq G H x d e h

theorem Internal.coverPrefunctor_costar_bijective {ι : Type v}
    (G : ι → Type u) [∀ i, Group (G i)] (H : Subgroup (FreeProduct G))
    (x : CoverVertex G H) :
    Bijective ((coverPrefunctor G H).costar x) := by
  refine ⟨Internal.coverPrefunctor_costar_injective G H x, ?_⟩
  intro f
  refine ⟨coverCostarInv G H x f, ?_⟩
  exact Internal.coverPrefunctor_costar_inv G H x f

theorem Internal.coverPrefunctor_isCovering {ι : Type v}
    (G : ι → Type u) [∀ i, Group (G i)] (H : Subgroup (FreeProduct G)) :
    (coverPrefunctor G H).IsCovering := by
  exact ⟨Internal.coverPrefunctor_star_bijective G H,
    Internal.coverPrefunctor_costar_bijective G H⟩

end GraphCoveringTheory.Kurosh
