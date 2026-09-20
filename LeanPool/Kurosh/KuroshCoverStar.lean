/-
Copyright (c) 2026 Arthur Freitas Ramos et al. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/
import LeanPool.Kurosh.KuroshCover
import Mathlib.Combinatorics.Quiver.Covering

/-!
# Kurosh Cover Star

Adapted for Lean Pool from Arthur742Ramos/KuroshSubgroupTheorem,
commit `911707126c8b9bb0c764bf853008fe1053c0aad9`: imports, API compatibility,
and proof organization were revised.
-/

open Set Function
open CategoryTheory
open scoped Pointwise
noncomputable section

/-- Classical equality used locally in this part of the Kurosh construction. -/
local instance GraphCoveringTheory.Kurosh.kuroshCoverStarDecidableEq
    (α : Type*) : DecidableEq α := Classical.decEq α

universe u v w

namespace GraphCoveringTheory.Kurosh

open Monoid.CoprodI

theorem test_rawBassSerreEdgeData_action_injective {ι : Type v}
    (G : ι → Type u) [∀ i, Group (G i)] (H : Subgroup (FreeProduct G))
    {h k : H} (e : rawBassSerreEdgeData G)
    (he : h.1 • e = k.1 • e) : h = k := by
  cases e with
  | mk g i =>
      apply Subtype.ext
      change (h.1 * g, i) = (k.1 * g, i) at he
      exact mul_right_cancel (congrArg Prod.fst he)

theorem test_rawBassSerreEdgeDataOf_cast {ι : Type v}
    (G : ι → Type u) [∀ i, Group (G i)]
    {a b a' b' : RawBassSerreVertex G}
    (ha : a = a') (hb : b = b') (e : a ⟶ b) :
    rawBassSerreEdgeDataOf G (Quiver.Hom.cast ha hb e) =
      rawBassSerreEdgeDataOf G e := by
  cases ha
  cases hb
  rfl

theorem test_coverEdgeMap_data {ι : Type v}
    (G : ι → Type u) [∀ i, Group (G i)] (H : Subgroup (FreeProduct G))
    {x y : CoverVertex G H}
    (d : @Quiver.Hom (CoverVertex G H) (coverQuiver G H) x y) :
    rawBassSerreEdgeDataOf G (coverEdgeMap G H d) =
      (treeKuroshProductToH G H d.1.1 *
        quotientEdgeCoherentSourceAlign G H d.1.2.2.2).1 •
        quotientEdgeRawData G H d.1.2.2.2 := by
  dsimp [coverEdgeMap]
  rw [test_rawBassSerreEdgeDataOf_cast]
  rfl

theorem test_coverVertexMap_orbit {ι : Type v}
    (G : ι → Type u) [∀ i, Group (G i)] (H : Subgroup (FreeProduct G))
    (x : CoverVertex G H) :
    actionOrbitMk H (RawBassSerreVertex G) (coverVertexMap G H x) = x.1 := by
  cases x with
  | mk a c =>
      induction c using Quotient.inductionOn with
      | _ p =>
          let q : H := treeKuroshProductToH G H p
          change actionOrbitMk H (RawBassSerreVertex G)
              (q.1 • rawTreeRepresentative G H a) = a
          rw [← Subgroup.smul_def q,
            actionOrbitMk_smul H (RawBassSerreVertex G) q]
          exact rawTreeRepresentative_orbit G H a

/-- Choose a subgroup element translating between representatives of the same edge orbit. -/
noncomputable def rawEdgeAlign {ι : Type v}
    (G : ι → Type u) [∀ i, Group (G i)] (H : Subgroup (FreeProduct G))
    {e f : rawBassSerreEdgeData G}
    (h : actionOrbitMk H (rawBassSerreEdgeData G) e =
      actionOrbitMk H (rawBassSerreEdgeData G) f) : H :=
  Classical.choose ((actionOrbitMk_eq_iff H (rawBassSerreEdgeData G) e f).1 h)

theorem test_rawEdgeAlign_spec {ι : Type v}
    (G : ι → Type u) [∀ i, Group (G i)] (H : Subgroup (FreeProduct G))
    {e f : rawBassSerreEdgeData G}
    (h : actionOrbitMk H (rawBassSerreEdgeData G) e =
      actionOrbitMk H (rawBassSerreEdgeData G) f) :
    (rawEdgeAlign G H h).1 • e = f :=
  Classical.choose_spec ((actionOrbitMk_eq_iff H (rawBassSerreEdgeData G) e f).1 h)

theorem test_quotientEdgeRawData_cast {ι : Type v}
    (G : ι → Type u) [∀ i, Group (G i)] (H : Subgroup (FreeProduct G))
    {a b a' b' : RawBassSerreOrbitVertex G H}
    (ha : a = a') (hb : b = b')
    (e : @Quiver.Hom (RawBassSerreOrbitVertex G H)
      (rawBassSerreOrbitQuiver.inst G H) a b) :
    quotientEdgeRawData G H (Quiver.Hom.cast ha hb e) =
      quotientEdgeRawData G H e := by
  cases ha
  cases hb
  rfl

theorem test_quotientEdgeRawData_orbit_of_raw {ι : Type v}
    (G : ι → Type u) [∀ i, Group (G i)] (H : Subgroup (FreeProduct G))
    {a b : RawBassSerreVertex G} (f : a ⟶ b) :
    actionOrbitMk H (rawBassSerreEdgeData G)
        (quotientEdgeRawData G H
          (rawBassSerreOrbitEdgeMap G H f)) =
      actionOrbitMk H (rawBassSerreEdgeData G)
        (rawBassSerreEdgeDataOf G f) := by
  cases f using RawBassSerreEdge.casesOn with
  | centralFactor g i =>
      change actionOrbitMk H (rawBassSerreEdgeData G)
          (quotientEdgeRawData G H
            (rawBassSerreOrbitQuiverEdge G H (g, i))) =
        actionOrbitMk H (rawBassSerreEdgeData G) (g, i)
      rw [show rawBassSerreOrbitQuiverEdge G H (g, i) =
          rawBassSerreOrbitQuiverEdge G H (g, i) from rfl]
      unfold quotientEdgeRawData
      simp [rawBassSerreOrbitQuiverEdge, rawBassSerreOrbitEdgeMk,
        actionOrbitMk]

theorem test_rawStar_eq_of_data_eq {ι : Type v}
    (G : ι → Type u) [∀ i, Group (G i)]
    {a b c : RawBassSerreVertex G}
    (f : @Quiver.Hom (RawBassSerreVertex G) (rawBassSerreQuiver G) a b)
    (g : @Quiver.Hom (RawBassSerreVertex G) (rawBassSerreQuiver G) a c)
    (h : rawBassSerreEdgeDataOf G f = rawBassSerreEdgeDataOf G g) :
    (⟨b, f⟩ : Quiver.Star a) = ⟨c, g⟩ := by
  cases f using RawBassSerreEdge.casesOn
  cases g using RawBassSerreEdge.casesOn
  cases h
  rfl

/-- Lift an outgoing Bass-Serre edge starting at the image of a covering vertex. -/
noncomputable def coverStarInv {ι : Type v}
    (G : ι → Type u) [∀ i, Group (G i)] (H : Subgroup (FreeProduct G))
    (x : CoverVertex G H) :
    Quiver.Star (coverVertexMap G H x) → Quiver.Star x := by
  cases x with
  | mk a c =>
      intro f
      cases f with
      | mk z f =>
          let q : CoverSource G H := Quotient.out c
          have hc : c = rightCosetMk
              (MonoidHom.range (treeKuroshVertexInclusion G H a)) q :=
            (Quotient.out_eq c).symm
          let e₀ : actionOrbitMk H (RawBassSerreVertex G)
                (coverVertexMap G H ⟨a, c⟩) ⟶
              actionOrbitMk H (RawBassSerreVertex G) z :=
            rawBassSerreOrbitEdgeMap G H f
          have ha : actionOrbitMk H (RawBassSerreVertex G)
                (coverVertexMap G H ⟨a, c⟩) = a :=
            test_coverVertexMap_orbit G H ⟨a, c⟩
          let e : a ⟶ actionOrbitMk H (RawBassSerreVertex G) z :=
            Quiver.Hom.cast ha rfl e₀
          let ce : CoverEdge G H := coverBaseEdge G H e
          let r : rawBassSerreEdgeData G := quotientEdgeRawData G H ce.2.2
          let fd : rawBassSerreEdgeData G := rawBassSerreEdgeDataOf G f
          have horbit : actionOrbitMk H (rawBassSerreEdgeData G) r =
                actionOrbitMk H (rawBassSerreEdgeData G) fd := by
            change actionOrbitMk H (rawBassSerreEdgeData G)
                (quotientEdgeRawData G H e) =
              actionOrbitMk H (rawBassSerreEdgeData G) fd
            rw [test_quotientEdgeRawData_cast G H ha rfl e₀]
            exact test_quotientEdgeRawData_orbit_of_raw G H f
          let t : H := rawEdgeAlign G H horbit
          let s : H := quotientEdgeCoherentSourceAlign G H ce.2.2
          let h₀ : H := treeKuroshProductToH G H q * s
          have ht_source : t.1 • rawBassSerreEdgeDataSource G r =
                rawBassSerreEdgeDataSource G fd := by
            calc
              t.1 • rawBassSerreEdgeDataSource G r =
                  rawBassSerreEdgeDataSource G (t.1 • r) := by
                    rw [rawBassSerreEdgeData_source_action]
              _ = rawBassSerreEdgeDataSource G fd := by
                rw [test_rawEdgeAlign_spec G H horbit]
          have h0_source : h₀.1 • rawBassSerreEdgeDataSource G r =
                coverVertexMap G H ⟨a, c⟩ := by
            dsimp [h₀]
            rw [mul_smul]
            rw [quotientEdgeCoherentSourceAlign_spec G H ce.2.2]
            change (treeKuroshProductToH G H q).1 •
                rawTreeRepresentative G H a =
              coverVertexMap G H ⟨a, c⟩
            rw [hc]
            exact (coverVertexMap_mk G H a q).symm
          have hu_source :
                (h₀⁻¹ * t).1 • rawBassSerreEdgeDataSource G r =
                  rawBassSerreEdgeDataSource G r := by
            have hcoe : (h₀⁻¹ * t).1 = h₀.1⁻¹ * t.1 := rfl
            rw [hcoe, mul_smul]
            rw [ht_source, rawBassSerreEdgeDataOf_source G f]
            rw [← h0_source]
            change (h₀⁻¹).1 • (h₀.1 • rawBassSerreEdgeDataSource G r) = _
            rw [smul_smul]
            simp
          have hv :
                (s * (h₀⁻¹ * t) * s⁻¹).1 •
                    rawTreeRepresentative G H a =
                  rawTreeRepresentative G H a := by
            have hs : s.1 • rawBassSerreEdgeDataSource G r =
                  rawTreeRepresentative G H a := by
              dsimp [s, r, ce]
              exact quotientEdgeCoherentSourceAlign_spec G H _
            rw [← hs]
            have hcoe : (s * (h₀⁻¹ * t) * s⁻¹).1 =
                s.1 * (h₀⁻¹ * t).1 * (s⁻¹).1 := rfl
            rw [hcoe]
            calc
              (s.1 * (h₀⁻¹ * t).1 * (s⁻¹).1) •
                    (s.1 • rawBassSerreEdgeDataSource G r) =
                  s.1 • ((h₀⁻¹ * t).1 •
                    ((s⁻¹).1 • (s.1 • rawBassSerreEdgeDataSource G r))) := by
                      simp only [smul_smul, mul_assoc]
              _ = s.1 • ((h₀⁻¹ * t).1 •
                    rawBassSerreEdgeDataSource G r) := by
                      simp
              _ = s.1 • rawBassSerreEdgeDataSource G r := by
                      rw [hu_source]
          let k : treeVertexStabilizer G H a :=
            ⟨s * (h₀⁻¹ * t) * s⁻¹, hv⟩
          let p : CoverSource G H :=
            q * treeKuroshVertexInclusion G H a k
          have hsource : coverEdgeSource G H (p, ce) =
                (⟨a, c⟩ : CoverVertex G H) := by
            apply congrArg (Sigma.mk a)
            change rightCosetMk
              (MonoidHom.range (treeKuroshVertexInclusion G H a)) p = c
            rw [hc]
            let kk : MonoidHom.range
                (treeKuroshVertexInclusion G H a) :=
              ⟨treeKuroshVertexInclusion G H a k, ⟨k, rfl⟩⟩
            apply (rightCosetMk_eq_iff
              (MonoidHom.range (treeKuroshVertexInclusion G H a)) p q).2
            refine ⟨kk⁻¹, ?_⟩
            dsimp [p]
            calc
              q * treeKuroshVertexInclusion G H a k *
                    (↑kk : CoverSource G H)⁻¹ =
                  q * (treeKuroshVertexInclusion G H a k *
                    (↑kk : CoverSource G H)⁻¹) := by rw [mul_assoc]
              _ = q := by
                have hkk : (↑kk : CoverSource G H) =
                    treeKuroshVertexInclusion G H a k := by
                  rfl
                rw [hkk, mul_inv_cancel, mul_one]
          let y := coverEdgeTarget G H (p, ce)
          exact ⟨y, ⟨(p, ce), hsource, rfl⟩⟩

theorem test_coverPrefunctor_star_inv {ι : Type v}
    (G : ι → Type u) [∀ i, Group (G i)] (H : Subgroup (FreeProduct G))
    (x : CoverVertex G H) (f : Quiver.Star (coverVertexMap G H x)) :
    (coverPrefunctor G H).star x (coverStarInv G H x f) = f := by
  cases x with
  | mk a c =>
      cases f with
      | mk z f =>
          dsimp [coverStarInv, coverPrefunctor, Prefunctor.star]
          apply test_rawStar_eq_of_data_eq G
          rw [test_coverEdgeMap_data]
          simp only [mul_inv_rev, map_mul, treeKuroshProductToH_vertex,
            mul_assoc, mul_inv_cancel_left,
            inv_mul_cancel, mul_one]
          exact test_rawEdgeAlign_spec G H _

theorem test_coverStar_data_eq {ι : Type v}
    (G : ι → Type u) [∀ i, Group (G i)] (H : Subgroup (FreeProduct G))
    (x : CoverVertex G H)
    {y z : CoverVertex G H}
    (d : @Quiver.Hom (CoverVertex G H) (coverQuiver G H) x y)
    (e : @Quiver.Hom (CoverVertex G H) (coverQuiver G H) x z)
    (h : (coverPrefunctor G H).star x
          (⟨y, d⟩ : Quiver.Star x) =
        (coverPrefunctor G H).star x
          (⟨z, e⟩ : Quiver.Star x)) :
    rawBassSerreEdgeDataOf G (coverEdgeMap G H d) =
      rawBassSerreEdgeDataOf G (coverEdgeMap G H e) := by
  exact congrArg
    (fun F : Quiver.Star (coverVertexMap G H x) =>
      rawBassSerreEdgeDataOf G F.2) h

theorem test_coverEdge_eq_of_val_eq {ι : Type v}
    (G : ι → Type u) [∀ i, Group (G i)] (H : Subgroup (FreeProduct G))
    {a b c : RawBassSerreOrbitVertex G H}
    (e : @Quiver.Hom (RawBassSerreOrbitVertex G H)
      (rawBassSerreOrbitQuiver.inst G H) a b)
    (f : @Quiver.Hom (RawBassSerreOrbitVertex G H)
      (rawBassSerreOrbitQuiver.inst G H) a c)
    (h : e.1 = f.1) :
    (⟨a, b, e⟩ : CoverEdge G H) = ⟨a, c, f⟩ := by
  rcases e with ⟨e, he⟩
  rcases f with ⟨f, hf⟩
  dsimp at h
  cases h
  have hbc : b = c := he.2.symm.trans hf.2
  cases hbc
  rfl

theorem test_coverEdge_eq_of_base_val_eq {ι : Type v}
    (G : ι → Type u) [∀ i, Group (G i)] (H : Subgroup (FreeProduct G))
    {e f : CoverEdge G H}
    (hs : e.1 = f.1)
    (hv : e.2.2.1 = f.2.2.1) : e = f := by
  cases e with
  | mk a e =>
      cases e with
      | mk b e =>
          cases f with
          | mk c f =>
              cases f with
              | mk d f =>
                  dsimp at hs hv
                  have hbd : b = d :=
                    e.2.2.symm.trans
                      ((congrArg (rawBassSerreOrbitEdgeTarget G H) hv).trans
                        f.2.2)
                  apply Sigma.ext hs
                  cases hs
                  apply heq_of_eq
                  apply Sigma.ext hbd
                  cases hbd
                  exact heq_of_eq (Subtype.ext hv)

theorem test_coverSource_coset_eq_of_edge_eq {ι : Type v}
    (G : ι → Type u) [∀ i, Group (G i)] (H : Subgroup (FreeProduct G))
    {x : CoverVertex G H} {p q : CoverSource G H}
    {e f : CoverEdge G H}
    (hef : e = f)
    (he : coverEdgeSource G H (p, e) = x)
    (hf : coverEdgeSource G H (q, f) = x) :
    rightCosetMk (MonoidHom.range (treeKuroshVertexInclusion G H e.1)) p =
      rightCosetMk (MonoidHom.range (treeKuroshVertexInclusion G H e.1)) q := by
  cases hef
  have h := he.trans hf.symm
  change (⟨e.1, rightCosetMk
      (MonoidHom.range (treeKuroshVertexInclusion G H e.1)) p⟩ :
        CoverVertex G H) =
    ⟨e.1, rightCosetMk
      (MonoidHom.range (treeKuroshVertexInclusion G H e.1)) q⟩ at h
  exact eq_of_heq (Sigma.ext_iff.mp h).2

theorem test_coverEdge_base_eq_of_map_data_eq {ι : Type v}
    (G : ι → Type u) [∀ i, Group (G i)] (H : Subgroup (FreeProduct G))
    (x : CoverVertex G H)
    {y z : CoverVertex G H}
    (d : @Quiver.Hom (CoverVertex G H) (coverQuiver G H) x y)
    (e : @Quiver.Hom (CoverVertex G H) (coverQuiver G H) x z)
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
    rw [test_coverEdgeMap_data G H d, test_coverEdgeMap_data G H e] at h
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
      _ = rawBassSerreOrbitEdgeMk G H re := by
        exact horbit
      _ = e.1.2.2.2.1 := quotientEdgeRawData_mk G H e.1.2.2.2
  have hsource : d.1.2.1 = e.1.2.1 := by
    have hd' := congrArg Sigma.fst d.2.1
    have he' := congrArg Sigma.fst e.2.1
    exact hd'.trans he'.symm
  exact test_coverEdge_eq_of_base_val_eq G H hsource hbase

theorem test_coverEdge_pair_eq_of_map_data_eq {ι : Type v}
    (G : ι → Type u) [∀ i, Group (G i)] (H : Subgroup (FreeProduct G))
    (x : CoverVertex G H)
    {y z : CoverVertex G H}
    (d : @Quiver.Hom (CoverVertex G H) (coverQuiver G H) x y)
    (e : @Quiver.Hom (CoverVertex G H) (coverQuiver G H) x z)
    (h : rawBassSerreEdgeDataOf G (coverEdgeMap G H d) =
      rawBassSerreEdgeDataOf G (coverEdgeMap G H e)) :
    d.1 = e.1 := by
  have hce : d.1.2 = e.1.2 :=
    test_coverEdge_base_eq_of_map_data_eq G H x d e h
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
    rw [test_coverEdgeMap_data G H d, test_coverEdgeMap_data G H e] at h
    simpa [hd, he, rd, re] using h
  have hdata' : hd.1 • re = he.1 • re := by
    simpa [rd, re, hr] using hdata
  have hde : hd = he := test_rawBassSerreEdgeData_action_injective
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
  have hcoset : rightCosetMk
        (MonoidHom.range (treeKuroshVertexInclusion G H d.1.2.1)) d.1.1 =
      rightCosetMk (MonoidHom.range
        (treeKuroshVertexInclusion G H d.1.2.1)) e.1.1 := by
    exact test_coverSource_coset_eq_of_edge_eq G H hce
      (he := d.2.1) (hf := e.2.1)
  rcases (rightCosetMk_eq_iff
    (MonoidHom.range (treeKuroshVertexInclusion G H d.1.2.1)) _ _).1
      hcoset with ⟨k, hpk⟩
  rcases k.property with ⟨kk, hkk⟩
  have hprod : treeKuroshProductToH G H d.1.1 *
        treeKuroshProductToH G H (k : CoverSource G H) =
      treeKuroshProductToH G H e.1.1 := by
    simpa only [map_mul] using congrArg (treeKuroshProductToH G H) hpk
  have hkphi : treeKuroshProductToH G H (k : CoverSource G H) = 1 := by
    have hprod' : treeKuroshProductToH G H d.1.1 *
          treeKuroshProductToH G H (k : CoverSource G H) =
        treeKuroshProductToH G H d.1.1 := by
      simpa [hphi] using hprod
    exact mul_left_cancel (hprod'.trans (by simp))
  have hkk1 : kk = 1 := by
    apply Subtype.ext
    calc
      (kk : H) = treeKuroshProductToH G H
          (treeKuroshVertexInclusion G H d.1.2.1 kk) :=
        (treeKuroshProductToH_vertex G H d.1.2.1 kk).symm
      _ = treeKuroshProductToH G H (k : CoverSource G H) := by rw [hkk]
      _ = 1 := hkphi
  have hk1 : (k : CoverSource G H) = 1 := by
    calc
      (k : CoverSource G H) = treeKuroshVertexInclusion G H d.1.2.1 kk := hkk.symm
      _ = treeKuroshVertexInclusion G H d.1.2.1 1 := by rw [hkk1]
      _ = 1 := by simp
  have hp : d.1.1 = e.1.1 := by
    calc
      d.1.1 = d.1.1 * 1 := by simp
      _ = d.1.1 * (k : CoverSource G H) := by rw [hk1]
      _ = e.1.1 := hpk
  exact Prod.ext hp hce

theorem test_coverStar_eq_of_pair_eq {ι : Type v}
    (G : ι → Type u) [∀ i, Group (G i)] (H : Subgroup (FreeProduct G))
    {x y z : CoverVertex G H}
    (d : @Quiver.Hom (CoverVertex G H) (coverQuiver G H) x y)
    (e : @Quiver.Hom (CoverVertex G H) (coverQuiver G H) x z)
    (hp : d.1 = e.1) :
    (⟨y, d⟩ : Quiver.Star x) = ⟨z, e⟩ := by
  have hyz : y = z := d.2.2.symm.trans
      ((congrArg (fun pe : CoverSource G H × CoverEdge G H =>
        coverEdgeTarget G H pe) hp).trans e.2.2)
  apply Sigma.ext hyz
  cases hyz
  exact heq_of_eq (Subtype.ext hp)

theorem test_coverPrefunctor_star_injective {ι : Type v}
    (G : ι → Type u) [∀ i, Group (G i)] (H : Subgroup (FreeProduct G))
    (x : CoverVertex G H) :
    Injective ((coverPrefunctor G H).star x) := by
  intro f g h
  cases f with
  | mk y d =>
      cases g with
      | mk z e =>
          apply test_coverStar_eq_of_pair_eq G H d e
          apply test_coverEdge_pair_eq_of_map_data_eq G H x d e
          exact test_coverStar_data_eq G H x d e h

theorem test_coverPrefunctor_star_bijective {ι : Type v}
    (G : ι → Type u) [∀ i, Group (G i)] (H : Subgroup (FreeProduct G))
    (x : CoverVertex G H) :
    Bijective ((coverPrefunctor G H).star x) := by
  refine ⟨test_coverPrefunctor_star_injective G H x, ?_⟩
  intro f
  refine ⟨coverStarInv G H x f, ?_⟩
  exact test_coverPrefunctor_star_inv G H x f

end GraphCoveringTheory.Kurosh
