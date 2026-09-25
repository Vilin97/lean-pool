/-
Copyright (c) 2026 Arthur Freitas Ramos et al. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/
module

public import LeanPool.Kurosh.KuroshCoverConnected

/-!
# Kurosh Cover Lift

Adapted for Lean Pool from Arthur742Ramos/KuroshSubgroupTheorem,
commit `911707126c8b9bb0c764bf853008fe1053c0aad9`: imports, API compatibility,
and proof organization were revised.
-/

@[expose] public section

open Set Function
open CategoryTheory
open scoped Pointwise
noncomputable section

/-- Classical equality used locally in this part of the Kurosh construction. -/
local instance GraphCoveringTheory.Kurosh.kuroshCoverLiftDecidableEq
    (α : Type*) : DecidableEq α := Classical.decEq α

universe u v

namespace GraphCoveringTheory.Kurosh

theorem Internal.coverSymmCovering {ι : Type v}
    (G : ι → Type u) [∀ i, Group (G i)] (H : Subgroup (FreeProduct G)) :
    (coverPrefunctor G H).symmetrify.IsCovering :=
  (Internal.coverPrefunctor_isCovering G H).symmetrify

/-- The covering projection induces an equivalence on symmetrified outgoing edges. -/
noncomputable def coverStarEquiv {ι : Type v}
    (G : ι → Type u) [∀ i, Group (G i)] (H : Subgroup (FreeProduct G))
    (u : CoverVertex G H) :
    @Quiver.Star (Quiver.Symmetrify (CoverVertex G H))
      (@Quiver.symmetrifyQuiver (CoverVertex G H) (coverQuiver G H)) u ≃
      @Quiver.Star (Quiver.Symmetrify (RawBassSerreVertex G))
        (@Quiver.symmetrifyQuiver (RawBassSerreVertex G)
          (rawBassSerreQuiver G))
        ((coverPrefunctor G H).symmetrify.obj u) :=
  Equiv.ofBijective ((coverPrefunctor G H).symmetrify.star u)
    ((Internal.coverSymmCovering G H).star_bijective u)

/-- Lift a symmetrified outgoing edge using the star equivalence. -/
noncomputable def coverStarLift {ι : Type v}
    (G : ι → Type u) [∀ i, Group (G i)] (H : Subgroup (FreeProduct G))
    (u : CoverVertex G H) {v : Quiver.Symmetrify (RawBassSerreVertex G)}
    (e : (coverPrefunctor G H).symmetrify.obj u ⟶ v) :
    @Quiver.Star (Quiver.Symmetrify (CoverVertex G H))
      (@Quiver.symmetrifyQuiver (CoverVertex G H) (coverQuiver G H)) u :=
  (coverStarEquiv G H u).symm ⟨v, e⟩

theorem Internal.coverStarLift_map {ι : Type v}
    (G : ι → Type u) [∀ i, Group (G i)] (H : Subgroup (FreeProduct G))
    (u : CoverVertex G H) {v : Quiver.Symmetrify (RawBassSerreVertex G)}
    (e : (coverPrefunctor G H).symmetrify.obj u ⟶ v) :
    ∃ h : (coverPrefunctor G H).symmetrify.obj
        (coverStarLift G H u e).1 = v,
      Quiver.Hom.cast rfl h
        ((coverPrefunctor G H).symmetrify.map
          (coverStarLift G H u e).2) = e := by
  have h := (coverStarEquiv G H u).apply_symm_apply
    (⟨v, e⟩ : Quiver.Star
      ((coverPrefunctor G H).symmetrify.obj u))
  refine ⟨congrArg Sigma.fst h, ?_⟩
  erw [Quiver.Hom.cast_eq_iff_heq]
  exact (Sigma.ext_iff.mp h).2

theorem Internal.coverStar_eq_mk_of_map_cast {ι : Type v}
    (G : ι → Type u) [∀ i, Group (G i)] (H : Subgroup (FreeProduct G))
    (u : CoverVertex G H)
    (s : @Quiver.Star (Quiver.Symmetrify (CoverVertex G H))
      (@Quiver.symmetrifyQuiver (CoverVertex G H) (coverQuiver G H)) u)
    {v : Quiver.Symmetrify (RawBassSerreVertex G)}
    (e : (coverPrefunctor G H).symmetrify.obj u ⟶ v)
    (hobj : (coverPrefunctor G H).symmetrify.obj s.1 = v)
    (hmap : Quiver.Hom.cast rfl hobj
      ((coverPrefunctor G H).symmetrify.map s.2) = e) :
    (coverPrefunctor G H).symmetrify.star u s = ⟨v, e⟩ := by
  apply Sigma.ext_iff.mpr
  refine ⟨hobj, ?_⟩
  erw [Quiver.Hom.cast_eq_iff_heq] at hmap
  exact hmap

theorem Internal.hom_reverse_cast {U : Type u} [q : Quiver.{v} U]
    [Quiver.HasReverse U] {a b a' b' : U}
    (e : a ⟶ b) (ha : a = a') (hb : b = b') :
    Quiver.reverse (e.cast ha hb) = (Quiver.reverse e).cast hb ha := by
  cases ha
  cases hb
  rfl

theorem Internal.coverReverseStar_map {ι : Type v}
    (G : ι → Type u) [∀ i, Group (G i)] (H : Subgroup (FreeProduct G))
    (u : CoverVertex G H)
    (d : @Quiver.Star (Quiver.Symmetrify (CoverVertex G H))
      (@Quiver.symmetrifyQuiver (CoverVertex G H) (coverQuiver G H)) u)
    {v : Quiver.Symmetrify (RawBassSerreVertex G)}
    (e : (coverPrefunctor G H).symmetrify.obj u ⟶ v)
    (hobj : (coverPrefunctor G H).symmetrify.obj d.1 = v)
    (hmap : Quiver.Hom.cast rfl hobj
      ((coverPrefunctor G H).symmetrify.map d.2) = e) :
    (coverPrefunctor G H).symmetrify.map (Quiver.reverse d.2) =
      (Quiver.reverse e).cast hobj.symm rfl := by
  cases hobj
  rw [← hmap]
  simp only [Quiver.Hom.cast_rfl_rfl]
  exact Prefunctor.map_reverse _ _

theorem Internal.coverReverseStar_map_transport {ι : Type v}
    (G : ι → Type u) [∀ i, Group (G i)] (H : Subgroup (FreeProduct G))
    (u : CoverVertex G H)
    (d : @Quiver.Star (Quiver.Symmetrify (CoverVertex G H))
      (@Quiver.symmetrifyQuiver (CoverVertex G H) (coverQuiver G H)) u)
    {v w : Quiver.Symmetrify (RawBassSerreVertex G)}
    (e : v ⟶ w)
    (hobj : (coverPrefunctor G H).symmetrify.obj u = v)
    (htarget : (coverPrefunctor G H).symmetrify.obj d.1 = w)
    (hmap : Quiver.Hom.cast rfl htarget
      ((coverPrefunctor G H).symmetrify.map d.2) =
      e.cast hobj.symm rfl) :
    Quiver.Hom.cast rfl hobj
        ((coverPrefunctor G H).symmetrify.map (Quiver.reverse d.2)) =
      (Quiver.reverse e).cast htarget.symm rfl := by
  cases hobj
  cases htarget
  have hmap' :
      (coverPrefunctor G H).symmetrify.map d.2 = e := by
    simpa using hmap
  have hreverse := congrArg Quiver.reverse hmap'
  rw [Quiver.Hom.cast_rfl_rfl, Quiver.Hom.cast_rfl_rfl]
  erw [Prefunctor.map_reverse]
  exact hreverse

/-- A lifted path from the auxiliary root together with its endpoint identification. -/
structure CoverPathLiftData {ι : Type v}
    (G : ι → Type u) [∀ i, Group (G i)] (H : Subgroup (FreeProduct G))
    {v : Quiver.Symmetrify (RawBassSerreVertex G)} where
  /-- The endpoint of the lifted path in the auxiliary covering graph. -/
  x : CoverVertex G H
  /-- The lifted path from the auxiliary covering root to `x`. -/
  path : @Quiver.Path (Quiver.Symmetrify (CoverVertex G H))
    (@Quiver.symmetrifyQuiver (CoverVertex G H) (coverQuiver G H))
    (coverVertexMk G H (rawBassSerreOrbitRoot G H) 1) x
  endpoint : (coverPrefunctor G H).symmetrify.obj x = v

/-- Lift a Bass-Serre path starting at the identity vertex to a path starting at the
auxiliary covering root. -/
noncomputable def coverPathLiftData {ι : Type v}
    (G : ι → Type u) [∀ i, Group (G i)] (H : Subgroup (FreeProduct G)) :
    ∀ {v : Quiver.Symmetrify (RawBassSerreVertex G)},
      @Quiver.Path (Quiver.Symmetrify (RawBassSerreVertex G))
        (@Quiver.symmetrifyQuiver (RawBassSerreVertex G)
          (rawBassSerreQuiver G))
        ((coverPrefunctor G H).symmetrify.obj
          (coverVertexMk G H (rawBassSerreOrbitRoot G H) 1)) v →
      CoverPathLiftData G H (v := v)
  | _, Quiver.Path.nil =>
      ⟨coverVertexMk G H (rawBassSerreOrbitRoot G H) 1,
        Quiver.Path.nil, rfl⟩
  | _, @Quiver.Path.cons _ _ _ b c p e => by
      let ih := coverPathLiftData G H p
      let e' := Quiver.Hom.cast ih.endpoint.symm rfl e
      let d := coverStarLift G H ih.x e'
      let hd := Internal.coverStarLift_map G H ih.x e'
      exact ⟨d.1, ih.path.cons d.2, hd.1⟩

theorem Internal.path_cast_cons_mid {U : Type u} [q : Quiver.{v} U]
    {a b c b' c' : U} (p : Quiver.Path a b) (e : b ⟶ c)
    (hb : b = b') (hc : c = c') :
    (p.cons e).cast rfl hc =
      (p.cast rfl hb).cons (e.cast hb hc) := by
  cases hb
  exact Quiver.Path.cast_cons p e rfl hc

theorem Internal.coverPathLiftData_map {ι : Type v}
    (G : ι → Type u) [∀ i, Group (G i)] (H : Subgroup (FreeProduct G))
    {v : Quiver.Symmetrify (RawBassSerreVertex G)}
    (p : @Quiver.Path (Quiver.Symmetrify (RawBassSerreVertex G))
      (@Quiver.symmetrifyQuiver (RawBassSerreVertex G)
        (rawBassSerreQuiver G))
      ((coverPrefunctor G H).symmetrify.obj
        (coverVertexMk G H (rawBassSerreOrbitRoot G H) 1)) v) :
    ((coverPrefunctor G H).symmetrify.mapPath
        (coverPathLiftData G H p).path).cast rfl
        (coverPathLiftData G H p).endpoint = p := by
  induction p with
  | nil => rfl
  | @cons b c p e ih =>
      let ihd := coverPathLiftData G H p
      let e' := Quiver.Hom.cast ihd.endpoint.symm rfl e
      let d := coverStarLift G H ihd.x e'
      let hd := Internal.coverStarLift_map G H ihd.x e'
      rcases hd with ⟨hdobj, hdmap⟩
      dsimp [coverPathLiftData]
      erw [Internal.path_cast_cons_mid
        (p := (coverPrefunctor G H).symmetrify.mapPath ihd.path)
        (e := (coverPrefunctor G H).symmetrify.map d.2)
        (hb := ihd.endpoint) (hc := hdobj)]
      rw [ih]
      have hedge :
          Quiver.Hom.cast ihd.endpoint hdobj
              ((coverPrefunctor G H).symmetrify.map d.2) = e := by
        calc
          Quiver.Hom.cast ihd.endpoint hdobj
                ((coverPrefunctor G H).symmetrify.map d.2) =
              (Quiver.Hom.cast rfl hdobj
                ((coverPrefunctor G H).symmetrify.map d.2)).cast
                ihd.endpoint rfl := by
              rw [Quiver.Hom.cast_cast]
          _ = e'.cast ihd.endpoint rfl := by rw [hdmap]
          _ = e := by
              dsimp [e']
              rw [Quiver.Hom.cast_cast]
              simp
      rw [hedge]

theorem Internal.coverPathLiftData_backtrack_endpoint {ι : Type v}
    (G : ι → Type u) [∀ i, Group (G i)] (H : Subgroup (FreeProduct G))
    {v w : Quiver.Symmetrify (RawBassSerreVertex G)}
    (p : @Quiver.Path (Quiver.Symmetrify (RawBassSerreVertex G))
      (@Quiver.symmetrifyQuiver (RawBassSerreVertex G)
        (rawBassSerreQuiver G))
      ((coverPrefunctor G H).symmetrify.obj
        (coverVertexMk G H (rawBassSerreOrbitRoot G H) 1)) v)
    (e : @Quiver.Hom (Quiver.Symmetrify (RawBassSerreVertex G))
      (@Quiver.symmetrifyQuiver (RawBassSerreVertex G)
        (rawBassSerreQuiver G)) v w) :
    (coverPathLiftData G H
      ((p.cons e).cons (Quiver.reverse e))).x =
      (coverPathLiftData G H p).x := by
  let ihd := coverPathLiftData G H p
  let e' := Quiver.Hom.cast ihd.endpoint.symm rfl e
  let d := coverStarLift G H ihd.x e'
  let hd := Internal.coverStarLift_map G H ihd.x e'
  rcases hd with ⟨hdobj, hdmap⟩
  dsimp [coverPathLiftData]
  let e2 := (Quiver.reverse e).cast hdobj.symm rfl
  have hrevmap :
      Quiver.Hom.cast rfl ihd.endpoint
          ((coverPrefunctor G H).symmetrify.map (Quiver.reverse d.2)) = e2 := by
    have h := Internal.coverReverseStar_map_transport (G := G) (H := H)
      (u := ihd.x) (d := d) (e := e) ihd.endpoint hdobj (by
        simpa [d, e'] using hdmap)
    simpa [e2] using h
  have hstar :
      (coverPrefunctor G H).symmetrify.star d.1
          (⟨ihd.x, Quiver.reverse d.2⟩ : Quiver.Star d.1) =
        ⟨v, e2⟩ := by
    apply Internal.coverStar_eq_mk_of_map_cast (G := G) (H := H)
      (u := d.1) (s := ⟨ihd.x, Quiver.reverse d.2⟩) (e := e2)
      ihd.endpoint
    exact hrevmap
  have hlift :
      coverStarLift G H d.1 e2 =
        (⟨ihd.x, Quiver.reverse d.2⟩ : Quiver.Star d.1) := by
    apply (coverStarEquiv G H d.1).injective
    calc
      coverStarEquiv G H d.1 (coverStarLift G H d.1 e2) =
          ⟨v, e2⟩ := (coverStarEquiv G H d.1).apply_symm_apply _
      _ = coverStarEquiv G H d.1
          (⟨ihd.x, Quiver.reverse d.2⟩ : Quiver.Star d.1) := hstar.symm
  change
      (coverStarLift G H d.1 e2).1 =
        (ihd.x : Quiver.Symmetrify (CoverVertex G H))
  exact congrArg Sigma.fst hlift

theorem Internal.coverStarLift_fst_eq_of_heq {ι : Type v}
    (G : ι → Type u) [∀ i, Group (G i)] (H : Subgroup (FreeProduct G))
    (u u' : CoverVertex G H)
    {v : Quiver.Symmetrify (RawBassSerreVertex G)}
    (e : (coverPrefunctor G H).symmetrify.obj u ⟶ v)
    (e' : (coverPrefunctor G H).symmetrify.obj u' ⟶ v)
    (hu : HEq u u') (he : HEq e e') :
    (coverStarLift G H u e).1 =
      (coverStarLift G H u' e').1 := by
  cases hu
  cases he
  rfl

theorem Internal.coverPathLiftData_append_edge_endpoint {ι : Type v}
    (G : ι → Type u) [∀ i, Group (G i)] (H : Subgroup (FreeProduct G))
    {v w : Quiver.Symmetrify (RawBassSerreVertex G)}
    (p q : @Quiver.Path (Quiver.Symmetrify (RawBassSerreVertex G))
      (@Quiver.symmetrifyQuiver (RawBassSerreVertex G)
        (rawBassSerreQuiver G))
      ((coverPrefunctor G H).symmetrify.obj
        (coverVertexMk G H (rawBassSerreOrbitRoot G H) 1)) v)
    (h : (coverPathLiftData G H p).x =
      (coverPathLiftData G H q).x)
    (e : @Quiver.Hom (Quiver.Symmetrify (RawBassSerreVertex G))
      (@Quiver.symmetrifyQuiver (RawBassSerreVertex G)
        (rawBassSerreQuiver G)) v w) :
    (coverPathLiftData G H (p.cons e)).x =
      (coverPathLiftData G H (q.cons e)).x := by
  let dp := coverPathLiftData G H p
  let dq := coverPathLiftData G H q
  let ep := Quiver.Hom.cast dp.endpoint.symm rfl e
  let eq := Quiver.Hom.cast dq.endpoint.symm rfl e
  have he_cast :
      Quiver.Hom.cast
          (congrArg (fun z : CoverVertex G H =>
            (coverPrefunctor G H).symmetrify.obj z) h) rfl ep = eq := by
    dsimp [ep, eq]
    rw [Quiver.Hom.cast_cast]
  have he : HEq ep eq :=
    (Quiver.Hom.cast_eq_iff_heq
      (congrArg (fun z : CoverVertex G H =>
        (coverPrefunctor G H).symmetrify.obj z) h) rfl ep eq).mp he_cast
  have hout := Internal.coverStarLift_fst_eq_of_heq G H dp.x dq.x ep eq
    (heq_of_eq h) he
  change
      (coverStarLift G H dp.x ep).1 =
        (coverStarLift G H dq.x eq).1
  exact hout

theorem Internal.coverPathLiftData_append_endpoint {ι : Type v}
    (G : ι → Type u) [∀ i, Group (G i)] (H : Subgroup (FreeProduct G))
    {v w : Quiver.Symmetrify (RawBassSerreVertex G)}
    (p q : @Quiver.Path (Quiver.Symmetrify (RawBassSerreVertex G))
      (@Quiver.symmetrifyQuiver (RawBassSerreVertex G)
        (rawBassSerreQuiver G))
      ((coverPrefunctor G H).symmetrify.obj
        (coverVertexMk G H (rawBassSerreOrbitRoot G H) 1)) v)
    (h : (coverPathLiftData G H p).x =
      (coverPathLiftData G H q).x)
    (r : @Quiver.Path (Quiver.Symmetrify (RawBassSerreVertex G))
      (@Quiver.symmetrifyQuiver (RawBassSerreVertex G)
        (rawBassSerreQuiver G)) v w) :
    (coverPathLiftData G H (p.comp r)).x =
      (coverPathLiftData G H (q.comp r)).x := by
  induction r with
  | nil => simpa using h
  | @cons b c r e ih =>
      rw [Quiver.Path.comp_cons, Quiver.Path.comp_cons]
      exact Internal.coverPathLiftData_append_edge_endpoint G H
        (p.comp r) (q.comp r) ih e

end GraphCoveringTheory.Kurosh
