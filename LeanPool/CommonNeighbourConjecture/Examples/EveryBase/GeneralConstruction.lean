/-
Copyright (c) 2026 Aluna Rizzoli and Adam R. Thomas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aluna Rizzoli, Adam R. Thomas
-/

import LeanPool.CommonNeighbourConjecture.Examples.EveryBase.AbstractSeed

/-!
# The abstract every-base-size construction

This module proves the base-array orbit-profile mechanism, the displayed
sumset obstruction, and the abstract exact-base-size counterexample theorem.
All seed and finite-colour hypotheses are exposed by the imported structures.
-/

namespace SaxlCounterexamples.EveryBase

open scoped Pointwise

variable {tail : Nat}

/-- The permutation-wreath group associated to a seed and colour system. -/
abbrev LinearTop (S : EveryBaseSeed) (K : BaseArrayColours S tail) :=
  Saxl.PermWreath S.H (Equiv.Perm K.C) K.C

/-- The product of seed modules indexed by tuple colours. -/
abbrev ProductModule (S : EveryBaseSeed) (K : BaseArrayColours S tail) :=
  K.C → S.V

instance (S : EveryBaseSeed) (K : BaseArrayColours S tail) :
    DistribMulAction (LinearTop S K) (ProductModule S K) where
  smul_zero g := by
    funext c
    simp [Saxl.permWreath_smul_apply]
  smul_add g x y := by
    funext c
    simp [Saxl.permWreath_smul_apply, smul_add]

/-- The generalized affine neighborhood of zero. -/
def neighbourSet (S : EveryBaseSeed) (K : BaseArrayColours S tail) :
    Set (ProductModule S K) :=
  Saxl.generalizedAffineKernelSet (LinearTop S K) (ProductModule S K) tail

/-- Read one colour-indexed column from an array of product-module rows. -/
def columnOf (rows : Fin (tail + 1) → ProductModule S K) (c : K.C) :
    Fin (tail + 1) → S.V := fun j ↦ rows j c

/-- The word of tuple colours determined by an array of rows. -/
def tupleColourWord (K : BaseArrayColours S tail)
    (rows : Fin (tail + 1) → ProductModule S K) : K.C → K.C :=
  fun c ↦ K.tupleCode.colour (columnOf rows c)

theorem neighbour_colourWord_bijective
    (S : EveryBaseSeed) (K : BaseArrayColours S tail)
    {x : ProductModule S K} (hx : x ∈ neighbourSet S K) :
    ∃ rows : Fin (tail + 1) → ProductModule S K,
      rows 0 = x ∧ Saxl.IsBaseTuple (LinearTop S K) (ProductModule S K) rows ∧
        Function.Bijective (tupleColourWord K rows) := by
  rcases hx with ⟨z, _hinj, hbase⟩
  let rows : Fin (tail + 1) → ProductModule S K := Fin.cons x z
  refine ⟨rows, by simp [rows], hbase, ?_⟩
  exact (symmetricTop_isBaseTuple_iff_bijective
    S.H S.V K.C K.tupleCode rows).1 hbase |>.2

/-- The multiset of vector-orbit colours of a product-module element. -/
def orbitProfile (K : BaseArrayColours S tail)
    (x : ProductModule S K) : Multiset K.D :=
  (Finset.univ : Finset K.C).val.map (fun c ↦ K.vectorCode.colour (x c))

/-- The reference multiset obtained from the first-colour projection. -/
def referenceProfile (K : BaseArrayColours S tail) : Multiset K.D :=
  (Finset.univ : Finset K.C).val.map K.firstColour

theorem profile_eq_reference_of_neighbour
    (S : EveryBaseSeed) (K : BaseArrayColours S tail)
    {x : ProductModule S K} (hx : x ∈ neighbourSet S K) :
    orbitProfile K x = referenceProfile K := by
  obtain ⟨rows, hrow0, hbase, hbij⟩ := neighbour_colourWord_bijective S K hx
  let e : K.C ≃ K.C := Equiv.ofBijective (tupleColourWord K rows) hbij
  have hentry : ∀ c : K.C,
      K.vectorCode.colour (x c) = K.firstColour (e c) := by
    intro c
    rw [← hrow0]
    exact K.firstColour_compat (columnOf rows c)
      ((symmetricTop_isBaseTuple_iff_bijective
        S.H S.V K.C K.tupleCode rows).1 hbase |>.1 c)
  rw [orbitProfile, referenceProfile]
  simp_rw [hentry]
  change (Finset.univ : Finset K.C).val.map (K.firstColour ∘ e) = _
  rw [← Multiset.map_map]
  have he := congrArg Finset.val (Finset.map_univ_equiv e)
  exact congrArg (Multiset.map K.firstColour) he

theorem value_eq_at_of_profile_eq_of_eq_off
    {C D : Type*} [Fintype C]
    (f g : C → D) (c0 : C)
    (hprofile : (Finset.univ : Finset C).val.map f =
      (Finset.univ : Finset C).val.map g)
    (hoff : ∀ c, c ≠ c0 → f c = g c) :
    f c0 = g c0 := by
  classical
  let s : Finset C := Finset.univ.erase c0
  have hs : s.val.map f = s.val.map g := by
    apply Multiset.map_congr rfl
    intro c hc
    apply hoff c
    intro heq
    subst c
    have hc' : c0 ∈ s := hc
    simp [s] at hc'
  have huniv : (Finset.univ : Finset C).val = c0 ::ₘ s.val := by
    have hnot : c0 ∉ s := by simp [s]
    have hcons : Finset.cons c0 s hnot = Finset.univ := by
      ext c
      simp [s]
    have hval := congrArg Finset.val hcons
    exact hval.symm
  rw [huniv, Multiset.map_cons, hs, Multiset.map_cons] at hprofile
  exact (Multiset.cons_inj_left _).mp hprofile

theorem neighbour_orbit_at_of_eq_off
    (S : EveryBaseSeed) (K : BaseArrayColours S tail)
    {x y : ProductModule S K} (hx : x ∈ neighbourSet S K)
    (hy : y ∈ neighbourSet S K) (c0 : K.C)
    (hoff : ∀ c, c ≠ c0 → x c = y c) :
    ∃ h : S.H, h • x c0 = y c0 := by
  apply (K.vectorCode.colour_eq_iff_sameOrbit (x c0) (y c0)).1
  apply value_eq_at_of_profile_eq_of_eq_off
    (fun c ↦ K.vectorCode.colour (x c))
    (fun c ↦ K.vectorCode.colour (y c)) c0
  · change orbitProfile K x = orbitProfile K y
    rw [profile_eq_reference_of_neighbour S K hx,
      profile_eq_reference_of_neighbour S K hy]
  · intro c hc
    rw [hoff c hc]

/-! ## The displayed bad vector and the abstract obstruction -/

theorem add_self_eq_zero_of_binaryModule (S : EveryBaseSeed) (v : S.V) :
    v + v = 0 := by
  rw [← two_nsmul, ← Nat.cast_smul_eq_nsmul (R := ZMod 2)]
  have hcast : ((2 : Nat) : ZMod 2) = 0 :=
    CharP.cast_eq_zero (ZMod 2) 2
  rw [hcast, zero_smul]

theorem eq_of_add_eq_zero_binaryModule (S : EveryBaseSeed)
    {x y : S.V} (h : x + y = 0) : x = y := by
  have hneg : -x = x :=
    neg_eq_of_add_eq_zero_right (add_self_eq_zero_of_binaryModule S x)
  exact ((neg_eq_of_add_eq_zero_right h).symm.trans hneg).symm

/-- The product vector supported at one colour with value `S.u`. -/
def badVector (S : EveryBaseSeed) (K : BaseArrayColours S tail)
    (c0 : K.C) : ProductModule S K :=
  Function.update (fun _ ↦ 0) c0 S.u

@[simp]
theorem badVector_at (S : EveryBaseSeed) (K : BaseArrayColours S tail)
    (c0 : K.C) : badVector S K c0 c0 = S.u := by
  simp [badVector]

theorem badVector_away (S : EveryBaseSeed) (K : BaseArrayColours S tail)
    {c c0 : K.C} (hne : c ≠ c0) : badVector S K c0 c = 0 := by
  simp [badVector, hne]

/-- Paper Lemma 6.3 at the abstract level. Its hypotheses consist only of
finite tuple-orbit codes and the explicit binary cycle obstruction stored in
`EveryBaseSeed`; neither irreducibility nor an external base-size theorem is
assumed. -/
theorem badVector_not_mem_neighbourSumset
    (S : EveryBaseSeed) (K : BaseArrayColours S tail) (c0 : K.C) :
    badVector S K c0 ∉ neighbourSet S K + neighbourSet S K := by
  intro hsumset
  obtain ⟨x, hx, y, hy, hsum⟩ := Set.mem_add.mp hsumset
  have hxy_off : ∀ c, c ≠ c0 → x c = y c := by
    intro c hc
    have hcoord := congrFun hsum c
    have hzero : x c + y c = 0 := by
      simpa [badVector_away S K hc] using hcoord
    exact eq_of_add_eq_zero_binaryModule S hzero
  obtain ⟨h, horbit⟩ := neighbour_orbit_at_of_eq_off S K hx hy c0 hxy_off
  apply u_ne_add_smul S h (x c0)
  calc
    S.u = badVector S K c0 c0 := (badVector_at S K c0).symm
    _ = x c0 + y c0 := congrFun hsum.symm c0
    _ = x c0 + h • x c0 := by rw [horbit]

/-- The abstract no-common-neighbour conclusion, obtained from the proved
generalized affine sumset criterion. -/
theorem abstractCoreObstruction
    (S : EveryBaseSeed) (K : BaseArrayColours S tail) (c0 : K.C) :
    ¬ Saxl.HasCommonNeighbour (ProductModule S K)
      (Saxl.GeneralizedAdjacent
        (Saxl.AffineGroup (LinearTop S K) (ProductModule S K))
        (ProductModule S K) tail)
      0 (badVector S K c0) := by
  rw [Saxl.generalizedAffine_hasCommonNeighbour_zero_iff_mem_add]
  exact badVector_not_mem_neighbourSumset S K c0

/-- Paper Theorem 6.4 at the abstract boundary. Exact linear tuple-base
size is an explicit hypothesis, normally discharged from a
`RegularTupleColourTower` by `linear_exactTupleBaseSize`; no literature
base-size formula is hidden here. -/
theorem abstractCoreFamily
    (S : EveryBaseSeed) (K : BaseArrayColours S tail) (c0 : K.C)
    (hlinear : ExactTupleBaseSize
      (LinearTop S K) (ProductModule S K) (tail + 1)) :
    Saxl.ExactBaseSize
        (Saxl.AffineGroup (LinearTop S K) (ProductModule S K))
        (ProductModule S K) (tail + 2) ∧
      ¬ Saxl.HasCommonNeighbour (ProductModule S K)
        (Saxl.GeneralizedAdjacent
          (Saxl.AffineGroup (LinearTop S K) (ProductModule S K))
          (ProductModule S K) tail)
        0 (badVector S K c0) := by
  constructor
  · simpa [Nat.add_assoc] using affine_exactBaseSize_succ
      (LinearTop S K) (ProductModule S K) (Nat.zero_lt_succ tail) hlinear
  · exact abstractCoreObstruction S K c0

end SaxlCounterexamples.EveryBase
