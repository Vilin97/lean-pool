/-
Copyright (c) 2026 Arseniy Akopyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arseniy Akopyan
-/

import LeanPool.NandakumarRamanaRao.NRR.PrimePolyhedron.FoxNeuwirth.EndpointStackAffinePullbackDescent
import LeanPool.NandakumarRamanaRao.NRR.PrimePolyhedron.FoxNeuwirth.StablePatchedHomotopyBoundary

/-!
# Compatible refined-chart maps and PL-ended homotopies

A regular endpoint approximation supplies a zero-free affine interpolation on every refined top
simplex.  The carrier theorem proves that these local formulas agree on shared faces, including
prime-translated chart occurrences.  This module packages those formulas as compatible chart maps
and constructs a chartwise zero-free homotopy

`PL(A₀) -> F₀ -> H -> F₁ -> PL(A₁)`.

The package is deliberately chart-local: Step 4 only samples finitely many affine collar vertices,
so no global quotient-map construction is required.  Decorated compatibility is exactly the
condition needed for those samples to descend to global collar vertices.
-/

namespace NRR
namespace FoxNeuwirthOrderComplex
namespace EquivariantPrismStableRelativeBoundary
namespace CompatibleRefinedChartHomotopy

open scoped BigOperators
open SphereOddDegree
open SphereOddDegree.AffineBarycentricSubdivision
open RefinedAffineMap
open EquivariantCoordinateHomotopy
open EndpointFaceRefinement

variable {p : Nat}

/-- The project simplex presentation maps continuously to the topological simplex. -/
theorem continuous_toDelta {d : Nat} :
    Continuous (StandardSimplex.toDelta (d := d)) :=
  Continuous.subtype_mk continuous_subtype_val _

/-- The topological simplex maps continuously to the project simplex presentation. -/
theorem continuous_ofDelta {d : Nat} :
    Continuous (StandardSimplex.ofDelta (d := d)) :=
  Continuous.subtype_mk continuous_subtype_val _

/-- A prime-compatible zero-free map written in every refined top-simplex chart. -/
structure ChartMap (hp : Nat.Prime p) (N : Nat) where
  /-- Coordinate values in each refined top-simplex chart. -/
  value : TopCell hp N -> StandardSimplex (p - 1) -> Fin p -> Real
  continuous_value : forall q, Continuous (value q)
  decorated_compatible : forall
      (g h : PrimeSymmetry p) (q r : TopCell hp N)
      (w v : StandardSimplex (p - 1)),
    g • chart hp N q (StandardSimplex.toDelta w) =
        h • chart hp N r (StandardSimplex.toDelta v) ->
      g • value q w = h • value r v
  zeroFree : forall q w, value q w ≠ 0

/-- A compatible chart homotopy between two compatible chart maps. -/
structure ChartHomotopy
    (hp : Nat.Prime p) (N : Nat) (K0 K1 : ChartMap hp N) where
  /-- The time-dependent coordinate values in each refined chart. -/
  value : TopCell hp N -> StandardSimplex (p - 1) -> Set.Icc (0 : Real) 1 ->
    Fin p -> Real
  continuous_value : forall q, Continuous (fun z :
    StandardSimplex (p - 1) × Set.Icc (0 : Real) 1 => value q z.1 z.2)
  value_zero : forall q w, value q w ⟨0, by simp⟩ = K0.value q w
  value_one : forall q w, value q w ⟨1, by simp⟩ = K1.value q w
  decorated_compatible : forall
      (g h : PrimeSymmetry p) (q r : TopCell hp N)
      (w v : StandardSimplex (p - 1)) (t : Set.Icc (0 : Real) 1),
    g • chart hp N q (StandardSimplex.toDelta w) =
        h • chart hp N r (StandardSimplex.toDelta v) ->
      g • value q w t = h • value r v t
  zeroFree : forall q w t, value q w t ≠ 0

/-- Prefix top cell of a chart after `k` additional subdivision stages. -/
noncomputable def ancestorTopCell
    (hp : Nat.Prime p) (N k : Nat) (q : TopCell hp (N + k)) : TopCell hp N :=
  (q.1, (splitRefinementWord N k q.2).1)

/-- Tail subdivision word of a chart after splitting off its first `N` stages. -/
noncomputable def ancestorTail
    {hp : Nat.Prime p} (N k : Nat) (q : TopCell hp (N + k)) : RefinementWord p k :=
  (splitRefinementWord N k q.2).2

/-- Pull a standard-simplex coordinate back to the ancestor chart. -/
noncomputable def ancestorWeight
    {hp : Nat.Prime p} (N k : Nat) (q : TopCell hp (N + k))
    (w : StandardSimplex (p - 1)) : StandardSimplex (p - 1) :=
  StandardSimplex.ofDelta
    (affineCompMap (p - 1) k
      (fun j => Simplex.refinementIndexPerm (ancestorTail N k q j))
      (StandardSimplex.toDelta w))

/-- A refined chart factors through its ancestor chart. -/
theorem chart_eq_ancestor
    (hp : Nat.Prime p) (N k : Nat) (q : TopCell hp (N + k))
    (w : StandardSimplex (p - 1)) :
    chart hp (N + k) q (StandardSimplex.toDelta w) =
      chart hp N (ancestorTopCell hp N k q)
        (StandardSimplex.toDelta (ancestorWeight N k q w)) := by
  have hsplit :
      (fun j => Simplex.refinementIndexPerm (q.2 j)) =
        appendRefinementWord N k
          (fun j => Simplex.refinementIndexPerm ((ancestorTopCell hp N k q).2 j))
          (fun j => Simplex.refinementIndexPerm (ancestorTail N k q j)) := by
    funext j
    refine Fin.addCases ?_ ?_ j
    · intro i
      simp [appendRefinementWord, ancestorTopCell, splitRefinementWord]
    · intro i
      simp [appendRefinementWord, ancestorTail, splitRefinementWord]
  simp only [chart, Simplex.refinedContinuousMap, ContinuousMap.comp_apply,
    ancestorWeight, StandardSimplex.toDelta_ofDelta]
  rw [hsplit, affineCompMap_append]
  rfl

/-- Pullback of standard-simplex coordinates to an ancestor chart is continuous. -/
theorem continuous_ancestorWeight
    {hp : Nat.Prime p} (N k : Nat) (q : TopCell hp (N + k)) :
    Continuous (fun w : StandardSimplex (p - 1) => ancestorWeight N k q w) := by
  unfold ancestorWeight
  exact continuous_ofDelta.comp
    (((affineCompMap (p - 1) k
      (fun j => Simplex.refinementIndexPerm (ancestorTail N k q j))).continuous).comp
      continuous_toDelta)

/-- Further spatial refinement of a compatible chart map. -/
noncomputable def ChartMap.refine
    {hp : Nat.Prime p} {N : Nat} (K : ChartMap hp N) (k : Nat) :
    ChartMap hp (N + k) where
  value q w := K.value (ancestorTopCell hp N k q) (ancestorWeight N k q w)
  continuous_value := by
    intro q
    exact (K.continuous_value _).comp (continuous_ancestorWeight N k q)
  decorated_compatible := by
    intro g h q r w v hchart
    apply K.decorated_compatible g h
    simpa [chart_eq_ancestor] using hchart
  zeroFree := by
    intro q w
    exact K.zeroFree _ _

/-- Further spatial refinement of a compatible chart homotopy. -/
noncomputable def ChartHomotopy.refine
    {hp : Nat.Prime p} {N : Nat} {K0 K1 : ChartMap hp N}
    (J : ChartHomotopy hp N K0 K1) (k : Nat) :
    ChartHomotopy hp (N + k) (K0.refine k) (K1.refine k) where
  value q w t := J.value (ancestorTopCell hp N k q) (ancestorWeight N k q w) t
  continuous_value := by
    intro q
    exact (J.continuous_value _).comp
      (((continuous_ancestorWeight N k q).comp continuous_fst).prodMk continuous_snd)
  value_zero := by intro q w; exact J.value_zero _ _
  value_one := by intro q w; exact J.value_one _ _
  decorated_compatible := by
    intro g h q r w v t hchart
    apply J.decorated_compatible g h
    simpa [chart_eq_ancestor] using hchart
  zeroFree := by intro q w t; exact J.zeroFree _ _ _

/-- The affine interpolation stored by one regular approximation, as a compatible chart map. -/
noncomputable def baseOriginalPLMap
    (hp : Nat.Prime p)
    {F : ContinuousCoordinateMap p}
    (A : RegularApproximation hp F) : ChartMap hp A.level where
  value q w := RefinedAffineMap.value hp A.level A.map q w
  continuous_value := by
    intro q
    apply continuous_pi
    intro c
    exact continuous_finsetSum _ (fun i _ =>
      ((continuous_apply i).comp continuous_subtype_val).mul continuous_const)
  decorated_compatible := by
    intro g h q r w v hchart
    exact RefinedChartCarrierEquivariant.decorated_value_eq_of_decorated_chart_eq
      hp A.level A.map A.equivariant q r g h w v hchart
  zeroFree := by
    intro q w
    have h := A.zeroFreeStraightLine q w
      (⟨1, by constructor <;> norm_num⟩ : Set.Icc (0 : Real) 1)
    simpa using h

/-- The same original PL interpolation represented on a further subdivision. -/
noncomputable def originalPLMap
    (hp : Nat.Prime p)
    {F : ContinuousCoordinateMap p}
    (A : RegularApproximation hp F) (k : Nat) : ChartMap hp (A.level + k) :=
  (baseOriginalPLMap hp A).refine k

/-- A compatible chart map induced by one global zero-free equivariant map. -/
noncomputable def ofGlobalMap
    (hp : Nat.Prime p) (N : Nat) (F : ZeroFreeMap hp) : ChartMap hp N where
  value q w := F.map (chart hp N q (StandardSimplex.toDelta w))
  continuous_value := by
    intro q
    exact F.map.continuous.comp ((chart hp N q).continuous.comp continuous_toDelta)
  decorated_compatible := by
    intro g h q r w v hchart
    have hg := F.equivariant g (chart hp N q (StandardSimplex.toDelta w))
    have hh := F.equivariant h (chart hp N r (StandardSimplex.toDelta v))
    rw [← hg, ← hh]
    exact congrArg F.map hchart
  zeroFree := by intro q w; exact F.zeroFree _

/-- Clamp a real number into the unit interval. -/
noncomputable def clampUnit (x : Real) : Set.Icc (0 : Real) 1 :=
  ⟨min 1 (max 0 x), by
    constructor
    · exact le_min zero_le_one (le_max_left _ _)
    · exact min_le_left _ _⟩

theorem continuous_clampUnit : Continuous clampUnit :=
  Continuous.subtype_mk (continuous_const.min (continuous_const.max continuous_id)) _

namespace ChartHomotopy

/-- Constant compatible chart homotopy. -/
noncomputable def refl
    (hp : Nat.Prime p) (N : Nat) (K : ChartMap hp N) :
    ChartHomotopy hp N K K where
  value q w _ := K.value q w
  continuous_value := by
    intro q
    exact (K.continuous_value q).comp continuous_fst
  value_zero := by simp
  value_one := by simp
  decorated_compatible := by
    intro g h q r w v t hchart
    exact K.decorated_compatible g h q r w v hchart
  zeroFree := by intro q w t; exact K.zeroFree q w

/-- Reverse a compatible chart homotopy. -/
noncomputable def symm
    {hp : Nat.Prime p} {N : Nat} {K0 K1 : ChartMap hp N}
    (J : ChartHomotopy hp N K0 K1) : ChartHomotopy hp N K1 K0 where
  value q w t := J.value q w
    ⟨1 - t.1, by constructor <;> linarith [t.2.1, t.2.2]⟩
  continuous_value := by
    intro q
    exact (J.continuous_value q).comp
      (continuous_fst.prodMk
        (Continuous.subtype_mk
          (continuous_const.sub (continuous_subtype_val.comp continuous_snd)) _))
  value_zero := by intro q w; simpa using J.value_one q w
  value_one := by intro q w; simpa using J.value_zero q w
  decorated_compatible := by
    intro g h q r w v t hchart
    exact J.decorated_compatible g h q r w v _ hchart
  zeroFree := by intro q w t; exact J.zeroFree q w _

/-- Concatenate compatible chart homotopies. -/
noncomputable def trans
    {hp : Nat.Prime p} {N : Nat} {K0 K1 K2 : ChartMap hp N}
    (J01 : ChartHomotopy hp N K0 K1)
    (J12 : ChartHomotopy hp N K1 K2) : ChartHomotopy hp N K0 K2 where
  value q w t := if t.1 <= 1 / 2 then
      J01.value q w (clampUnit (2 * t.1))
    else
      J12.value q w (clampUnit (2 * t.1 - 1))
  continuous_value := by
    intro q
    apply Continuous.if_le
    · exact (J01.continuous_value q).comp
        (continuous_fst.prodMk
          (continuous_clampUnit.comp
            (continuous_const.mul (continuous_subtype_val.comp continuous_snd))))
    · exact (J12.continuous_value q).comp
        (continuous_fst.prodMk
          (continuous_clampUnit.comp
            ((continuous_const.mul
              (continuous_subtype_val.comp continuous_snd)).sub continuous_const)))
    · exact continuous_subtype_val.comp continuous_snd
    · exact continuous_const
    · intro z hz
      have h2 : (2 : Real) * z.2.1 = 1 := by rw [hz]; norm_num
      have hA : clampUnit (2 * (z.2 : Real)) = ⟨1, by norm_num⟩ := by
        apply Subtype.ext
        simp [clampUnit, h2]
      have hB : clampUnit (2 * (z.2 : Real) - 1) = ⟨0, by norm_num⟩ := by
        apply Subtype.ext
        simp [clampUnit, h2]
      rw [hA, hB]
      exact (J01.value_one q z.1).trans (J12.value_zero q z.1).symm
  value_zero := by
    intro q w
    have hcond : ((0 : Real)) ≤ 1 / 2 := by norm_num
    have hz : clampUnit (2 * (0 : Real)) = ⟨0, by norm_num⟩ := by
      apply Subtype.ext
      simp [clampUnit]
    show (if ((0 : Real)) ≤ 1 / 2 then J01.value q w (clampUnit (2 * (0 : Real)))
      else J12.value q w (clampUnit (2 * (0 : Real) - 1))) = K0.value q w
    rw [if_pos hcond, hz]
    exact J01.value_zero q w
  value_one := by
    intro q w
    have hcond : ¬ ((1 : Real)) ≤ 1 / 2 := by norm_num
    have hz : clampUnit (2 * (1 : Real) - 1) = ⟨1, by norm_num⟩ := by
      apply Subtype.ext
      norm_num [clampUnit]
    show (if ((1 : Real)) ≤ 1 / 2 then J01.value q w (clampUnit (2 * (1 : Real)))
      else J12.value q w (clampUnit (2 * (1 : Real) - 1))) = K2.value q w
    rw [if_neg hcond, hz]
    exact J12.value_one q w
  decorated_compatible := by
    intro g h q r w v t hchart
    split_ifs <;>
      first
      | exact J01.decorated_compatible g h q r w v _ hchart
      | exact J12.decorated_compatible g h q r w v _ hchart
  zeroFree := by
    intro q w t
    split_ifs <;> first | exact J01.zeroFree q w _ | exact J12.zeroFree q w _

end ChartHomotopy

/-- Restrict a global zero-free equivariant homotopy to every refined chart. -/
noncomputable def ofGlobalHomotopy
    (hp : Nat.Prime p) (N : Nat)
    {F0 F1 : ZeroFreeMap hp} (H : ZeroFreeHomotopy hp F0 F1) :
    ChartHomotopy hp N (ofGlobalMap hp N F0) (ofGlobalMap hp N F1) where
  value q w t := H.map (chart hp N q (StandardSimplex.toDelta w), t)
  continuous_value := by
    intro q
    exact H.map.continuous.comp
      ((((chart hp N q).continuous.comp continuous_toDelta).comp continuous_fst).prodMk
        continuous_snd)
  value_zero := by intro q w; exact H.map_zero _
  value_one := by intro q w; exact H.map_one _
  decorated_compatible := by
    intro g h q r w v t hchart
    have hg := H.equivariant g (chart hp N q (StandardSimplex.toDelta w)) t
    have hh := H.equivariant h (chart hp N r (StandardSimplex.toDelta v)) t
    rw [← hg, ← hh]
    exact congrArg (fun x => H.map (x, t)) hchart
  zeroFree := by intro q w t; exact H.zeroFree _ _

/-- Zero-free chart homotopy from the original PL interpolation to the global endpoint map. -/
noncomputable def originalPLToGlobal
    (hp : Nat.Prime p) (F : ZeroFreeMap hp)
    (A : StableRegularApproximation hp F.map) (k : Nat) :
    ChartHomotopy hp (A.toRegularApproximation.level + k)
      (originalPLMap hp A.toRegularApproximation k)
      (ofGlobalMap hp (A.toRegularApproximation.level + k) F) where
  value q w t :=
    (1 - t.1) • (originalPLMap hp A.toRegularApproximation k).value q w +
      t.1 • F.map
        (chart hp (A.toRegularApproximation.level + k) q
          (StandardSimplex.toDelta w))
  continuous_value := by
    intro q
    exact ((continuous_const.sub (continuous_subtype_val.comp continuous_snd)).smul
        (((originalPLMap hp A.toRegularApproximation k).continuous_value q).comp
          continuous_fst)).add
      ((continuous_subtype_val.comp continuous_snd).smul
        (((F.map.continuous.comp
          ((chart hp (A.toRegularApproximation.level + k) q).continuous.comp
            continuous_toDelta))).comp continuous_fst))
  value_zero := by
    intro q w
    show (1 - (0 : Real)) • (originalPLMap hp A.toRegularApproximation k).value q w +
        (0 : Real) • F.map
          (chart hp (A.toRegularApproximation.level + k) q
            (StandardSimplex.toDelta w)) =
      (originalPLMap hp A.toRegularApproximation k).value q w
    module
  value_one := by
    intro q w
    show (1 - (1 : Real)) • (originalPLMap hp A.toRegularApproximation k).value q w +
        (1 : Real) • F.map
          (chart hp (A.toRegularApproximation.level + k) q
            (StandardSimplex.toDelta w)) =
      F.map (chart hp (A.toRegularApproximation.level + k) q
        (StandardSimplex.toDelta w))
    module
  decorated_compatible := by
    intro g h q r w v t hchart
    have h1 := (originalPLMap hp A.toRegularApproximation k).decorated_compatible
      g h q r w v hchart
    have h2 : g • F.map (chart hp (A.toRegularApproximation.level + k) q
          (StandardSimplex.toDelta w)) =
        h • F.map (chart hp (A.toRegularApproximation.level + k) r
          (StandardSimplex.toDelta v)) := by
      rw [← F.equivariant g, ← F.equivariant h]
      exact congrArg F.map hchart
    funext i
    have e1 := congrFun h1 i
    have e2 := congrFun h2 i
    simp only [PrimeSymmetry.smul_coordinate_apply, Pi.add_apply, Pi.smul_apply,
      smul_eq_mul] at e1 e2 ⊢
    rw [e1, e2]
  zeroFree := by
    intro q w t
    let q0 := ancestorTopCell hp A.toRegularApproximation.level k q
    let w0 := ancestorWeight A.toRegularApproximation.level k q w
    have h := A.toRegularApproximation.zeroFreeStraightLine q0 w0
      ⟨1 - t.1, by constructor <;> linarith [t.2.1, t.2.2]⟩
    simpa [originalPLMap, ChartMap.refine, baseOriginalPLMap,
      q0, w0, chart_eq_ancestor, add_smul, smul_add, add_comm] using h

/-- Zero-free chart homotopy from the global endpoint map to the original PL interpolation. -/
noncomputable def globalToOriginalPL
    (hp : Nat.Prime p) (F : ZeroFreeMap hp)
    (A : StableRegularApproximation hp F.map) (k : Nat) :
    ChartHomotopy hp (A.toRegularApproximation.level + k)
      (ofGlobalMap hp (A.toRegularApproximation.level + k) F)
      (originalPLMap hp A.toRegularApproximation k) :=
  (originalPLToGlobal hp F A k).symm

/-- Transport a compatible chart map along an equality of subdivision levels. -/
noncomputable def ChartMap.castLevel
    {hp : Nat.Prime p} {N M : Nat} (h : N = M) (K : ChartMap hp N) : ChartMap hp M :=
  h ▸ K

theorem ChartMap.castLevel_ofGlobalMap
    {hp : Nat.Prime p} {N M : Nat} (h : N = M) (F : ZeroFreeMap hp) :
    ChartMap.castLevel h (ofGlobalMap hp N F) = ofGlobalMap hp M F := by
  subst h
  rfl

/-- Transport a compatible chart homotopy along an equality of subdivision levels. -/
noncomputable def ChartHomotopy.castLevel
    {hp : Nat.Prime p} {N M : Nat} (h : N = M) {K0 K1 : ChartMap hp N}
    (J : ChartHomotopy hp N K0 K1) :
    ChartHomotopy hp M (ChartMap.castLevel h K0) (ChartMap.castLevel h K1) := by
  subst h
  exact J

/-- Canonical common spatial level used by the PL-ended middle homotopy. -/
def baseCommonLevel
    {hp : Nat.Prime p} {F0 F1 : ZeroFreeMap hp}
    (A0 : StableRegularApproximation hp F0.map)
    (A1 : StableRegularApproximation hp F1.map) : Nat :=
  A0.toRegularApproximation.level + A1.toRegularApproximation.level + 1

/-- The two component levels agree with the common level after reassociation. -/
theorem upperLevel_eq_baseCommonLevel
    {hp : Nat.Prime p} {F0 F1 : ZeroFreeMap hp}
    (A0 : StableRegularApproximation hp F0.map)
    (A1 : StableRegularApproximation hp F1.map) :
    A1.toRegularApproximation.level + (A0.toRegularApproximation.level + 1) =
      baseCommonLevel A0 A1 := by
  simp [baseCommonLevel]
  omega

/-- The chartwise middle homotopy with exact endpoint PL maps. -/
noncomputable def plEndedHomotopy
    (hp : Nat.Prime p)
    (F0 F1 : ZeroFreeMap hp)
    (H : ZeroFreeHomotopy hp F0 F1)
    (A0 : StableRegularApproximation hp F0.map)
    (A1 : StableRegularApproximation hp F1.map) :
    ChartHomotopy hp (baseCommonLevel A0 A1)
      (originalPLMap hp A0.toRegularApproximation
        (A1.toRegularApproximation.level + 1))
      (ChartMap.castLevel (upperLevel_eq_baseCommonLevel A0 A1)
        (originalPLMap hp A1.toRegularApproximation
          (A0.toRegularApproximation.level + 1))) := by
  have hlast :=
    (globalToOriginalPL hp F1 A1 (A0.toRegularApproximation.level + 1)).castLevel
      (upperLevel_eq_baseCommonLevel A0 A1)
  rw [ChartMap.castLevel_ofGlobalMap] at hlast
  exact (originalPLToGlobal hp F0 A0 (A1.toRegularApproximation.level + 1)).trans
    ((ofGlobalHomotopy hp (baseCommonLevel A0 A1) H).trans hlast)

end CompatibleRefinedChartHomotopy
end EquivariantPrismStableRelativeBoundary
end FoxNeuwirthOrderComplex
end NRR
