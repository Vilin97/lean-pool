/-
Copyright (c) 2026 Wouter Cames van Batenburg, Samuel Korsky. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wouter Cames van Batenburg, Samuel Korsky
-/

module

public import LeanPool.MooreBound.DegreeDiameter.FlagSpace
public import LeanPool.MooreBound.DegreeDiameter.Symmetry
public import Mathlib.LinearAlgebra.Basis.Prod
public import Mathlib.LinearAlgebra.Pi
public import Mathlib.LinearAlgebra.Prod
public import Mathlib.LinearAlgebra.StdBasis

/-!
# A big cell of even partial flags

We construct a recursive affine cell inside the even partial flags.  At one
step the ambient space is `K² × W`.  A linear map `L : K² → W` supplies its
graph as the first retained two-dimensional subspace, and an even partial
flag in `W` supplies all later retained subspaces.  The graph recovers `L`;
after `L` is known, inverse skew transport recovers the old partial flag.
The resulting number of free scalar parameters satisfies
`d(k+1) = 2*(2*k+1) + d(k)`, hence `d(k)=2*k²`.

Lean Pool port of wewantmoore commit d59bd80ea93fabb9faf769e790ab47692645e022.
The port adds a namespace and adapts proofs to the current Mathlib APIs and repository style.
-/

public section

namespace MooreBound

open Module

namespace DegreeDiameter

universe u

section Prepend

variable {K X Y : Type*} [DivisionRing K]
  [AddCommGroup X] [Module K X] [AddCommGroup Y] [Module K Y]

/-- The evident equivalence between a product submodule and the product of
the two submodule types. -/
def submoduleProdEquiv (P : Submodule K X) (Q : Submodule K Y) :
    P.prod Q ≃ₗ[K] P × Q where
  toFun z := (⟨z.1.1, z.2.1⟩, ⟨z.1.2, z.2.2⟩)
  invFun z := ⟨(z.1.1, z.2.1), z.1.2, z.2.2⟩
  left_inv z := by cases z; rfl
  right_inv z := by cases z with | mk a b => cases a; cases b; rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem finrank_submodule_prod
    [FiniteDimensional K X] [FiniteDimensional K Y]
    (P : Submodule K X) (Q : Submodule K Y) :
    finrank K (P.prod Q) = finrank K P + finrank K Q := by
  calc
    finrank K (P.prod Q) = finrank K (P × Q) := (submoduleProdEquiv P Q).finrank_eq
    _ = finrank K P + finrank K Q := Module.finrank_prod

variable {m : ℕ}

/-- Put the standard two-dimensional flag before a complete flag `F`. -/
noncomputable def prependTwoComplete (F : CompleteFlag K Y m) :
    CompleteFlag K ((Fin 2 → K) × Y) (m + 2) := by
  let bY : Basis (Fin m) K Y := Classical.choose (common_apartment K Y F F)
  letI : FiniteDimensional K Y := bY.finiteDimensional_of_finite
  let b : Basis (Fin 2) K (Fin 2 → K) := Pi.basisFun K (Fin 2)
  let S : Fin ((m + 2) + 1) → Submodule K ((Fin 2 → K) × Y) := fun i ↦
    if hi : i.val < 2 then
      (b.flag ⟨i.val, by omega⟩).prod ⊥
    else
      (⊤ : Submodule K (Fin 2 → K)).prod (F ⟨i.val - 2, by omega⟩)
  have hmono : Monotone S := by
    intro i j hij
    dsimp [S]
    split_ifs with hi hj
    · rintro z hz
      exact ⟨b.flag_mono (by simpa using hij) hz.1, hz.2⟩
    · rintro z hz
      have hz0 : z.2 = 0 := (Submodule.mem_bot K).mp hz.2
      exact ⟨Submodule.mem_top, by rw [hz0]; exact Submodule.zero_mem _⟩
    · omega
    · rintro z hz
      refine ⟨hz.1, F.strictMono_space.monotone ?_ hz.2⟩
      exact Fin.mk_le_mk.mpr (by omega)
  have hrank : ∀ i, finrank K (S i) = i.val := by
    intro i
    by_cases hi : i.val < 2
    · have hSi : S i = (b.flag ⟨i.val, by omega⟩).prod ⊥ := by
        simp [S, show i.val ≤ 1 by omega]
      have hb := (CompleteFlag.ofBasis b).finrank_space ⟨i.val, by omega⟩
      change finrank K (b.flag ⟨i.val, by omega⟩) = i.val at hb
      calc
        finrank K (S i) = finrank K ((b.flag ⟨i.val, by omega⟩).prod ⊥) :=
          congrArg (fun T : Submodule K ((Fin 2 → K) × Y) ↦ finrank K T) hSi
        _ = finrank K (b.flag ⟨i.val, by omega⟩) + finrank K (⊥ : Submodule K Y) :=
          finrank_submodule_prod _ _
        _ = i.val := by simpa using hb
    · have hSi : S i = (⊤ : Submodule K (Fin 2 → K)).prod
          (F ⟨i.val - 2, by omega⟩) := by
        simp [S, show ¬ i.val ≤ 1 by omega]
      have htwo : finrank K (Fin 2 → K) = 2 := by simp
      calc
        finrank K (S i) = finrank K ((⊤ : Submodule K (Fin 2 → K)).prod
            (F ⟨i.val - 2, by omega⟩)) :=
          congrArg (fun T : Submodule K ((Fin 2 → K) × Y) ↦ finrank K T) hSi
        _ = finrank K (⊤ : Submodule K (Fin 2 → K)) +
            finrank K (F ⟨i.val - 2, by omega⟩) := finrank_submodule_prod _ _
        _ = i.val := by
          rw [finrank_top, htwo, F.finrank_space]
          simp only
          omega
  exact
    { space := S
      strictMono_space := fun i j hij ↦
        lt_of_le_of_ne (hmono hij.le) (by
          intro heq
          have hfr := congrArg
            (fun T : Submodule K ((Fin 2 → K) × Y) ↦ finrank K T) heq
          rw [hrank, hrank] at hfr
          omega)
      finrank_space := hrank
      space_zero := by simp [S, b]
      space_last := by
        change S (Fin.last (m + 2)) = ⊤
        dsimp [S]
        have hi : (⟨(m + 2) - 2, by omega⟩ : Fin (m + 1)) = Fin.last m := by
          apply Fin.ext
          simp
        rw [hi, F.space_last]
        simp }

/-- Shift a rank in the old flag past the two newly prepended ranks. -/
def shiftedRank (m : ℕ) (i : Fin (m + 1)) : Fin ((m + 2) + 1) :=
  ⟨i.val + 2, by omega⟩

@[simp]
theorem prependTwoComplete_shifted (F : CompleteFlag K Y m) (i : Fin (m + 1)) :
    prependTwoComplete F (shiftedRank m i) =
      (⊤ : Submodule K (Fin 2 → K)).prod (F i) := by
  simp [prependTwoComplete, shiftedRank]

/-- The lower block-unitriangular equivalence `(x,y) ↦ (x, y + L x)`. -/
def skewEquiv (L : (Fin 2 → K) →ₗ[K] Y) :
    ((Fin 2 → K) × Y) ≃ₗ[K] ((Fin 2 → K) × Y) :=
  (LinearEquiv.refl K (Fin 2 → K)).skewProd (LinearEquiv.refl K Y) L

@[simp]
theorem skewEquiv_apply (L : (Fin 2 → K) →ₗ[K] Y) (z : (Fin 2 → K) × Y) :
    skewEquiv L z = (z.1, z.2 + L z.1) := rfl

/-- The image of the horizontal two-space under the skew equivalence is the
graph of `L`. -/
theorem map_top_prod_bot_skewEquiv (L : (Fin 2 → K) →ₗ[K] Y) :
    ((⊤ : Submodule K (Fin 2 → K)).prod (⊥ : Submodule K Y)).map
      (skewEquiv L).toLinearMap = L.graph := by
  ext z
  constructor
  · rintro ⟨w, hw, rfl⟩
    have hw0 : w.2 = 0 := (Submodule.mem_bot K).mp hw.2
    change (skewEquiv L w).2 = L (skewEquiv L w).1
    simp [hw0]
  · intro hz
    change z.2 = L z.1 at hz
    refine ⟨(z.1, 0), ⟨Submodule.mem_top, Submodule.zero_mem _⟩, ?_⟩
    apply Prod.ext
    · rfl
    · simpa using hz.symm

theorem linearMap_graph_injective :
    Function.Injective (fun L : (Fin 2 → K) →ₗ[K] Y ↦ L.graph) := by
  intro L M h
  change L.graph = M.graph at h
  apply LinearMap.ext
  intro (x : Fin 2 → K)
  have hx : (x, L x) ∈ L.graph := rfl
  rw [h] at hx
  exact hx

/-- Prepend two ranks and skew them so that rank two is `graph L`. -/
noncomputable def skewPrependComplete (L : (Fin 2 → K) →ₗ[K] Y)
    (F : CompleteFlag K Y m) : CompleteFlag K ((Fin 2 → K) × Y) (m + 2) :=
  (prependTwoComplete F).map (skewEquiv L)

@[simp]
theorem skewPrependComplete_shifted (L : (Fin 2 → K) →ₗ[K] Y)
    (F : CompleteFlag K Y m) (i : Fin (m + 1)) :
    skewPrependComplete L F (shiftedRank m i) =
      ((⊤ : Submodule K (Fin 2 → K)).prod (F i)).map (skewEquiv L).toLinearMap := by
  simp [skewPrependComplete, prependTwoComplete_shifted]

theorem skewPrependComplete_rank_two (L : (Fin 2 → K) →ₗ[K] Y)
    (F : CompleteFlag K Y m) :
    skewPrependComplete L F (shiftedRank m 0) = L.graph := by
  rw [skewPrependComplete_shifted, F.space_zero, map_top_prod_bot_skewEquiv]

/-- Equality of the new even parts recovers both the graph parameter and the
old even part. -/
theorem skewPrepend_evenPart_recover
    {L M : (Fin 2 → K) →ₗ[K] Y} {F G : CompleteFlag K Y m}
    (h : PartialFlag.ofComplete 0 (skewPrependComplete L F) =
      PartialFlag.ofComplete 0 (skewPrependComplete M G)) :
    L = M ∧ PartialFlag.ofComplete 0 F = PartialFlag.ofComplete 0 G := by
  have htwo := congrFun (congrArg Subtype.val h) (shiftedRank m 0)
  have hgraph : L.graph = M.graph := by
    have heven : (shiftedRank m (0 : Fin (m + 1))).val % 2 = 0 := by
      simp [shiftedRank]
    change flagPart 0 (skewPrependComplete L F) (shiftedRank m 0) =
      flagPart 0 (skewPrependComplete M G) (shiftedRank m 0) at htwo
    simp only [flagPart, Nat.zero_mod, ite_eq_left heven] at htwo
    simpa only [skewPrependComplete_rank_two] using htwo
  have hLM : L = M := linearMap_graph_injective hgraph
  subst M
  refine ⟨rfl, ?_⟩
  apply PartialFlag.ext
  intro i
  by_cases hi : i.val % 2 = 0
  · have hshift := congrFun (congrArg Subtype.val h) (shiftedRank m i)
    have hshiftEven : (shiftedRank m i).val % 2 = 0 := by
      simp [shiftedRank]
      omega
    simp only [PartialFlag.ofComplete, flagPart, hshiftEven, Nat.zero_mod, ↓reduceIte,
      skewPrependComplete_shifted] at hshift
    have hmaps :
        ((⊤ : Submodule K (Fin 2 → K)).prod (F i)).map (skewEquiv L).toLinearMap =
          ((⊤ : Submodule K (Fin 2 → K)).prod (G i)).map (skewEquiv L).toLinearMap := by
      exact hshift
    have hprod : (⊤ : Submodule K (Fin 2 → K)).prod (F i) =
        (⊤ : Submodule K (Fin 2 → K)).prod (G i) :=
      (Submodule.map_injective_of_injective (skewEquiv L).injective) hmaps
    have hc := congrArg
      (fun S : Submodule K ((Fin 2 → K) × Y) ↦
        S.comap (LinearMap.inr K (Fin 2 → K) Y)) hprod
    simpa [PartialFlag.ofComplete, flagPart, hi, Submodule.prod_comap_inr] using hc
  · simp [PartialFlag.ofComplete, flagPart, hi]

end Prepend

section BigCell

variable (K : Type u) [Field K]

/-- The recursive affine parameter space. -/
def BigCell : ℕ → Type u
  | 0 => ULift.{u} Unit
  | k + 1 => ((Fin 2 → K) →ₗ[K] FlagSpace K k) × BigCell k

instance bigCellFinite [Finite K] (k : ℕ) : Finite (BigCell K k) := by
  induction k with
  | zero => simp only [BigCell]; infer_instance
  | succ k ih =>
      simp only [BigCell]
      let : Finite (BigCell K k) := ih
      let : Finite ((Fin 2 → K) →ₗ[K] FlagSpace K k) :=
        Finite.of_injective
          (fun L : (Fin 2 → K) →ₗ[K] FlagSpace K k ↦ (L : (Fin 2 → K) → FlagSpace K k))
          LinearMap.coe_injective
      infer_instance

/-- Choose a complete representative of a partial flag. -/
noncomputable def representativeComplete {V : Type*} [AddCommGroup V] [Module K V]
    {n parity : ℕ} (P : PartialFlag (K := K) (V := V) (n := n) parity) :
    CompleteFlag K V n := Classical.choose P.property

theorem representativeComplete_part {V : Type*} [AddCommGroup V] [Module K V]
    {n parity : ℕ} (P : PartialFlag (K := K) (V := V) (n := n) parity) :
    PartialFlag.ofComplete parity (representativeComplete K P) = P := by
  apply Subtype.ext
  exact Classical.choose_spec P.property

/-- The big-cell injection into even partial flags. -/
noncomputable def bigCellFlag : ∀ k : ℕ, BigCell K k →
    EvenPartialFlag (K := K) (V := FlagSpace K k) (n := flagDim k)
  | 0, _ => PartialFlag.ofComplete 0
      (CompleteFlag.ofBasis (Pi.basisFun K (Fin 1)))
  | k + 1, z =>
      let P := bigCellFlag k z.2
      PartialFlag.ofComplete 0
        (skewPrependComplete z.1 (representativeComplete K P))

theorem bigCellFlag_injective : ∀ k : ℕ, Function.Injective (bigCellFlag K k) := by
  intro k
  induction k with
  | zero =>
      intro x y _
      change ULift.{u} Unit at x y
      apply ULift.ext
      exact Subsingleton.elim _ _
  | succ k ih =>
      intro x y hxy
      change PartialFlag.ofComplete 0
          (skewPrependComplete x.1 (representativeComplete K (bigCellFlag K k x.2))) =
        PartialFlag.ofComplete 0
          (skewPrependComplete y.1 (representativeComplete K (bigCellFlag K k y.2))) at hxy
      obtain ⟨hmap, hpart⟩ := skewPrepend_evenPart_recover hxy
      have hold : bigCellFlag K k x.2 = bigCellFlag K k y.2 := by
        calc
          bigCellFlag K k x.2 = PartialFlag.ofComplete 0
              (representativeComplete K (bigCellFlag K k x.2)) :=
            (representativeComplete_part K _).symm
          _ = PartialFlag.ofComplete 0
              (representativeComplete K (bigCellFlag K k y.2)) := hpart
          _ = bigCellFlag K k y.2 := representativeComplete_part K _
      exact Prod.ext hmap (ih hold)

theorem natCard_linearMap_from_two (k : ℕ) :
    Nat.card ((Fin 2 → K) →ₗ[K] FlagSpace K k) =
      Nat.card K ^ (2 * flagDim k) := by
  calc
    Nat.card ((Fin 2 → K) →ₗ[K] FlagSpace K k) =
        Nat.card (Fin 2 → FlagSpace K k) :=
      Nat.card_congr (LinearEquiv.piRing K (FlagSpace K k) (Fin 2) K).toEquiv
    _ = Nat.card (FlagSpace K k) ^ 2 := by
      rw [Nat.card_fun]
      simp
    _ = (Nat.card K ^ flagDim k) ^ 2 := by rw [natCard_flagSpace]
    _ = Nat.card K ^ (2 * flagDim k) := by
      rw [← pow_mul]
      congr 1
      omega

theorem natCard_bigCell (k : ℕ) :
    Nat.card (BigCell K k) = Nat.card K ^ (2 * k * k) := by
  induction k with
  | zero => simp [BigCell]
  | succ k ih =>
      rw [show BigCell K (k + 1) =
          (((Fin 2 → K) →ₗ[K] FlagSpace K k) × BigCell K k) by rfl,
        Nat.card_prod, natCard_linearMap_from_two, ih, ← pow_add]
      congr 1
      rw [flagDim_eq]
      ring

/-- The `2*k²`-dimensional affine cell gives the required vertex lower
bound. -/
theorem natCard_evenPartialFlag_lower [Finite K] (k : ℕ) :
    Nat.card K ^ (2 * k * k) ≤
      Nat.card (EvenPartialFlag (K := K) (V := FlagSpace K k) (n := flagDim k)) := by
  rw [← natCard_bigCell K k]
  exact Nat.card_le_card_of_injective (bigCellFlag K k) (bigCellFlag_injective K k)

end BigCell

end DegreeDiameter

end MooreBound
