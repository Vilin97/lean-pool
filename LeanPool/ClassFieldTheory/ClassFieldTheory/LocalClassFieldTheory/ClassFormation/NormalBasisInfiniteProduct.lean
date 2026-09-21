/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.GaloisCohomology.Cyclic.Herbrand.NormalBasisLattice
import LeanPool.ClassFieldTheory.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.PrincipalUnitQuotients
import LeanPool.ClassFieldTheory.GaloisCohomology.Cyclic.Herbrand.HerbrandLowDegree.Basic
import LeanPool.ClassFieldTheory.ClassFieldTheory.LocalClassFieldTheory.ClassFormation.Valuation
/-! Provides the public declarations in the `LocalClassFieldTheory.ClassFormation.NormalBasisInfiniteProduct` Lean module. -/

namespace LocalClassFieldTheory
open CyclicCohomology

open CyclicCohomology LocalFieldTheory

noncomputable section

universe u

open scoped BigOperators
open scoped ValuativeRel
open Filter IsNonarchimedeanLocalField
open CyclicCohomology.ProfiniteCohomology.Herbrand

variable (K L : Type u) [Field K] [Field L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [ValuativeRel L]
  [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]

omit [FiniteDimensional K L] [IsGalois K L] in
/-- An element of `π_K^m 𝒪_L`, viewed in `L`, is represented by an
element of `𝓂_L^m`.  This is the valuation-extension bridge needed to turn
normal-basis corrections into the usual principal-unit corrections. -/
theorem chosenBaseUniformizerPow_integerRingFieldSubmodule_exists_mem_maximalIdeal_pow
    (m : Nat) {x : L}
    (hx : x ∈ chosenBaseUniformizerPowSubmodule K L m
      (integerRingFieldSubmodule K L)) :
    ∃ a : 𝒪[L], a ∈ (𝓂[L] ^ m : Ideal 𝒪[L]) ∧ (a : L) = x := by
  rcases (mem_chosenBaseUniformizerPowSubmodule_iff
      (K := K) (L := L) m (integerRingFieldSubmodule K L) x).1 hx with
    ⟨y, hy, rfl⟩
  let yInt : 𝒪[L] := ⟨y,
    (mem_integerRingFieldSubmodule_iff (K := K) (L := L) y).1 hy⟩
  let πL : 𝒪[L] :=
    integerRingMapOfValuationExtension K L (chosenIntegerRingUniformizer K)
  have hπL : πL ∈ (𝓂[L] : Ideal 𝒪[L]) := by
    exact integerRingMap_uniformizer_mem_maximalIdeal_of_valuationExtension
      (K := K) (L := L)
  refine ⟨πL ^ m * yInt, ?_, ?_⟩
  · exact Ideal.mul_mem_right yInt _ (Ideal.pow_mem_pow hπL m)
  · dsimp [πL, yInt]
    rw [map_pow]
    rfl

/-- Once `π_K^bM ⊆ 𝒪_L` and `b+1 ≤ n`, a correction in
`V^(n+i)` is an honest element of the usual principal-unit group `U_L^(i+1)`. -/
theorem chosenNormalBasisPrincipalUnitSet_mem_principalUnits_succ_of_lattice_bound
    {b n i : Nat}
    (hb : chosenBaseUniformizerPowSubmodule K L b
        (chosenNormalBasisIntegerLattice K L) ≤
      integerRingFieldSubmodule K L)
    (hbn : b + 1 ≤ n) {z : 𝒪[L]ˣ}
    (hz : z ∈ chosenNormalBasisPrincipalUnitSet K L (n + i)) :
    z ∈ principalUnits L (1 + i) := by
  rcases Nat.exists_eq_add_of_le hbn with ⟨r, rfl⟩
  let x : L := ((((z : 𝒪[L]ˣ) : 𝒪[L]) - 1 : 𝒪[L]) : L)
  have hxdeep : x ∈ chosenBaseUniformizerPowSubmodule K L
      (b + ((1 + r) + i)) (chosenNormalBasisIntegerLattice K L) := by
    simpa [x, Nat.add_assoc] using hz
  have hxint : x ∈ chosenBaseUniformizerPowSubmodule K L ((1 + r) + i)
      (integerRingFieldSubmodule K L) :=
    chosenBaseUniformizerPowSubmodule_add_le_chosenBaseUniformizerPowSubmodule_of_le
      (K := K) (L := L) (a := b) (n := (1 + r) + i) hb hxdeep
  rcases chosenBaseUniformizerPow_integerRingFieldSubmodule_exists_mem_maximalIdeal_pow
      (K := K) (L := L) ((1 + r) + i) hxint with ⟨a, ha, hax⟩
  have hpow : (𝓂[L] ^ ((1 + r) + i) : Ideal 𝒪[L]) ≤
      (𝓂[L] ^ (1 + i) : Ideal 𝒪[L]) := by
    apply Ideal.pow_le_pow_right
    exact Nat.add_le_add_right (Nat.le_add_right 1 r) i
  have ha' : a ∈ (𝓂[L] ^ (1 + i) : Ideal 𝒪[L]) := hpow ha
  rw [mem_principalUnits_iff]
  have haeq : a = ((z : 𝒪[L]ˣ) : 𝒪[L]) - 1 := by
    apply Subtype.ext
    simpa [x] using hax
  simpa [haeq] using ha'

/-- Once the normal-basis lattice has entered `𝒪_L`, a sequence whose
`i`-th term lies in `V^(n+i)` converges to `1` in `𝒪_L`. -/
theorem tendsto_chosenNormalBasisPrincipalUnitSequence_one_of_lattice_bound
    [UniformSpace L] [IsUniformAddGroup L] [IsNonarchimedeanLocalField L]
    {b n : Nat}
    (hb : chosenBaseUniformizerPowSubmodule K L b
        (chosenNormalBasisIntegerLattice K L) ≤
      integerRingFieldSubmodule K L)
    (hbn : b + 1 ≤ n) (z : Nat → 𝒪[L]ˣ)
    (hz : ∀ i : Nat, z i ∈ chosenNormalBasisPrincipalUnitSet K L (n + i)) :
    Tendsto (fun i : Nat => ((z i : 𝒪[L]ˣ) : 𝒪[L])) atTop
      (nhds (1 : 𝒪[L])) := by
  have hsub : Tendsto
      (fun i : Nat => ((z i : 𝒪[L]ˣ) : 𝒪[L]) - 1) atTop
      (nhds (0 : 𝒪[L])) := by
    rw [tendsto_def]
    intro s hs
    rcases eventually_maximalIdeal_pow_subset_nhds_zero L s hs with ⟨N, hN⟩
    filter_upwards [eventually_ge_atTop N] with i hi
    apply hN (1 + i)
    · exact le_trans hi (Nat.le_add_left i 1)
    · exact (mem_principalUnits_iff L (z i) (1 + i)).1
        (chosenNormalBasisPrincipalUnitSet_mem_principalUnits_succ_of_lattice_bound
          (K := K) (L := L) hb hbn (hz i))
  simpa using hsub.const_add (1 : 𝒪[L])

/-- Every ring equivalence of the valuation integer ring is continuous.  The
proof uses the maximal-ideal powers as a neighborhood basis and the fact that
a ring equivalence preserves each such power. -/
theorem continuous_integerRingEquiv_of_isNonarchimedeanLocalField
    [UniformSpace L] [IsUniformAddGroup L] [IsNonarchimedeanLocalField L]
    (e : 𝒪[L] ≃+* 𝒪[L]) : Continuous e := by
  apply continuous_of_continuousAt_zero e.toAddMonoidHom
  rw [ContinuousAt, map_zero, tendsto_def]
  intro s hs
  rcases exists_maximalIdeal_pow_subset_nhds_zero L s hs with ⟨N, hN⟩
  exact Filter.mem_of_superset (maximalIdeal_pow_mem_nhds_zero L N)
    (fun x hx => hN
      ((integerRingEquiv_mem_maximalIdeal_pow L e N x).2 hx))

omit [IsGalois K L] [TopologicalSpace K] [IsNonarchimedeanLocalField K] in
/-- Finite Tate norms for the actual `Gal(L / K)` action commute with limits
of valuation-ring units.  This is just continuity of each Galois conjugate
followed by continuity of a finite product. -/
theorem tendsto_galoisGroupIntegerUnits_tateNorm_of_tendsto
    [UniformSpace L] [IsUniformAddGroup L] [IsNonarchimedeanLocalField L]
    [IsIntegralClosure 𝒪[L] 𝒪[K] L]
    (f : Nat → 𝒪[L]ˣ) (x : 𝒪[L]ˣ)
    (hf : Tendsto (fun d : Nat => ((f d : 𝒪[L]ˣ) : 𝒪[L])) atTop
      (nhds ((x : 𝒪[L]ˣ) : 𝒪[L]))) :
    letI := galoisGroupIntegerUnitsMulDistribMulActionOfIsIntegralClosure K L
    Tendsto
      (fun d : Nat =>
        ((tateNorm (Gal(L / K)) 𝒪[L]ˣ (f d) : 𝒪[L]ˣ) : 𝒪[L]))
      atTop
      (nhds ((tateNorm (Gal(L / K)) 𝒪[L]ˣ x : 𝒪[L]ˣ) : 𝒪[L])) := by
  let := galoisGroupIntegerUnitsMulDistribMulActionOfIsIntegralClosure K L
  have hσ (sigma : Gal(L / K)) : Tendsto
      (fun d : Nat => ((sigma • f d : 𝒪[L]ˣ) : 𝒪[L])) atTop
      (nhds ((sigma • x : 𝒪[L]ˣ) : 𝒪[L])) := by
    have he :=
      (continuous_integerRingEquiv_of_isNonarchimedeanLocalField L
        (galoisGroupIntegerRingEquivOfIsIntegralClosure K L sigma)).tendsto
          ((x : 𝒪[L]ˣ) : 𝒪[L]) |>.comp hf
    rw [show
      (⇑(galoisGroupIntegerRingEquivOfIsIntegralClosure K L sigma) ∘
          fun d : Nat => ((f d : 𝒪[L]ˣ) : 𝒪[L])) =
        (fun d : Nat =>
          (galoisGroupIntegerRingEquivOfIsIntegralClosure K L sigma)
            ((f d : 𝒪[L]ˣ) : 𝒪[L])) by
      funext d
      rfl] at he
    simpa [
      galoisGroupIntegerUnitsMulDistribMulActionOfIsIntegralClosure_smul] using he
  have hprod := tendsto_finsetProd
    (Finset.univ : Finset (Gal(L / K))) (fun sigma _ => hσ sigma)
  convert hprod using 1 <;> simp [tateNorm]

omit [FiniteDimensional K L] [IsGalois K L]
    [TopologicalSpace K] [IsNonarchimedeanLocalField K] in
/-- The actual multiplicative coboundary `x ↦ g(x)x⁻¹` on valuation-ring
units commutes with limits taken in `𝒪_L`.  We use continuity of the
restricted Galois automorphism, and continuity of inversion away from zero in
the ambient local field. -/
theorem tendsto_galoisGroupIntegerUnits_sigmaMinusOne_of_tendsto
    [UniformSpace L] [IsUniformAddGroup L] [IsNonarchimedeanLocalField L]
    [IsIntegralClosure 𝒪[L] 𝒪[K] L]
    (g : Gal(L / K)) (f : Nat → 𝒪[L]ˣ) (x : 𝒪[L]ˣ)
    (hf : Tendsto (fun d : Nat => ((f d : 𝒪[L]ˣ) : 𝒪[L])) atTop
      (nhds ((x : 𝒪[L]ˣ) : 𝒪[L]))) :
    letI := galoisGroupIntegerUnitsMulDistribMulActionOfIsIntegralClosure K L
    Tendsto
      (fun d : Nat =>
        ((sigmaMinusOne (Gal(L / K)) 𝒪[L]ˣ g (f d) : 𝒪[L]ˣ) : 𝒪[L]))
      atTop
      (nhds ((sigmaMinusOne (Gal(L / K)) 𝒪[L]ˣ g x : 𝒪[L]ˣ) : 𝒪[L])) := by
  let := galoisGroupIntegerUnitsMulDistribMulActionOfIsIntegralClosure K L
  have hgO : Tendsto
      (fun d : Nat => ((g • f d : 𝒪[L]ˣ) : 𝒪[L])) atTop
      (nhds ((g • x : 𝒪[L]ˣ) : 𝒪[L])) := by
    have he :=
      (continuous_integerRingEquiv_of_isNonarchimedeanLocalField L
        (galoisGroupIntegerRingEquivOfIsIntegralClosure K L g)).tendsto
          ((x : 𝒪[L]ˣ) : 𝒪[L]) |>.comp hf
    rw [show
      (⇑(galoisGroupIntegerRingEquivOfIsIntegralClosure K L g) ∘
          fun d : Nat => ((f d : 𝒪[L]ˣ) : 𝒪[L])) =
        (fun d : Nat =>
          (galoisGroupIntegerRingEquivOfIsIntegralClosure K L g)
            ((f d : 𝒪[L]ˣ) : 𝒪[L])) by
      funext d
      rfl] at he
    simpa [
      galoisGroupIntegerUnitsMulDistribMulActionOfIsIntegralClosure_smul] using he
  have hfL : Tendsto
      (fun d : Nat => (((f d : 𝒪[L]ˣ) : 𝒪[L]) : L)) atTop
      (nhds (((x : 𝒪[L]ˣ) : 𝒪[L]) : L)) :=
    continuous_subtype_val.tendsto ((x : 𝒪[L]ˣ) : 𝒪[L]) |>.comp hf
  have hgL : Tendsto
      (fun d : Nat => (((g • f d : 𝒪[L]ˣ) : 𝒪[L]) : L)) atTop
      (nhds (((g • x : 𝒪[L]ˣ) : 𝒪[L]) : L)) :=
    continuous_subtype_val.tendsto ((g • x : 𝒪[L]ˣ) : 𝒪[L]) |>.comp hgO
  have hinv_coe (u : 𝒪[L]ˣ) :
      ((((u⁻¹ : 𝒪[L]ˣ) : 𝒪[L])) : L) =
        ((((u : 𝒪[L]ˣ) : 𝒪[L])) : L)⁻¹ := by
    apply eq_inv_of_mul_eq_one_right
    exact congrArg (fun y : 𝒪[L] => (y : L)) u.val_inv
  apply tendsto_subtype_rng.2
  have h := hgL.mul (hfL.inv₀ (by
    intro hx0
    apply Units.ne_zero x
    apply Subtype.ext
    exact hx0))
  convert h using 1 <;> simp [sigmaMinusOne, hinv_coe]

/-- Regard a normal-basis correction sequence as the usual sequence of
successively deeper principal units. -/
def chosenNormalBasisPrincipalUnitSequenceAsPrincipalUnits
    {b n : Nat}
    (hb : chosenBaseUniformizerPowSubmodule K L b
        (chosenNormalBasisIntegerLattice K L) ≤
      integerRingFieldSubmodule K L)
    (hbn : b + 1 ≤ n) (z : Nat → 𝒪[L]ˣ)
    (hz : ∀ i : Nat, z i ∈ chosenNormalBasisPrincipalUnitSet K L (n + i))
    (i : Nat) : principalUnits L (1 + i) :=
  ⟨z i,
    chosenNormalBasisPrincipalUnitSet_mem_principalUnits_succ_of_lattice_bound
      (K := K) (L := L) hb hbn (hz i)⟩

/-- Coercing the principal-unit sequence returns the original normal-basis correction term. -/
@[simp]
theorem chosenNormalBasisPrincipalUnitSequenceAsPrincipalUnits_val
    {b n : Nat}
    (hb : chosenBaseUniformizerPowSubmodule K L b
        (chosenNormalBasisIntegerLattice K L) ≤
      integerRingFieldSubmodule K L)
    (hbn : b + 1 ≤ n) (z : Nat → 𝒪[L]ˣ)
    (hz : ∀ i : Nat, z i ∈ chosenNormalBasisPrincipalUnitSet K L (n + i))
    (i : Nat) :
    (chosenNormalBasisPrincipalUnitSequenceAsPrincipalUnits K L hb hbn z hz i : 𝒪[L]ˣ) = z i :=
  rfl

/-- Finite products of a normal-basis correction sequence. -/
def chosenNormalBasisPrincipalUnitCorrectionProduct (z : Nat → 𝒪[L]ˣ) :
    Nat → 𝒪[L]ˣ
  | 0 => 1
  | d + 1 => chosenNormalBasisPrincipalUnitCorrectionProduct z d * z d

/-- The empty normal-basis correction product is the identity unit. -/
@[simp]
theorem chosenNormalBasisPrincipalUnitCorrectionProduct_zero (z : Nat → 𝒪[L]ˣ) :
    chosenNormalBasisPrincipalUnitCorrectionProduct (L := L) z 0 = 1 :=
  rfl

/-- A successor correction product appends the correction at the preceding index. -/
@[simp]
theorem chosenNormalBasisPrincipalUnitCorrectionProduct_succ
    (z : Nat → 𝒪[L]ˣ) (d : Nat) :
    chosenNormalBasisPrincipalUnitCorrectionProduct (L := L) z (d + 1) =
      chosenNormalBasisPrincipalUnitCorrectionProduct (L := L) z d * z d :=
  rfl

/-- The normal-basis partial products are definitionally the standard
principal-unit correction products after the lattice-to-ideal bridge. -/
theorem chosenNormalBasisPrincipalUnitCorrectionProduct_eq_principalUnitsCorrectionProduct
    {b n : Nat}
    (hb : chosenBaseUniformizerPowSubmodule K L b
        (chosenNormalBasisIntegerLattice K L) ≤
      integerRingFieldSubmodule K L)
    (hbn : b + 1 ≤ n) (z : Nat → 𝒪[L]ˣ)
    (hz : ∀ i : Nat, z i ∈ chosenNormalBasisPrincipalUnitSet K L (n + i))
    (d : Nat) :
    chosenNormalBasisPrincipalUnitCorrectionProduct (L := L) z d =
      principalUnitsCorrectionProduct L 1
        (chosenNormalBasisPrincipalUnitSequenceAsPrincipalUnits K L hb hbn z hz) d := by
  induction d with
  | zero => rfl
  | succ d ih =>
      rw [chosenNormalBasisPrincipalUnitCorrectionProduct_succ,
        principalUnitsCorrectionProduct_succ, ih]
      rfl

omit [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)] in

/-- If `V^n` is multiplicatively closed, every finite correction product
stays in `V^n`. -/
theorem chosenNormalBasisPrincipalUnitCorrectionProduct_mem
    {n : Nat}
    (hmul : ∀ u : 𝒪[L]ˣ, u ∈ chosenNormalBasisPrincipalUnitSet K L n →
      ∀ v : 𝒪[L]ˣ, v ∈ chosenNormalBasisPrincipalUnitSet K L n →
        u * v ∈ chosenNormalBasisPrincipalUnitSet K L n)
    (z : Nat → 𝒪[L]ˣ)
    (hz : ∀ i : Nat, z i ∈ chosenNormalBasisPrincipalUnitSet K L (n + i))
    (d : Nat) :
    chosenNormalBasisPrincipalUnitCorrectionProduct (L := L) z d ∈
      chosenNormalBasisPrincipalUnitSet K L n := by
  induction d with
  | zero =>
      exact chosenNormalBasisPrincipalUnitSet_one_mem (K := K) (L := L) n
  | succ d ih =>
      rw [chosenNormalBasisPrincipalUnitCorrectionProduct_succ]
      apply hmul _ ih (z d)
      exact chosenBaseUniformizerPowSubmodule_antitone
        (K := K) (L := L) (chosenNormalBasisIntegerLattice K L)
        (Nat.le_add_right n d) (hz d)

omit [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)] in

/-- The quotient of two partial products is controlled by the filtration
level at the earlier index.  This is the exact tail recurrence used in both
`H⁰` and `H⁻¹` correction arguments. -/
theorem chosenNormalBasisPrincipalUnitCorrectionProduct_div_mem
    {n : Nat}
    (hmul : ∀ k : Nat, n ≤ k →
      ∀ u : 𝒪[L]ˣ, u ∈ chosenNormalBasisPrincipalUnitSet K L k →
        ∀ v : 𝒪[L]ˣ, v ∈ chosenNormalBasisPrincipalUnitSet K L k →
          u * v ∈ chosenNormalBasisPrincipalUnitSet K L k)
    (z : Nat → 𝒪[L]ˣ)
    (hz : ∀ i : Nat, z i ∈ chosenNormalBasisPrincipalUnitSet K L (n + i))
    (m d : Nat) :
    chosenNormalBasisPrincipalUnitCorrectionProduct (L := L) z (m + d) /
        chosenNormalBasisPrincipalUnitCorrectionProduct (L := L) z m ∈
      chosenNormalBasisPrincipalUnitSet K L (n + m) := by
  induction d with
  | zero => simp
  | succ d ih =>
      have hprod :
          chosenNormalBasisPrincipalUnitCorrectionProduct (L := L) z (m + (d + 1)) =
            chosenNormalBasisPrincipalUnitCorrectionProduct (L := L) z (m + d) *
              z (m + d) := by
        rw [Nat.add_succ]
        rfl
      rw [hprod]
      have hzlevel : z (m + d) ∈ chosenNormalBasisPrincipalUnitSet K L (n + m) :=
        chosenBaseUniformizerPowSubmodule_antitone
          (K := K) (L := L) (chosenNormalBasisIntegerLattice K L)
          (Nat.add_le_add_left (Nat.le_add_right m d) n) (hz (m + d))
      have hEq :
          chosenNormalBasisPrincipalUnitCorrectionProduct (L := L) z (m + d) *
                z (m + d) /
              chosenNormalBasisPrincipalUnitCorrectionProduct (L := L) z m =
            (chosenNormalBasisPrincipalUnitCorrectionProduct (L := L) z (m + d) /
                chosenNormalBasisPrincipalUnitCorrectionProduct (L := L) z m) *
              z (m + d) := by
        simp [div_eq_mul_inv, mul_assoc, mul_comm]
      rw [hEq]
      exact hmul (n + m) (Nat.le_add_right n m) _ ih _ hzlevel

/-- Completeness of `𝒪_L` gives a unit-valued limit for the normal-basis
partial products once the lattice sequence has been embedded in
`U_L^(i+1)`. -/
theorem exists_tendsto_chosenNormalBasisPrincipalUnitCorrectionProduct_principalUnit
    [UniformSpace L] [IsUniformAddGroup L] [IsNonarchimedeanLocalField L]
    {b n : Nat}
    (hb : chosenBaseUniformizerPowSubmodule K L b
        (chosenNormalBasisIntegerLattice K L) ≤
      integerRingFieldSubmodule K L)
    (hbn : b + 1 ≤ n) (z : Nat → 𝒪[L]ˣ)
    (hz : ∀ i : Nat, z i ∈ chosenNormalBasisPrincipalUnitSet K L (n + i)) :
    ∃ x : principalUnits L 1,
      Tendsto
        (fun d : Nat =>
          ((chosenNormalBasisPrincipalUnitCorrectionProduct (L := L) z d : 𝒪[L]ˣ) :
            𝒪[L]))
        atTop (nhds (((x : principalUnits L 1) : 𝒪[L]ˣ) : 𝒪[L])) := by
  let zU : ∀ i : Nat, principalUnits L (1 + i) :=
    chosenNormalBasisPrincipalUnitSequenceAsPrincipalUnits K L hb hbn z hz
  rcases exists_tendsto_principalUnitsCorrectionProduct_principalUnit
      L 1 (by rfl) zU with ⟨x, hx⟩
  refine ⟨x, hx.congr' (Eventually.of_forall ?_)⟩
  intro d
  exact congrArg (fun q : 𝒪[L]ˣ => (q : 𝒪[L]))
    (chosenNormalBasisPrincipalUnitCorrectionProduct_eq_principalUnitsCorrectionProduct
      (K := K) (L := L) hb hbn z hz d).symm

omit [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)] in

/-- A unit-valued limit of partial products remains in the initial
normal-basis filtration level whenever that lattice is closed. -/
theorem chosenNormalBasisPrincipalUnitCorrectionProduct_limit_mem
    [UniformSpace L] [IsUniformAddGroup L] [IsNonarchimedeanLocalField L]
    {n : Nat}
    (hclosed : IsClosed
      ((chosenBaseUniformizerPowSubmodule K L n
        (chosenNormalBasisIntegerLattice K L) : Set L)))
    (hmul : ∀ u : 𝒪[L]ˣ, u ∈ chosenNormalBasisPrincipalUnitSet K L n →
      ∀ v : 𝒪[L]ˣ, v ∈ chosenNormalBasisPrincipalUnitSet K L n →
        u * v ∈ chosenNormalBasisPrincipalUnitSet K L n)
    (z : Nat → 𝒪[L]ˣ)
    (hz : ∀ i : Nat, z i ∈ chosenNormalBasisPrincipalUnitSet K L (n + i))
    (x : 𝒪[L]ˣ)
    (hx : Tendsto
      (fun d : Nat =>
        ((chosenNormalBasisPrincipalUnitCorrectionProduct (L := L) z d : 𝒪[L]ˣ) :
          𝒪[L]))
      atTop (nhds ((x : 𝒪[L]ˣ) : 𝒪[L]))) :
    x ∈ chosenNormalBasisPrincipalUnitSet K L n := by
  have hxL : Tendsto
      (fun d : Nat =>
        (((chosenNormalBasisPrincipalUnitCorrectionProduct (L := L) z d : 𝒪[L]ˣ) :
          𝒪[L]) : L))
      atTop (nhds ((((x : 𝒪[L]ˣ) : 𝒪[L])) : L)) :=
    (continuous_subtype_val.tendsto ((x : 𝒪[L]ˣ) : 𝒪[L])).comp hx
  have hsub : Tendsto
      (fun d : Nat =>
        (((((chosenNormalBasisPrincipalUnitCorrectionProduct (L := L) z d : 𝒪[L]ˣ) :
          𝒪[L]) - 1 : 𝒪[L]) : L)))
      atTop (nhds (((((x : 𝒪[L]ˣ) : 𝒪[L]) - 1 : 𝒪[L]) : L))) := by
    simpa using hxL.sub (tendsto_const_nhds (x := (1 : L)))
  rw [mem_chosenNormalBasisPrincipalUnitSet_iff]
  exact submodule_mem_of_tendsto_of_forall_mem_of_closed
    (K := K) (L := L) hclosed hsub
    (fun d => chosenNormalBasisPrincipalUnitCorrectionProduct_mem
      (K := K) (L := L) hmul z hz d)

/-- Infinite-product boundary for the local class-field axiom: for all sufficiently large
`n`, every sequence `z_i ∈ V^(n+i)` has partial products converging to an
actual unit of `V^n`. -/
theorem exists_tendsto_chosenNormalBasisPrincipalUnitCorrectionProduct
    [UniformSpace L] [IsUniformAddGroup L] [IsNonarchimedeanLocalField L]
    [Module.Finite 𝒪[K] 𝒪[L]] :
    ∃ c : Nat, ∀ n : Nat, c ≤ n →
      ∀ z : Nat → 𝒪[L]ˣ,
        (∀ i : Nat, z i ∈ chosenNormalBasisPrincipalUnitSet K L (n + i)) →
          ∃ x : 𝒪[L]ˣ,
            Tendsto
                (fun d : Nat =>
                  ((chosenNormalBasisPrincipalUnitCorrectionProduct (L := L) z d :
                    𝒪[L]ˣ) : 𝒪[L]))
                atTop (nhds ((x : 𝒪[L]ˣ) : 𝒪[L])) ∧
              x ∈ chosenNormalBasisPrincipalUnitSet K L n := by
  rcases exists_chosenBaseUniformizerPow_chosenNormalBasisIntegerLattice_le_integerRingFieldSubmodule
      (K := K) (L := L) with ⟨b, hb⟩
  rcases exists_chosenBaseUniformizerPow_chosenNormalBasisIntegerLattice_mul_mul_mem_self
      (K := K) (L := L) with ⟨cMul, hcMul⟩
  rcases exists_chosenBaseUniformizerPow_chosenNormalBasisIntegerLattice_isClosed
      (K := K) (L := L) with ⟨cClosed, hcClosed⟩
  refine ⟨max (b + 1) (max cMul cClosed), ?_⟩
  intro n hn z hz
  have hbn : b + 1 ≤ n :=
    le_trans (le_max_left (b + 1) (max cMul cClosed)) hn
  have hrest : max cMul cClosed ≤ max (b + 1) (max cMul cClosed) :=
    le_max_right (b + 1) (max cMul cClosed)
  have hcMuln : cMul ≤ n :=
    le_trans (le_trans (le_max_left cMul cClosed) hrest) hn
  have hcClosedn : cClosed ≤ n :=
    le_trans (le_trans (le_max_right cMul cClosed) hrest) hn
  let hmulLattice := hcMul n hcMuln
  have hmul : ∀ u : 𝒪[L]ˣ, u ∈ chosenNormalBasisPrincipalUnitSet K L n →
      ∀ v : 𝒪[L]ˣ, v ∈ chosenNormalBasisPrincipalUnitSet K L n →
        u * v ∈ chosenNormalBasisPrincipalUnitSet K L n := by
    intro u hu v hv
    exact chosenNormalBasisPrincipalUnitSet_mul_mem
      (K := K) (L := L) hmulLattice hu hv
  rcases exists_tendsto_chosenNormalBasisPrincipalUnitCorrectionProduct_principalUnit
      (K := K) (L := L) hb hbn z hz with ⟨x, hx⟩
  let xu : 𝒪[L]ˣ := (x : principalUnits L 1)
  refine ⟨xu, ?_, ?_⟩
  · exact hx
  · exact chosenNormalBasisPrincipalUnitCorrectionProduct_limit_mem
      (K := K) (L := L) (hcClosed n hcClosedn) hmul z hz xu hx

end
end LocalClassFieldTheory
