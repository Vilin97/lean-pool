/-
Copyright (c) 2026 Guanghao Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Guanghao Li
-/
module

public import LeanPool.RiemannRochFunctionFields.Genus.Ramification
public import LeanPool.RiemannRochFunctionFields.EllipticCurve.Dedekind
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Convert
import Mathlib.Tactic.ByContra
import Mathlib.Algebra.Polynomial.Degree.IsMonicOfDegree

/-!
# The unique place at infinity of a Weierstrass function field

For the Weierstrass equation, put `t = x⁻¹` and `z = y t²`.  The transformed equation is
monic in `z`, so `z` belongs to the integral closure of the valuation ring at infinity.  Modulo
any prime above infinity it first gives `z = 0`, and then `t ∈ P²`.  Thus every such prime has
ramification index two.  The fundamental ramification–inertia identity for the quadratic
extension then proves that the prime is unique and has inertia degree one.
-/

@[expose] public section

open FunctionField
open FunctionField.Chart
open Polynomial
open scoped Polynomial RatFunc

namespace WeierstrassCurve.Affine.Chart

noncomputable section

variable {k : Type*} [Field k] (W : WeierstrassCurve.Affine k) [W.IsElliptic]
variable (K : Type*) [Field K] [Algebra W.CoordinateRing K]
  [IsFractionRing W.CoordinateRing K]
variable [Algebra k[X] K] [IsScalarTower k[X] W.CoordinateRing K]
  [Algebra k⟮X⟯ K] [IsScalarTower k[X] k⟮X⟯ K]
  [_root_.FunctionField k K] [Algebra.IsSeparable k⟮X⟯ K]

/-- The canonical constant-field algebra structure used locally in the infinity chart. -/
local instance instAlgebraConstants : Algebra k K := FunctionField.algebraConstants k K
local instance instConstantsTower : IsScalarTower k k[X] K :=
  FunctionField.algebraConstants_isScalarTower k K
local instance instCoordinateConstantsTower : IsScalarTower k W.CoordinateRing K :=
  IsScalarTower.of_algebraMap_eq fun c => by
    rw [IsScalarTower.algebraMap_apply k k[X] K,
      IsScalarTower.algebraMap_apply k k[X] W.CoordinateRing,
      ← IsScalarTower.algebraMap_apply k[X] W.CoordinateRing K]

local notation "A∞" => inftyValuationSubring k
local notation "S∞" => infiniteIntegers k K

local instance instFaithfulInfinity : FaithfulSMul A∞ S∞ :=
  FaithfulSMul.of_field_isFractionRing A∞ S∞ k⟮X⟯ K

local instance instNoZeroSMulDivisorsInfinity : NoZeroSMulDivisors A∞ S∞ := ⟨by
  intro c x h
  rw [Algebra.smul_def] at h
  rcases eq_zero_or_eq_zero_of_mul_eq_zero h with hc | hx
  · exact Or.inl ((faithfulSMul_iff_algebraMap_injective A∞ S∞).mp inferInstance
      (by simpa using hc))
  · exact Or.inr hx
⟩

local instance instInfinityConstantsTower : IsScalarTower k A∞ K :=
  IsScalarTower.of_algebraMap_eq fun c => by
    change algebraMap k K c = algebraMap k⟮X⟯ K (RatFunc.C c)
    rw [IsScalarTower.algebraMap_apply k k[X] K,
      IsScalarTower.algebraMap_apply k[X] k⟮X⟯ K]
    rfl

omit [WeierstrassCurve.IsElliptic W] [IsFractionRing W.CoordinateRing K] [_root_.FunctionField k K]
  [Algebra.IsSeparable k⟮X⟯ K] in
lemma xCoord_eq_XK :
    algebraMap W.CoordinateRing K (CoordinateRing.mk W (Polynomial.C Polynomial.X)) =
      XK k K := by
  have hx : CoordinateRing.mk W (Polynomial.C Polynomial.X) =
      algebraMap k[X] W.CoordinateRing Polynomial.X := rfl
  rw [hx, ← IsScalarTower.algebraMap_apply k[X] W.CoordinateRing K]
  change algebraMap k[X] K Polynomial.X = XK k K
  rw [IsScalarTower.algebraMap_apply k[X] k⟮X⟯ K]
  exact congrArg (algebraMap k⟮X⟯ K) (RatFunc.algebraMap_X (K := k))

omit [WeierstrassCurve.IsElliptic W] [IsFractionRing W.CoordinateRing K] [_root_.FunctionField k K]
  [Algebra.IsSeparable k⟮X⟯ K] in
lemma yCoord_equation :
    (W⁄K).Equation (XK k K) (W.yCoord K) := by
  have h := (coordinate_equation W).map (algebraMap W.CoordinateRing K)
  convert h using 1
  · ext <;> simp only [WeierstrassCurve.baseChange, WeierstrassCurve.map]
    all_goals exact IsScalarTower.algebraMap_apply k W.CoordinateRing K _
  · exact (xCoord_eq_XK W K).symm
  · rfl

/-- The integral infinity-chart coordinate `z = y t²`. -/
noncomputable def infinityZ : K := W.yCoord K * (tK k K) ^ 2

omit [WeierstrassCurve.IsElliptic W] [IsFractionRing W.CoordinateRing K] [_root_.FunctionField k K]
  [Algebra.IsSeparable k⟮X⟯ K] in
lemma infinityZ_equation :
    (infinityZ W K) ^ 2 +
        (algebraMap k K W.a₁ * tK k K + algebraMap k K W.a₃ * (tK k K) ^ 2) *
          infinityZ W K -
      (tK k K + algebraMap k K W.a₂ * (tK k K) ^ 2 +
        algebraMap k K W.a₄ * (tK k K) ^ 3 +
        algebraMap k K W.a₆ * (tK k K) ^ 4) = 0 := by
  have heq := (W⁄K).equation_iff (XK k K) (W.yCoord K) |>.mp
    (yCoord_equation W K)
  change W.yCoord K ^ 2 + algebraMap k K W.a₁ * XK k K * W.yCoord K +
      algebraMap k K W.a₃ * W.yCoord K =
    XK k K ^ 3 + algebraMap k K W.a₂ * XK k K ^ 2 +
      algebraMap k K W.a₄ * XK k K + algebraMap k K W.a₆ at heq
  have hxt : XK k K * tK k K = 1 := XK_mul_tK k K
  dsimp [infinityZ]
  linear_combination (tK k K) ^ 4 * heq +
    (-(algebraMap k K W.a₁) * W.yCoord K * (tK k K) ^ 3 +
      tK k K * ((XK k K * tK k K) ^ 2 + XK k K * tK k K + 1) +
      algebraMap k K W.a₂ * (tK k K) ^ 2 * (XK k K * tK k K + 1) +
      algebraMap k K W.a₄ * (tK k K) ^ 3) * hxt

omit [WeierstrassCurve.IsElliptic W] [IsFractionRing W.CoordinateRing K] [_root_.FunctionField k K]
  [Algebra.IsSeparable k⟮X⟯ K] in
lemma infinityZ_isIntegral : IsIntegral A∞ (infinityZ W K) := by
  let t : A∞ := tA k
  let c : k →+* A∞ := algebraMap k A∞
  let p : A∞[X] :=
    X ^ 2 + C (c W.a₁ * t + c W.a₃ * t ^ 2) * X -
      C (t + c W.a₂ * t ^ 2 + c W.a₄ * t ^ 3 + c W.a₆ * t ^ 4)
  refine ⟨p, ?_, ?_⟩
  · dsimp [p]
    simpa only [sub_eq_add_neg, ← Polynomial.C_neg] using
      (isMonicOfDegree_add_add_two
        (c W.a₁ * t + c W.a₃ * t ^ 2)
        (-(t + c W.a₂ * t ^ 2 + c W.a₄ * t ^ 3 + c W.a₆ * t ^ 4))).monic
  · simp only [p, eval₂_add, eval₂_sub, eval₂_pow, eval₂_X, eval₂_mul, eval₂_C]
    dsimp [t, c]
    have htmap : algebraMap A∞ K (tA k) = tK k K := rfl
    simp only [map_add, map_mul, map_pow, htmap]
    rw [← IsScalarTower.algebraMap_apply k A∞ K W.a₁,
      ← IsScalarTower.algebraMap_apply k A∞ K W.a₃,
      ← IsScalarTower.algebraMap_apply k A∞ K W.a₂,
      ← IsScalarTower.algebraMap_apply k A∞ K W.a₄,
      ← IsScalarTower.algebraMap_apply k A∞ K W.a₆]
    exact infinityZ_equation W K

/-- The infinity-chart coordinate `z` as an element of the integral closure at infinity. -/
noncomputable def infinityZInt : S∞ :=
  ⟨infinityZ W K, (mem_integralClosure_iff (R := A∞) (A := K)).2
    (infinityZ_isIntegral W K)⟩

/-- The local parameter `t = X⁻¹` in the integral closure at infinity. -/
noncomputable def infinityTInt : S∞ := algebraMap A∞ S∞ (tA k)

omit [WeierstrassCurve.IsElliptic W] [IsFractionRing W.CoordinateRing K] [_root_.FunctionField k K]
  [Algebra.IsSeparable k⟮X⟯ K] in
lemma infinityZInt_equation :
    let z := infinityZInt W K
    let t := infinityTInt (k := k) K
    let c : k →+* S∞ := (algebraMap A∞ S∞).comp (algebraMap k A∞)
    z ^ 2 + (c W.a₁ * t + c W.a₃ * t ^ 2) * z -
      (t + c W.a₂ * t ^ 2 + c W.a₄ * t ^ 3 + c W.a₆ * t ^ 4) = 0 := by
  dsimp
  apply Subtype.ext
  change (infinityZ W K) ^ 2 +
      (algebraMap A∞ K (algebraMap k A∞ W.a₁) * algebraMap A∞ K (tA k) +
        algebraMap A∞ K (algebraMap k A∞ W.a₃) * (algebraMap A∞ K (tA k)) ^ 2) *
        infinityZ W K -
    (algebraMap A∞ K (tA k) +
      algebraMap A∞ K (algebraMap k A∞ W.a₂) * (algebraMap A∞ K (tA k)) ^ 2 +
      algebraMap A∞ K (algebraMap k A∞ W.a₄) * (algebraMap A∞ K (tA k)) ^ 3 +
      algebraMap A∞ K (algebraMap k A∞ W.a₆) * (algebraMap A∞ K (tA k)) ^ 4) = 0
  have htmap : algebraMap A∞ K (tA k) = tK k K := rfl
  rw [htmap,
    ← IsScalarTower.algebraMap_apply k A∞ K W.a₁,
    ← IsScalarTower.algebraMap_apply k A∞ K W.a₃,
    ← IsScalarTower.algebraMap_apply k A∞ K W.a₂,
    ← IsScalarTower.algebraMap_apply k A∞ K W.a₄,
    ← IsScalarTower.algebraMap_apply k A∞ K W.a₆]
  exact infinityZ_equation W K

include W in
omit [WeierstrassCurve.IsElliptic W] [IsFractionRing W.CoordinateRing K] in
lemma infinity_map_maximalIdeal_le_sq
    (v : IsDedekindDomain.HeightOneSpectrum S∞) :
    Ideal.map (algebraMap A∞ S∞) (IsLocalRing.maximalIdeal A∞) ≤ v.asIdeal ^ 2 := by
  let P := v.asIdeal
  let z := infinityZInt W K
  let t := infinityTInt (k := k) K
  let c : k →+* S∞ := (algebraMap A∞ S∞).comp (algebraMap k A∞)
  have hunder : P.under A∞ = IsLocalRing.maximalIdeal A∞ :=
    IsLocalRing.eq_maximalIdeal (Ideal.IsMaximal.under A∞ P)
  have hmap : Ideal.map (algebraMap A∞ S∞) (IsLocalRing.maximalIdeal A∞) ≤ P := by
    rw [← hunder]
    exact Ideal.map_comap_le
  have htA : tA k ∈ IsLocalRing.maximalIdeal A∞ := by
    rw [maximalIdeal_infty_eq_span_t k]
    exact Ideal.mem_span_singleton_self (tA k)
  have ht : t ∈ P := hmap (Ideal.mem_map_of_mem (algebraMap A∞ S∞) htA)
  have hBt : c W.a₁ * t + c W.a₃ * t ^ 2 ∈ P := by
    rw [show c W.a₁ * t + c W.a₃ * t ^ 2 = (c W.a₁ + c W.a₃ * t) * t by ring]
    exact P.mul_mem_left _ ht
  have hR : t + c W.a₂ * t ^ 2 + c W.a₄ * t ^ 3 + c W.a₆ * t ^ 4 ∈ P := by
    rw [show t + c W.a₂ * t ^ 2 + c W.a₄ * t ^ 3 + c W.a₆ * t ^ 4 =
      (1 + c W.a₂ * t + c W.a₄ * t ^ 2 + c W.a₆ * t ^ 3) * t by ring]
    exact P.mul_mem_left _ ht
  have heq := infinityZInt_equation W K
  dsimp only at heq
  have hz2 : z ^ 2 ∈ P := by
    rw [show z ^ 2 =
      (t + c W.a₂ * t ^ 2 + c W.a₄ * t ^ 3 + c W.a₆ * t ^ 4) -
        (c W.a₁ * t + c W.a₃ * t ^ 2) * z by linear_combination heq]
    exact P.sub_mem hR (by simpa [mul_comm] using P.mul_mem_left z hBt)
  have hz : z ∈ P := by
    have hzz : z * z ∈ P := by simpa [pow_two] using hz2
    exact (v.isPrime.mem_or_mem hzz).elim id id
  have ht2 : t ∈ P ^ 2 := by
    rw [pow_two]
    have hzz : z ^ 2 ∈ P * P := by
      simpa [pow_two] using Ideal.mul_mem_mul hz hz
    have hBz : (c W.a₁ * t + c W.a₃ * t ^ 2) * z ∈ P * P :=
      Ideal.mul_mem_mul hBt hz
    have hhigh : c W.a₂ * t ^ 2 + c W.a₄ * t ^ 3 + c W.a₆ * t ^ 4 ∈ P * P := by
      rw [show c W.a₂ * t ^ 2 + c W.a₄ * t ^ 3 + c W.a₆ * t ^ 4 =
        (c W.a₂ + c W.a₄ * t + c W.a₆ * t ^ 2) * (t * t) by ring]
      exact (P * P).mul_mem_left _ (Ideal.mul_mem_mul ht ht)
    rw [show t = z ^ 2 + (c W.a₁ * t + c W.a₃ * t ^ 2) * z -
      (c W.a₂ * t ^ 2 + c W.a₄ * t ^ 3 + c W.a₆ * t ^ 4) by
        linear_combination -heq]
    exact (P * P).sub_mem ((P * P).add_mem hzz hBz) hhigh
  rw [maximalIdeal_infty_eq_span_t k, Ideal.map_span, Set.image_singleton, Ideal.span_le]
  rintro _ rfl
  exact ht2

include W in
omit [WeierstrassCurve.IsElliptic W] in
lemma infinity_ramificationIdx_eq_two
    (v : IsDedekindDomain.HeightOneSpectrum S∞) :
    (IsLocalRing.maximalIdeal A∞).ramificationIdx' v.asIdeal = 2 := by
  let p := IsLocalRing.maximalIdeal A∞
  let P := v.asIdeal
  have hle2 : Ideal.map (algebraMap A∞ S∞) p ≤ P ^ 2 :=
    infinity_map_maximalIdeal_le_sq W K v
  have hpP : Ideal.map (algebraMap A∞ S∞) p ≤ P :=
    hle2.trans (Ideal.pow_le_self (by omega))
  have hne1 : p.ramificationIdx' P ≠ 1 :=
    (Ideal.ramificationIdx'_ne_one_iff hpP).2 hle2
  have hp0 : p ≠ ⊥ :=
    Ring.ne_bot_of_isMaximal_of_not_isField (IsLocalRing.maximalIdeal.isMaximal A∞)
      (IsDiscreteValuationRing.not_isField A∞)
  have hunder : P.under A∞ = p :=
    IsLocalRing.eq_maximalIdeal (Ideal.IsMaximal.under A∞ P)
  let : P.LiesOver p := ⟨hunder.symm⟩
  have hne0 : p.ramificationIdx' P ≠ 0 :=
    Ideal.IsDedekindDomain.ramificationIdx'_ne_zero_of_liesOver (S := S∞) P hp0
  have hle : p.ramificationIdx' P ≤ Module.finrank k⟮X⟯ K :=
    Ideal.ramificationIdx'_le_finrank (S := S∞) k⟮X⟯ K hp0 P
  rw [W.finrank_ratFunc_eq_two K] at hle
  change p.ramificationIdx' P = 2
  omega

include W in
omit [WeierstrassCurve.IsElliptic W] in
lemma infinity_sum_ramification_inertia :
    let p := IsLocalRing.maximalIdeal A∞
    ∑ P ∈ IsDedekindDomain.primesOverFinset p S∞,
      p.ramificationIdx' P * p.inertiaDeg' P = 2 := by
  dsimp
  have hp0 : IsLocalRing.maximalIdeal A∞ ≠ ⊥ :=
    Ring.ne_bot_of_isMaximal_of_not_isField (IsLocalRing.maximalIdeal.isMaximal A∞)
      (IsDiscreteValuationRing.not_isField A∞)
  rw [Ideal.sum_ramificationIdx'_mul_inertiaDeg' (S := S∞) k⟮X⟯ K hp0,
    W.finrank_ratFunc_eq_two K]

include W in
omit [WeierstrassCurve.IsElliptic W] in
lemma infinity_inertiaDeg_eq_one
    (v : IsDedekindDomain.HeightOneSpectrum S∞) :
    (IsLocalRing.maximalIdeal A∞).inertiaDeg' v.asIdeal = 1 := by
  let p := IsLocalRing.maximalIdeal A∞
  let P := v.asIdeal
  have hp0 : p ≠ ⊥ :=
    Ring.ne_bot_of_isMaximal_of_not_isField (IsLocalRing.maximalIdeal.isMaximal A∞)
      (IsDiscreteValuationRing.not_isField A∞)
  have hunder : P.under A∞ = p :=
    IsLocalRing.eq_maximalIdeal (Ideal.IsMaximal.under A∞ P)
  let : P.LiesOver p := ⟨hunder.symm⟩
  have hP : P ∈ IsDedekindDomain.primesOverFinset p S∞ :=
    (IsDedekindDomain.mem_primesOverFinset_iff hp0 (P := P)).2
      ⟨v.isPrime, (show P.LiesOver p from inferInstance)⟩
  let g : Ideal S∞ → ℕ := fun Q => p.ramificationIdx' Q * p.inertiaDeg' Q
  have hsum : (∑ Q ∈ IsDedekindDomain.primesOverFinset p S∞, g Q) = 2 := by
    simpa [g] using infinity_sum_ramification_inertia W K
  have hterm : g P ≤ 2 := by
    rw [← hsum, ← Finset.add_sum_erase _ _ hP]
    omega
  have he : p.ramificationIdx' P = 2 := infinity_ramificationIdx_eq_two W K v
  have hfpos : 0 < p.inertiaDeg' P := Ideal.inertiaDeg'_pos p P
  dsimp [g] at hterm
  rw [he] at hterm
  change p.inertiaDeg' P = 1
  omega

include W in
omit [WeierstrassCurve.IsElliptic W] in
lemma infinity_heightOne_unique
    (v w : IsDedekindDomain.HeightOneSpectrum S∞) : v = w := by
  apply IsDedekindDomain.HeightOneSpectrum.ext
  let p := IsLocalRing.maximalIdeal A∞
  let P := v.asIdeal
  let Q := w.asIdeal
  have hp0 : p ≠ ⊥ :=
    Ring.ne_bot_of_isMaximal_of_not_isField (IsLocalRing.maximalIdeal.isMaximal A∞)
      (IsDiscreteValuationRing.not_isField A∞)
  have hPunder : P.under A∞ = p :=
    IsLocalRing.eq_maximalIdeal (Ideal.IsMaximal.under A∞ P)
  have hQunder : Q.under A∞ = p :=
    IsLocalRing.eq_maximalIdeal (Ideal.IsMaximal.under A∞ Q)
  let : P.LiesOver p := ⟨hPunder.symm⟩
  have hP : P ∈ IsDedekindDomain.primesOverFinset p S∞ :=
    (IsDedekindDomain.mem_primesOverFinset_iff hp0 (P := P)).2
      ⟨v.isPrime, (show P.LiesOver p from inferInstance)⟩
  let : Q.LiesOver p := ⟨hQunder.symm⟩
  have hQ : Q ∈ IsDedekindDomain.primesOverFinset p S∞ :=
    (IsDedekindDomain.mem_primesOverFinset_iff hp0 (P := Q)).2
      ⟨w.isPrime, (show Q.LiesOver p from inferInstance)⟩
  by_contra hne
  let g : Ideal S∞ → ℕ := fun R => p.ramificationIdx' R * p.inertiaDeg' R
  let F := IsDedekindDomain.primesOverFinset p S∞
  have hsum : F.sum g = 2 := by
    simpa [F, g] using infinity_sum_ramification_inertia W K
  have hQerase : Q ∈ F.erase P := Finset.mem_erase.2 ⟨Ne.symm hne, hQ⟩
  have hQle : g Q ≤ (F.erase P).sum g :=
    Finset.single_le_sum (fun _ _ => Nat.zero_le _) hQerase
  have hdecomp : (F.erase P).sum g + g P = 2 := by
    calc
      (F.erase P).sum g + g P = F.sum g := Finset.sum_erase_add F g hP
      _ = 2 := hsum
  have heP : p.ramificationIdx' P = 2 := infinity_ramificationIdx_eq_two W K v
  have heQ : p.ramificationIdx' Q = 2 := infinity_ramificationIdx_eq_two W K w
  have hfP : 0 < p.inertiaDeg' P := Ideal.inertiaDeg'_pos p P
  have hfQ : 0 < p.inertiaDeg' Q := Ideal.inertiaDeg'_pos p Q
  dsimp [g] at hQle hdecomp
  rw [heP] at hdecomp
  rw [heQ] at hQle
  omega

/-- The unique height-one prime in the integral closure of the infinity valuation ring. -/
noncomputable def infinityHeightOne : IsDedekindDomain.HeightOneSpectrum S∞ := by
  let p := IsLocalRing.maximalIdeal A∞
  have hp0 : p ≠ ⊥ :=
    Ring.ne_bot_of_isMaximal_of_not_isField (IsLocalRing.maximalIdeal.isMaximal A∞)
      (IsDiscreteValuationRing.not_isField A∞)
  let hex := Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := S∞) p
  let P : Ideal S∞ := Classical.choose hex
  have hP : P.IsMaximal ∧ P.LiesOver p := Classical.choose_spec hex
  letI : P.LiesOver p := hP.2
  exact ⟨P, hP.1.isPrime, Ideal.ne_bot_of_liesOver_of_ne_bot hp0 P⟩

/-- The unique place of the elliptic function field above the point at infinity. -/
noncomputable def infinityPlace : PlaceA k K := Sum.inr (infinityHeightOne (k := k) K)

include W in
omit [WeierstrassCurve.IsElliptic W] in
theorem infinityPlace_deg_one : placeDegree k K (infinityPlace K) = 1 := by
  rw [infinityPlace, placeDegree_infinite_eq_inertiaDeg]
  have hunder : (infinityHeightOne (k := k) K).asIdeal.under A∞ =
      IsLocalRing.maximalIdeal A∞ :=
    IsLocalRing.eq_maximalIdeal
      (Ideal.IsMaximal.under A∞ (infinityHeightOne (k := k) K).asIdeal)
  rw [hunder]
  exact infinity_inertiaDeg_eq_one W K (infinityHeightOne (k := k) K)

end

end WeierstrassCurve.Affine.Chart
