/-
Copyright (c) 2026 Arseniy Akopyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arseniy Akopyan
-/
module


public import Mathlib.Geometry.Manifold.Instances.Sphere

public import LeanPool.NandakumarRamanaRao.NRR.OddSphereDegree.AlgebraicTopology.SubChainSubspaceBridge
public import LeanPool.NandakumarRamanaRao.NRR.OddSphereDegree.SphereTopHomology
/-!
# The Mayer–Vietoris recursive step for sphere homology

For `n ≥ 1` we prove `Hₙ₊₁(Sⁿ⁺¹; ℤ) ≅ Hₙ(Sⁿ; ℤ)` (`sphereTopHomologyStepMV`),
the recursive `step` of `SphereSuspensionTower`.

Cover `Sⁿ⁺¹` by the two punctured spheres `U = Sⁿ⁺¹ \ {north}` and
`V = Sⁿ⁺¹ \ {south}`. Both are contractible (stereographic projection), so their
positive homology vanishes, and the Mayer–Vietoris connecting isomorphism
(`mvHomologyIsoSucc`) gives `Hₙ₊₁(Sⁿ⁺¹) ≅ Hₙ(U ∩ V)`. The intersection
`U ∩ V` is the equatorial band, homotopy equivalent to `Sⁿ`; the subspace bridge
(`subspaceHomologyIsoℤ`) and homotopy invariance then identify its homology with
`Hₙ(Sⁿ)`.
-/

@[expose] public section

open CategoryTheory AlgebraicTopology Limits Metric
open SphereOddDegree.AffineBarycentricSubdivision

noncomputable section
namespace SphereOddDegree

variable (n : ℕ)

/-- The north pole of `Sⁿ⁺¹` as a unit vector `e₀`. -/
def northVec : EuclideanSpace ℝ (Fin (n + 2)) := PiLp.single 2 0 1

theorem norm_northVec : ‖northVec n‖ = 1 := by
  dsimp [northVec]
  rw [PiLp.norm_single]
  simp

/-- The north pole of `Sⁿ⁺¹`. -/
def northPole : Sphere (n + 1) := ⟨northVec n, by simp [norm_northVec]⟩

/-- The south pole of `Sⁿ⁺¹`, the antipode of the north pole. -/
def southPole : Sphere (n + 1) := ⟨-northVec n, by simp [norm_northVec]⟩

theorem northPole_ne_southPole : northPole n ≠ southPole n := by
  intro h
  apply_fun Subtype.val at h
  simp only [northPole, southPole] at h
  have hv : northVec n = 0 := by
    have h2 : (2 : ℝ) • northVec n = 0 := by rw [two_smul]; nth_rewrite 2 [h]; abel
    rcases smul_eq_zero.mp h2 with h0 | h0
    · norm_num at h0
    · exact h0
  have hnorm := norm_northVec n
  rw [hv, norm_zero] at hnorm
  norm_num at hnorm

/-- The upper punctured sphere `Sⁿ⁺¹ \ {north}`. -/
def upperPunctured : Set (Sphere (n + 1)) := {northPole n}ᶜ

/-- The lower punctured sphere `Sⁿ⁺¹ \ {south}`. -/
def lowerPunctured : Set (Sphere (n + 1)) := {southPole n}ᶜ

theorem isOpen_upperPunctured : IsOpen (upperPunctured n) :=
  isOpen_compl_singleton

theorem isOpen_lowerPunctured : IsOpen (lowerPunctured n) :=
  isOpen_compl_singleton

theorem upper_union_lower : upperPunctured n ∪ lowerPunctured n = Set.univ := by
  rw [upperPunctured, lowerPunctured, ← Set.compl_inter]
  rw [Set.compl_univ_iff, Set.eq_empty_iff_forall_notMem]
  rintro x ⟨hx1, hx2⟩
  rw [Set.mem_singleton_iff] at hx1 hx2
  exact northPole_ne_southPole n (hx1 ▸ hx2)

/-- The equatorial band `Sⁿ⁺¹ \ {north, south}`. -/
def sphereBand : Set (Sphere (n + 1)) := upperPunctured n ∩ lowerPunctured n

/-! ## Contractibility of the punctured spheres -/

instance contractible_upperPunctured : ContractibleSpace (upperPunctured n) := by
  have hv : ‖northVec n‖ = 1 := norm_northVec n
  have hs : (upperPunctured n : Set (Sphere (n + 1))) = (stereographic hv).source := by
    rw [stereographic_source]
    rfl
  have e1 : (upperPunctured n : Type _) ≃ₜ (stereographic hv).source :=
    Homeomorph.setCongr hs
  have e2 : ((stereographic hv).source : Type _) ≃ₜ ((stereographic hv).target : Type _) :=
    (stereographic hv).toHomeomorphSourceTarget
  have e3 : ((stereographic hv).target : Type _) ≃ₜ (↥(ℝ ∙ northVec n)ᗮ) :=
    (Homeomorph.setCongr (stereographic_target hv)).trans (Homeomorph.Set.univ _)
  exact (e1.trans (e2.trans e3)).contractibleSpace

instance contractible_lowerPunctured : ContractibleSpace (lowerPunctured n) := by
  have hv : ‖-northVec n‖ = 1 := by rw [norm_neg, norm_northVec]
  have hs : (lowerPunctured n : Set (Sphere (n + 1))) = (stereographic hv).source := by
    rw [stereographic_source]
    rfl
  have e1 : (lowerPunctured n : Type _) ≃ₜ (stereographic hv).source :=
    Homeomorph.setCongr hs
  have e2 : ((stereographic hv).source : Type _) ≃ₜ ((stereographic hv).target : Type _) :=
    (stereographic hv).toHomeomorphSourceTarget
  have e3 : ((stereographic hv).target : Type _) ≃ₜ (↥(ℝ ∙ -northVec n)ᗮ) :=
    (Homeomorph.setCongr (stereographic_target hv)).trans (Homeomorph.Set.univ _)
  exact (e1.trans (e2.trans e3)).contractibleSpace

/-! ## The equatorial band is homotopy equivalent to `Sⁿ` -/

/-
The equatorial band `Sⁿ⁺¹ \ {north, south}` is homotopy equivalent to `Sⁿ`.
-/
/-! ### Construction of the band ≃ Sⁿ homotopy equivalence -/

/-- The squared norm of the equatorial part (coordinates `1 .. n+1`) of a point of
`Sⁿ⁺¹`. -/
def eqNormSq (x : Sphere (n + 1)) : ℝ := ∑ i : Fin (n + 1), (x.val i.succ) ^ 2

theorem eqNormSq_eq (x : Sphere (n + 1)) : eqNormSq n x = 1 - (x.val 0) ^ 2 := by
  have h_norm_sq : ‖x.val‖^2 = ∑ i : Fin (n + 2), (x.val i)^2 := by
    rw [ EuclideanSpace.norm_eq ];
    rw [ Real.sq_sqrt <| Finset.sum_nonneg fun _ _ => sq_nonneg _, Finset.sum_congr rfl fun _ _
      => by
      rw [ Real.norm_eq_abs, sq_abs ] ];
  simp_all +decide [ Fin.sum_univ_succ, eqNormSq ]

theorem eqNormSq_pos {x : Sphere (n + 1)} (hx : x ∈ sphereBand n) : 0 < eqNormSq n x := by
  contrapose! hx
  have h_zero : ∀ i : Fin (n + 1), x.val i.succ = 0 := by
    intro i
    have h_sq := le_antisymm (le_trans (Finset.single_le_sum (fun a _ => sq_nonneg (x.val
      (Fin.succ a))) (Finset.mem_univ i)) hx) (sq_nonneg _)
    exact sq_eq_zero_iff.mp h_sq
  have h_eq0 : (x.val 0)^2 = 1 := by
    have := eqNormSq_eq n x
    linarith [show 0 ≤ eqNormSq n x from Finset.sum_nonneg fun _ _ => sq_nonneg _]
  have h_eq : x.val = northVec n ∨ x.val = -northVec n := by
    cases sq_eq_one_iff.mp h_eq0 with
    | inl h1 =>
      left
      ext i
      induction i using Fin.inductionOn with
      | zero => exact h1
      | succ j =>
        dsimp [northVec]
        rw [h_zero j, Pi.single_eq_of_ne (Fin.succ_ne_zero j) 1]
    | inr h1 =>
      right
      ext i
      induction i using Fin.inductionOn with
      | zero => exact h1
      | succ j =>
        dsimp [northVec]
        rw [h_zero j, Pi.single_eq_of_ne (Fin.succ_ne_zero j) 1, neg_zero]
  dsimp [sphereBand, upperPunctured, lowerPunctured]
  rcases h_eq with h | h
  · intro hc
    exact hc.1 (Subtype.ext h)
  · intro hc
    exact hc.2 (Subtype.ext h)

/-- The equatorial-projection map underlying `band → Sⁿ`: drop coordinate `0` and
normalize. -/
def fFun (x : Sphere (n + 1)) : EuclideanSpace ℝ (Fin (n + 1)) :=
  (WithLp.equiv 2 (Fin (n + 1) → ℝ)).symm (fun i => x.val i.succ / Real.sqrt (eqNormSq n x))

theorem fFun_mem {x : Sphere (n + 1)} (hx : x ∈ sphereBand n) :
    fFun n x ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1 := by
      simp +decide only [fFun, WithLp.equiv_symm_apply, mem_sphere_iff_norm, sub_zero,
        EuclideanSpace.norm_eq, norm_div, Real.norm_eq_abs, Real.sqrt_eq_one];
      norm_num [ div_pow, Real.sq_sqrt ( show 0 ≤ eqNormSq n x from Finset.sum_nonneg fun _ _ =>
        sq_nonneg _ ) ];
      rw [ ← Finset.sum_div _ _ _, eqNormSq ];
      exact div_self <| ne_of_gt <| eqNormSq_pos n hx

theorem continuous_fFun_band :
    Continuous (fun x : ↥(sphereBand n) => (⟨fFun n x.val, fFun_mem n x.2⟩ : Sphere n)) := by
      refine Continuous.subtype_mk ?_ ?_;
      refine continuous_iff_continuousAt.mpr ?_;
      intro x
      have h_cont : ContinuousAt (fun x : EuclideanSpace ℝ (Fin (n + 2)) => (WithLp.equiv 2 (Fin
        (n + 1) → ℝ)).symm (fun i => x i.succ / Real.sqrt (∑ i : Fin (n + 1), (x i.succ) ^ 2)))
        x.val := by
        refine ContinuousAt.comp (?_ : ContinuousAt (fun x : Fin (n + 1) → ℝ =>
          (WithLp.equiv 2 (Fin (n + 1) → ℝ)).symm x) _) ?_
        · exact Continuous.continuousAt ( by continuity );
        · refine tendsto_pi_nhds.mpr fun i => ContinuousAt.div ?_ ?_ ?_;
          · exact Continuous.continuousAt ( by
              exact continuous_apply _ |> Continuous.comp <| by
                continuity );
          · fun_prop;
          · exact ne_of_gt <| Real.sqrt_pos.mpr <| eqNormSq_pos n x.2;
      exact h_cont.tendsto.comp ( continuous_subtype_val.continuousAt.comp (
        continuous_subtype_val.continuousAt ) )

/-- The continuous map `band → Sⁿ`. -/
def bandToSphere : C(↥(sphereBand n), Sphere n) :=
  ⟨fun x => ⟨fFun n x.val, fFun_mem n x.2⟩, continuous_fFun_band n⟩

/-- The inclusion map underlying `Sⁿ → band`: prepend a `0` coordinate. -/
def gFun (y : Sphere n) : EuclideanSpace ℝ (Fin (n + 2)) :=
  (WithLp.equiv 2 (Fin (n + 2) → ℝ)).symm (Fin.cons 0 (fun i => y.val i))

theorem gFun_mem_sphere (y : Sphere n) :
    gFun n y ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 2))) 1 := by
      simp +decide only [gFun, WithLp.equiv_symm_apply, mem_sphere_iff_norm, sub_zero,
        EuclideanSpace.norm_eq, Real.norm_eq_abs, sq_abs, Real.sqrt_eq_one];
      convert y.2 using 1;
      rw [ mem_sphere_zero_iff_norm, EuclideanSpace.norm_eq ]; norm_num [ Fin.sum_univ_succ ]

theorem gFun_mem_band (y : Sphere n) :
    (⟨gFun n y, gFun_mem_sphere n y⟩ : Sphere (n + 1)) ∈ sphereBand n := by
  constructor <;> intro h
  · have hcoord := congrArg (fun z : Sphere (n + 1) => z.val 0)
      (Set.mem_singleton_iff.mp h)
    simp [northPole, northVec, gFun] at hcoord
  · have hcoord := congrArg (fun z : Sphere (n + 1) => z.val 0)
      (Set.mem_singleton_iff.mp h)
    simp [southPole, northVec, gFun] at hcoord

theorem continuous_gFun :
    Continuous (fun y : Sphere n =>
      (⟨⟨gFun n y, gFun_mem_sphere n y⟩, gFun_mem_band n y⟩ : ↥(sphereBand n))) := by
        refine Continuous.subtype_mk ( Continuous.subtype_mk ?_ ?_ ) ?_;
        -- The function y ↦ Fin.cons 0 (fun i => y.val i) is continuous because it is a
        -- composition of continuous functions.
        have h_cont : Continuous (fun y : Sphere n => Fin.cons 0 (fun i => y.val i) : Sphere n →
          Fin (n + 2) → ℝ) := by
          refine continuous_pi_iff.mpr ?_;
          intro i; induction i using Fin.inductionOn <;> simp_all +decide only [Fin.cons,
            Fin.cases_succ, Fin.cases_zero];
          · exact continuous_const;
          · fun_prop;
        convert h_cont using 1;
        exact iff_of_true ( Continuous.comp ( by continuity ) h_cont ) h_cont

/-- The continuous map `Sⁿ → band`. -/
def sphereToBand : C(Sphere n, ↥(sphereBand n)) :=
  ⟨fun y => ⟨⟨gFun n y, gFun_mem_sphere n y⟩, gFun_mem_band n y⟩, continuous_gFun n⟩

theorem bandToSphere_comp_sphereToBand :
    (bandToSphere n).comp (sphereToBand n) = ContinuousMap.id (Sphere n) := by
      ext i; simp only [bandToSphere, fFun, WithLp.equiv_symm_apply, sphereToBand, gFun,
        ContinuousMap.comp_apply, ContinuousMap.coe_mk, Fin.cons_succ, ContinuousMap.id_apply];
      rw [ eqNormSq_eq ]; norm_num [ Fin.sum_univ_succ ]

/-- The straight-line-on-the-sphere homotopy from `sphereToBand ∘ bandToSphere` to the
identity of the band. -/
def bandHomotopyFun (p : unitInterval × ↥(sphereBand n)) : EuclideanSpace ℝ (Fin (n + 2)) :=
  (1 - (p.1 : ℝ)) • ((sphereToBand n (bandToSphere n p.2)).val.val) + (p.1 : ℝ) • p.2.val.val

theorem bandHomotopyFun_ne_zero (p : unitInterval × ↥(sphereBand n)) :
    bandHomotopyFun n p ≠ 0 := by
      unfold bandHomotopyFun;
      obtain ⟨i, hi⟩ : ∃ i : Fin (n + 1), p.2.val.val i.succ ≠ 0 := by
        have h_pos : 0 < ∑ i : Fin (n + 1), (p.2.val.val i.succ) ^ 2 := by
          exact eqNormSq_pos n p.2.2;
        exact not_forall.mp fun h => h_pos.ne' <| Finset.sum_eq_zero fun i _ => by
          simp +decide [ h i ];
      intro h; have := congr_arg ( fun x => x i.succ ) h; norm_num [ hi, sphereToBand,
        bandToSphere, fFun, gFun ] at this;
      by_cases h : p.1.val = 0 <;> simp_all +decide only [ne_eq, div_eq_mul_inv, mul_comm,
        Set.Icc.coe_eq_zero, sub_zero, one_smul, zero_smul, add_zero, one_mul, zero_mul,
        mul_eq_zero, inv_eq_zero, or_false];
      · exact absurd this ( ne_of_gt ( Real.sqrt_pos.mpr ( eqNormSq_pos n p.2.2 ) ) );
      · exact hi ( by
          nlinarith [ show 0 < ( 1 - p.1.val ) * ( Real.sqrt ( eqNormSq n p.2.val ) ) ⁻¹ +
            p.1.val from by
            exact add_pos_of_nonneg_of_pos ( mul_nonneg ( sub_nonneg.2 <| p.1.2.2 ) <|
              inv_nonneg.2 <| Real.sqrt_nonneg _ ) <| lt_of_le_of_ne ( p.1.2.1 ) <| Ne.symm <| by
              aesop ] )

theorem bandHomotopy_mem_sphere (p : unitInterval × ↥(sphereBand n)) :
    (‖bandHomotopyFun n p‖⁻¹ • bandHomotopyFun n p) ∈
      Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 2))) 1 := by
        simp +decide [  norm_smul, bandHomotopyFun_ne_zero ]

theorem bandHomotopy_mem_band (p : unitInterval × ↥(sphereBand n)) :
    (⟨‖bandHomotopyFun n p‖⁻¹ • bandHomotopyFun n p, bandHomotopy_mem_sphere n p⟩ : Sphere (n + 1))
      ∈ sphereBand n := by
  obtain ⟨i, hi⟩ : ∃ i : Fin (n + 1), p.2.val.val i.succ ≠ 0 := by
    exact not_forall.mp fun h => absurd (eqNormSq_pos n p.2.2) (by simp [h, eqNormSq])
  have h_coord : (‖bandHomotopyFun n p‖⁻¹ • bandHomotopyFun n p) (Fin.succ i) ≠ 0 := by
    have h_ne : bandHomotopyFun n p ≠ 0 := bandHomotopyFun_ne_zero n p
    have h_norm_pos : 0 < ‖bandHomotopyFun n p‖ := norm_pos_iff.mpr h_ne
    have h_inv_pos : 0 < ‖bandHomotopyFun n p‖⁻¹ := inv_pos.mpr h_norm_pos
    intro hc
    have hc' : (bandHomotopyFun n p) (Fin.succ i) = 0 := by
      have : (‖bandHomotopyFun n p‖⁻¹ • bandHomotopyFun n p) (Fin.succ i) = ‖bandHomotopyFun n
        p‖⁻¹ * (bandHomotopyFun n p) (Fin.succ i) := rfl
      rw [this] at hc
      exact mul_eq_zero.mp hc |>.resolve_left h_inv_pos.ne'
    dsimp [bandHomotopyFun, sphereToBand, bandToSphere, fFun, gFun] at hc'
    have : ((1 - (p.1 : ℝ)) * (Real.sqrt (eqNormSq n p.2.val))⁻¹ + (p.1 : ℝ)) * p.2.val.val
      i.succ = 0 := by
      calc ((1 - (p.1 : ℝ)) * (Real.sqrt (eqNormSq n p.2.val))⁻¹ + (p.1 : ℝ)) * p.2.val.val i.succ
        _ = (1 - (p.1 : ℝ)) * (p.2.val.val i.succ / Real.sqrt (eqNormSq n p.2.val)) + (p.1 : ℝ)
          * p.2.val.val i.succ := by
          ring
        _ = 0 := hc'
    have h_coeff_pos : 0 < (1 - (p.1 : ℝ)) * (Real.sqrt (eqNormSq n p.2.val))⁻¹ + (p.1 : ℝ) := by
      by_cases ht : (p.1 : ℝ) = 0
      · rw [ht, sub_zero, one_mul, add_zero]
        exact inv_pos.mpr (Real.sqrt_pos.mpr (eqNormSq_pos n p.2.2))
      · have hp1 : 0 < (p.1 : ℝ) := lt_of_le_of_ne p.1.2.1 (Ne.symm ht)
        have hp2 : 0 ≤ (1 - (p.1 : ℝ)) * (Real.sqrt (eqNormSq n p.2.val))⁻¹ :=
          mul_nonneg (sub_nonneg.mpr p.1.2.2) (inv_nonneg.mpr (Real.sqrt_nonneg _))
        linarith
    have := mul_eq_zero.mp this |>.resolve_left h_coeff_pos.ne'
    exact hi this
  constructor <;> intro h <;> simp only [Set.mem_singleton_iff] at h
  · have h0 := congr_arg (fun z : Sphere (n + 1) => z.val (Fin.succ i)) h
    dsimp [northPole, northVec] at h0
    rw [Pi.single_eq_of_ne (Fin.succ_ne_zero i) 1] at h0
    exact h_coord h0
  · have h0 := congr_arg (fun z : Sphere (n + 1) => z.val (Fin.succ i)) h
    dsimp [southPole, northVec] at h0
    rw [Pi.single_eq_of_ne (Fin.succ_ne_zero i) 1, neg_zero] at h0
    exact h_coord h0

theorem continuous_bandHomotopy :
    Continuous (fun p : unitInterval × ↥(sphereBand n) =>
      (⟨⟨‖bandHomotopyFun n p‖⁻¹ • bandHomotopyFun n p, bandHomotopy_mem_sphere n p⟩,
        bandHomotopy_mem_band n p⟩ : ↥(sphereBand n))) := by
  refine Continuous.subtype_mk (Continuous.subtype_mk ?_ _) _
  have h_fun : Continuous (fun p : unitInterval × ↥(sphereBand n) => bandHomotopyFun n p) := by
    dsimp [bandHomotopyFun]
    refine Continuous.add ?_ ?_
    · refine Continuous.smul (continuous_const.sub (continuous_subtype_val.comp continuous_fst)) ?_
      exact (sphereToBand n).continuous.comp ((bandToSphere n).continuous.comp continuous_snd)
        |>.subtype_val.subtype_val
    · exact (continuous_subtype_val.comp continuous_fst).smul continuous_snd.subtype_val.subtype_val
  have h_inv : Continuous (fun p : unitInterval × ↥(sphereBand n) => ‖bandHomotopyFun n p‖⁻¹) := by
    refine Continuous.inv₀ (Continuous.norm h_fun) ?_
    intro x
    exact norm_ne_zero_iff.mpr (bandHomotopyFun_ne_zero n x)
  exact Continuous.smul h_inv h_fun

theorem bandHomotopy_zero (x : ↥(sphereBand n)) :
    (⟨⟨‖bandHomotopyFun n (0, x)‖⁻¹ • bandHomotopyFun n (0, x), bandHomotopy_mem_sphere n (0, x)⟩,
        bandHomotopy_mem_band n (0, x)⟩ : ↥(sphereBand n))
      = (sphereToBand n).comp (bandToSphere n) x := by
        -- Since $t = 0$, we have $bandHomotopyFun n (0, x) = gfx$ by definition.
        have h_bandHomotopy_zero : bandHomotopyFun n (0, x) = (sphereToBand n (bandToSphere n
          x)).val.val := by
          unfold bandHomotopyFun; norm_num [ sphereToBand, bandToSphere, fFun, gFun ];
        simp +decide [ h_bandHomotopy_zero ]

theorem bandHomotopy_one (x : ↥(sphereBand n)) :
    (⟨⟨‖bandHomotopyFun n (1, x)‖⁻¹ • bandHomotopyFun n (1, x), bandHomotopy_mem_sphere n (1, x)⟩,
        bandHomotopy_mem_band n (1, x)⟩ : ↥(sphereBand n))
      = ContinuousMap.id _ x := by
        norm_num [ bandHomotopyFun ]

/-- The homotopy `sphereToBand ∘ bandToSphere ≃ id`. -/
def bandHomotopy :
    ContinuousMap.Homotopy ((sphereToBand n).comp (bandToSphere n)) (ContinuousMap.id _) where
  toFun p := ⟨⟨‖bandHomotopyFun n p‖⁻¹ • bandHomotopyFun n p, bandHomotopy_mem_sphere n p⟩,
    bandHomotopy_mem_band n p⟩
  continuous_toFun := continuous_bandHomotopy n
  map_zero_left := bandHomotopy_zero n
  map_one_left := bandHomotopy_one n

/-- The equatorial band `Sⁿ⁺¹ \ {north, south}` is homotopy equivalent to `Sⁿ`. -/
def sphereBandHomotopyEquiv : ContinuousMap.HomotopyEquiv (sphereBand n) (Sphere n) where
  toFun := bandToSphere n
  invFun := sphereToBand n
  left_inv := ⟨bandHomotopy n⟩
  right_inv := bandToSphere_comp_sphereToBand n ▸ ContinuousMap.Homotopic.refl _

/-! ## Assembly of the Mayer–Vietoris step -/

/-- The categorical space `Sⁿ⁺¹` realized as a `TopCat` from the library model. -/
abbrev sphereSpace : TopCat.{0} := TopCat.of (Sphere (n + 1))

/-- The upper punctured sphere as an open set of `Sⁿ⁺¹`. -/
def upperOpens : TopologicalSpace.Opens (sphereSpace n) :=
  ⟨upperPunctured n, isOpen_upperPunctured n⟩

/-- The lower punctured sphere as an open set of `Sⁿ⁺¹`. -/
def lowerOpens : TopologicalSpace.Opens (sphereSpace n) :=
  ⟨lowerPunctured n, isOpen_lowerPunctured n⟩

instance contractible_upperOpens :
    ContractibleSpace (upperOpens n : Set (sphereSpace n)) := contractible_upperPunctured n

instance contractible_lowerOpens :
    ContractibleSpace (lowerOpens n : Set (sphereSpace n)) := contractible_lowerPunctured n

theorem upperOpens_sup_lowerOpens : upperOpens n ⊔ lowerOpens n = ⊤ := by
  apply TopologicalSpace.Opens.ext
  simpa [upperOpens, lowerOpens] using upper_union_lower n

/-- The integral homology of the band is isomorphic to `Hₙ(Sⁿ; ℤ)`, via the
subspace bridge and homotopy invariance. -/
def bandHomologyIso :
    (subChainComplex ℤ (sphereSpace n)
      ((upperOpens n : Set (sphereSpace n)) ∩ (lowerOpens n : Set (sphereSpace n)))).homology n ≅
      sphereTopHomologyℤ n :=
  subspaceHomologyIsoℤ (sphereSpace n)
      ((upperOpens n : Set (sphereSpace n)) ∩ (lowerOpens n : Set (sphereSpace n))) n
    ≪≫ singularHomologyℤIsoOfHomotopyEquivSpace n (sphereBandHomotopyEquiv n)
    ≪≫ (sphereModelHomologyIso n n).symm

/-- **The Mayer–Vietoris recursive step.** For `n ≥ 1`,
`Hₙ₊₁(Sⁿ⁺¹; ℤ) ≅ Hₙ(Sⁿ; ℤ)`. -/
def sphereTopHomologyStepMV (hn : 1 ≤ n) :
    sphereTopHomologyℤ (n + 1) ≅ sphereTopHomologyℤ n :=
  sphereModelHomologyIso (n + 1) (n + 1)
    ≪≫ mvHomologyIsoSucc ℤ (upperOpens n) (lowerOpens n) (upperOpens_sup_lowerOpens n) n
        (isZero_subChainComplex_homology_of_contractible _ _ (n + 1) (by omega))
        (isZero_subChainComplex_homology_of_contractible _ _ (n + 1) (by omega))
        (isZero_subChainComplex_homology_of_contractible _ _ n hn)
        (isZero_subChainComplex_homology_of_contractible _ _ n hn)
    ≪≫ bandHomologyIso n

end SphereOddDegree
