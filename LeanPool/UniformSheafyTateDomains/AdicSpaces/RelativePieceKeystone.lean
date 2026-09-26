/-
Copyright (c) 2026 Christopher Birkbeck, Alex Torzewski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Birkbeck, Alex Torzewski
-/
module


/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
public import LeanPool.UniformSheafyTateDomains.AdicSpaces.Wedhorn828
public import LeanPool.UniformSheafyTateDomains.AdicSpaces.LaurentRefinementCore
public import LeanPool.UniformSheafyTateDomains.AdicSpaces.GeometricReduction
public import LeanPool.UniformSheafyTateDomains.AdicSpaces.PresheafIdentification
public import LeanPool.UniformSheafyTateDomains.AdicSpaces.RestrictionFlatness
public import LeanPool.UniformSheafyTateDomains.AdicSpaces.FaithfulLocLift

/-!
# The relative-piece keystone (Wedhorn Prop 8.2 / Prop 8.16) and Prop 8.30 / Cor 8.32

The general-piece base change `𝒪_X(E) ≃+* 𝒪_B(im E)` for rational pieces `E ⊆ D₀`,
`B := 𝒪_X(D₀)` (the G1 stack: `imagePieceDatum`, `genPiece_relative_equiv`,
`relativePiece_equiv`, the canonical-map trackings, and the restriction square),
together with the Prop 8.30 flatness chain and the Cor 8.32 faithful-flatness /
separation consequences (relocated from `Wedhorn828.lean` so they can consume the
keystone: the Remark-7.55 chain `prop_8_30_remark755_chain` reduces to the
whole-space case through it).

Split out of `WedhornCechAcyclicity.lean` (which imports this file) on 2026-06-11
so the import direction `Wedhorn828 → this file → WedhornCechAcyclicity` lets the
flatness chain see the keystone.

## References

* [T. Wedhorn, *Adic Spaces*][wedhorn2019adic], Prop 8.2, Remark 8.4, Prop 8.16,
  Remark 7.55, Prop 8.30, Cor 8.32 (wedhorn.txt:3504-3517, 4095-4140)
-/

@[expose] public section

namespace ValuationSpectrum

open Pointwise

universe u

variable {A : Type u} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
  [PlusSubring A] [IsHuberRing A]

/-! ## The gen-piece data and the G1 relative-piece stack -/

/-- `s · (t/s) = t` in the localization. (Relocated with the G1 stack from
`WedhornCechAcyclicity.lean`, 2026-06-11.) -/
theorem algebraMap_s_mul_divByS (D : RationalLocData A) (t : A) :
    algebraMap A (Localization.Away D.s) D.s * divByS t D.s =
      algebraMap A (Localization.Away D.s) t := by
  unfold divByS
  rw [show algebraMap A (Localization.Away D.s) D.s =
      IsLocalization.mk' (Localization.Away D.s) D.s (1 : Submonoid.powers D.s) from
      (IsLocalization.mk'_one _ _).symm, ← IsLocalization.mk'_mul,
    show algebraMap A (Localization.Away D.s) t =
      IsLocalization.mk' (Localization.Away D.s) t (1 : Submonoid.powers D.s) from
      (IsLocalization.mk'_one _ _).symm]
  apply IsLocalization.mk'_eq_of_eq
  simp [mul_comm]

omit [PlusSubring A] [IsHuberRing A] in
/-- **Absorption (Wedhorn §8.1-style)**: a high power of the ideal of definition
multiplies any finitely many fixed ring elements into `A₀` (continuity of
multiplication + openness of `A₀` + the `I`-adic neighborhood basis). -/
theorem pod_absorb_finset_mul_pow (P : PairOfDefinition A) (S : Finset A) :
    ∃ N : ℕ, ∀ a ∈ S, ∀ b : P.A₀, b ∈ P.I ^ N → (↑b : A) * a ∈ P.A₀ := by
  classical
  have hone : ∀ a : A, ∃ N : ℕ, ∀ b : P.A₀, b ∈ P.I ^ N → (↑b : A) * a ∈ P.A₀ := by
    intro a
    have hcont : Continuous (fun x : P.A₀ => (↑x : A) * a) :=
      continuous_subtype_val.mul continuous_const
    have h0 : (fun x : P.A₀ => (↑x : A) * a) 0 ∈ (P.A₀ : Set A) := by
      simp only [ZeroMemClass.coe_zero, zero_mul]
      exact P.A₀.zero_mem
    have hpre : (fun x : P.A₀ => (↑x : A) * a) ⁻¹' (P.A₀ : Set A) ∈
        nhds (0 : P.A₀) :=
      hcont.continuousAt.preimage_mem_nhds (P.isOpen.mem_nhds h0)
    obtain ⟨n, -, hn⟩ := P.isAdic.hasBasis_nhds_zero.mem_iff.mp hpre
    exact ⟨n, fun b hb => hn hb⟩
  choose Nf hNf using hone
  refine ⟨S.sup Nf, fun a ha b hb => hNf a b ?_⟩
  exact Ideal.pow_le_pow_right (Finset.le_sup ha) hb

omit [PlusSubring A] [IsHuberRing A] in
/-- **General gen-set piece openness**: for `T` spanning the unit ideal and `t ∈ T`,
the piece `R(T/t)` satisfies the `hopen`-condition — high `I`-powers divide by `t`
into the ring of definition, via the span-combination `1 = Σ c_{t'}·t'` and
absorption of the coefficients (Wedhorn p. 83, the `U_t := R(T/t)` cover form). -/
theorem genPiece_hopen (P : PairOfDefinition A) (T : Finset A) (t : A)
    (hspan : Ideal.span (T : Set A) = ⊤) :
    ∃ N : ℕ, ∀ b : P.A₀, b ∈ P.I ^ N →
      divByS (↑b : A) t ∈ locSubring P T t := by
  classical
  have h1 : (1 : A) ∈ Ideal.span (T : Set A) := hspan ▸ Submodule.mem_top
  obtain ⟨c, _hc_supp, hc⟩ := Submodule.mem_span_finset.mp h1
  obtain ⟨N, hN⟩ := pod_absorb_finset_mul_pow P (T.image c)
  refine ⟨N, fun b hb => ?_⟩
  -- `divByS b t = Σ_{t' ∈ T} aM (b·c t') · divByS t' t` (cancel the away-unit `aM t`)
  have hkey : divByS (↑b : A) t = ∑ t' ∈ T,
      algebraMap A (Localization.Away t) ((↑b : A) * c t') * divByS t' t := by
    refine (IsLocalization.Away.algebraMap_isUnit
      (S := Localization.Away t) t).mul_left_cancel ?_
    have hL : algebraMap A (Localization.Away t) t * divByS (↑b : A) t =
        algebraMap A (Localization.Away t) (↑b : A) := by
      unfold divByS
      exact IsLocalization.mk'_spec' (M := Submonoid.powers t)
        (Localization.Away t) (↑b : A) ⟨t, 1, pow_one t⟩
    rw [hL, Finset.mul_sum]
    have hterm : ∀ t' ∈ T, algebraMap A (Localization.Away t) t *
        (algebraMap A (Localization.Away t) ((↑b : A) * c t') * divByS t' t) =
        algebraMap A (Localization.Away t) ((↑b : A) * c t' * t') := by
      intro t' _
      have h2 : algebraMap A (Localization.Away t) t * divByS t' t =
          algebraMap A (Localization.Away t) t' := by
        unfold divByS
        exact IsLocalization.mk'_spec' (M := Submonoid.powers t)
          (Localization.Away t) t' ⟨t, 1, pow_one t⟩
      rw [show algebraMap A (Localization.Away t) t *
          (algebraMap A (Localization.Away t) ((↑b : A) * c t') * divByS t' t) =
        algebraMap A (Localization.Away t) ((↑b : A) * c t') *
          (algebraMap A (Localization.Away t) t * divByS t' t) from by ring]
      rw [h2, ← map_mul]
    rw [Finset.sum_congr rfl hterm, ← map_sum]
    congr 1
    calc (↑b : A) = (↑b : A) * 1 := (mul_one _).symm
      _ = (↑b : A) * ∑ t' ∈ T, c t' * t' := by
          rw [show ∑ t' ∈ T, c t' * t' = (1 : A) from by
            simpa only [smul_eq_mul] using hc]
      _ = ∑ t' ∈ T, (↑b : A) * c t' * t' := by rw [Finset.mul_sum]; ring_nf
  rw [hkey]
  refine Subring.sum_mem _ (fun t' ht' => Subring.mul_mem _ ?_ ?_)
  · exact algebraMap_mem_locSubring P T t
      (hN (c t') (Finset.mem_image_of_mem c ht') b hb)
  · exact divByS_mem_locSubring P T t ht'

/-- The span of the image of an ideal-generating set is the unit ideal. -/
theorem span_image_canonicalMap_eq_top
    [IsTateRing A] [IsNoetherianRing A]
    (D₀ : RationalLocData A) (T : Finset A)
    (hspan : Ideal.span (T : Set A) = ⊤) :
    Ideal.span (D₀.canonicalMap '' (T : Set A)) = ⊤ := by
  rw [← Ideal.map_span D₀.canonicalMap, hspan]
  exact Ideal.map_top _

omit [PlusSubring A] [IsHuberRing A] in
/-- **The A-side gen-set piece** `R(T/t)` (Wedhorn p. 83's `U_t := R(T/t)` cover form),
with the `hopen`-condition supplied by `genPiece_hopen` (span + absorption).
(`A⁺`-free: the datum and its openness use only the pair of definition.) -/
noncomputable def genPieceDatum (P : PairOfDefinition A) (T : Finset A) (t : A)
    (hspan : Ideal.span (T : Set A) = ⊤) : RationalLocData A :=
  { P := P
    T := T
    s := t
    hopen := genPiece_hopen P T t hspan }

omit [PlusSubring A] [IsHuberRing A] in
@[simp] theorem genPieceDatum_P (P : PairOfDefinition A) (T : Finset A) (t : A)
    (hspan : Ideal.span (T : Set A) = ⊤) : (genPieceDatum P T t hspan).P = P := rfl

omit [PlusSubring A] [IsHuberRing A] in
@[simp] theorem genPieceDatum_T (P : PairOfDefinition A) (T : Finset A) (t : A)
    (hspan : Ideal.span (T : Set A) = ⊤) : (genPieceDatum P T t hspan).T = T := rfl

omit [PlusSubring A] [IsHuberRing A] in
@[simp] theorem genPieceDatum_s (P : PairOfDefinition A) (T : Finset A) (t : A)
    (hspan : Ideal.span (T : Set A) = ⊤) : (genPieceDatum P T t hspan).s = t := rfl

/-- **The B-side image piece** `R(canMap T / canMap t)` over `B = presheafValue D₀`
(Wedhorn Remark 8.4 / Prop 8.2(1) vocabulary: the rational subset of `Spa 𝒪_X(D₀)`
corresponding to `D₀ ∩ R(T/t)`). The `hopen`-condition is `genPiece_hopen` at `B`
(span-combination + absorption). -/
noncomputable def imagePieceDatum
    [IsTateRing A] [IsNoetherianRing A] [IsStronglyNoetherian A] [T2Space A]
    [NonarchimedeanRing A] [HasLocLiftPowerBounded A]
    [letI : UniformSpace A := IsTopologicalAddGroup.rightUniformSpace A;
      CompleteSpace A]
    (D₀ : RationalLocData A) (T : Finset A) (t : A)
    (hspan : Ideal.span (T : Set A) = ⊤) :
    RationalLocData (presheafValue D₀) :=
  haveI hTateB : IsTateRing (presheafValue D₀) := presheafValue_isTateRing_faithful D₀
  haveI : IsNoetherianRing (presheafValue D₀) :=
    presheafValue_isNoetherianRing_faithful D₀
  haveI : IsStronglyNoetherian (presheafValue D₀) :=
    presheafValue_isStronglyNoetherian_faithful D₀
  haveI : IsHuberRing (presheafValue D₀) := hTateB.toIsHuberRing
  letI : DecidableEq (presheafValue D₀) := Classical.decEq _
  letI : DecidableEq (RationalLocData (presheafValue D₀)) := Classical.decEq _
  { P := presheafValue_concretePair D₀
    T := T.image D₀.canonicalMap
    s := D₀.canonicalMap t
    hopen := genPiece_hopen (presheafValue_concretePair D₀)
      (T.image D₀.canonicalMap) (D₀.canonicalMap t)
      (by rw [Finset.coe_image]; exact span_image_canonicalMap_eq_top D₀ T hspan) }

/-- The pair of definition of `imagePieceDatum` is `presheafValue_concretePair D₀`.

Named projection lemma (see `RationalLocData.interSamePair_P`): pair-equality proofs
between two `imagePieceDatum`s must be built from this by `Eq.trans`/`Eq.symm` so they
stay well-typed at reducible transparency (a bare `rfl` needs the semireducible
`imagePieceDatum` unfolded and makes v4.33 `kabstract` choke on any enclosing goal). -/
theorem imagePieceDatum_P
    [IsTateRing A] [IsNoetherianRing A] [IsStronglyNoetherian A] [T2Space A]
    [NonarchimedeanRing A] [HasLocLiftPowerBounded A]
    [letI : UniformSpace A := IsTopologicalAddGroup.rightUniformSpace A;
      CompleteSpace A]
    (D₀ : RationalLocData A) (T : Finset A) (t : A)
    (hspan : Ideal.span (T : Set A) = ⊤) :
    (imagePieceDatum D₀ T t hspan).P = presheafValue_concretePair D₀ := rfl

/-- The image piece is rational (Wedhorn 7.29): its tray is the `canonicalMap`-image of
a `⊤`-spanning family, which spans `⊤` (`span_image_canonicalMap_eq_top`). -/
theorem imagePieceDatum_isRational
    [IsTateRing A] [IsNoetherianRing A] [IsStronglyNoetherian A] [T2Space A]
    [NonarchimedeanRing A] [HasLocLiftPowerBounded A]
    [letI : UniformSpace A := IsTopologicalAddGroup.rightUniformSpace A;
      CompleteSpace A]
    (D₀ : RationalLocData A) (T : Finset A) (t : A)
    (hspan : Ideal.span (T : Set A) = ⊤) :
    (imagePieceDatum D₀ T t hspan).IsRational := by
  letI : DecidableEq (presheafValue D₀) := Classical.decEq _
  refine RationalLocData.isRational_of_span_eq_top ?_
  show Ideal.span (((T.image D₀.canonicalMap) : Finset (presheafValue D₀)) :
    Set (presheafValue D₀)) = ⊤
  rw [Finset.coe_image]
  exact span_image_canonicalMap_eq_top D₀ T hspan

/-- **General relative piece, forward base unit (G1-1)**: `s_inter = D₀.s·t` maps to a
unit of `Localization.Away (canMap t)` over `B`. -/
theorem genPiece_rel_baseHom_isUnit
    [IsTateRing A] [IsNoetherianRing A] [IsStronglyNoetherian A] [T2Space A]
    [NonarchimedeanRing A] [HasLocLiftPowerBounded A]
    [letI : UniformSpace A := IsTopologicalAddGroup.rightUniformSpace A;
      CompleteSpace A]
    (D₀ : RationalLocData A) (T : Finset A) (t : A)
    (hspan : Ideal.span (T : Set A) = ⊤) :
    IsUnit (((algebraMap (presheafValue D₀) (Localization.Away
        ((imagePieceDatum D₀ T t hspan).s))).comp D₀.canonicalMap)
      ((D₀.interSamePair (genPieceDatum D₀.P T t hspan) rfl).s)) := by
  have hs : ((D₀.interSamePair (genPieceDatum D₀.P T t hspan) rfl).s : A) =
      D₀.s * t := rfl
  rw [RingHom.comp_apply, hs, map_mul, map_mul]
  refine IsUnit.mul ?_ ?_
  · exact ((isUnit_s_in_presheafValue D₀).map _)
  · exact IsLocalization.Away.algebraMap_isUnit
      (S := Localization.Away ((imagePieceDatum D₀ T t hspan).s))
      ((imagePieceDatum D₀ T t hspan).s)

/-- **General relative piece, forward loc-hom (G1-2)**. -/
noncomputable def genPiece_rel_forwardLocHom
    [IsTateRing A] [IsNoetherianRing A] [IsStronglyNoetherian A] [T2Space A]
    [NonarchimedeanRing A] [HasLocLiftPowerBounded A]
    [letI : UniformSpace A := IsTopologicalAddGroup.rightUniformSpace A;
      CompleteSpace A]
    (D₀ : RationalLocData A) (T : Finset A) (t : A)
    (hspan : Ideal.span (T : Set A) = ⊤) :
    Localization.Away ((D₀.interSamePair (genPieceDatum D₀.P T t hspan) rfl).s) →+*
      Localization.Away ((imagePieceDatum D₀ T t hspan).s) :=
  IsLocalization.Away.lift
    (x := (D₀.interSamePair (genPieceDatum D₀.P T t hspan) rfl).s)
    (g := (algebraMap (presheafValue D₀) (Localization.Away
      ((imagePieceDatum D₀ T t hspan).s))).comp D₀.canonicalMap)
    (genPiece_rel_baseHom_isUnit D₀ T t hspan)

/-- G1-3: the forward loc-hom sends `algebraMap a ↦ algebraMap (canonicalMap a)`. -/
theorem genPiece_rel_forwardLocHom_algebraMap
    [IsTateRing A] [IsNoetherianRing A] [IsStronglyNoetherian A] [T2Space A]
    [NonarchimedeanRing A] [HasLocLiftPowerBounded A]
    [letI : UniformSpace A := IsTopologicalAddGroup.rightUniformSpace A;
      CompleteSpace A]
    (D₀ : RationalLocData A) (T : Finset A) (t : A)
    (hspan : Ideal.span (T : Set A) = ⊤) (a : A) :
    genPiece_rel_forwardLocHom D₀ T t hspan
        (algebraMap A (Localization.Away
          ((D₀.interSamePair (genPieceDatum D₀.P T t hspan) rfl).s)) a) =
      algebraMap (presheafValue D₀)
        (Localization.Away ((imagePieceDatum D₀ T t hspan).s))
        (D₀.canonicalMap a) := by
  rw [genPiece_rel_forwardLocHom, IsLocalization.Away.lift_eq]
  rfl

/-- **General relative piece, per-generator witnesses (G1-4)**: every
`t' ∈ T_inter` (a product `p·q`, `p ∈ insert D₀.s D₀.T`, `q ∈ insert t T`) has a
`locSubring`-witness over the B-side image datum: `y = aM(coe(p/s))·((im q)/(im t))`.
Uniform equation (no unit-juggling); only the membership splits on `q = t` vs `q ∈ T`. -/
theorem genPiece_rel_forward_witness
    [IsTateRing A] [IsNoetherianRing A] [IsStronglyNoetherian A] [T2Space A]
    [NonarchimedeanRing A] [HasLocLiftPowerBounded A]
    [letI : UniformSpace A := IsTopologicalAddGroup.rightUniformSpace A;
      CompleteSpace A]
    (D₀ : RationalLocData A) (T : Finset A) (t : A)
    (hspan : Ideal.span (T : Set A) = ⊤)
    (w : A) (hw : w ∈ (D₀.interSamePair (genPieceDatum D₀.P T t hspan) rfl).T) :
    ∃ y : Localization.Away ((imagePieceDatum D₀ T t hspan).s),
      y ∈ locSubring (imagePieceDatum D₀ T t hspan).P
          (imagePieceDatum D₀ T t hspan).T (imagePieceDatum D₀ T t hspan).s ∧
      ((imagePieceDatum D₀ T t hspan).coeRingHom).comp
        (genPiece_rel_forwardLocHom D₀ T t hspan)
        (divByS w ((D₀.interSamePair (genPieceDatum D₀.P T t hspan) rfl).s)) =
      (imagePieceDatum D₀ T t hspan).coeRingHom y := by
  classical
  haveI hTateB : IsTateRing (presheafValue D₀) := presheafValue_isTateRing_faithful D₀
  haveI hNoethB : IsNoetherianRing (presheafValue D₀) :=
    presheafValue_isNoetherianRing_faithful D₀
  set DI := D₀.interSamePair (genPieceDatum D₀.P T t hspan) rfl with hDI
  set DB := imagePieceDatum D₀ T t hspan with hDB
  set F := (DB.coeRingHom).comp (genPiece_rel_forwardLocHom D₀ T t hspan) with hF
  have hF_alg : ∀ a : A, F (algebraMap A (Localization.Away DI.s) a) =
      DB.canonicalMap (D₀.canonicalMap a) := by
    intro a
    rw [hF, RingHom.comp_apply, genPiece_rel_forwardLocHom_algebraMap]
    rfl
  have hu : IsUnit (F (algebraMap A (Localization.Away DI.s) DI.s)) := by
    rw [hF_alg]
    exact (genPiece_rel_baseHom_isUnit D₀ T t hspan).map DB.coeRingHom
  have hF_div : ∀ (c : A) (z : presheafValue DB),
      F (algebraMap A (Localization.Away DI.s) c) =
        F (algebraMap A (Localization.Away DI.s) DI.s) * z →
      F (divByS c DI.s) = z := by
    intro c z hz
    have h1 : F (algebraMap A (Localization.Away DI.s) DI.s) * F (divByS c DI.s) =
        F (algebraMap A (Localization.Away DI.s) c) := by
      rw [← map_mul, algebraMap_s_mul_divByS]
    exact hu.mul_left_cancel (h1.trans hz)
  have hps : ∀ p : A, D₀.canonicalMap p =
      D₀.canonicalMap D₀.s * D₀.coeRingHom (divByS p D₀.s) := by
    intro p
    rw [show D₀.canonicalMap D₀.s * D₀.coeRingHom (divByS p D₀.s) =
      D₀.coeRingHom (algebraMap A (Localization.Away D₀.s) D₀.s *
        divByS p D₀.s) from by rw [map_mul]; rfl]
    rw [algebraMap_s_mul_divByS]
    rfl
  have hA₀ : ∀ p ∈ insert D₀.s D₀.T,
      D₀.coeRingHom (divByS p D₀.s) ∈ (presheafValue_concretePair D₀).A₀ := by
    intro p hp
    rw [presheafValue_concretePair_A₀]
    rcases Finset.mem_insert.mp hp with rfl | hp'
    · have h1 : divByS D₀.s D₀.s = 1 := by
        unfold divByS
        exact IsLocalization.mk'_self (M := Submonoid.powers D₀.s)
          (S := Localization.Away D₀.s) ⟨1, pow_one D₀.s⟩
      rw [h1, map_one]
      exact one_mem _
    · exact subset_closure ⟨⟨divByS p D₀.s,
        divByS_mem_locSubring D₀.P D₀.T D₀.s hp'⟩, rfl⟩
  -- the B-side `q/t`-identity: `canMap_B (canMap q) = canMap_B (canMap t) · coe ((im q)/(im t))`
  have hqt : ∀ q : A, DB.canonicalMap (D₀.canonicalMap q) =
      DB.canonicalMap (D₀.canonicalMap t) *
        DB.coeRingHom (divByS (D₀.canonicalMap q) DB.s) := by
    intro q
    rw [show DB.canonicalMap (D₀.canonicalMap t) *
        DB.coeRingHom (divByS (D₀.canonicalMap q) DB.s) =
      DB.coeRingHom (algebraMap (presheafValue D₀) (Localization.Away DB.s)
        (D₀.canonicalMap t) * divByS (D₀.canonicalMap q) DB.s) from by
      rw [map_mul]; rfl]
    rw [show algebraMap (presheafValue D₀) (Localization.Away DB.s)
        (D₀.canonicalMap t) = algebraMap (presheafValue D₀) (Localization.Away DB.s)
        DB.s from rfl]
    rw [algebraMap_s_mul_divByS]
    rfl
  -- the witness membership for the `q`-factor
  have hq_mem : ∀ q ∈ insert t T,
      divByS (D₀.canonicalMap q) DB.s ∈ locSubring DB.P DB.T DB.s := by
    intro q hq
    rcases Finset.mem_insert.mp hq with rfl | hq'
    · have h1 : divByS (D₀.canonicalMap q) DB.s = 1 := by
        rw [show (DB.s : presheafValue D₀) = D₀.canonicalMap q from rfl]
        unfold divByS
        exact IsLocalization.mk'_self (M := Submonoid.powers (D₀.canonicalMap q))
          (S := Localization.Away (D₀.canonicalMap q)) ⟨1, pow_one _⟩
      rw [h1]
      exact one_mem _
    · refine divByS_mem_locSubring DB.P DB.T DB.s ?_
      show D₀.canonicalMap q ∈ T.image D₀.canonicalMap
      exact Finset.mem_image_of_mem _ hq'
  -- decompose `w = p · q`
  have hw' : w ∈ ((insert D₀.s D₀.T).product
      (insert t T)).image (fun r : A × A => r.1 * r.2) := hw
  rw [Finset.mem_image] at hw'
  obtain ⟨⟨p, q⟩, hpq, rfl⟩ := hw'
  have hp : p ∈ insert D₀.s D₀.T := (Finset.mem_product.mp hpq).1
  have hq : q ∈ insert t T := (Finset.mem_product.mp hpq).2
  rw [show (((p, q).1 : A) * (p, q).2 : A) = p * q from rfl]
  refine ⟨algebraMap (presheafValue D₀) (Localization.Away DB.s)
      (D₀.coeRingHom (divByS p D₀.s)) * divByS (D₀.canonicalMap q) DB.s,
    (locSubring DB.P DB.T DB.s).mul_mem
      (algebraMap_mem_locSubring DB.P DB.T DB.s (hA₀ p hp))
      (hq_mem q hq), ?_⟩
  refine hF_div _ _ ?_
  rw [hF_alg, hF_alg]
  rw [show DB.coeRingHom (algebraMap (presheafValue D₀) (Localization.Away DB.s)
      (D₀.coeRingHom (divByS p D₀.s)) * divByS (D₀.canonicalMap q) DB.s) =
    DB.canonicalMap (D₀.coeRingHom (divByS p D₀.s)) *
      DB.coeRingHom (divByS (D₀.canonicalMap q) DB.s) from by rw [map_mul]; rfl]
  rw [show ((D₀.interSamePair (genPieceDatum D₀.P T t hspan) rfl).s : A) =
    D₀.s * t from rfl]
  rw [map_mul (D₀.canonicalMap), map_mul (D₀.canonicalMap), map_mul (DB.canonicalMap),
    map_mul (DB.canonicalMap)]
  rw [show D₀.canonicalMap p = D₀.canonicalMap D₀.s *
    D₀.coeRingHom (divByS p D₀.s) from hps p]
  rw [map_mul (DB.canonicalMap), hqt q]
  ring

/-- G1-5: forward continuity. -/
theorem genPiece_rel_forwardCompletion_continuous
    [IsTateRing A] [IsNoetherianRing A] [IsStronglyNoetherian A] [T2Space A]
    [NonarchimedeanRing A] [HasLocLiftPowerBounded A]
    [letI : UniformSpace A := IsTopologicalAddGroup.rightUniformSpace A;
      CompleteSpace A]
    (D₀ : RationalLocData A) (T : Finset A) (t : A)
    (hspan : Ideal.span (T : Set A) = ⊤) :
    @Continuous _ _ (D₀.interSamePair (genPieceDatum D₀.P T t hspan) rfl).topology _
      (((imagePieceDatum D₀ T t hspan).coeRingHom).comp (genPiece_rel_forwardLocHom D₀ T t hspan)) := by
  classical
  haveI hTateB : IsTateRing (presheafValue D₀) := presheafValue_isTateRing_faithful D₀
  haveI hNoethB : IsNoetherianRing (presheafValue D₀) :=
    presheafValue_isNoetherianRing_faithful D₀
  set DI := (D₀.interSamePair (genPieceDatum D₀.P T t hspan) rfl) with hDI
  set DB := (imagePieceDatum D₀ T t hspan) with hDB
  set F := (DB.coeRingHom).comp (genPiece_rel_forwardLocHom D₀ T t hspan) with hF
  have hF_alg : ∀ a : A, F (algebraMap A (Localization.Away DI.s) a) =
      DB.canonicalMap (D₀.canonicalMap a) := by
    intro a
    rw [hF, RingHom.comp_apply, genPiece_rel_forwardLocHom_algebraMap]
    rfl
  change @Continuous _ _ (locTopology DI.P DI.T DI.s DI.hopen) _ F
  refine locTopology_continuous_lift DI.P DI.T DI.s DI.hopen F ?_ ?_
  · have heq : F.comp (algebraMap A (Localization.Away DI.s)) =
        (DB.canonicalMap).comp D₀.canonicalMap := by
      ext a; exact hF_alg a
    rw [heq]
    exact (canonicalMap_continuous DB).comp (canonicalMap_continuous D₀)
  · intro w hw
    obtain ⟨y, hy_mem, hy_eq⟩ := genPiece_rel_forward_witness D₀ T t hspan w hw
    rw [show F (divByS w DI.s) = DB.coeRingHom y from hy_eq]
    have hbddB := CompletionLocalization.coeRingHom_image_locSubring_isBounded DB
    refine hbddB.subset ?_
    rintro _ ⟨k, rfl⟩
    exact ⟨y ^ k, pow_mem hy_mem k, by rw [map_pow]⟩

/-- G1-6: forward map. -/
noncomputable def genPiece_rel_forward
    [IsTateRing A] [IsNoetherianRing A] [IsStronglyNoetherian A] [T2Space A]
    [NonarchimedeanRing A] [HasLocLiftPowerBounded A]
    [letI : UniformSpace A := IsTopologicalAddGroup.rightUniformSpace A;
      CompleteSpace A]
    (D₀ : RationalLocData A) (T : Finset A) (t : A)
    (hspan : Ideal.span (T : Set A) = ⊤) :
    presheafValue (D₀.interSamePair (genPieceDatum D₀.P T t hspan) rfl) →+* presheafValue (imagePieceDatum D₀ T t hspan) := by
  letI : UniformSpace (Localization.Away (D₀.interSamePair (genPieceDatum D₀.P T t hspan) rfl).s) := (D₀.interSamePair (genPieceDatum D₀.P T t hspan) rfl).uniformSpace
  letI : IsTopologicalRing (Localization.Away (D₀.interSamePair (genPieceDatum D₀.P T t hspan) rfl).s) := (D₀.interSamePair (genPieceDatum D₀.P T t hspan) rfl).isTopologicalRing
  letI : IsUniformAddGroup (Localization.Away (D₀.interSamePair (genPieceDatum D₀.P T t hspan) rfl).s) := (D₀.interSamePair (genPieceDatum D₀.P T t hspan) rfl).isUniformAddGroup
  exact UniformSpace.Completion.extensionHom
    (((imagePieceDatum D₀ T t hspan).coeRingHom).comp (genPiece_rel_forwardLocHom D₀ T t hspan))
    (genPiece_rel_forwardCompletion_continuous D₀ T t hspan)

/-- G1-6′ coe-tracking. -/
theorem genPiece_rel_forward_coe
    [IsTateRing A] [IsNoetherianRing A] [IsStronglyNoetherian A] [T2Space A]
    [NonarchimedeanRing A] [HasLocLiftPowerBounded A]
    [letI : UniformSpace A := IsTopologicalAddGroup.rightUniformSpace A;
      CompleteSpace A]
    (D₀ : RationalLocData A) (T : Finset A) (t : A)
    (hspan : Ideal.span (T : Set A) = ⊤)
    (y : Localization.Away (D₀.interSamePair (genPieceDatum D₀.P T t hspan) rfl).s) :
    genPiece_rel_forward D₀ T t hspan ((D₀.interSamePair (genPieceDatum D₀.P T t hspan) rfl).coeRingHom y) =
      (imagePieceDatum D₀ T t hspan).coeRingHom (genPiece_rel_forwardLocHom D₀ T t hspan y) := by
  letI : UniformSpace (Localization.Away (D₀.interSamePair (genPieceDatum D₀.P T t hspan) rfl).s) := (D₀.interSamePair (genPieceDatum D₀.P T t hspan) rfl).uniformSpace
  letI : IsTopologicalRing (Localization.Away (D₀.interSamePair (genPieceDatum D₀.P T t hspan) rfl).s) := (D₀.interSamePair (genPieceDatum D₀.P T t hspan) rfl).isTopologicalRing
  letI : IsUniformAddGroup (Localization.Away (D₀.interSamePair (genPieceDatum D₀.P T t hspan) rfl).s) := (D₀.interSamePair (genPieceDatum D₀.P T t hspan) rfl).isUniformAddGroup
  exact UniformSpace.Completion.extensionHom_coe
    (((imagePieceDatum D₀ T t hspan).coeRingHom).comp (genPiece_rel_forwardLocHom D₀ T t hspan))
    (genPiece_rel_forwardCompletion_continuous D₀ T t hspan) y

/-- G1-7a: backward base unit (the restriction of `canMap t` is a unit, dividing the
unit `canMap (D₀.s·t)`). -/
theorem genPiece_rel_backward_baseHom_isUnit
    [IsTateRing A] [IsNoetherianRing A] [IsStronglyNoetherian A] [T2Space A]
    [NonarchimedeanRing A] [HasLocLiftPowerBounded A]
    [letI : UniformSpace A := IsTopologicalAddGroup.rightUniformSpace A;
      CompleteSpace A]
    (D₀ : RationalLocData A) (T : Finset A) (t : A)
    (hspan : Ideal.span (T : Set A) = ⊤) :
    IsUnit ((restrictionMapHom D₀ (D₀.interSamePair (genPieceDatum D₀.P T t hspan) rfl)
        (RationalLocData.interSamePair_subset_left _ _ _))
      ((imagePieceDatum D₀ T t hspan).s)) := by
  rw [show ((imagePieceDatum D₀ T t hspan).s : presheafValue D₀) = D₀.canonicalMap t from rfl]
  rw [restrictionMapHom_canonicalMap]
  have hu : IsUnit ((D₀.interSamePair (genPieceDatum D₀.P T t hspan) rfl).canonicalMap ((D₀.interSamePair (genPieceDatum D₀.P T t hspan) rfl).s)) := isUnit_s_in_presheafValue _
  rw [show ((D₀.interSamePair (genPieceDatum D₀.P T t hspan) rfl).s : A) = D₀.s * t from rfl, map_mul] at hu
  exact isUnit_of_mul_isUnit_right hu

/-- G1-7b: backward loc-hom. -/
noncomputable def genPiece_rel_backwardLocHom
    [IsTateRing A] [IsNoetherianRing A] [IsStronglyNoetherian A] [T2Space A]
    [NonarchimedeanRing A] [HasLocLiftPowerBounded A]
    [letI : UniformSpace A := IsTopologicalAddGroup.rightUniformSpace A;
      CompleteSpace A]
    (D₀ : RationalLocData A) (T : Finset A) (t : A)
    (hspan : Ideal.span (T : Set A) = ⊤) :
    Localization.Away ((imagePieceDatum D₀ T t hspan).s) →+* presheafValue (D₀.interSamePair (genPieceDatum D₀.P T t hspan) rfl) :=
  IsLocalization.Away.lift
    (x := (imagePieceDatum D₀ T t hspan).s)
    (g := restrictionMapHom D₀ (D₀.interSamePair (genPieceDatum D₀.P T t hspan) rfl)
      (RationalLocData.interSamePair_subset_left _ _ _))
    (genPiece_rel_backward_baseHom_isUnit D₀ T t hspan)

/-- G1-7c: backward loc-hom tracking. -/
theorem genPiece_rel_backwardLocHom_algebraMap
    [IsTateRing A] [IsNoetherianRing A] [IsStronglyNoetherian A] [T2Space A]
    [NonarchimedeanRing A] [HasLocLiftPowerBounded A]
    [letI : UniformSpace A := IsTopologicalAddGroup.rightUniformSpace A;
      CompleteSpace A]
    (D₀ : RationalLocData A) (T : Finset A) (t : A)
    (hspan : Ideal.span (T : Set A) = ⊤) (x : presheafValue D₀) :
    genPiece_rel_backwardLocHom D₀ T t hspan
        (algebraMap (presheafValue D₀) (Localization.Away ((imagePieceDatum D₀ T t hspan).s)) x) =
      restrictionMapHom D₀ (D₀.interSamePair (genPieceDatum D₀.P T t hspan) rfl)
        (RationalLocData.interSamePair_subset_left _ _ _) x := by
  rw [genPiece_rel_backwardLocHom, IsLocalization.Away.lift_eq]

/-- G1-7d: the `q/t`-generator identity in `O_X(D₀ ∩ R(T/t))`: `canMap_DI q` is
`canMap_DI t` times the image of `(D₀.s·q)/s_inter` (cancel the unit `canMap D₀.s`). -/
theorem genPiece_rel_canonicalMap_q_eq
    [IsTateRing A] [IsNoetherianRing A] [IsStronglyNoetherian A] [T2Space A]
    [NonarchimedeanRing A] [HasLocLiftPowerBounded A]
    [letI : UniformSpace A := IsTopologicalAddGroup.rightUniformSpace A;
      CompleteSpace A]
    (D₀ : RationalLocData A) (T : Finset A) (t : A)
    (hspan : Ideal.span (T : Set A) = ⊤) (q : A) :
    (D₀.interSamePair (genPieceDatum D₀.P T t hspan) rfl).canonicalMap q =
      (D₀.interSamePair (genPieceDatum D₀.P T t hspan) rfl).canonicalMap t * (D₀.interSamePair (genPieceDatum D₀.P T t hspan) rfl).coeRingHom (divByS (D₀.s * q) (D₀.interSamePair (genPieceDatum D₀.P T t hspan) rfl).s) := by
  set DI := (D₀.interSamePair (genPieceDatum D₀.P T t hspan) rfl) with hDI
  have hchase : ∀ c : A, DI.canonicalMap DI.s * DI.coeRingHom (divByS c DI.s) =
      DI.canonicalMap c := by
    intro c
    rw [show DI.canonicalMap DI.s * DI.coeRingHom (divByS c DI.s) =
      DI.coeRingHom (algebraMap A (Localization.Away DI.s) DI.s *
        divByS c DI.s) from by rw [map_mul]; rfl]
    rw [algebraMap_s_mul_divByS]
    rfl
  have hsplit : DI.canonicalMap DI.s = DI.canonicalMap D₀.s * DI.canonicalMap t := by
    rw [show DI.canonicalMap DI.s = DI.canonicalMap (D₀.s * t) from by
      rw [show (DI.s : A) = D₀.s * t from rfl]]
    rw [map_mul]
  have hu_s : IsUnit (DI.canonicalMap D₀.s) := by
    have hu : IsUnit (DI.canonicalMap DI.s) := isUnit_s_in_presheafValue DI
    rw [hsplit] at hu
    exact isUnit_of_mul_isUnit_left hu
  refine hu_s.mul_left_cancel ?_
  have h2 := hchase (D₀.s * q)
  rw [hsplit] at h2
  calc DI.canonicalMap D₀.s * DI.canonicalMap q = DI.canonicalMap (D₀.s * q) := by
        rw [map_mul]
    _ = DI.canonicalMap D₀.s * DI.canonicalMap t *
        DI.coeRingHom (divByS (D₀.s * q) DI.s) := h2.symm
    _ = DI.canonicalMap D₀.s * (DI.canonicalMap t *
        DI.coeRingHom (divByS (D₀.s * q) DI.s)) := by ring

/-- G1-7e: backward continuity (each image-generator `(im q)/(im t)` lands on the
ring-of-definition element `(D₀.s·q)/s_inter`). -/
theorem genPiece_rel_backwardLocHom_continuous
    [IsTateRing A] [IsNoetherianRing A] [IsStronglyNoetherian A] [T2Space A]
    [NonarchimedeanRing A] [HasLocLiftPowerBounded A]
    [letI : UniformSpace A := IsTopologicalAddGroup.rightUniformSpace A;
      CompleteSpace A]
    (D₀ : RationalLocData A) (T : Finset A) (t : A)
    (hspan : Ideal.span (T : Set A) = ⊤) :
    @Continuous _ _ (imagePieceDatum D₀ T t hspan).topology _
      (genPiece_rel_backwardLocHom D₀ T t hspan) := by
  classical
  haveI hTateB : IsTateRing (presheafValue D₀) := presheafValue_isTateRing_faithful D₀
  haveI hNoethB : IsNoetherianRing (presheafValue D₀) :=
    presheafValue_isNoetherianRing_faithful D₀
  set DI := (D₀.interSamePair (genPieceDatum D₀.P T t hspan) rfl) with hDI
  set DB := (imagePieceDatum D₀ T t hspan) with hDB
  change @Continuous _ _ (locTopology DB.P DB.T DB.s DB.hopen) _
    (genPiece_rel_backwardLocHom D₀ T t hspan)
  refine locTopology_continuous_lift DB.P DB.T DB.s DB.hopen
    (genPiece_rel_backwardLocHom D₀ T t hspan) ?_ ?_
  · have heq : (genPiece_rel_backwardLocHom D₀ T t hspan).comp
        (algebraMap (presheafValue D₀) (Localization.Away DB.s)) =
        restrictionMapHom D₀ DI (RationalLocData.interSamePair_subset_left _ _ _) := by
      ext x; exact genPiece_rel_backwardLocHom_algebraMap D₀ T t hspan x
    rw [heq]
    exact restrictionMapHom_continuous D₀ DI _
  · intro w hw
    have hw' : w ∈ T.image D₀.canonicalMap := hw
    rw [Finset.mem_image] at hw'
    obtain ⟨q, hq, rfl⟩ := hw'
    have hu_b : IsUnit (genPiece_rel_backwardLocHom D₀ T t hspan
        (algebraMap (presheafValue D₀) (Localization.Away DB.s) DB.s)) := by
      rw [genPiece_rel_backwardLocHom_algebraMap]
      exact genPiece_rel_backward_baseHom_isUnit D₀ T t hspan
    have hwit : genPiece_rel_backwardLocHom D₀ T t hspan
        (divByS (D₀.canonicalMap q) DB.s) =
        DI.coeRingHom (divByS (D₀.s * q) DI.s) := by
      refine hu_b.mul_left_cancel ?_
      have h1 : genPiece_rel_backwardLocHom D₀ T t hspan
          (algebraMap (presheafValue D₀) (Localization.Away DB.s) DB.s) *
          genPiece_rel_backwardLocHom D₀ T t hspan
            (divByS (D₀.canonicalMap q) DB.s) =
          genPiece_rel_backwardLocHom D₀ T t hspan
            (algebraMap (presheafValue D₀) (Localization.Away DB.s)
              (D₀.canonicalMap q)) := by
        rw [← map_mul]
        congr 1
        exact algebraMap_s_mul_divByS DB (D₀.canonicalMap q)
      rw [h1, genPiece_rel_backwardLocHom_algebraMap,
        genPiece_rel_backwardLocHom_algebraMap]
      rw [show (DB.s : presheafValue D₀) = D₀.canonicalMap t from rfl]
      rw [restrictionMapHom_canonicalMap, restrictionMapHom_canonicalMap]
      exact genPiece_rel_canonicalMap_q_eq D₀ T t hspan q
    rw [hwit]
    have hbdd := CompletionLocalization.coeRingHom_image_locSubring_isBounded DI
    refine hbdd.subset ?_
    rintro _ ⟨k, rfl⟩
    refine ⟨divByS (D₀.s * q) DI.s ^ k, pow_mem (divByS_mem_locSubring DI.P DI.T DI.s
      ?_) k, by rw [map_pow]⟩
    show D₀.s * q ∈ ((insert D₀.s D₀.T).product
      (insert t T)).image (fun r : A × A => r.1 * r.2)
    exact Finset.mem_image.mpr ⟨(D₀.s, q), Finset.mem_product.mpr
      ⟨Finset.mem_insert_self _ _, Finset.mem_insert_of_mem hq⟩, rfl⟩

/-- G1-7f: backward map. -/
noncomputable def genPiece_rel_backward
    [IsTateRing A] [IsNoetherianRing A] [IsStronglyNoetherian A] [T2Space A]
    [NonarchimedeanRing A] [HasLocLiftPowerBounded A]
    [letI : UniformSpace A := IsTopologicalAddGroup.rightUniformSpace A;
      CompleteSpace A]
    (D₀ : RationalLocData A) (T : Finset A) (t : A)
    (hspan : Ideal.span (T : Set A) = ⊤) :
    presheafValue (imagePieceDatum D₀ T t hspan) →+* presheafValue (D₀.interSamePair (genPieceDatum D₀.P T t hspan) rfl) := by
  letI : UniformSpace (Localization.Away (imagePieceDatum D₀ T t hspan).s) := (imagePieceDatum D₀ T t hspan).uniformSpace
  letI : IsTopologicalRing (Localization.Away (imagePieceDatum D₀ T t hspan).s) := (imagePieceDatum D₀ T t hspan).isTopologicalRing
  letI : IsUniformAddGroup (Localization.Away (imagePieceDatum D₀ T t hspan).s) := (imagePieceDatum D₀ T t hspan).isUniformAddGroup
  exact UniformSpace.Completion.extensionHom
    (genPiece_rel_backwardLocHom D₀ T t hspan)
    (genPiece_rel_backwardLocHom_continuous D₀ T t hspan)

/-- G1-7f′ coe-tracking. -/
theorem genPiece_rel_backward_coe
    [IsTateRing A] [IsNoetherianRing A] [IsStronglyNoetherian A] [T2Space A]
    [NonarchimedeanRing A] [HasLocLiftPowerBounded A]
    [letI : UniformSpace A := IsTopologicalAddGroup.rightUniformSpace A;
      CompleteSpace A]
    (D₀ : RationalLocData A) (T : Finset A) (t : A)
    (hspan : Ideal.span (T : Set A) = ⊤)
    (y : Localization.Away (imagePieceDatum D₀ T t hspan).s) :
    genPiece_rel_backward D₀ T t hspan ((imagePieceDatum D₀ T t hspan).coeRingHom y) =
      genPiece_rel_backwardLocHom D₀ T t hspan y := by
  letI : UniformSpace (Localization.Away (imagePieceDatum D₀ T t hspan).s) := (imagePieceDatum D₀ T t hspan).uniformSpace
  letI : IsTopologicalRing (Localization.Away (imagePieceDatum D₀ T t hspan).s) := (imagePieceDatum D₀ T t hspan).isTopologicalRing
  letI : IsUniformAddGroup (Localization.Away (imagePieceDatum D₀ T t hspan).s) := (imagePieceDatum D₀ T t hspan).isUniformAddGroup
  exact UniformSpace.Completion.extensionHom_coe
    (genPiece_rel_backwardLocHom D₀ T t hspan)
    (genPiece_rel_backwardLocHom_continuous D₀ T t hspan) y

/-- G1-8a: loc-level restriction base unit (`D₀.s` divides the localized-away unit
`s_inter = D₀.s·t`). -/
theorem genPiece_rel_locRestriction_baseUnit
    [IsTateRing A] [IsNoetherianRing A]
    (D₀ : RationalLocData A) (T : Finset A) (t : A)
    (hspan : Ideal.span (T : Set A) = ⊤) :
    IsUnit (algebraMap A (Localization.Away (D₀.interSamePair (genPieceDatum D₀.P T t hspan) rfl).s) D₀.s) := by
  have h2 : IsUnit (algebraMap A (Localization.Away (D₀.interSamePair (genPieceDatum D₀.P T t hspan) rfl).s) D₀.s *
      algebraMap A (Localization.Away (D₀.interSamePair (genPieceDatum D₀.P T t hspan) rfl).s) t) := by
    rw [← map_mul]
    rw [show ((D₀.s * t : A)) = (D₀.interSamePair (genPieceDatum D₀.P T t hspan) rfl).s from rfl]
    exact IsLocalization.Away.algebraMap_isUnit
      (S := Localization.Away (D₀.interSamePair (genPieceDatum D₀.P T t hspan) rfl).s) (D₀.interSamePair (genPieceDatum D₀.P T t hspan) rfl).s
  exact isUnit_of_mul_isUnit_left h2

/-- G1-8a′: loc-level restriction. -/
noncomputable def genPiece_rel_locRestriction
    [IsTateRing A] [IsNoetherianRing A]
    (D₀ : RationalLocData A) (T : Finset A) (t : A)
    (hspan : Ideal.span (T : Set A) = ⊤) :
    Localization.Away D₀.s →+* Localization.Away (D₀.interSamePair (genPieceDatum D₀.P T t hspan) rfl).s :=
  IsLocalization.Away.lift (x := D₀.s)
    (g := algebraMap A (Localization.Away (D₀.interSamePair (genPieceDatum D₀.P T t hspan) rfl).s))
    (genPiece_rel_locRestriction_baseUnit D₀ T t hspan)

/-- G1-8a″ tracking. -/
theorem genPiece_rel_locRestriction_algebraMap
    [IsTateRing A] [IsNoetherianRing A]
    (D₀ : RationalLocData A) (T : Finset A) (t : A)
    (hspan : Ideal.span (T : Set A) = ⊤) (a : A) :
    genPiece_rel_locRestriction D₀ T t hspan
        (algebraMap A (Localization.Away D₀.s) a) =
      algebraMap A (Localization.Away (D₀.interSamePair (genPieceDatum D₀.P T t hspan) rfl).s) a := by
  rw [genPiece_rel_locRestriction, IsLocalization.Away.lift_eq]

/-- G1-8b: restriction factorization. -/
theorem genPiece_rel_restriction_factor
    [IsTateRing A] [IsNoetherianRing A] [IsStronglyNoetherian A] [T2Space A]
    [NonarchimedeanRing A] [HasLocLiftPowerBounded A]
    [letI : UniformSpace A := IsTopologicalAddGroup.rightUniformSpace A;
      CompleteSpace A]
    (D₀ : RationalLocData A) (T : Finset A) (t : A)
    (hspan : Ideal.span (T : Set A) = ⊤) :
    (restrictionMapHom D₀ (D₀.interSamePair (genPieceDatum D₀.P T t hspan) rfl)
        (RationalLocData.interSamePair_subset_left _ _ _)).comp D₀.coeRingHom =
      ((D₀.interSamePair (genPieceDatum D₀.P T t hspan) rfl).coeRingHom).comp (genPiece_rel_locRestriction D₀ T t hspan) := by
  refine IsLocalization.ringHom_ext (Submonoid.powers D₀.s) ?_
  ext a
  simp only [RingHom.comp_apply]
  rw [show D₀.coeRingHom (algebraMap A (Localization.Away D₀.s) a) =
    D₀.canonicalMap a from rfl, restrictionMapHom_canonicalMap,
    genPiece_rel_locRestriction_algebraMap]
  rfl

/-- G1-8c: loc-level roundtrip 1. -/
theorem genPiece_rel_locRoundtrip1
    [IsTateRing A] [IsNoetherianRing A] [IsStronglyNoetherian A] [T2Space A]
    [NonarchimedeanRing A] [HasLocLiftPowerBounded A]
    [letI : UniformSpace A := IsTopologicalAddGroup.rightUniformSpace A;
      CompleteSpace A]
    (D₀ : RationalLocData A) (T : Finset A) (t : A)
    (hspan : Ideal.span (T : Set A) = ⊤) :
    (genPiece_rel_backwardLocHom D₀ T t hspan).comp
        (genPiece_rel_forwardLocHom D₀ T t hspan) =
      (D₀.interSamePair (genPieceDatum D₀.P T t hspan) rfl).coeRingHom := by
  refine IsLocalization.ringHom_ext (Submonoid.powers (D₀.interSamePair (genPieceDatum D₀.P T t hspan) rfl).s) ?_
  ext a
  simp only [RingHom.comp_apply]
  rw [genPiece_rel_forwardLocHom_algebraMap,
    genPiece_rel_backwardLocHom_algebraMap, restrictionMapHom_canonicalMap]
  rfl

/-- G1-8d: loc-level roundtrip 2. -/
theorem genPiece_rel_locRoundtrip2
    [IsTateRing A] [IsNoetherianRing A] [IsStronglyNoetherian A] [T2Space A]
    [NonarchimedeanRing A] [HasLocLiftPowerBounded A]
    [letI : UniformSpace A := IsTopologicalAddGroup.rightUniformSpace A;
      CompleteSpace A]
    (D₀ : RationalLocData A) (T : Finset A) (t : A)
    (hspan : Ideal.span (T : Set A) = ⊤) :
    (genPiece_rel_forwardLocHom D₀ T t hspan).comp
        (genPiece_rel_locRestriction D₀ T t hspan) =
      (algebraMap (presheafValue D₀) (Localization.Away (imagePieceDatum D₀ T t hspan).s)).comp
        D₀.coeRingHom := by
  refine IsLocalization.ringHom_ext (Submonoid.powers D₀.s) ?_
  ext a
  simp only [RingHom.comp_apply]
  rw [genPiece_rel_locRestriction_algebraMap, genPiece_rel_forwardLocHom_algebraMap]
  rfl

/-- G1-8e: `backward ∘ forward = id`. -/
theorem genPiece_rel_backward_forward
    [IsTateRing A] [IsNoetherianRing A] [IsStronglyNoetherian A] [T2Space A]
    [NonarchimedeanRing A] [HasLocLiftPowerBounded A]
    [letI : UniformSpace A := IsTopologicalAddGroup.rightUniformSpace A;
      CompleteSpace A]
    (D₀ : RationalLocData A) (T : Finset A) (t : A)
    (hspan : Ideal.span (T : Set A) = ⊤)
    (x : presheafValue (D₀.interSamePair (genPieceDatum D₀.P T t hspan) rfl)) :
    genPiece_rel_backward D₀ T t hspan (genPiece_rel_forward D₀ T t hspan x) = x := by
  letI : UniformSpace (Localization.Away (D₀.interSamePair (genPieceDatum D₀.P T t hspan) rfl).s) := (D₀.interSamePair (genPieceDatum D₀.P T t hspan) rfl).uniformSpace
  letI : IsTopologicalRing (Localization.Away (D₀.interSamePair (genPieceDatum D₀.P T t hspan) rfl).s) := (D₀.interSamePair (genPieceDatum D₀.P T t hspan) rfl).isTopologicalRing
  letI : IsUniformAddGroup (Localization.Away (D₀.interSamePair (genPieceDatum D₀.P T t hspan) rfl).s) := (D₀.interSamePair (genPieceDatum D₀.P T t hspan) rfl).isUniformAddGroup
  letI : UniformSpace (Localization.Away (imagePieceDatum D₀ T t hspan).s) := (imagePieceDatum D₀ T t hspan).uniformSpace
  letI : IsTopologicalRing (Localization.Away (imagePieceDatum D₀ T t hspan).s) := (imagePieceDatum D₀ T t hspan).isTopologicalRing
  letI : IsUniformAddGroup (Localization.Away (imagePieceDatum D₀ T t hspan).s) := (imagePieceDatum D₀ T t hspan).isUniformAddGroup
  refine @UniformSpace.Completion.ext'
    (Localization.Away (D₀.interSamePair (genPieceDatum D₀.P T t hspan) rfl).s) (D₀.interSamePair (genPieceDatum D₀.P T t hspan) rfl).uniformSpace
    (presheafValue (D₀.interSamePair (genPieceDatum D₀.P T t hspan) rfl)) _ _ _ _
    (UniformSpace.Completion.continuous_extension.comp
      UniformSpace.Completion.continuous_extension)
    continuous_id ?_ x
  intro a
  show genPiece_rel_backward D₀ T t hspan (genPiece_rel_forward D₀ T t hspan
    ((D₀.interSamePair (genPieceDatum D₀.P T t hspan) rfl).coeRingHom a)) = (D₀.interSamePair (genPieceDatum D₀.P T t hspan) rfl).coeRingHom a
  rw [genPiece_rel_forward_coe, genPiece_rel_backward_coe]
  exact RingHom.congr_fun (genPiece_rel_locRoundtrip1 D₀ T t hspan) a

/-- G1-8f: forward-restriction intertwining (the Prop 8.2 naturality). -/
theorem genPiece_rel_forward_restriction
    [IsTateRing A] [IsNoetherianRing A] [IsStronglyNoetherian A] [T2Space A]
    [NonarchimedeanRing A] [HasLocLiftPowerBounded A]
    [letI : UniformSpace A := IsTopologicalAddGroup.rightUniformSpace A;
      CompleteSpace A]
    (D₀ : RationalLocData A) (T : Finset A) (t : A)
    (hspan : Ideal.span (T : Set A) = ⊤)
    (x : presheafValue D₀) :
    genPiece_rel_forward D₀ T t hspan
        (restrictionMapHom D₀ (D₀.interSamePair (genPieceDatum D₀.P T t hspan) rfl)
          (RationalLocData.interSamePair_subset_left _ _ _) x) =
      (imagePieceDatum D₀ T t hspan).canonicalMap x := by
  letI : UniformSpace (Localization.Away D₀.s) := D₀.uniformSpace
  letI : IsTopologicalRing (Localization.Away D₀.s) := D₀.isTopologicalRing
  letI : IsUniformAddGroup (Localization.Away D₀.s) := D₀.isUniformAddGroup
  letI : UniformSpace (Localization.Away (D₀.interSamePair (genPieceDatum D₀.P T t hspan) rfl).s) := (D₀.interSamePair (genPieceDatum D₀.P T t hspan) rfl).uniformSpace
  letI : IsTopologicalRing (Localization.Away (D₀.interSamePair (genPieceDatum D₀.P T t hspan) rfl).s) := (D₀.interSamePair (genPieceDatum D₀.P T t hspan) rfl).isTopologicalRing
  letI : IsUniformAddGroup (Localization.Away (D₀.interSamePair (genPieceDatum D₀.P T t hspan) rfl).s) := (D₀.interSamePair (genPieceDatum D₀.P T t hspan) rfl).isUniformAddGroup
  letI : UniformSpace (Localization.Away (imagePieceDatum D₀ T t hspan).s) := (imagePieceDatum D₀ T t hspan).uniformSpace
  letI : IsTopologicalRing (Localization.Away (imagePieceDatum D₀ T t hspan).s) := (imagePieceDatum D₀ T t hspan).isTopologicalRing
  letI : IsUniformAddGroup (Localization.Away (imagePieceDatum D₀ T t hspan).s) := (imagePieceDatum D₀ T t hspan).isUniformAddGroup
  refine @UniformSpace.Completion.ext' (Localization.Away D₀.s) D₀.uniformSpace
    (presheafValue (imagePieceDatum D₀ T t hspan)) _ _ _ _
    (UniformSpace.Completion.continuous_extension.comp
      UniformSpace.Completion.continuous_extension)
    (canonicalMap_continuous (imagePieceDatum D₀ T t hspan)) ?_ x
  intro z
  show genPiece_rel_forward D₀ T t hspan
      (restrictionMapHom D₀ (D₀.interSamePair (genPieceDatum D₀.P T t hspan) rfl)
        (RationalLocData.interSamePair_subset_left _ _ _) (D₀.coeRingHom z)) =
    (imagePieceDatum D₀ T t hspan).canonicalMap (D₀.coeRingHom z)
  rw [show restrictionMapHom D₀ (D₀.interSamePair (genPieceDatum D₀.P T t hspan) rfl)
      (RationalLocData.interSamePair_subset_left _ _ _) (D₀.coeRingHom z) =
    (D₀.interSamePair (genPieceDatum D₀.P T t hspan) rfl).coeRingHom (genPiece_rel_locRestriction D₀ T t hspan z) from
    RingHom.congr_fun (genPiece_rel_restriction_factor D₀ T t hspan) z]
  rw [genPiece_rel_forward_coe]
  exact congrArg _ (RingHom.congr_fun (genPiece_rel_locRoundtrip2 D₀ T t hspan) z)

/-- G1-8g: `forward ∘ backward = id`. -/
theorem genPiece_rel_forward_backward
    [IsTateRing A] [IsNoetherianRing A] [IsStronglyNoetherian A] [T2Space A]
    [NonarchimedeanRing A] [HasLocLiftPowerBounded A]
    [letI : UniformSpace A := IsTopologicalAddGroup.rightUniformSpace A;
      CompleteSpace A]
    (D₀ : RationalLocData A) (T : Finset A) (t : A)
    (hspan : Ideal.span (T : Set A) = ⊤)
    (y : presheafValue (imagePieceDatum D₀ T t hspan)) :
    genPiece_rel_forward D₀ T t hspan (genPiece_rel_backward D₀ T t hspan y) = y := by
  haveI hTateB : IsTateRing (presheafValue D₀) := presheafValue_isTateRing_faithful D₀
  haveI hNoethB : IsNoetherianRing (presheafValue D₀) :=
    presheafValue_isNoetherianRing_faithful D₀
  have hloc : (genPiece_rel_forward D₀ T t hspan).comp
      (genPiece_rel_backwardLocHom D₀ T t hspan) =
      (imagePieceDatum D₀ T t hspan).coeRingHom := by
    refine IsLocalization.ringHom_ext (Submonoid.powers (imagePieceDatum D₀ T t hspan).s) ?_
    ext x
    simp only [RingHom.comp_apply]
    rw [genPiece_rel_backwardLocHom_algebraMap, genPiece_rel_forward_restriction]
    rfl
  letI : UniformSpace (Localization.Away (D₀.interSamePair (genPieceDatum D₀.P T t hspan) rfl).s) := (D₀.interSamePair (genPieceDatum D₀.P T t hspan) rfl).uniformSpace
  letI : IsTopologicalRing (Localization.Away (D₀.interSamePair (genPieceDatum D₀.P T t hspan) rfl).s) := (D₀.interSamePair (genPieceDatum D₀.P T t hspan) rfl).isTopologicalRing
  letI : IsUniformAddGroup (Localization.Away (D₀.interSamePair (genPieceDatum D₀.P T t hspan) rfl).s) := (D₀.interSamePair (genPieceDatum D₀.P T t hspan) rfl).isUniformAddGroup
  letI : UniformSpace (Localization.Away (imagePieceDatum D₀ T t hspan).s) := (imagePieceDatum D₀ T t hspan).uniformSpace
  letI : IsTopologicalRing (Localization.Away (imagePieceDatum D₀ T t hspan).s) := (imagePieceDatum D₀ T t hspan).isTopologicalRing
  letI : IsUniformAddGroup (Localization.Away (imagePieceDatum D₀ T t hspan).s) := (imagePieceDatum D₀ T t hspan).isUniformAddGroup
  refine @UniformSpace.Completion.ext'
    (Localization.Away (imagePieceDatum D₀ T t hspan).s) (imagePieceDatum D₀ T t hspan).uniformSpace
    (presheafValue (imagePieceDatum D₀ T t hspan)) _ _ _ _
    (UniformSpace.Completion.continuous_extension.comp
      UniformSpace.Completion.continuous_extension)
    continuous_id ?_ y
  intro w
  show genPiece_rel_forward D₀ T t hspan (genPiece_rel_backward D₀ T t hspan
    ((imagePieceDatum D₀ T t hspan).coeRingHom w)) = (imagePieceDatum D₀ T t hspan).coeRingHom w
  rw [genPiece_rel_backward_coe]
  exact RingHom.congr_fun hloc w

/-- **The general relative-piece identification (Wedhorn Prop 8.2 / Remark 8.4)**:
the structure ring of `D₀ ∩ R(T/t)` is the structure ring of the image piece
`R(canMap T / canMap t)` over `B = 𝒪_X(D₀)`, for any ideal-generating `T`.
The R2-transport workhorse (T-R2-SECTION-COMPAT). -/
noncomputable def genPiece_relative_equiv
    [IsTateRing A] [IsNoetherianRing A] [IsStronglyNoetherian A] [T2Space A]
    [NonarchimedeanRing A] [HasLocLiftPowerBounded A]
    [letI : UniformSpace A := IsTopologicalAddGroup.rightUniformSpace A;
      CompleteSpace A]
    (D₀ : RationalLocData A) (T : Finset A) (t : A)
    (hspan : Ideal.span (T : Set A) = ⊤) :
    presheafValue (D₀.interSamePair (genPieceDatum D₀.P T t hspan) rfl) ≃+* presheafValue (imagePieceDatum D₀ T t hspan) :=
  RingEquiv.ofRingHom (genPiece_rel_forward D₀ T t hspan)
    (genPiece_rel_backward D₀ T t hspan)
    (RingHom.ext (genPiece_rel_forward_backward D₀ T t hspan))
    (RingHom.ext (genPiece_rel_backward_forward D₀ T t hspan))

/-- The general relative-piece iso intertwines restriction with `canonicalMap` over `B`
(Wedhorn Prop 8.2 base-change naturality; the transport-compatibility). -/
theorem genPiece_relative_equiv_restrictionMap
    [IsTateRing A] [IsNoetherianRing A] [IsStronglyNoetherian A] [T2Space A]
    [NonarchimedeanRing A] [HasLocLiftPowerBounded A]
    [letI : UniformSpace A := IsTopologicalAddGroup.rightUniformSpace A;
      CompleteSpace A]
    (D₀ : RationalLocData A) (T : Finset A) (t : A)
    (hspan : Ideal.span (T : Set A) = ⊤)
    (x : presheafValue D₀) :
    genPiece_relative_equiv D₀ T t hspan
        (restrictionMap D₀ (D₀.interSamePair (genPieceDatum D₀.P T t hspan) rfl)
          (RationalLocData.interSamePair_subset_left _ _ _) x) =
      (imagePieceDatum D₀ T t hspan).canonicalMap x :=
  genPiece_rel_forward_restriction D₀ T t hspan x

/-- The image-span proof at the `Finset`-coe form (helper for the B-cover). -/
theorem imageGenCover_span
    [IsTateRing A] [IsNoetherianRing A]
    (D₀ : RationalLocData A) [DecidableEq (presheafValue D₀)] (T : Finset A)
    (hspan : Ideal.span (T : Set A) = ⊤) :
    Ideal.span ((T.image D₀.canonicalMap : Finset (presheafValue D₀)) :
      Set (presheafValue D₀)) = ⊤ := by
  rw [Finset.coe_image]
  exact span_image_canonicalMap_eq_top D₀ T hspan

/-- **THE 8.16-KEYSTONE (Wedhorn Prop 8.16 / Prop 8.2, [Hu2] 1.4.4)**: for a
rational piece `E` inside `D₀` (with the rational-subset span condition of
Wedhorn Def 7.29), the section ring `𝒪_X(E)` is canonically isomorphic to the
`B`-side section ring of the image datum `R_B(im E.T / im E.s)`,
`B := 𝒪_X(D₀)`. This is the general-piece base change behind BOTH "we may
assume X = V" (Prop 8.30's opening, wedhorn.txt:4099) and the R2-transport
of acyclicity to general bases.

Factors through two PROVEN pieces: the open-equality
`E ≈ D₀ ∩ R(E.T/E.s)` (restriction-bijectivity between open-equal data) and
the relative-piece equivalence `genPiece_relative_equiv` (the
Example-6.38-template machinery, G1). -/
noncomputable def relativePiece_equiv
    [IsTateRing A] [IsNoetherianRing A] [IsStronglyNoetherian A] [T2Space A]
    [NonarchimedeanRing A] [HasLocLiftPowerBounded A]
    [letI : UniformSpace A := IsTopologicalAddGroup.rightUniformSpace A;
      CompleteSpace A]
    (D₀ E : RationalLocData A)
    (hE_sub : rationalOpen E.T E.s ⊆ rationalOpen D₀.T D₀.s)
    (hspanE : Ideal.span (E.T : Set A) = ⊤) :
    presheafValue E ≃+* presheafValue (imagePieceDatum D₀ E.T E.s hspanE) :=
  have h_eq : rationalOpen E.T E.s =
      rationalOpen (D₀.interSamePair (genPieceDatum D₀.P E.T E.s hspanE) rfl).T
        (D₀.interSamePair (genPieceDatum D₀.P E.T E.s hspanE) rfl).s := by
    -- v4.33: `rw [interSamePair_rationalOpen]` fails to match through the goal's embedded
    -- `rfl : (genPieceDatum …).P = D₀.P` (re-checked at reducible transparency). Apply the
    -- lemma with an explicit `genPieceDatum_P` proof instead and compose by `Eq.trans`.
    have h := RationalLocData.interSamePair_rationalOpen D₀
      (genPieceDatum D₀.P E.T E.s hspanE) (genPieceDatum_P D₀.P E.T E.s hspanE)
    rw [genPieceDatum_T, genPieceDatum_s] at h
    exact (h.trans (Set.inter_eq_right.mpr hE_sub)).symm
  (RingEquiv.ofBijective
    (restrictionMapHom E
      (D₀.interSamePair (genPieceDatum D₀.P E.T E.s hspanE) rfl) h_eq.symm.le)
    (restrictionMap_bijective_of_rationalOpen_eq E
      (D₀.interSamePair (genPieceDatum D₀.P E.T E.s hspanE) rfl) h_eq)).trans
    (genPiece_relative_equiv D₀ E.T E.s hspanE)

/-- The 8.16-keystone intertwines the canonical maps: restricting `x : 𝒪_X(D₀)`
to `E` and passing to the `B`-side equals the `B`-side canonical map of `x`
(Wedhorn Prop 8.2 base-change naturality, general-piece form). -/
theorem relativePiece_equiv_restrictionMap
    [IsTateRing A] [IsNoetherianRing A] [IsStronglyNoetherian A] [T2Space A]
    [NonarchimedeanRing A] [HasLocLiftPowerBounded A]
    [letI : UniformSpace A := IsTopologicalAddGroup.rightUniformSpace A;
      CompleteSpace A]
    (D₀ E : RationalLocData A)
    (hE_sub : rationalOpen E.T E.s ⊆ rationalOpen D₀.T D₀.s)
    (hspanE : Ideal.span (E.T : Set A) = ⊤)
    (x : presheafValue D₀) :
    relativePiece_equiv D₀ E hE_sub hspanE
        (restrictionMap D₀ E hE_sub x) =
      (imagePieceDatum D₀ E.T E.s hspanE).canonicalMap x := by
  have h_eq : rationalOpen E.T E.s =
      rationalOpen (D₀.interSamePair (genPieceDatum D₀.P E.T E.s hspanE) rfl).T
        (D₀.interSamePair (genPieceDatum D₀.P E.T E.s hspanE) rfl).s := by
    -- v4.33: `rw [interSamePair_rationalOpen]` fails to match through the goal's embedded
    -- `rfl : (genPieceDatum …).P = D₀.P` (re-checked at reducible transparency). Apply the
    -- lemma with an explicit `genPieceDatum_P` proof instead and compose by `Eq.trans`.
    have h := RationalLocData.interSamePair_rationalOpen D₀
      (genPieceDatum D₀.P E.T E.s hspanE) (genPieceDatum_P D₀.P E.T E.s hspanE)
    rw [genPieceDatum_T, genPieceDatum_s] at h
    exact (h.trans (Set.inter_eq_right.mpr hE_sub)).symm
  show genPiece_relative_equiv D₀ E.T E.s hspanE
      (restrictionMapHom E
        (D₀.interSamePair (genPieceDatum D₀.P E.T E.s hspanE) rfl) h_eq.symm.le
        (restrictionMap D₀ E hE_sub x)) =
    (imagePieceDatum D₀ E.T E.s hspanE).canonicalMap x
  have hcomp : restrictionMapHom E
      (D₀.interSamePair (genPieceDatum D₀.P E.T E.s hspanE) rfl) h_eq.symm.le
      (restrictionMap D₀ E hE_sub x) =
      restrictionMap D₀
        (D₀.interSamePair (genPieceDatum D₀.P E.T E.s hspanE) rfl)
        (RationalLocData.interSamePair_subset_left _ _ _) x :=
    congrFun (restrictionMap_comp D₀ E
      (D₀.interSamePair (genPieceDatum D₀.P E.T E.s hspanE) rfl)
      hE_sub h_eq.symm.le) x
  rw [hcomp]
  exact genPiece_relative_equiv_restrictionMap D₀ E.T E.s hspanE x

/-- **The comap characterisation of image-piece opens** (Wedhorn Prop 8.2 +
Remark 8.4: the homeomorphism `Spa B ≅ U` matches rational subsets, [Hu2] 1.4.4):
a point of `Spv B` lies in the image piece's rational open iff it is a Spa-`B`
point whose `A`-shadow lies in the original piece's rational open. The conditions
transport verbatim through `comap_vle` (an equality of propositions). -/
theorem imagePieceDatum_mem_rationalOpen_iff
    [IsTateRing A] [IsNoetherianRing A] [IsStronglyNoetherian A] [T2Space A]
    [NonarchimedeanRing A] [HasLocLiftPowerBounded A]
    [letI : UniformSpace A := IsTopologicalAddGroup.rightUniformSpace A;
      CompleteSpace A]
    (D₀ E : RationalLocData A) (hspanE : Ideal.span (E.T : Set A) = ⊤)
    (w : Spv (presheafValue D₀)) :
    haveI hTateB : IsTateRing (presheafValue D₀) := presheafValue_isTateRing_faithful D₀
    haveI : IsHuberRing (presheafValue D₀) := hTateB.toIsHuberRing
    haveI : DecidableEq (presheafValue D₀) := Classical.decEq _
    (w ∈ rationalOpen (imagePieceDatum D₀ E.T E.s hspanE).T
        (imagePieceDatum D₀ E.T E.s hspanE).s ↔
      w ∈ Spa (presheafValue D₀) (presheafValue D₀)⁺ ∧
        comap D₀.canonicalMap w ∈ rationalOpen E.T E.s) := by
  haveI hTateB : IsTateRing (presheafValue D₀) := presheafValue_isTateRing_faithful D₀
  haveI : IsHuberRing (presheafValue D₀) := hTateB.toIsHuberRing
  letI : DecidableEq (presheafValue D₀) := Classical.decEq _
  have hT : (imagePieceDatum D₀ E.T E.s hspanE).T = E.T.image D₀.canonicalMap := rfl
  have hs : (imagePieceDatum D₀ E.T E.s hspanE).s = D₀.canonicalMap E.s := rfl
  constructor
  · rintro ⟨hspa, hcond, hnz⟩
    refine ⟨hspa, comap_mem_spa (canonicalMap_continuous D₀)
      D₀.canonicalMap_integral hspa, fun t ht => ?_, fun h0 => ?_⟩
    · rw [comap_vle]
      have := hcond (D₀.canonicalMap t) (by rw [hT]; exact Finset.mem_image_of_mem _ ht)
      rwa [hs] at this
    · rw [comap_vle, map_zero] at h0
      rw [hs] at hnz
      exact hnz h0
  · rintro ⟨hspa, -, hcond, hnz⟩
    refine ⟨hspa, fun x hx => ?_, fun h0 => ?_⟩
    · rw [hT, Finset.mem_image] at hx
      obtain ⟨t, ht, rfl⟩ := hx
      rw [hs]
      have := hcond t ht
      rwa [comap_vle] at this
    · rw [hs] at h0
      exact hnz (by rw [comap_vle, map_zero]; exact h0)

/-- Image pieces preserve containment of rational opens (Wedhorn Remark 8.4). -/
theorem imagePieceDatum_rationalOpen_mono
    [IsTateRing A] [IsNoetherianRing A] [IsStronglyNoetherian A] [T2Space A]
    [NonarchimedeanRing A] [HasLocLiftPowerBounded A]
    [letI : UniformSpace A := IsTopologicalAddGroup.rightUniformSpace A;
      CompleteSpace A]
    (D₀ E E' : RationalLocData A)
    (hspanE : Ideal.span (E.T : Set A) = ⊤)
    (hspanE' : Ideal.span (E'.T : Set A) = ⊤)
    (h : rationalOpen E'.T E'.s ⊆ rationalOpen E.T E.s) :
    haveI hTateB : IsTateRing (presheafValue D₀) := presheafValue_isTateRing_faithful D₀
    haveI : IsHuberRing (presheafValue D₀) := hTateB.toIsHuberRing
    rationalOpen (imagePieceDatum D₀ E'.T E'.s hspanE').T
        (imagePieceDatum D₀ E'.T E'.s hspanE').s ⊆
      rationalOpen (imagePieceDatum D₀ E.T E.s hspanE).T
        (imagePieceDatum D₀ E.T E.s hspanE).s := by
  haveI hTateB : IsTateRing (presheafValue D₀) := presheafValue_isTateRing_faithful D₀
  haveI : IsHuberRing (presheafValue D₀) := hTateB.toIsHuberRing
  intro w hw
  rw [imagePieceDatum_mem_rationalOpen_iff] at hw ⊢
  exact ⟨hw.1, h hw.2⟩

/-- Image pieces match intersections of rational opens (Wedhorn Remark 8.4). -/
theorem imagePieceDatum_rationalOpen_inter
    [IsTateRing A] [IsNoetherianRing A] [IsStronglyNoetherian A] [T2Space A]
    [NonarchimedeanRing A] [HasLocLiftPowerBounded A]
    [letI : UniformSpace A := IsTopologicalAddGroup.rightUniformSpace A;
      CompleteSpace A]
    (D₀ E₁ E₂ E₃ : RationalLocData A)
    (hspanE₁ : Ideal.span (E₁.T : Set A) = ⊤)
    (hspanE₂ : Ideal.span (E₂.T : Set A) = ⊤)
    (hspanE₃ : Ideal.span (E₃.T : Set A) = ⊤)
    (h₃ : rationalOpen E₃.T E₃.s =
      rationalOpen E₁.T E₁.s ∩ rationalOpen E₂.T E₂.s) :
    haveI hTateB : IsTateRing (presheafValue D₀) := presheafValue_isTateRing_faithful D₀
    haveI : IsHuberRing (presheafValue D₀) := hTateB.toIsHuberRing
    rationalOpen (imagePieceDatum D₀ E₃.T E₃.s hspanE₃).T
        (imagePieceDatum D₀ E₃.T E₃.s hspanE₃).s =
      rationalOpen (imagePieceDatum D₀ E₁.T E₁.s hspanE₁).T
          (imagePieceDatum D₀ E₁.T E₁.s hspanE₁).s ∩
        rationalOpen (imagePieceDatum D₀ E₂.T E₂.s hspanE₂).T
          (imagePieceDatum D₀ E₂.T E₂.s hspanE₂).s := by
  haveI hTateB : IsTateRing (presheafValue D₀) := presheafValue_isTateRing_faithful D₀
  haveI : IsHuberRing (presheafValue D₀) := hTateB.toIsHuberRing
  ext w
  rw [Set.mem_inter_iff, imagePieceDatum_mem_rationalOpen_iff,
    imagePieceDatum_mem_rationalOpen_iff, imagePieceDatum_mem_rationalOpen_iff, h₃]
  constructor
  · rintro ⟨hspa, h₁, h₂⟩
    exact ⟨⟨hspa, h₁⟩, hspa, h₂⟩
  · rintro ⟨⟨hspa, h₁⟩, -, h₂⟩
    exact ⟨hspa, h₁, h₂⟩

/-- **The keystone restriction square** (Wedhorn Prop 8.16 naturality for nested
pieces, [Hu2] 1.4.4): for rational pieces `E' ⊆ E ⊆ D₀` the base-change
isomorphisms intertwine the `A`-side and `B`-side restriction maps:

```
        𝒪_X(E)  ──restrict──→  𝒪_X(E')
          ≃ keystone_E            ≃ keystone_E'
        𝒪_B(im E) ─restrict─→  𝒪_B(im E')
```

**Proof recipe (G1/G3b)**: both composites are continuous ring homomorphisms
`𝒪_X(E) → 𝒪_B(im E')`; they agree on the canonical `A`-image by
`relativePiece_equiv_restrictionMap` + `restrictionMapHom_canonicalMap` (both
sides send `(canonicalMap E a)` to `(im E').canonicalMap (D₀.canonicalMap a)`-
style values), hence on the dense localization image (ring homs preserve the
inverted `E.s`), hence everywhere by continuity + `T2`. Same 8-step stack as
`genPiece_relative_equiv`'s G3b overlap squares. -/
theorem relativePiece_equiv_restrict_square
    [IsTateRing A] [IsNoetherianRing A] [IsStronglyNoetherian A] [T2Space A]
    [NonarchimedeanRing A] [HasLocLiftPowerBounded A] [IsRingOfIntegralElements (A⁺)]
    [letI : UniformSpace A := IsTopologicalAddGroup.rightUniformSpace A;
      CompleteSpace A]
    (D₀ E E' : RationalLocData A)
    (hE_sub : rationalOpen E.T E.s ⊆ rationalOpen D₀.T D₀.s)
    (hE'_sub : rationalOpen E'.T E'.s ⊆ rationalOpen E.T E.s)
    (hspanE : Ideal.span (E.T : Set A) = ⊤)
    (hspanE' : Ideal.span (E'.T : Set A) = ⊤)
    (y : presheafValue E) :
    haveI hTateB : IsTateRing (presheafValue D₀) := presheafValue_isTateRing_faithful D₀
    haveI : IsHuberRing (presheafValue D₀) := hTateB.toIsHuberRing
    haveI : IsNoetherianRing (presheafValue D₀) :=
      presheafValue_isNoetherianRing_faithful D₀
    haveI : @CompleteSpace (presheafValue D₀)
        (IsTopologicalAddGroup.rightUniformSpace (presheafValue D₀)) :=
      presheafValue_completeSpace_rightUniformSpace D₀
    haveI : HasLocLiftPowerBounded (presheafValue D₀) := hasLocLiftPowerBounded_faithful
    relativePiece_equiv D₀ E' (hE'_sub.trans hE_sub) hspanE'
        (restrictionMap E E' hE'_sub y) =
      restrictionMap (imagePieceDatum D₀ E.T E.s hspanE)
        (imagePieceDatum D₀ E'.T E'.s hspanE')
        (imagePieceDatum_rationalOpen_mono D₀ E E' hspanE hspanE' hE'_sub)
        (relativePiece_equiv D₀ E hE_sub hspanE y) := by
  haveI hTateB : IsTateRing (presheafValue D₀) := presheafValue_isTateRing_faithful D₀
  haveI : IsNoetherianRing (presheafValue D₀) :=
    presheafValue_isNoetherianRing_faithful D₀
  haveI : IsHuberRing (presheafValue D₀) := hTateB.toIsHuberRing
  haveI : @CompleteSpace (presheafValue D₀)
      (IsTopologicalAddGroup.rightUniformSpace (presheafValue D₀)) :=
    presheafValue_completeSpace_rightUniformSpace D₀
  haveI : HasLocLiftPowerBounded (presheafValue D₀) := hasLocLiftPowerBounded_faithful
  haveI : IsStronglyNoetherian (presheafValue D₀) :=
    presheafValue_isStronglyNoetherian_faithful D₀
  haveI : IsHuberRing (presheafValue D₀) := hTateB.toIsHuberRing
  -- both composites, postcomposed with `E.coeRingHom`, agree as ring homs out of
  -- the localization (determined on the `algebraMap`-range by the trackings)
  have hloc :
      ((relativePiece_equiv D₀ E' (hE'_sub.trans hE_sub) hspanE') :
          presheafValue E' →+* presheafValue (imagePieceDatum D₀ E'.T E'.s hspanE')).comp
        ((restrictionMapHom E E' hE'_sub).comp E.coeRingHom) =
      ((restrictionMapHom (imagePieceDatum D₀ E.T E.s hspanE)
          (imagePieceDatum D₀ E'.T E'.s hspanE')
          (imagePieceDatum_rationalOpen_mono D₀ E E' hspanE hspanE' hE'_sub)).comp
        (((relativePiece_equiv D₀ E hE_sub hspanE) :
          presheafValue E →+* presheafValue (imagePieceDatum D₀ E.T E.s hspanE)).comp
          E.coeRingHom)) := by
    refine IsLocalization.ringHom_ext (Submonoid.powers E.s) ?_
    ext a
    simp only [RingHom.comp_apply, RingEquiv.coe_toRingHom]
    rw [show E.coeRingHom (algebraMap A (Localization.Away E.s) a) =
      E.canonicalMap a from rfl]
    rw [restrictionMapHom_canonicalMap E E' hE'_sub a]
    rw [show (E'.canonicalMap a : presheafValue E') =
        restrictionMapHom D₀ E' (hE'_sub.trans hE_sub) (D₀.canonicalMap a) from
      (restrictionMapHom_canonicalMap D₀ E' (hE'_sub.trans hE_sub) a).symm]
    rw [show (E.canonicalMap a : presheafValue E) =
        restrictionMapHom D₀ E hE_sub (D₀.canonicalMap a) from
      (restrictionMapHom_canonicalMap D₀ E hE_sub a).symm]
    rw [show (relativePiece_equiv D₀ E' (hE'_sub.trans hE_sub) hspanE')
          (restrictionMapHom D₀ E' (hE'_sub.trans hE_sub) (D₀.canonicalMap a)) =
        (imagePieceDatum D₀ E'.T E'.s hspanE').canonicalMap (D₀.canonicalMap a) from
      relativePiece_equiv_restrictionMap D₀ E' (hE'_sub.trans hE_sub) hspanE'
        (D₀.canonicalMap a)]
    rw [show (relativePiece_equiv D₀ E hE_sub hspanE)
          (restrictionMapHom D₀ E hE_sub (D₀.canonicalMap a)) =
        (imagePieceDatum D₀ E.T E.s hspanE).canonicalMap (D₀.canonicalMap a) from
      relativePiece_equiv_restrictionMap D₀ E hE_sub hspanE (D₀.canonicalMap a)]
    exact (restrictionMapHom_canonicalMap (imagePieceDatum D₀ E.T E.s hspanE)
      (imagePieceDatum D₀ E'.T E'.s hspanE')
      (imagePieceDatum_rationalOpen_mono D₀ E E' hspanE hspanE' hE'_sub)
      (D₀.canonicalMap a)).symm
  -- extend along the dense localization image by continuity (both composites are
  -- compositions of completion extensions) + T2
  letI : UniformSpace (Localization.Away E.s) := E.uniformSpace
  letI : IsTopologicalRing (Localization.Away E.s) := E.isTopologicalRing
  letI : IsUniformAddGroup (Localization.Away E.s) := E.isUniformAddGroup
  letI : UniformSpace (Localization.Away E'.s) := E'.uniformSpace
  letI : IsTopologicalRing (Localization.Away E'.s) := E'.isTopologicalRing
  letI : IsUniformAddGroup (Localization.Away E'.s) := E'.isUniformAddGroup
  letI : UniformSpace (Localization.Away
      (D₀.interSamePair (genPieceDatum D₀.P E'.T E'.s hspanE') rfl).s) :=
    (D₀.interSamePair (genPieceDatum D₀.P E'.T E'.s hspanE') rfl).uniformSpace
  letI : IsTopologicalRing (Localization.Away
      (D₀.interSamePair (genPieceDatum D₀.P E'.T E'.s hspanE') rfl).s) :=
    (D₀.interSamePair (genPieceDatum D₀.P E'.T E'.s hspanE') rfl).isTopologicalRing
  letI : IsUniformAddGroup (Localization.Away
      (D₀.interSamePair (genPieceDatum D₀.P E'.T E'.s hspanE') rfl).s) :=
    (D₀.interSamePair (genPieceDatum D₀.P E'.T E'.s hspanE') rfl).isUniformAddGroup
  letI : UniformSpace (Localization.Away
      (D₀.interSamePair (genPieceDatum D₀.P E.T E.s hspanE) rfl).s) :=
    (D₀.interSamePair (genPieceDatum D₀.P E.T E.s hspanE) rfl).uniformSpace
  letI : IsTopologicalRing (Localization.Away
      (D₀.interSamePair (genPieceDatum D₀.P E.T E.s hspanE) rfl).s) :=
    (D₀.interSamePair (genPieceDatum D₀.P E.T E.s hspanE) rfl).isTopologicalRing
  letI : IsUniformAddGroup (Localization.Away
      (D₀.interSamePair (genPieceDatum D₀.P E.T E.s hspanE) rfl).s) :=
    (D₀.interSamePair (genPieceDatum D₀.P E.T E.s hspanE) rfl).isUniformAddGroup
  letI : UniformSpace (Localization.Away (imagePieceDatum D₀ E.T E.s hspanE).s) :=
    (imagePieceDatum D₀ E.T E.s hspanE).uniformSpace
  letI : IsTopologicalRing
      (Localization.Away (imagePieceDatum D₀ E.T E.s hspanE).s) :=
    (imagePieceDatum D₀ E.T E.s hspanE).isTopologicalRing
  letI : IsUniformAddGroup
      (Localization.Away (imagePieceDatum D₀ E.T E.s hspanE).s) :=
    (imagePieceDatum D₀ E.T E.s hspanE).isUniformAddGroup
  refine @UniformSpace.Completion.ext' (Localization.Away E.s) E.uniformSpace
    (presheafValue (imagePieceDatum D₀ E'.T E'.s hspanE')) _ _ _ _
    (UniformSpace.Completion.continuous_extension.comp
      (UniformSpace.Completion.continuous_extension.comp
        UniformSpace.Completion.continuous_extension))
    (UniformSpace.Completion.continuous_extension.comp
      (UniformSpace.Completion.continuous_extension.comp
        UniformSpace.Completion.continuous_extension))
    ?_ y
  intro z
  exact RingHom.congr_fun hloc z

/-! ## Prop 8.30 (flatness of restriction) + Cor 8.32 (relocated from `Wedhorn828.lean`) -/

section Wedhorn828Tail

variable [HasLocLiftPowerBounded A]
variable [IsTateRing A] [IsNoetherianRing A] [IsStronglyNoetherian A] [T2Space A]
  [NonarchimedeanRing A] [CompatiblePlusSubring A]
  [letI : UniformSpace A := IsTopologicalAddGroup.rightUniformSpace A; CompleteSpace A]
-- The IRIE instance for completions (`presheafValuePlus_isRingOfIntegralElements`) now requires
-- the base affinoid interface `[IsRingOfIntegralElements (A⁺)]`; it is derivable from
-- `[CompatiblePlusSubring A]` but the multi-step instance synthesis is not auto-included, so we
-- thread it explicitly. (Diamond-free: `IsRingOfIntegralElements` is an all-`Prop` class.)
variable [IsRingOfIntegralElements (A⁺)]

/-- **Faithful per-step flatness for Prop 8.30 (Remark 7.55 basic-Laurent step).**

For a `LaurentNormalized` rational locale `D'` rationally contained in `E`, the restriction
`O_X(E) → O_X(D')` is flat as a `presheafValue E`-module along `restrictionMapHom E D' hsub`.

This is the FAITHFUL (case-(b), noeth-`A₀`-free) analogue of
`restrictionMap_flat_of_rational_subset_laurentNormalized` (`RestrictionFlatness.lean:1060`), which
routes through the case-(a) engine `presheafValue_flat_of_canonical` with
`(P : PairOfDefinition A) [IsNoetherianRing P.A₀]`. Here we instead use:

* the (noeth-`A₀`-free) relative Wedhorn-2.13 iso `relativeLaurentNormalized_equiv E D' hsub :
  presheafValue D' ≃+* presheafValue X̄` with `X̄ := relativeRationalLocData_laurentNormalized E D'
  hsub`, and its `restrictionMapHom ↔ X̄.canonicalMap` intertwining
  `relativeLaurentNormalized_equiv_intertwine`;
* the FAITHFUL Example-6.38 + Lemma-8.31 engine `presheafValue_flat_of_canonical_faithful` over the
  base `B := presheafValue E` (giving `Module.Flat B (presheafValue X̄)` along `X̄.canonicalMap`),
  which needs only `[IsStronglyNoetherian B]` + `[IsHuberRing B]` + `[CompatiblePlusSubring B]` —
  NO `hb`-via-whole-space, NO `[IsDomain]`, NO noeth-`A₀`;
* `Module.Flat.of_linearEquiv` to transport across the relative iso.

The two power-boundedness inputs are exactly Wedhorn's reduction guarantees for a basic-Laurent
step: `hb` (`invS X̄` power-bounded) from `1 ∈ X̄.T` (since `1 ∈ D'.T` by `LaurentNormalized` and
`E.canonicalMap 1 = 1 ∈ X̄.T = D'.T.image E.canonicalMap`), via `invS_isPowerBounded_of_one_mem_T`;
and `hT_pb` (each `t ∈ X̄.T` power-bounded) from `canonicalMap_isPowerBounded_of_mem_A₀` applied to
`E` (each `t ∈ X̄.T` is `E.canonicalMap t'` for `t' ∈ D'.T ⊆ D'.P.A₀ ⊆ E.P.A₀`).

**The flat-transport logic of this lemma is sorry-free.** The faithful engine
`presheafValue_flat_of_canonical_faithful` was `omit`-cleaned this session of
`[CompatiblePlusSubring A]` and `[HasLocLiftPowerBounded A]`, leaving it dependent only on
`[IsStronglyNoetherian B]` + `[IsHuberRing B]` + `[PlusSubring B]` — all available at `B :=
presheafValue E` (the last two automatically, since the ambient `A` carries `[PlusSubring A]` and
`IsTateRing B ⟶ IsHuberRing B`). So NO false `CompatiblePlusSubring B` instance is needed (that class
is false-in-general for a completion, as `RationalLocData.P` ranges over arbitrary pairs).

The lemma transitively carries `sorryAx` through exactly ONE faithful residual:
`presheafValue_mvRestricted_surjection` (the relative Example 6.38 surjection
`A⟨X₁..Xₙ₊ₘ⟩ ↠ (presheafValue E)⟨Y₁..Yₘ⟩`), via `presheafValue_isStronglyNoetherian_faithful`, which
installs the `IsStronglyNoetherian B` bundle member FAITHFULLY (Example 6.38). This REPLACES the
false `isStronglyNoetherian_of_isNoetherianRing_isTateRing` (the bare "noeth + Tate ⟹ strongly-noeth",
B2-retired 2026-06-05), so the strong-noeth here no longer depends on `_sub_lemma_L5_1_3_inductive_step`.
The relative-equiv transport itself
(`relativeLaurentNormalized_equiv` + `_intertwine` + the faithful engine + `Module.Flat.of_linearEquiv`)
is genuinely sorry-free.

The hypothesis `hD'_T_pb : ∀ t' ∈ D'.T, t' ∈ E.P.A₀` is NOT a work-deferral: power-boundedness of
each generator `t/s` (the `hT_pb` the Example-6.38 presentation genuinely requires) holds precisely
when `algebraMap t' ∈ locSubring E.P E.T E.s`, i.e. `t' ∈ E.P.A₀` — this is the standard
Wedhorn-Remark-7.32 / basic-Laurent side-condition "the Laurent generators lie in the ring of
definition", supplied by every caller (cf. `restrictionMap_flat_via_normalizedMinus`'s
`hf : f ∈ E₀.P.A₀`, `RestrictionFlatness.lean:1127`). -/
theorem prop_8_30_basic_laurent_step_flat
    (E D' : RationalLocData A) [LaurentNormalized D']
    (hsub : rationalOpen D'.T D'.s ⊆ rationalOpen E.T E.s)
    (hD'_T_pb : ∀ t' ∈ D'.T, t' ∈ E.P.A₀) :
    @Module.Flat (presheafValue E) (presheafValue D') _ _
      (restrictionMapHom E D' hsub).toModule := by
  classical
  -- Faithful Tate / strongly-noetherian / Huber bundle on `B := presheafValue E`.  The engine
  -- `presheafValue_flat_of_canonical_faithful` needs only `[IsStronglyNoetherian B]` + `[IsHuberRing
  -- B]` + `[PlusSubring B]` (verified this session by `omit`-cleaning its `[CompatiblePlusSubring A]`
  -- and `[HasLocLiftPowerBounded A]`).  `[PlusSubring B]` is the auto-derived
  -- `RationalLocData.presheafValuePlusSubring` (ambient `A` carries `[PlusSubring A]`); `[IsHuberRing
  -- B]` follows from `IsTateRing B`.  NO `[CompatiblePlusSubring B]` (which is false-in-general for a
  -- completion — `RationalLocData.P` is an arbitrary pair), NO noeth-`A₀`, NO `[IsDomain]`.
  letI hTateE : IsTateRing (presheafValue E) := presheafValue_isTateRing_concrete E
  haveI : IsNoetherianRing (presheafValue E) := presheafValue_isNoetherianRing_faithful E
  haveI : IsStronglyNoetherian (presheafValue E) :=
    presheafValue_isStronglyNoetherian_faithful E
  haveI : IsHuberRing (presheafValue E) := hTateE.toIsHuberRing
  letI : DecidableEq (presheafValue E) := Classical.decEq _
  -- The relative Wedhorn-2.13 locale `Xbar` (`X̄`) of `D'` over `B`.
  set Xbar : RationalLocData (presheafValue E) :=
    relativeRationalLocData_laurentNormalized E D' hsub with hXbar
  -- `hb`: `invS Xbar` is power-bounded since `1 ∈ Xbar.T`.
  have hone_mem : (1 : presheafValue E) ∈ Xbar.T := by
    rw [hXbar, relativeRationalLocData_laurentNormalized_T E D' hsub]
    rw [show (1 : presheafValue E) = E.canonicalMap (1 : A) from (map_one E.canonicalMap).symm]
    exact Finset.mem_image_of_mem _ LaurentNormalized.one_mem_T
  have hb : TopologicalRing.IsPowerBounded (invS Xbar) := by
    rw [invS_eq_coeRingHom_divByS_one]
    exact CompletionLocalization.invS_isPowerBounded_of_one_mem_T Xbar hone_mem
  -- `hT_pb`: each `t ∈ Xbar.T = D'.T.image E.canonicalMap` is `E.canonicalMap t'` with `t' ∈ E.P.A₀`.
  -- Power-boundedness of `E.canonicalMap t'` for `t' ∈ E.P.A₀`: all powers of `algebraMap t'` stay
  -- in `locSubring`, whose `coeRingHom`-image is bounded (inlined `canonicalMap_isPowerBounded_of_mem_A₀`,
  -- `TateAcyclicityFinalAssembly.lean:2524`, to avoid an import cycle — that file is downstream).
  have hT_pb : ∀ t ∈ Xbar.T, TopologicalRing.IsPowerBounded t := by
    intro t ht
    rw [hXbar, relativeRationalLocData_laurentNormalized_T E D' hsub,
      Finset.mem_image] at ht
    obtain ⟨t', ht'_mem, rfl⟩ := ht
    have ha : t' ∈ E.P.A₀ := hD'_T_pb t' ht'_mem
    have hcm : E.canonicalMap t' =
        E.coeRingHom (algebraMap A (Localization.Away E.s) t') := rfl
    rw [hcm]
    have hmem : algebraMap A (Localization.Away E.s) t' ∈ locSubring E.P E.T E.s :=
      algebraMap_mem_locSubring E.P E.T E.s ha
    have hpow : ∀ n : ℕ, (algebraMap A (Localization.Away E.s) t') ^ n ∈
        locSubring E.P E.T E.s :=
      fun n => (locSubring E.P E.T E.s).pow_mem hmem n
    have hrange : Set.range
        ((E.coeRingHom (algebraMap A (Localization.Away E.s) t')) ^ · :
          ℕ → presheafValue E) ⊆
        E.coeRingHom '' (locSubring E.P E.T E.s :
          Set (Localization.Away E.s)) := by
      rintro _ ⟨n, rfl⟩
      change (E.coeRingHom (algebraMap A (Localization.Away E.s) t')) ^ n ∈ _
      rw [← map_pow]
      exact ⟨(algebraMap A (Localization.Away E.s) t') ^ n, hpow n, rfl⟩
    exact (CompletionLocalization.coeRingHom_image_locSubring_isBounded E).subset hrange
  -- `hA_complete`: completeness of `B` w.r.t. the right-uniform structure.
  have hA_complete : @CompleteSpace (presheafValue E)
      (IsTopologicalAddGroup.rightUniformSpace (presheafValue E)) :=
    presheafValue_completeSpace_rightUniformSpace E
  -- Step 1 (FAITHFUL Example 6.38 + Lemma 8.31 over `B`): `presheafValue Xbar` is flat over `B` along
  -- `Xbar.canonicalMap`.  NO `hb`-via-whole-space, NO noeth-`A₀`, NO `[IsDomain]`.
  haveI hflat_Xbar :
      @Module.Flat (presheafValue E) (presheafValue Xbar) _ _
        (RingHom.toModule Xbar.canonicalMap) :=
    presheafValue_flat_of_canonical_faithful Xbar hb hA_complete hT_pb
  -- Step 2 (relative Wedhorn 2.13 + transport): the relative iso intertwines `restrictionMapHom`
  -- with `Xbar.canonicalMap`; transport flatness across it via `Module.Flat.of_linearEquiv`.
  let e := relativeLaurentNormalized_equiv E D' hsub
  change @Module.Flat (presheafValue E) (presheafValue D') _ _
    ((restrictionMapHom E D' hsub).toModule)
  letI : Module (presheafValue E) (presheafValue D') :=
    (restrictionMapHom E D' hsub).toModule
  letI : Module (presheafValue E) (presheafValue Xbar) :=
    RingHom.toModule Xbar.canonicalMap
  have he_smul : ∀ (a : presheafValue E) (x : presheafValue D'),
      e (a • x) = a • e x := by
    intro a x
    change e (restrictionMapHom E D' hsub a * x) = Xbar.canonicalMap a * e x
    rw [e.map_mul]
    congr 1
    exact relativeLaurentNormalized_equiv_intertwine E D' hsub a
  exact @Module.Flat.of_linearEquiv (presheafValue E)
    (presheafValue Xbar) (presheafValue D')
    _ _ _ _ _ hflat_Xbar
    { toLinearMap :=
        { toFun := e
          map_add' := e.map_add
          map_smul' := he_smul }
      invFun := e.symm
      left_inv := e.symm_apply_apply
      right_inv := e.apply_symm_apply }

omit [CompatiblePlusSubring A] in
/-- **A1a engine — `presheafValue(R(f/1))` is flat over `A`, ARBITRARY `f`** (Wedhorn Lemma 8.31(2),
fSubX shape). Transports the proven faithful `lemma_8_31_fSubX_flat` (`A⟨X⟩/(f − X)` flat over `A`,
`[IsNoetherianRing A]`-only, arbitrary `f`) across the faithful fSubX iso `unitDatum_quotEquiv`
(Wedhorn Example 6.38, the `R(f/1)` quotient comparison `presheafValue (unitDatum P f) ≃+* A⟨X⟩/(f −
X)`, relocated up to `Wedhorn828` so this upstream engine can consume it). This is the per-step engine
the Remark-7.55 chain needs where the new generator `f = tᵢ/s` is NOT power-bounded in the base — the
gap `prop_8_30_basic_laurent_step_flat` (which requires `D'.T ⊆ E.P.A₀`) cannot fill. NO `hT_pb`. All
instance hypotheses (incl. completeness) come from the `Wedhorn828Tail` section variables. -/
theorem presheafValue_flat_of_unitDatum_faithful (P : PairOfDefinition A) (f : A) :
    @Module.Flat A (presheafValue (unitDatum P f)) _ _
      (RingHom.toModule (unitDatum P f).canonicalMap) := by
  haveI hflat_quot : Module.Flat A (↥(TateAlgebra A) ⧸ unitDatumSpanIdeal (A := A) f) :=
    lemma_8_31_fSubX_flat (A := A) f
  let e := unitDatum_quotEquiv P f
  change @Module.Flat A (presheafValue (unitDatum P f)) _ _
    (RingHom.toModule (unitDatum P f).canonicalMap)
  letI : Module A (presheafValue (unitDatum P f)) :=
    RingHom.toModule (unitDatum P f).canonicalMap
  have he_smul : ∀ (a : A) (x : presheafValue (unitDatum P f)), e (a • x) = a • e x := by
    intro a x
    change e ((unitDatum P f).canonicalMap a * x) =
      (Ideal.Quotient.mk (unitDatumSpanIdeal (A := A) f))
        (algebraMap A ↥(TateAlgebra A) a) * e x
    rw [e.map_mul]; congr 1
    exact unitDatum_quotEquiv_canonicalMap P f a
  exact @Module.Flat.of_linearEquiv A
    (↥(TateAlgebra A) ⧸ unitDatumSpanIdeal (A := A) f)
    (presheafValue (unitDatum P f)) _ _ _ _ _ hflat_quot
    { toLinearMap := { toFun := e, map_add' := e.map_add, map_smul' := he_smul }
      invFun := e.symm
      left_inv := e.symm_apply_apply
      right_inv := e.apply_symm_apply }

omit [CompatiblePlusSubring A] in
/-- **coUnit engine — `presheafValue(R(1/f))` is flat over `A`, ARBITRARY `f`** (Wedhorn Lemma 8.31(2),
oneSubfX shape; the dual of `presheafValue_flat_of_unitDatum_faithful`). Transports the proven
`lemma_8_31_oneSubfX_flat` (`A⟨X⟩/(1 − fX)` flat over `A`) across the faithful oneSubfX iso
`coUnitDatum_quotEquiv` (`presheafValue (coUnitDatum P f) ≃+* A⟨X⟩/(1 − fX)`). This is the
dominating-unit base step `X₀ = {1 ≤ x(s/u)} = coUnitDatum(s·u⁻¹)` of the Remark-7.55 chain. -/
theorem presheafValue_flat_of_coUnitDatum_faithful (P : PairOfDefinition A) (f : A) :
    @Module.Flat A (presheafValue (coUnitDatum P f)) _ _
      (RingHom.toModule (coUnitDatum P f).canonicalMap) := by
  haveI hflat_quot : Module.Flat A (↥(TateAlgebra A) ⧸ coUnitDatumSpanIdeal (A := A) f) :=
    lemma_8_31_oneSubfX_flat (A := A) f
  let e := coUnitDatum_quotEquiv P f
  change @Module.Flat A (presheafValue (coUnitDatum P f)) _ _
    (RingHom.toModule (coUnitDatum P f).canonicalMap)
  letI : Module A (presheafValue (coUnitDatum P f)) :=
    RingHom.toModule (coUnitDatum P f).canonicalMap
  have he_smul : ∀ (a : A) (x : presheafValue (coUnitDatum P f)), e (a • x) = a • e x := by
    intro a x
    change e ((coUnitDatum P f).canonicalMap a * x) =
      (Ideal.Quotient.mk (coUnitDatumSpanIdeal (A := A) f))
        (algebraMap A ↥(TateAlgebra A) a) * e x
    rw [e.map_mul]; congr 1
    exact coUnitDatum_quotEquiv_canonicalMap P f a
  exact @Module.Flat.of_linearEquiv A
    (↥(TateAlgebra A) ⧸ coUnitDatumSpanIdeal (A := A) f)
    (presheafValue (coUnitDatum P f)) _ _ _ _ _ hflat_quot
    { toLinearMap := { toFun := e, map_add' := e.map_add, map_smul' := he_smul }
      invFun := e.symm
      left_inv := e.symm_apply_apply
      right_inv := e.apply_symm_apply }

omit [CompatiblePlusSubring A] in
/-- **Remark 7.55, step 0 — the dominating unit over `B = 𝒪_X(D)`** (Wedhorn p.70: *"Since `U` is
quasi-compact, there exists by Corollary 7.32 a unit `u ∈ A×` such that `|u(x)| < |s(x)|` for all
`x ∈ U`"*). For the image piece `W := imagePieceDatum D E.T E.s hspanE` of the whole space `Spa B`,
there is a unit `u ∈ B×` strictly dominated by the denominator `W.s` on `rationalOpen W` — the
witness for the base `X₀ = {1 ≤ x(W.s/u)}` of the Remark-7.55 chain. Proven via the singleton
Cor 7.32 (`exists_dominating_unit_noHArch`, sorry-free) at `B`, on the quasi-compact `rationalOpen W`
(`isCompact_preimage_rationalOpen_noHArch`); `W.s ≠ 0` on `rationalOpen W` by definition. -/
theorem remark755_dominating_unit_over_presheafValue
    (D E : RationalLocData A) (hspanE : Ideal.span (E.T : Set A) = ⊤) :
    ∃ u : (presheafValue D)ˣ,
      ∀ y : ↥(Spa (presheafValue D) (presheafValue D)⁺),
        (y.1 : Spv (presheafValue D)) ∈
          rationalOpen (imagePieceDatum D E.T E.s hspanE).T (imagePieceDatum D E.T E.s hspanE).s →
        (y.1.vle (u : presheafValue D) (imagePieceDatum D E.T E.s hspanE).s ∧
         ¬ y.1.vle (imagePieceDatum D E.T E.s hspanE).s (u : presheafValue D)) := by
  haveI hTate : IsTateRing (presheafValue D) := presheafValue_isTateRing_concrete D
  haveI : IsHuberRing (presheafValue D) := hTate.toIsHuberRing
  set W := imagePieceDatum D E.T E.s hspanE with hW
  have hW_rat : W.IsRational := by
    rw [hW]
    exact imagePieceDatum_isRational D E.T E.s hspanE
  have hY := isCompact_preimage_rationalOpen_noHArch (A := presheafValue D)
    (IsRingOfIntegralElements.isOpen
      (B := ((presheafValue D)⁺ : Subring (presheafValue D)))) W hW_rat
  obtain ⟨u, hu⟩ := exists_dominating_unit_noHArch (A := presheafValue D) hY W.s
    (fun y hy => (Set.mem_preimage.mp hy).2.2)
  exact ⟨u, fun y hy => hu y (Set.mem_preimage.mpr hy)⟩

omit [CompatiblePlusSubring A] in
/-- **`s`-absorption `rationalOpen` equality** (Remark 7.55 single-step over `B = 𝒪_X(D₀)`).
The image piece `imagePieceDatum D₀ {f, s} s` (the `genPiece` with the denominator `s` included
among the generators, so `span{f,s} = ⊤` is free) has the SAME `rationalOpen` over `Spa B` as the
single `unitDatum (canMap f · (canMap s)⁻¹)`: the `canMap s`-generator constraint `w.vle (canMap s)
(canMap s)` is reflexivity (vacuous), `¬w.vle (canMap s) 0` holds since `canMap s` is a unit, and
`w.vle (canMap f)(canMap s) ⟺ w.vle (canMap f·(canMap s)⁻¹) 1` by unit cancellation. Isolated `sorry`
(the `vle` set-equality; all constraints are free for Spa points). -/
theorem imagePieceDatum_denomGen_rationalOpen_eq [DecidableEq A] (D₀ : RationalLocData A) (f s : A)
    (hspan : Ideal.span (({f, s} : Finset A) : Set A) = ⊤)
    (hs_unit : IsUnit (D₀.canonicalMap s)) :
    rationalOpen (imagePieceDatum D₀ {f, s} s hspan).T (imagePieceDatum D₀ {f, s} s hspan).s =
      rationalOpen ({D₀.canonicalMap f * Ring.inverse (D₀.canonicalMap s)} : Finset (presheafValue D₀)) 1 := by
  letI hTateB : IsTateRing (presheafValue D₀) := presheafValue_isTateRing_concrete D₀
  letI : DecidableEq (presheafValue D₀) := Classical.decEq _
  have hT : (imagePieceDatum D₀ {f, s} s hspan).T = ({f, s} : Finset A).image D₀.canonicalMap := rfl
  have hSs : (imagePieceDatum D₀ {f, s} s hspan).s = D₀.canonicalMap s := rfl
  set cs := D₀.canonicalMap s with hcs
  set cf := D₀.canonicalMap f with hcf
  have hsi : cs * Ring.inverse cs = 1 := Ring.mul_inverse_cancel cs hs_unit
  have his : Ring.inverse cs * cs = 1 := Ring.inverse_mul_cancel cs hs_unit
  rw [hT, hSs]
  apply Set.ext
  intro w
  rw [rationalOpen, rationalOpen, Set.mem_sep_iff, Set.mem_sep_iff]
  refine and_congr_right fun _ => ?_
  constructor
  · rintro ⟨hgen, _⟩
    refine ⟨?_, not_vle_zero_of_isUnit isUnit_one w⟩
    intro t ht
    rw [Finset.mem_singleton] at ht; subst ht
    have hcf : w.vle cf cs :=
      hgen cf (Finset.mem_image_of_mem _ (Finset.mem_insert_self f {s}))
    have h2 := w.mul_vle_mul_left hcf (Ring.inverse cs)
    rwa [hsi] at h2
  · rintro ⟨hg, _⟩
    refine ⟨?_, not_vle_zero_of_isUnit hs_unit w⟩
    intro t ht
    rw [Finset.mem_image] at ht
    obtain ⟨x, hx, rfl⟩ := ht
    have hg1 : w.vle (cf * Ring.inverse cs) 1 := hg _ (Finset.mem_singleton_self _)
    rw [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · have h2 := w.mul_vle_mul_left hg1 cs
      rw [one_mul, mul_assoc, his, mul_one] at h2
      exact h2
    · exact w.vle_refl cs

omit [CompatiblePlusSubring A] in
/-- **domUnit `rationalOpen`-eq (Remark 7.55 chain step over `B`, two-level)** — the image piece
`imagePieceDatum D₀ {g, ↑u, s} s` (denominator `s`, generators `g`, the *unit* `↑u`, and `s`; so
`span{g,↑u,s} = ⊤` is free via `↑u`) has the SAME `rationalOpen` over `Spa B` as the single
`unitDatum (canMap g · (canMap s)⁻¹)`. The `↑u`-generator constraint `w.vle (canMap ↑u)(canMap s)` is
REDUNDANT: every Spa-`B` point `w` pulls back (`comap_canonicalMap_mem_rationalOpen`) to a point of
`rationalOpen D₀`, where `h_dom` (the chain invariant `D₀ ⊆ {x(u) ≤ x(s)}`) forces `↑u ≤ᵥ s`; the
`s`-generator is reflexive and `¬w.vle (canMap s) 0` holds since `canMap s` is a unit. This is the
domUnit analogue of `imagePieceDatum_denomGen_rationalOpen_eq` — it lets the chain run at base `B`
(span⊤ from the unit `↑u`, not from `s` being a unit), keeping every piece two-level. -/
theorem imagePieceDatum_domUnit_rationalOpen_eq [DecidableEq A] (D₀ : RationalLocData A) (g s u : A)
    (hspan : Ideal.span (({g, u} : Finset A) : Set A) = ⊤)
    (hs_unit : IsUnit (D₀.canonicalMap s))
    (h_pb : D₀.canonicalMap u * Ring.inverse (D₀.canonicalMap s) ∈ (presheafValue D₀)⁺) :
    rationalOpen (imagePieceDatum D₀ {g, u} s hspan).T
        (imagePieceDatum D₀ {g, u} s hspan).s =
      rationalOpen ({D₀.canonicalMap g * Ring.inverse (D₀.canonicalMap s)} :
        Finset (presheafValue D₀)) 1 := by
  letI hTateB : IsTateRing (presheafValue D₀) := presheafValue_isTateRing_concrete D₀
  letI : DecidableEq (presheafValue D₀) := Classical.decEq _
  have hT : (imagePieceDatum D₀ {g, u} s hspan).T =
      ({g, u} : Finset A).image D₀.canonicalMap := rfl
  have hSs : (imagePieceDatum D₀ {g, u} s hspan).s = D₀.canonicalMap s := rfl
  set cs := D₀.canonicalMap s with hcs
  set cg := D₀.canonicalMap g with hcg
  have hsi : cs * Ring.inverse cs = 1 := Ring.mul_inverse_cancel cs hs_unit
  have his : Ring.inverse cs * cs = 1 := Ring.inverse_mul_cancel cs hs_unit
  rw [hT, hSs]
  apply Set.ext
  intro w
  rw [rationalOpen, rationalOpen, Set.mem_sep_iff, Set.mem_sep_iff]
  refine and_congr_right fun hspa => ?_
  constructor
  · rintro ⟨hgen, _⟩
    refine ⟨?_, not_vle_zero_of_isUnit isUnit_one w⟩
    intro t ht
    rw [Finset.mem_singleton] at ht; subst ht
    have hcgs : w.vle cg cs :=
      hgen cg (Finset.mem_image_of_mem _ (Finset.mem_insert_self g {u}))
    have h2 := w.mul_vle_mul_left hcgs (Ring.inverse cs)
    rwa [hsi] at h2
  · rintro ⟨hg, _⟩
    refine ⟨?_, not_vle_zero_of_isUnit hs_unit w⟩
    intro t ht
    rw [Finset.mem_image] at ht
    obtain ⟨x, hx, rfl⟩ := ht
    have hg1 : w.vle (cg * Ring.inverse cs) 1 := hg _ (Finset.mem_singleton_self _)
    rw [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · have h2 := w.mul_vle_mul_left hg1 cs
      rw [one_mul, mul_assoc, his, mul_one] at h2
      exact h2
    · have hle := vle_one_of_mem_spa hspa h_pb
      have h2 := w.mul_vle_mul_left hle cs
      rw [one_mul, mul_assoc, his, mul_one] at h2
      exact h2

omit [CompatiblePlusSubring A] in
/-- **Per-step core (Remark 7.55, the A1a fSubX step over `B`)** — `𝒪_B(imagePieceDatum D₀ {f,s} s)`
is flat over `B = presheafValue D₀`. The image piece equals (same `rationalOpen`, by
`imagePieceDatum_denomGen_rationalOpen_eq`) the single `unitDatum (canMap f·(canMap s)⁻¹)`, which is
flat over `B` by the arbitrary-`f` engine `presheafValue_flat_of_unitDatum_faithful`; flatness
transports across the restriction iso (which intertwines the two `canonicalMap`s). This is the genuine
per-step the Remark-7.55 chain folds; the denominator `s` need not be power-bounded. -/
theorem flat_imagePieceDatum_denomGen [DecidableEq A] (D₀ : RationalLocData A) (f s : A)
    (hspan : Ideal.span (({f, s} : Finset A) : Set A) = ⊤)
    (hs_unit : IsUnit (D₀.canonicalMap s)) :
    @Module.Flat (presheafValue D₀) (presheafValue (imagePieceDatum D₀ {f, s} s hspan)) _ _
      (RingHom.toModule (imagePieceDatum D₀ {f, s} s hspan).canonicalMap) := by
  classical
  letI hTateB : IsTateRing (presheafValue D₀) := presheafValue_isTateRing_concrete D₀
  haveI : IsNoetherianRing (presheafValue D₀) := presheafValue_isNoetherianRing_faithful D₀
  haveI : IsStronglyNoetherian (presheafValue D₀) := presheafValue_isStronglyNoetherian_faithful D₀
  haveI : IsHuberRing (presheafValue D₀) := hTateB.toIsHuberRing
  letI : DecidableEq (presheafValue D₀) := Classical.decEq _
  haveI hCompleteB : @CompleteSpace (presheafValue D₀)
      (IsTopologicalAddGroup.rightUniformSpace (presheafValue D₀)) :=
    presheafValue_completeSpace_rightUniformSpace D₀
  -- FAITHFUL re-wiring: shadow the generic `hasLocLiftPowerBounded_of_stronglyNoetherianTate`
  -- instance (whose 2 fields are opaque sorries 7.52(2)/7.41) with the source-justified faithful
  -- route (7.51(2) + [Hu2] 3.3); the internal `restrictionMapHom W U`/`restrictionMap_bijective`
  -- over `presheafValue D₀` (in `e` below) then route through it. The conclusion is about
  -- `W.canonicalMap` (instance-independent), so this is diamond-free.
  haveI : HasLocLiftPowerBounded (presheafValue D₀) := hasLocLiftPowerBounded_faithful
  set g : presheafValue D₀ := D₀.canonicalMap f * Ring.inverse (D₀.canonicalMap s) with hg
  set W := imagePieceDatum D₀ {f, s} s hspan with hW
  set U : RationalLocData (presheafValue D₀) :=
    unitDatum (presheafValue_concretePair D₀) g with hU
  -- The image piece and the unit datum have equal `rationalOpen` (the `s`-absorption).
  have h_ro : rationalOpen W.T W.s = rationalOpen U.T U.s := by
    rw [hW, hU]
    change rationalOpen (imagePieceDatum D₀ {f, s} s hspan).T
        (imagePieceDatum D₀ {f, s} s hspan).s =
      rationalOpen ({g} : Finset (presheafValue D₀)) 1
    rw [hg]; exact imagePieceDatum_denomGen_rationalOpen_eq D₀ f s hspan hs_unit
  -- `𝒪(U) = 𝒪(unitDatum g)` is flat over `B` by the arbitrary-`f` engine.
  haveI hflat_U : @Module.Flat (presheafValue D₀) (presheafValue U) _ _
      (RingHom.toModule U.canonicalMap) := by
    rw [hU]; exact presheafValue_flat_of_unitDatum_faithful (presheafValue_concretePair D₀) g
  -- Transport flatness across the restriction iso `e : 𝒪(W) ≃+* 𝒪(U)` (equal `rationalOpen`),
  -- which intertwines `W.canonicalMap` with `U.canonicalMap` (`restrictionMapHom_canonicalMap`).
  let e : presheafValue W ≃+* presheafValue U :=
    RingEquiv.ofBijective (restrictionMapHom W U h_ro.symm.le)
      (restrictionMap_bijective_of_rationalOpen_eq W U h_ro)
  letI : Module (presheafValue D₀) (presheafValue W) := RingHom.toModule W.canonicalMap
  letI : Module (presheafValue D₀) (presheafValue U) := RingHom.toModule U.canonicalMap
  have he_smul : ∀ (a : presheafValue D₀) (x : presheafValue W), e (a • x) = a • e x := by
    intro a x
    change e (W.canonicalMap a * x) = U.canonicalMap a * e x
    rw [e.map_mul]; congr 1
    change restrictionMapHom W U h_ro.symm.le (W.canonicalMap a) = U.canonicalMap a
    exact restrictionMapHom_canonicalMap W U h_ro.symm.le a
  exact @Module.Flat.of_linearEquiv (presheafValue D₀) (presheafValue U) (presheafValue W)
    _ _ _ _ _ hflat_U
    { toLinearMap := { toFun := e, map_add' := e.map_add, map_smul' := he_smul }
      invFun := e.symm
      left_inv := e.symm_apply_apply
      right_inv := e.apply_symm_apply }

omit [CompatiblePlusSubring A] in
/-- **Per-step of the Remark 7.55 chain** — `flat(𝒪(D₀ ∩ R({g,s}/s)) over 𝒪 D₀)` when `s` is a unit
on `𝒪 D₀`. The step locale `D₀.interSamePair (genPieceDatum D₀.P {g,s} s)` has structure ring
`≅ 𝒪_{𝒪 D₀}(imagePieceDatum D₀ {g,s} s)` (`genPiece_relative_equiv`, Wedhorn Prop 8.2), flat over `𝒪 D₀`
by `flat_imagePieceDatum_denomGen` (s-absorption + fSubX engine); the iso intertwines restriction with
`canonicalMap` (`genPiece_relative_equiv_restrictionMap`), transporting flatness. -/
theorem flat_chainStep [DecidableEq A] (D₀ : RationalLocData A) (g s : A)
    (hspan : Ideal.span (({g, s} : Finset A) : Set A) = ⊤)
    (hs_unit : IsUnit (D₀.canonicalMap s)) :
    @Module.Flat (presheafValue D₀)
      (presheafValue (D₀.interSamePair (genPieceDatum D₀.P {g, s} s hspan) rfl)) _ _
      (restrictionMapHom D₀ (D₀.interSamePair (genPieceDatum D₀.P {g, s} s hspan) rfl)
        (RationalLocData.interSamePair_subset_left _ _ _)).toModule := by
  set D' := D₀.interSamePair (genPieceDatum D₀.P {g, s} s hspan) rfl with hD'
  set Wimg := imagePieceDatum D₀ {g, s} s hspan with hWimg
  haveI hflat_img : @Module.Flat (presheafValue D₀) (presheafValue Wimg) _ _
      (RingHom.toModule Wimg.canonicalMap) :=
    flat_imagePieceDatum_denomGen D₀ g s hspan hs_unit
  let e := genPiece_relative_equiv D₀ {g, s} s hspan
  letI : Module (presheafValue D₀) (presheafValue D') :=
    (restrictionMapHom D₀ D' (RationalLocData.interSamePair_subset_left _ _ _)).toModule
  letI : Module (presheafValue D₀) (presheafValue Wimg) := RingHom.toModule Wimg.canonicalMap
  have he_smul : ∀ (a : presheafValue D₀) (x : presheafValue D'), e (a • x) = a • e x := by
    intro a x
    change e (restrictionMapHom D₀ D' (RationalLocData.interSamePair_subset_left _ _ _) a * x) =
      Wimg.canonicalMap a * e x
    rw [e.map_mul]; congr 1
    exact genPiece_relative_equiv_restrictionMap D₀ {g, s} s hspan a
  exact @Module.Flat.of_linearEquiv (presheafValue D₀)
    (presheafValue Wimg) (presheafValue D')
    _ _ _ _ _ hflat_img
    { toLinearMap := { toFun := e, map_add' := e.map_add, map_smul' := he_smul }
      invFun := e.symm
      left_inv := e.symm_apply_apply
      right_inv := e.apply_symm_apply }

omit [CompatiblePlusSubring A] in
/-- **domUnit per-step core** — `𝒪_B(imagePieceDatum D₀ {g,u} s)` is flat over `B`, when `s` is a unit
on `B` and the unit `u` is dominated by `s` on `rationalOpen D₀` (`h_dom`). The image piece equals the
single `unitDatum (canMap g · (canMap s)⁻¹)` (`imagePieceDatum_domUnit_rationalOpen_eq`, the
`u`-redundancy), flat over `B` by the arbitrary-`f` engine; flatness transports across the restriction
iso. The domUnit analogue of `flat_imagePieceDatum_denomGen` — keeps the chain at base `B` (span⊤ from
the unit `u`, not from `s` being a unit). -/
theorem flat_imagePieceDatum_domUnit [DecidableEq A] (D₀ : RationalLocData A) (g s u : A)
    (hspan : Ideal.span (({g, u} : Finset A) : Set A) = ⊤)
    (hs_unit : IsUnit (D₀.canonicalMap s))
    (h_pb : D₀.canonicalMap u * Ring.inverse (D₀.canonicalMap s) ∈ (presheafValue D₀)⁺) :
    @Module.Flat (presheafValue D₀) (presheafValue (imagePieceDatum D₀ {g, u} s hspan)) _ _
      (RingHom.toModule (imagePieceDatum D₀ {g, u} s hspan).canonicalMap) := by
  classical
  letI hTateB : IsTateRing (presheafValue D₀) := presheafValue_isTateRing_concrete D₀
  haveI : IsNoetherianRing (presheafValue D₀) := presheafValue_isNoetherianRing_faithful D₀
  haveI : IsStronglyNoetherian (presheafValue D₀) := presheafValue_isStronglyNoetherian_faithful D₀
  haveI : IsHuberRing (presheafValue D₀) := hTateB.toIsHuberRing
  letI : DecidableEq (presheafValue D₀) := Classical.decEq _
  haveI hCompleteB : @CompleteSpace (presheafValue D₀)
      (IsTopologicalAddGroup.rightUniformSpace (presheafValue D₀)) :=
    presheafValue_completeSpace_rightUniformSpace D₀
  -- FAITHFUL re-wiring (see `flat_imagePieceDatum_denomGen`): route the internal
  -- `restrictionMapHom`-over-`presheafValue D₀` through the source-justified faithful `HasLocLift`.
  haveI : HasLocLiftPowerBounded (presheafValue D₀) := hasLocLiftPowerBounded_faithful
  set gg : presheafValue D₀ := D₀.canonicalMap g * Ring.inverse (D₀.canonicalMap s) with hgg
  set W := imagePieceDatum D₀ {g, u} s hspan with hW
  set U : RationalLocData (presheafValue D₀) :=
    unitDatum (presheafValue_concretePair D₀) gg with hU
  have h_ro : rationalOpen W.T W.s = rationalOpen U.T U.s := by
    rw [hW, hU]
    change rationalOpen (imagePieceDatum D₀ {g, u} s hspan).T
        (imagePieceDatum D₀ {g, u} s hspan).s =
      rationalOpen ({gg} : Finset (presheafValue D₀)) 1
    rw [hgg]; exact imagePieceDatum_domUnit_rationalOpen_eq D₀ g s u hspan hs_unit h_pb
  haveI hflat_U : @Module.Flat (presheafValue D₀) (presheafValue U) _ _
      (RingHom.toModule U.canonicalMap) := by
    rw [hU]; exact presheafValue_flat_of_unitDatum_faithful (presheafValue_concretePair D₀) gg
  let e : presheafValue W ≃+* presheafValue U :=
    RingEquiv.ofBijective (restrictionMapHom W U h_ro.symm.le)
      (restrictionMap_bijective_of_rationalOpen_eq W U h_ro)
  letI : Module (presheafValue D₀) (presheafValue W) := RingHom.toModule W.canonicalMap
  letI : Module (presheafValue D₀) (presheafValue U) := RingHom.toModule U.canonicalMap
  have he_smul : ∀ (a : presheafValue D₀) (x : presheafValue W), e (a • x) = a • e x := by
    intro a x
    change e (W.canonicalMap a * x) = U.canonicalMap a * e x
    rw [e.map_mul]; congr 1
    change restrictionMapHom W U h_ro.symm.le (W.canonicalMap a) = U.canonicalMap a
    exact restrictionMapHom_canonicalMap W U h_ro.symm.le a
  exact @Module.Flat.of_linearEquiv (presheafValue D₀) (presheafValue U) (presheafValue W)
    _ _ _ _ _ hflat_U
    { toLinearMap := { toFun := e, map_add' := e.map_add, map_smul' := he_smul }
      invFun := e.symm
      left_inv := e.symm_apply_apply
      right_inv := e.apply_symm_apply }

omit [CompatiblePlusSubring A] in
/-- **domUnit chain step (Remark 7.55, two-level over `B`)** — `flat(𝒪(D₀ ∩ R({g,u}/s)) over 𝒪 D₀)`
when `s` is a unit on `𝒪 D₀` and the unit `u` is dominated by `s` on `rationalOpen D₀`. Span⊤ comes
from the UNIT `u` (not from `s`), so this applies at base `B` where `s = canMap E.s` is NOT a unit —
keeping every chain piece two-level. The step locale `≅ 𝒪_{𝒪 D₀}(imagePieceDatum D₀ {g,u} s)`
(`genPiece_relative_equiv`), flat by `flat_imagePieceDatum_domUnit`; transported across the restriction
iso. The domUnit analogue of `flat_chainStep`. -/
theorem flat_chainStep_domUnit [DecidableEq A] (D₀ : RationalLocData A) (g s u : A)
    (hspan : Ideal.span (({g, u} : Finset A) : Set A) = ⊤)
    (hs_unit : IsUnit (D₀.canonicalMap s))
    (h_pb : D₀.canonicalMap u * Ring.inverse (D₀.canonicalMap s) ∈ (presheafValue D₀)⁺) :
    @Module.Flat (presheafValue D₀)
      (presheafValue (D₀.interSamePair (genPieceDatum D₀.P {g, u} s hspan) rfl)) _ _
      (restrictionMapHom D₀ (D₀.interSamePair (genPieceDatum D₀.P {g, u} s hspan) rfl)
        (RationalLocData.interSamePair_subset_left _ _ _)).toModule := by
  set D' := D₀.interSamePair (genPieceDatum D₀.P {g, u} s hspan) rfl with hD'
  set Wimg := imagePieceDatum D₀ {g, u} s hspan with hWimg
  haveI hflat_img : @Module.Flat (presheafValue D₀) (presheafValue Wimg) _ _
      (RingHom.toModule Wimg.canonicalMap) :=
    flat_imagePieceDatum_domUnit D₀ g s u hspan hs_unit h_pb
  let e := genPiece_relative_equiv D₀ {g, u} s hspan
  letI : Module (presheafValue D₀) (presheafValue D') :=
    (restrictionMapHom D₀ D' (RationalLocData.interSamePair_subset_left _ _ _)).toModule
  letI : Module (presheafValue D₀) (presheafValue Wimg) := RingHom.toModule Wimg.canonicalMap
  have he_smul : ∀ (a : presheafValue D₀) (x : presheafValue D'), e (a • x) = a • e x := by
    intro a x
    change e (restrictionMapHom D₀ D' (RationalLocData.interSamePair_subset_left _ _ _) a * x) =
      Wimg.canonicalMap a * e x
    rw [e.map_mul]; congr 1
    exact genPiece_relative_equiv_restrictionMap D₀ {g, u} s hspan a
  exact @Module.Flat.of_linearEquiv (presheafValue D₀)
    (presheafValue Wimg) (presheafValue D')
    _ _ _ _ _ hflat_img
    { toLinearMap := { toFun := e, map_add' := e.map_add, map_smul' := he_smul }
      invFun := e.symm
      left_inv := e.symm_apply_apply
      right_inv := e.apply_symm_apply }

omit [CompatiblePlusSubring A] in
/-- **X₁ coUnit step over `B = 𝒪_X(D)`** (Remark 7.55 dominating-unit base): `𝒪_B(coUnitDatum f)`
is flat over `B`, for any `f ∈ B`. The coUnit engine `presheafValue_flat_of_coUnitDatum_faithful`
instantiated at the base `B = presheafValue D` (with `B`'s faithful bundle). Separated as its own
lemma so the chain assembly composes it by reference (avoiding inline `whnf` on the nested
`presheafValue`). -/
theorem flat_presheafValue_coUnitDatum_at_base (D : RationalLocData A) (f : presheafValue D) :
    @Module.Flat (presheafValue D)
      (presheafValue (coUnitDatum (presheafValue_concretePair D) f)) _ _
      (RingHom.toModule (coUnitDatum (presheafValue_concretePair D) f).canonicalMap) := by
  letI hTateB : IsTateRing (presheafValue D) := presheafValue_isTateRing_concrete D
  haveI : IsNoetherianRing (presheafValue D) := presheafValue_isNoetherianRing_faithful D
  haveI : IsStronglyNoetherian (presheafValue D) := presheafValue_isStronglyNoetherian_faithful D
  haveI : IsHuberRing (presheafValue D) := hTateB.toIsHuberRing
  haveI hCompleteB : @CompleteSpace (presheafValue D)
      (IsTopologicalAddGroup.rightUniformSpace (presheafValue D)) :=
    presheafValue_completeSpace_rightUniformSpace D
  exact presheafValue_flat_of_coUnitDatum_faithful (presheafValue_concretePair D) f

section
open Classical
omit [CompatiblePlusSubring A]

/-- **genPieceUnit `rationalOpen`-eq** — `R({↑u}/sB) = R({1}/(sB·↑u⁻¹))` for `↑u` a unit
(`x(↑u) ≤ x(sB) ⟺ x(1) ≤ x(sB·↑u⁻¹)`, unit cancellation). Extracted so the engine's `h_ro` is
a one-liner (matching `imagePieceDatum_domUnit_rationalOpen_eq`'s structure). -/
theorem genPieceUnit_coUnit_rationalOpen_eq (P : PairOfDefinition A) (u : Aˣ) (sB : A)
    (hspan : Ideal.span (({(↑u : A)} : Finset A) : Set A) = ⊤) :
    rationalOpen (genPieceDatum P {(↑u : A)} sB hspan).T (genPieceDatum P {(↑u : A)} sB hspan).s =
      rationalOpen (coUnitDatum P (sB * ↑u⁻¹)).T (coUnitDatum P (sB * ↑u⁻¹)).s := by
  classical
  have hui : (↑u : A) * (↑u⁻¹ : A) = 1 := by rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hiu : (↑u⁻¹ : A) * (↑u : A) = 1 := by rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hWT : (genPieceDatum P {(↑u : A)} sB hspan).T = {(↑u : A)} := rfl
  have hWs : (genPieceDatum P {(↑u : A)} sB hspan).s = sB := rfl
  have hUT : (coUnitDatum P (sB * ↑u⁻¹)).T = {(1 : A)} := rfl
  have hUs : (coUnitDatum P (sB * ↑u⁻¹)).s = sB * ↑u⁻¹ := rfl
  rw [hWT, hWs, hUT, hUs]
  apply Set.ext
  intro w
  rw [rationalOpen, rationalOpen, Set.mem_sep_iff, Set.mem_sep_iff]
  refine and_congr_right fun hspa => ?_
  constructor
  · rintro ⟨hgen, hnz⟩
    have h1 : w.vle (↑u : A) sB := hgen _ (Finset.mem_singleton_self _)
    refine ⟨fun t ht => ?_, ?_⟩
    · rw [Finset.mem_singleton] at ht; subst ht
      have h2 := w.mul_vle_mul_left h1 (↑u⁻¹ : A)
      rwa [hui] at h2
    · intro h0
      exact hnz (by have h2 := w.mul_vle_mul_left h0 (↑u : A)
                    rwa [mul_assoc, hiu, mul_one, zero_mul] at h2)
  · rintro ⟨hgen, hnz⟩
    have h1 : w.vle (1 : A) (sB * ↑u⁻¹) := hgen _ (Finset.mem_singleton_self _)
    refine ⟨fun t ht => ?_, ?_⟩
    · rw [Finset.mem_singleton] at ht; subst ht
      have h2 := w.mul_vle_mul_left h1 (↑u : A)
      rwa [one_mul, mul_assoc, hiu, mul_one] at h2
    · intro h0
      exact hnz (by have h2 := w.mul_vle_mul_left h0 (↑u⁻¹ : A)
                    rwa [zero_mul] at h2)

/-- **Flat transport across equal `rationalOpen`** — generic in `D₁ D₂`: if they have the same
`rationalOpen` and `𝒪(D₁)` is flat over `A`, so is `𝒪(D₂)`. The restriction `𝒪(D₂) ≃+* 𝒪(D₁)` is
the iso (`restrictionMap_bijective_of_rationalOpen_eq`); flatness transports
(`Module.Flat.of_linearEquiv`). Generic so the transport elaborates ONCE for OPAQUE data — applied to
specific datums it is a direct `exact`, sidestepping the per-datum (two-nontrivial-denominator) `whnf`
blow-up that an inline transport hits. -/
theorem flat_of_rationalOpen_eq
    [IsTateRing A] [IsNoetherianRing A] [IsStronglyNoetherian A] [T2Space A]
    [NonarchimedeanRing A] [HasLocLiftPowerBounded A]
    [letI : UniformSpace A := IsTopologicalAddGroup.rightUniformSpace A; CompleteSpace A]
    (D₁ D₂ : RationalLocData A)
    (h_ro : rationalOpen D₂.T D₂.s = rationalOpen D₁.T D₁.s)
    (hflat : @Module.Flat A (presheafValue D₁) _ _ (RingHom.toModule D₁.canonicalMap)) :
    @Module.Flat A (presheafValue D₂) _ _ (RingHom.toModule D₂.canonicalMap) := by
  let e : presheafValue D₂ ≃+* presheafValue D₁ :=
    RingEquiv.ofBijective (restrictionMapHom D₂ D₁ h_ro.symm.le)
      (restrictionMap_bijective_of_rationalOpen_eq D₂ D₁ h_ro)
  letI : Module A (presheafValue D₁) := RingHom.toModule D₁.canonicalMap
  letI : Module A (presheafValue D₂) := RingHom.toModule D₂.canonicalMap
  have he_smul : ∀ (a : A) (x : presheafValue D₂), e (a • x) = a • e x := by
    intro a x
    change e (D₂.canonicalMap a * x) = D₁.canonicalMap a * e x
    rw [e.map_mul]; congr 1
    exact restrictionMapHom_canonicalMap D₂ D₁ h_ro.symm.le a
  exact @Module.Flat.of_linearEquiv A (presheafValue D₁) (presheafValue D₂)
    _ _ _ _ _ hflat
    { toLinearMap := { toFun := e, map_add' := e.map_add, map_smul' := he_smul }
      invFun := e.symm
      left_inv := e.symm_apply_apply
      right_inv := e.apply_symm_apply }

/-- **genPieceUnit engine** — `𝒪(genPieceDatum P {↑u} sB)` flat over `A` (`↑u` a unit). Same
`rationalOpen` as `coUnitDatum (sB·↑u⁻¹)`, flat by the coUnit engine; one-line transport via the
generic `flat_of_rationalOpen_eq`. -/
theorem presheafValue_flat_of_genPieceUnit_faithful
    [IsTateRing A] [IsNoetherianRing A] [IsStronglyNoetherian A] [T2Space A]
    [NonarchimedeanRing A] [HasLocLiftPowerBounded A]
    [letI : UniformSpace A := IsTopologicalAddGroup.rightUniformSpace A; CompleteSpace A]
    (P : PairOfDefinition A) (u : Aˣ) (sB : A)
    (hspan : Ideal.span (({(↑u : A)} : Finset A) : Set A) = ⊤) :
    @Module.Flat A (presheafValue (genPieceDatum P {(↑u : A)} sB hspan)) _ _
      (RingHom.toModule (genPieceDatum P {(↑u : A)} sB hspan).canonicalMap) := by
  have h_ro := genPieceUnit_coUnit_rationalOpen_eq P u sB hspan
  have hflat := presheafValue_flat_of_coUnitDatum_faithful P (sB * ↑u⁻¹)
  exact flat_of_rationalOpen_eq _ _ h_ro hflat

/-- **Per-step `h_pb` discharge** — `canMap t · (canMap (D₀.s))⁻¹ ∈ D₀⁺` for any generator
`t ∈ D₀.T`. STRUCTURAL: `t/(D₀.s) = divByS t (D₀.s) ∈ locPlusSubring` (the generator-over-denominator
is a defining generator of the plus-subring, `divByS_mem_locPlusSubring`), and its `coeRingHom`-image
lies in `completedPlusSubring = (presheafValue D₀)⁺` (`coeRingHom_mem_completedPlusSubring`). The
element equals `coeRingHom (divByS t (D₀.s))` since `canMap = coeRingHom ∘ algebraMap`,
`Ring.inverse (canMap (D₀.s)) = invS`, `invS = coeRingHom (divByS 1 (D₀.s))`, and `divByS t (D₀.s)
= algebraMap t · divByS 1 (D₀.s)`. -/
theorem domUnit_invDenom_mem_completedPlus (D₀ : RationalLocData A) {t : A} (ht : t ∈ D₀.T) :
    D₀.canonicalMap t * Ring.inverse (D₀.canonicalMap D₀.s) ∈ D₀.completedPlusSubring := by
  have e1 := algebraMap_s_mul_divByS D₀ t
  have e2 := algebraMap_s_mul_divByS D₀ (1 : A)
  rw [map_one] at e2
  have hb : divByS t D₀.s =
      algebraMap A (Localization.Away D₀.s) t * divByS (1 : A) D₀.s := by
    calc divByS t D₀.s
        = (algebraMap A (Localization.Away D₀.s) D₀.s * divByS (1 : A) D₀.s) * divByS t D₀.s := by
            rw [e2, one_mul]
      _ = divByS (1 : A) D₀.s *
            (algebraMap A (Localization.Away D₀.s) D₀.s * divByS t D₀.s) := by ring
      _ = divByS (1 : A) D₀.s * algebraMap A (Localization.Away D₀.s) t := by rw [e1]
      _ = algebraMap A (Localization.Away D₀.s) t * divByS (1 : A) D₀.s := by ring
  have hinv : Ring.inverse (D₀.canonicalMap D₀.s) = invS D₀ := by
    have h1 : Ring.inverse (D₀.canonicalMap D₀.s) * D₀.canonicalMap D₀.s = 1 :=
      Ring.inverse_mul_cancel _ D₀.canonicalMap_s_isUnit
    calc Ring.inverse (D₀.canonicalMap D₀.s)
        = Ring.inverse (D₀.canonicalMap D₀.s) * (D₀.canonicalMap D₀.s * invS D₀) := by
            rw [canonicalMap_s_mul_invS, mul_one]
      _ = Ring.inverse (D₀.canonicalMap D₀.s) * D₀.canonicalMap D₀.s * invS D₀ := by ring
      _ = invS D₀ := by rw [h1, one_mul]
  have heq : D₀.canonicalMap t * Ring.inverse (D₀.canonicalMap D₀.s) =
      D₀.coeRingHom (divByS t D₀.s) := by
    rw [hinv, invS_eq_coeRingHom_divByS_one, hb, map_mul]
    simp only [RationalLocData.canonicalMap, RingHom.comp_apply]
  rw [heq]
  exact D₀.coeRingHom_mem_completedPlusSubring (D₀.divByS_mem_locPlusSubring ht)

/-- **`sB`-relative `h_pb` discharge** — `canMap u · (canMap sB)⁻¹ ∈ D⁺` whenever `sB` divides the
denominator (`D.s = sB·c`) and the witness `u·c ∈ D.T`. Reduces to `domUnit_invDenom_mem_completedPlus`
at `u·c` over `D.s` via the cofactor identity `u/sB = (u·c)/D.s` (`canMap c` is a unit since `c ∣ D.s`).
This is what discharges each chain step's `h_pb`: `interSamePair` multiplies denoms so `Xⱼ.s = sB^{j+1}`,
but the product structure keeps `↑u·sB^j ∈ Xⱼ.T`, so `↑u/sB` is structural at every piece. -/
theorem domUnit_invDenom_mem_completedPlus_general (D : RationalLocData A) (u sB c : A)
    (hs : D.s = sB * c) (hmem : u * c ∈ D.T) :
    D.canonicalMap u * Ring.inverse (D.canonicalMap sB) ∈ D.completedPlusSubring := by
  have hsc : D.canonicalMap D.s = D.canonicalMap sB * D.canonicalMap c := by rw [hs, map_mul]
  have hc_unit : IsUnit (D.canonicalMap c) :=
    isUnit_of_mul_isUnit_right (hsc ▸ D.canonicalMap_s_isUnit)
  have heq : D.canonicalMap u * Ring.inverse (D.canonicalMap sB) =
      D.canonicalMap (u * c) * Ring.inverse (D.canonicalMap D.s) := by
    rw [map_mul, hsc, Ring.mul_inverse_rev, ← mul_assoc,
      mul_assoc (D.canonicalMap u) (D.canonicalMap c) (Ring.inverse (D.canonicalMap c)),
      Ring.mul_inverse_cancel _ hc_unit, mul_one]
  rw [heq]
  exact domUnit_invDenom_mem_completedPlus D hmem

/-- `sB` is a unit in `𝒪(D)` when it divides the denominator `D.s` (`D.s = sB·c`). -/
theorem canonicalMap_isUnit_of_dvd_s (D : RationalLocData A) (sB c : A) (hs : D.s = sB * c) :
    IsUnit (D.canonicalMap sB) :=
  isUnit_of_mul_isUnit_left
    (show IsUnit (D.canonicalMap sB * D.canonicalMap c) by
      rw [← map_mul, ← hs]; exact D.canonicalMap_s_isUnit)

/-- `span{g, ↑u} = ⊤` for `↑u` a unit (the dominating unit makes every chain-step piece rational). -/
theorem span_pair_unit_eq_top (g : A) (u : Aˣ) :
    Ideal.span ((({g, (↑u : A)} : Finset A)) : Set A) = ⊤ :=
  Ideal.eq_top_of_isUnit_mem _ (Ideal.subset_span (by simp)) u.isUnit

/-- One Remark-7.55 chain step: intersect `D'` with the dominating-unit piece `R({g, ↑u}/sB)`
(`interSamePair`, so the denominator becomes `D'.s · sB`). -/
noncomputable def chainStep (u : Aˣ) (sB : A)
    (D' : RationalLocData A) (g : A) : RationalLocData A :=
  D'.interSamePair (genPieceDatum D'.P {g, (↑u : A)} sB (span_pair_unit_eq_top g u)) rfl

/-- `interSamePair`'s generator set as a pointwise product `(insert D₁.s D₁.T) * (insert D₂.s D₂.T)`
(symbolic in `D₂`, so applying it to a concrete second datum avoids reducing that datum's `hopen`). -/
theorem interSamePair_T_mul (D₁ D₂ : RationalLocData A) (hP : D₂.P = D₁.P) :
    (D₁.interSamePair D₂ hP).T = (insert D₁.s D₁.T) * (insert D₂.s D₂.T) := by
  rw [Finset.mul_def]; rfl

/-- **Chain invariant propagation** — the structural witness `∃c, D.s = sB·c ∧ ↑u·c ∈ D.T` survives
one `chainStep`: the denominator multiplies by `sB` (new cofactor `c·sB`) and `(↑u·c)·sB` lands in the
product generator set. This is what keeps `h_pb`/`hs_unit` structural along the whole fold. -/
theorem chainStep_invariant (u : Aˣ) (sB c : A)
    (D' : RationalLocData A) (g : A) (hs : D'.s = sB * c) (hmem : (↑u : A) * c ∈ D'.T) :
    (chainStep u sB D' g).s = sB * (c * sB) ∧
      (↑u : A) * (c * sB) ∈ (chainStep u sB D' g).T := by
  refine ⟨by show D'.s * sB = sB * (c * sB); rw [hs]; ring, ?_⟩
  have hrw : (↑u : A) * (c * sB) = ((↑u : A) * c) * sB := by ring
  rw [hrw,
    show (chainStep u sB D' g).T = _ from
      interSamePair_T_mul D' (genPieceDatum D'.P {g, (↑u : A)} sB (span_pair_unit_eq_top g u)) rfl,
    genPieceDatum_s, genPieceDatum_T]
  exact Finset.mul_mem_mul (Finset.mem_insert_of_mem hmem) (Finset.mem_insert_self _ _)

/-- The fold's `rationalOpen` shrinks: `R(foldl gens D₀) ⊆ R(D₀)` (each step is an intersection). -/
theorem foldl_chainStep_subset (u : Aˣ) (sB : A) (gens : List A) (D₀ : RationalLocData A) :
    rationalOpen (gens.foldl (chainStep u sB) D₀).T (gens.foldl (chainStep u sB) D₀).s ⊆
      rationalOpen D₀.T D₀.s := by
  induction gens generalizing D₀ with
  | nil => exact subset_refl _
  | cons g gs ih =>
    exact (ih (chainStep u sB D₀ g)).trans
      (RationalLocData.interSamePair_subset_left D₀
        (genPieceDatum D₀.P {g, (↑u : A)} sB (span_pair_unit_eq_top g u)) rfl)

/-- **The Remark-7.55 fold (list-induction core).** Folding `chainStep` over `gens` keeps `𝒪(foldl)`
flat over `𝒪(D₀)`: each step is `flat_chainStep_domUnit` (the `CompatiblePlusSubring`-free domUnit
step, whose `hs_unit`/`h_pb` are discharged structurally from the carried invariant `D₀.s = sB·c ∧
↑u·c ∈ D₀.T`), composed by `restrictionMap_flat_trans`; the invariant propagates by
`chainStep_invariant`. No added hypothesis on the headline — `c` is the cofactor witness, discharged
at the call site (`c = 1` for `X₀`). -/
theorem flat_domUnit_listFold
    [IsTateRing A] [IsNoetherianRing A] [IsStronglyNoetherian A] [T2Space A]
    [NonarchimedeanRing A] [HasLocLiftPowerBounded A]
    [letI : UniformSpace A := IsTopologicalAddGroup.rightUniformSpace A; CompleteSpace A]
    (u : Aˣ) (sB : A) (gens : List A) (D₀ : RationalLocData A) (c : A)
    (hs : D₀.s = sB * c) (hmem : (↑u : A) * c ∈ D₀.T) :
    @Module.Flat (presheafValue D₀) (presheafValue (gens.foldl (chainStep u sB) D₀)) _ _
      (restrictionMapHom D₀ (gens.foldl (chainStep u sB) D₀)
        (foldl_chainStep_subset u sB gens D₀)).toModule := by
  induction gens generalizing D₀ c with
  | nil => exact restrictionMapHom_refl_flat D₀ (foldl_chainStep_subset u sB [] D₀)
  | cons g gs ih =>
    obtain ⟨hs', hmem'⟩ := chainStep_invariant u sB c D₀ g hs hmem
    exact restrictionMap_flat_trans D₀ (chainStep u sB D₀ g)
      (gs.foldl (chainStep u sB) (chainStep u sB D₀ g))
      (RationalLocData.interSamePair_subset_left D₀
        (genPieceDatum D₀.P {g, (↑u : A)} sB (span_pair_unit_eq_top g u)) rfl)
      (foldl_chainStep_subset u sB gs (chainStep u sB D₀ g))
      (flat_chainStep_domUnit D₀ g sB (↑u) (span_pair_unit_eq_top g u)
        (canonicalMap_isUnit_of_dvd_s D₀ sB c hs)
        (domUnit_invDenom_mem_completedPlus_general D₀ (↑u) sB c hs hmem))
      (ih (chainStep u sB D₀ g) (c * sB) hs' hmem')

/-- **Compose `A → 𝒪(X₀) → 𝒪(D')`** — flatness of the whole-space-canonical `A → 𝒪(D')` from the
base step `A → 𝒪(X₀)` (`X₀.canonicalMap`) and the relative step `𝒪(X₀) → 𝒪(D')` (`restrictionMapHom`),
via `Module.Flat.trans`. The scalar tower is `restrictionMapHom_canonicalMap` (restriction commutes with
the canonical map). Generic in `X₀ D'` so the tower elaborates once. -/
theorem flat_trans_via_canonicalMap
    [IsTateRing A] [IsNoetherianRing A] [IsStronglyNoetherian A] [T2Space A]
    [NonarchimedeanRing A] [HasLocLiftPowerBounded A]
    [letI : UniformSpace A := IsTopologicalAddGroup.rightUniformSpace A; CompleteSpace A]
    (X₀ D' : RationalLocData A) (h : rationalOpen D'.T D'.s ⊆ rationalOpen X₀.T X₀.s)
    (hX0 : @Module.Flat A (presheafValue X₀) _ _ (RingHom.toModule X₀.canonicalMap))
    (hfold : @Module.Flat (presheafValue X₀) (presheafValue D') _ _
      (restrictionMapHom X₀ D' h).toModule) :
    @Module.Flat A (presheafValue D') _ _ (RingHom.toModule D'.canonicalMap) := by
  letI : Algebra A (presheafValue X₀) := X₀.canonicalMap.toAlgebra
  letI : Algebra (presheafValue X₀) (presheafValue D') := (restrictionMapHom X₀ D' h).toAlgebra
  letI : Algebra A (presheafValue D') := D'.canonicalMap.toAlgebra
  letI : Module A (presheafValue X₀) := Algebra.toModule
  letI : Module (presheafValue X₀) (presheafValue D') := Algebra.toModule
  letI : Module A (presheafValue D') := Algebra.toModule
  haveI : IsScalarTower A (presheafValue X₀) (presheafValue D') :=
    IsScalarTower.of_algebraMap_eq fun x => (restrictionMapHom_canonicalMap X₀ D' h x).symm
  haveI : Module.Flat A (presheafValue X₀) := hX0
  haveI : Module.Flat (presheafValue X₀) (presheafValue D') := hfold
  exact Module.Flat.trans A (presheafValue X₀) (presheafValue D')

/-- One `chainStep`'s `rationalOpen` is the intersection `R(D') ∩ R({g,↑u}/sB)`
(`interSamePair_rationalOpen` + the `genPieceDatum` field projections). -/
theorem chainStep_rationalOpen (u : Aˣ) (sB : A) (D' : RationalLocData A) (g : A) :
    rationalOpen (chainStep u sB D' g).T (chainStep u sB D' g).s =
      rationalOpen D'.T D'.s ∩ rationalOpen ({g, (↑u : A)} : Finset A) sB := by
  simp only [chainStep]
  -- v4.33: `rw [interSamePair_rationalOpen]` fails to match through `chainStep`'s embedded
  -- `_hP` proof (re-checked at reducible transparency); apply the lemma with an explicit
  -- `genPieceDatum_P` proof and close by proof-irrelevance defeq (`exact`).
  have h := RationalLocData.interSamePair_rationalOpen D'
    (genPieceDatum D'.P {g, (↑u : A)} sB (span_pair_unit_eq_top g u))
    (genPieceDatum_P D'.P {g, (↑u : A)} sB (span_pair_unit_eq_top g u))
  rw [genPieceDatum_T, genPieceDatum_s] at h
  exact h

/-- **The fold's `rationalOpen` membership.** `v ∈ R(foldl gens X₀)` iff `v ∈ R(X₀)` and `v` lies
in each step piece `R({g,↑u}/sB)`. By induction on `gens` (each step is the intersection
`chainStep_rationalOpen`). -/
theorem mem_foldl_chainStep (u : Aˣ) (sB : A) (gens : List A) (X₀ : RationalLocData A) (v : Spv A) :
    v ∈ rationalOpen (gens.foldl (chainStep u sB) X₀).T (gens.foldl (chainStep u sB) X₀).s ↔
      v ∈ rationalOpen X₀.T X₀.s ∧
        ∀ g ∈ gens, v ∈ rationalOpen ({g, (↑u : A)} : Finset A) sB := by
  induction gens generalizing X₀ with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih (chainStep u sB X₀ g), chainStep_rationalOpen,
      Set.mem_inter_iff, List.forall_mem_cons]
    tauto

/-- **Endpoint: `R(W/sB) = R(foldl W.toList X₀)`** (Wedhorn `Xₙ = im E`). The fold over `W`'s
generators (on the dominating-unit base `X₀ = R({↑u}/sB)`) recovers `R(W/sB)`: the fold carries an
extra `v(↑u) ≤ v(sB)` condition (from `X₀` and each step piece), which is **free** on `R(W/sB)` via
the dominating-unit hypothesis `hu` (Cor 7.32). -/
theorem foldl_rationalOpen_eq_base (P : PairOfDefinition A) (u : Aˣ) (sB : A) (W : Finset A)
    (hspan_u : Ideal.span (({(↑u : A)} : Finset A) : Set A) = ⊤)
    (hu : ∀ v ∈ rationalOpen W sB, v.vle (↑u) sB) :
    rationalOpen W sB =
      rationalOpen (W.toList.foldl (chainStep u sB) (genPieceDatum P {(↑u : A)} sB hspan_u)).T
        (W.toList.foldl (chainStep u sB) (genPieceDatum P {(↑u : A)} sB hspan_u)).s := by
  ext v
  rw [mem_foldl_chainStep]
  constructor
  · intro hv
    have huv := hu v hv
    obtain ⟨hspa, hgen, hsupp⟩ := hv
    refine ⟨⟨hspa, ?_, hsupp⟩, fun g hg => ⟨hspa, ?_, hsupp⟩⟩
    · intro t ht
      rw [genPieceDatum_T, Finset.mem_singleton] at ht; subst ht
      rw [genPieceDatum_s]; exact huv
    · intro t ht
      rw [Finset.mem_insert, Finset.mem_singleton] at ht
      rcases ht with rfl | rfl
      · exact hgen t (Finset.mem_toList.mp hg)
      · exact huv
  · rintro ⟨hX₀, hg⟩
    obtain ⟨hspa, -, hsupp⟩ := hX₀
    refine ⟨hspa, ?_, hsupp⟩
    intro t ht
    exact (hg t (Finset.mem_toList.mpr ht)).2.1 t (Finset.mem_insert_self t _)

/-- **Whole-space Prop 8.30 (Remark 7.55 chain), assembled downstream.**
`𝒪_B(im E)` is flat over `B = 𝒪_X(D)`, for `im E = imagePieceDatum D E.T E.s` the whole-space
image of a `span = ⊤` rational piece. Proven by folding `flat_chainStep_domUnit` over `E.T`'s
generators (the `CompatiblePlusSubring`-free domUnit per-step) on top of the `X₀` dominating-unit
coUnit base, discharging the chain invariant `h_pb` via the [Hu2] 3.3 power-bounded keystone.
The downstream counterpart of `prop_8_30_imagePiece_wholeSpace_flat`. -/
theorem prop_8_30_imagePiece_assembled
    [IsTateRing A] [IsNoetherianRing A] [IsStronglyNoetherian A] [T2Space A]
    [NonarchimedeanRing A] [HasLocLiftPowerBounded A]
    [letI : UniformSpace A := IsTopologicalAddGroup.rightUniformSpace A; CompleteSpace A]
    (D E : RationalLocData A) (hspanE : Ideal.span (E.T : Set A) = ⊤) :
    @Module.Flat (presheafValue D) (presheafValue (imagePieceDatum D E.T E.s hspanE)) _ _
      ((imagePieceDatum D E.T E.s hspanE).canonicalMap).toModule := by
  classical
  haveI hTateB : IsTateRing (presheafValue D) := presheafValue_isTateRing_concrete D
  haveI : IsNoetherianRing (presheafValue D) := presheafValue_isNoetherianRing_faithful D
  haveI : IsStronglyNoetherian (presheafValue D) := presheafValue_isStronglyNoetherian_faithful D
  haveI : IsHuberRing (presheafValue D) := hTateB.toIsHuberRing
  haveI hCompleteB : @CompleteSpace (presheafValue D)
      (IsTopologicalAddGroup.rightUniformSpace (presheafValue D)) :=
    presheafValue_completeSpace_rightUniformSpace D
  -- Remark 7.55 dominating unit `u` (`|u| ≤ |sB|` on `rationalOpen (im E)`).
  obtain ⟨u, hu⟩ := remark755_dominating_unit_over_presheafValue D E hspanE
  have hspan_u : Ideal.span (({(↑u : presheafValue D)} : Finset (presheafValue D)) :
      Set (presheafValue D)) = ⊤ := by
    rw [Finset.coe_singleton]; exact Ideal.span_singleton_eq_top.mpr u.isUnit
  -- X₀ = R({↑u}/sB), flat over B (the dominating-unit base; genPieceUnit engine at A := B).
  have hX0 := presheafValue_flat_of_genPieceUnit_faithful (presheafValue_concretePair D) u
    (imagePieceDatum D E.T E.s hspanE).s hspan_u
  set sB := (imagePieceDatum D E.T E.s hspanE).s with hsB
  set X₀ := genPieceDatum (presheafValue_concretePair D) {(↑u : presheafValue D)} sB hspan_u with hX₀
  set gens := (imagePieceDatum D E.T E.s hspanE).T.toList with hgens
  -- The Remark-7.55 fold is flat over `𝒪(X₀)` (invariant `X₀.s = sB·1`, `↑u·1 ∈ X₀.T = {↑u}`).
  have hfold := flat_domUnit_listFold u sB gens X₀ 1
    (by rw [hX₀, genPieceDatum_s, mul_one])
    (by rw [hX₀, genPieceDatum_T, mul_one]; exact Finset.mem_singleton_self _)
  -- Compose `B → 𝒪(X₀) → 𝒪(foldl)`.
  have hfoldB := flat_trans_via_canonicalMap X₀ (gens.foldl (chainStep u sB) X₀)
    (foldl_chainStep_subset u sB gens X₀) hX0 hfold
  -- Endpoint: `foldl gens X₀ ≈ im E` (same `rationalOpen`), the `↑u`-condition free via `hu`.
  have h_ro : rationalOpen (imagePieceDatum D E.T E.s hspanE).T
        (imagePieceDatum D E.T E.s hspanE).s =
      rationalOpen (gens.foldl (chainStep u sB) X₀).T (gens.foldl (chainStep u sB) X₀).s :=
    foldl_rationalOpen_eq_base (presheafValue_concretePair D) u sB
      (imagePieceDatum D E.T E.s hspanE).T hspan_u
      (fun v hv => (hu ⟨v, rationalOpen_subset_spa hv⟩ hv).1)
  exact flat_of_rationalOpen_eq (gens.foldl (chainStep u sB) X₀)
    (imagePieceDatum D E.T E.s hspanE) h_ro hfoldB

end

omit [CompatiblePlusSubring A] in
/-- **GENUINE RESIDUAL — whole-space Prop 8.30 over `B = 𝒪_X(D)` (Remark-7.55 chain)**
(Wedhorn Remark 7.55, `wedhorn.txt:3504`–`3517`).

This is the *second* of Wedhorn's two reductions, AFTER "we may assume `X = V`"
(`prop_8_30_remark755_chain`'s keystone base change): for the rational subset `im E`
of the *whole space* `Spa B`, the canonical restriction `B → 𝒪_B(im E)` is flat.

Wedhorn (Remark 7.55, **read verbatim from the PDF p.70**) decomposes
`Spa B ⊇ X₀ ⊇ X₁ ⊇ ⋯ ⊇ Xₙ = im E`: `X₀ = {1 ≤ x(s/u)}` for the dominating unit
`u ∈ B×` (Cor 7.32, `remark755_dominating_unit_over_presheafValue` PROVEN), on which `s`
becomes a unit (Prop 7.52); then `Xᵢ = Xᵢ₋₁ ∩ {x(tᵢ/s) ≤ 1}`.

**FAITHFUL per-step (the A1a engine, PROVEN).** Over `Bᵢ₋₁ := 𝒪_B(Xᵢ₋₁)` (where `s` is a
unit), each step is the single basic piece `R((tᵢ/s)/1) = unitDatum(tᵢ/s)`, with `tᵢ/s`
**NOT power-bounded** in `Bᵢ₋₁`. So it is `presheafValue_flat_of_unitDatum_faithful` (the
relocated faithful Example-6.38 fSubX iso `unitDatum_quotEquiv` + `lemma_8_31_fSubX_flat`,
arbitrary `f`), **NOT** `prop_8_30_basic_laurent_step_flat` — the latter requires
`hD'_T_pb : D'.T ⊆ E.P.A₀` (`LaurentNormalized`, generators power-bounded), which `tᵢ/s`
**fails**, so that route is unavailable here.

**Remaining content (the chain assembly).** The per-step identification
`𝒪(Xᵢ) ≅ 𝒪_{Bᵢ₋₁}(unitDatum(tᵢ/s))` is the **relative single-step Example 6.38**: via the
Spa-correspondence `Spa(Bᵢ₋₁) ≅ rationalOpen(Xᵢ₋₁)` (Step 1, sorry-free) the absorption is
all-free for Spa points — `comap_canonicalMap_vle` (Presheaf:485) gives `w.vle (canMap tⱼ)
(canMap s)` ∀`tⱼ∈Xᵢ₋₁.T`, and `canonicalMap_s_isUnit` gives `¬w.vle (canMap s) 0` — so
`rationalOpen` collapses to the single `unitDatum`, `restrictionMap_bijective_of_rationalOpen_eq`
(GeometricReduction:411) gives the iso, then the A1a engine finishes. Fold via
`restrictionMap_flat_chain`. **⚠ Do NOT** route through a general multivariate
`A⟨X₁..Xₘ⟩/(s·Xᵢ−tᵢ)` flatness — that needs a restricted-power-series **Fubini** absent from
mathlib (the CLAUDE.md case-study divergence trap). Isolated per the CLAUDE.md
sub-lemma-with-`sorry` rule; NO added hypothesis. -/
theorem prop_8_30_imagePiece_wholeSpace_flat
    (D E : RationalLocData A) (hspanE : Ideal.span (E.T : Set A) = ⊤) :
    @Module.Flat (presheafValue D) (presheafValue (imagePieceDatum D E.T E.s hspanE)) _ _
      ((imagePieceDatum D E.T E.s hspanE).canonicalMap).toModule :=
  prop_8_30_imagePiece_assembled D E hspanE

omit [CompatiblePlusSubring A] in
/-- **The Remark-7.55 chain decomposition for Prop 8.30** (Wedhorn p. 81,
`wedhorn.txt:4099`–`4104`): flatness of `𝒪_X(D) → 𝒪_X(D')` for `D' ⊆ D` rational.

Wedhorn's FIRST reduction ("we may assume `X = V`") is now PROVEN here via the
8.16-keystone `relativePiece_equiv`: base-change to `B := 𝒪_X(D)` identifies
`𝒪_X(D') ≅ 𝒪_B(im D')` (`im D'` a rational subset of the whole space `Spa B`),
intertwining the restriction `𝒪_X(D) → 𝒪_X(D')` with the whole-space canonical
restriction `B → 𝒪_B(im D')` (`relativePiece_equiv_restrictionMap`). Flatness
transports across the iso by `Module.Flat.of_linearEquiv`, reducing to the
whole-space residual `prop_8_30_imagePiece_wholeSpace_flat` (Wedhorn's SECOND
reduction, the genuine Remark 7.55 chain). -/
theorem prop_8_30_remark755_chain
    (D D' : RationalLocData A)
    (h : rationalOpen D'.T D'.s ⊆ rationalOpen D.T D.s)
    (hD : D.IsRational) (hD' : D'.IsRational)
    [IsTateRing (presheafValue D)]
    [IsNoetherianRing (presheafValue D)]
    [IsHuberRing (presheafValue D)]
    [NonarchimedeanRing (presheafValue D)]
    [T2Space (presheafValue D)]
    [IsStronglyNoetherian (presheafValue D)] :
    @Module.Flat (presheafValue D) (presheafValue D') _ _
      (restrictionMapHom D D' h).toModule := by
  -- Wedhorn "we may assume X = V": base-change to B := 𝒪_X(D) via the 8.16-keystone.
  set W := imagePieceDatum D D'.T D'.s hD'.span_eq_top with hW
  set e := relativePiece_equiv D D' h hD'.span_eq_top with he
  -- Whole-space flatness over B (Remark 7.55 chain residual).
  have hflatW : @Module.Flat (presheafValue D) (presheafValue W) _ _
      (W.canonicalMap).toModule :=
    prop_8_30_imagePiece_wholeSpace_flat D D' hD'.span_eq_top
  -- Transport across e (intertwining restrictionMapHom with the B-canonical map).
  letI : Module (presheafValue D) (presheafValue D') := (restrictionMapHom D D' h).toModule
  letI : Module (presheafValue D) (presheafValue W) := W.canonicalMap.toModule
  have he_smul : ∀ (a : presheafValue D) (x : presheafValue D'), e (a • x) = a • e x := by
    intro a x
    change e (restrictionMapHom D D' h a * x) = W.canonicalMap a * e x
    rw [e.map_mul]
    congr 1
    exact relativePiece_equiv_restrictionMap D D' h hD'.span_eq_top a
  exact @Module.Flat.of_linearEquiv (presheafValue D)
    (presheafValue W) (presheafValue D')
    _ _ _ _ _ hflatW
    { toLinearMap :=
        { toFun := e
          map_add' := e.map_add
          map_smul' := he_smul }
      invFun := e.symm
      left_inv := e.symm_apply_apply
      right_inv := e.apply_symm_apply }

omit [CompatiblePlusSubring A] in
theorem prop_8_30_relative_laurent_flat
    (D D' : RationalLocData A)
    (h : rationalOpen D'.T D'.s ⊆ rationalOpen D.T D.s)
    (hD : D.IsRational) (hD' : D'.IsRational)
    [hTate : IsTateRing (presheafValue D)]
    [hNoeth : IsNoetherianRing (presheafValue D)]
    [IsHuberRing (presheafValue D)]
    [NonarchimedeanRing (presheafValue D)]
    [T2Space (presheafValue D)]
    [IsStronglyNoetherian (presheafValue D)] :
    @Module.Flat (presheafValue D) (presheafValue D') _ _
      (restrictionMapHom D D' h).toModule :=
  -- The Remark-7.55 chain folds the per-step faithful flatness
  -- (`prop_8_30_basic_laurent_step_flat`) by `Module.Flat.trans`; the chain-decomposition object
  -- is the isolated residual `prop_8_30_remark755_chain` (geometric content of Remark 7.55).
  prop_8_30_remark755_chain D D' h hD hD'

omit [CompatiblePlusSubring A] in
theorem prop_8_30_flat_of_faithful_base
    (D D' : RationalLocData A)
    (h : rationalOpen D'.T D'.s ⊆ rationalOpen D.T D.s)
    (hD : D.IsRational) (hD' : D'.IsRational)
    (hTate : IsTateRing (presheafValue D))
    (hNoeth : IsNoetherianRing (presheafValue D)) :
    @Module.Flat (presheafValue D) (presheafValue D') _ _
      (restrictionMapHom D D' h).toModule := by
  -- Step 1 (faithful): assemble the complete strongly-noetherian-Tate bundle on `B := presheafValue
  -- D`. `IsTateRing`/`IsNoetherianRing` come in as `hTate`/`hNoeth`; `IsHuberRing` from `IsTateRing`;
  -- `NonarchimedeanRing`/`T2Space` are derivable from the plain `presheafValue` (completion)
  -- instances; `IsStronglyNoetherian` from `presheafValue_isStronglyNoetherian_faithful` (Ex. 6.38).
  -- None of this uses any `PairOfDefinition` / noeth-`A₀`.
  haveI := hTate
  haveI := hNoeth
  haveI : IsHuberRing (presheafValue D) := hTate.toIsHuberRing
  haveI : NonarchimedeanRing (presheafValue D) := inferInstance
  haveI : T2Space (presheafValue D) := inferInstance
  haveI : IsStronglyNoetherian (presheafValue D) :=
    presheafValue_isStronglyNoetherian_faithful D
  -- Steps 2–4 (Remark 7.55 + relative Example 6.38 over `B` + Lemma 8.31): the single genuine
  -- residual, isolated faithfully (NO noeth-`A₀`). See `prop_8_30_relative_laurent_flat`.
  exact prop_8_30_relative_laurent_flat D D' h hD hD'

omit [CompatiblePlusSubring A] in
/-- **Proposition 8.30** (Wedhorn p.81, `wedhorn.txt:4095`): for rational subsets `U ⊆ V`
the restriction `O_X(V) → O_X(U)` is flat.

Faithful assembly of Wedhorn's four steps (see the section docstring above):

* **Step 1 (Example 6.38, the base):** `presheafValue_isTateRing_faithful` +
  `presheafValue_isNoetherianRing_faithful` promote `B := presheafValue D` to a complete strongly
  noetherian Tate ring (the derived members `IsHuberRing`/`IsStronglyNoetherian` follow, the latter
  via `presheafValue_isStronglyNoetherian_faithful` (Example 6.38, faithful); `NonarchimedeanRing`/`T2Space`/
  `PlusSubring` are plain instances). NO `IsLinearTopology` member — that was REMOVED (false for a
  Tate ring; see the note above `presheafValue_isNoetherianRing_residual`).
* **Steps 2–4 (Remark 7.55 + Example 6.38 over `B` + Lemma 8.31):**
  `prop_8_30_flat_of_faithful_base` → `prop_8_30_relative_laurent_flat` → the Remark-7.55 chain
  `prop_8_30_remark755_chain`, each step of which is the FAITHFUL per-step flatness
  `prop_8_30_basic_laurent_step_flat` (relative Wedhorn-2.13 iso + the `omit`-cleaned faithful engine
  `presheafValue_flat_of_canonical_faithful` over `B`, NO `[CompatiblePlusSubring B]`/noeth-`A₀`).

FAITHFUL: the `section Wedhorn828` `A`-bundle only — no `PairOfDefinition`, no noeth-`A₀`, no
data/witness parameters on this signature. The `IsRational` hypotheses are NOT additions:
they are Wedhorn's own Definition 7.29 ("rational subsets" requires `T·A` open,
wedhorn.txt:3100) — the statement "U ⊆ V ⊆ X **two rational subsets**" (wedhorn.txt:4096)
quantifies over exactly these (Def-7.29 restoration, user-approved 2026-06-11).
The faithful per-step flat engine is now written with
sorry-free transport logic; the remaining `sorry`s are precise faithful-route residuals (NOT
noeth-`A₀` smuggling), none adding a hypothesis to this signature:
* `prop_8_30_remark755_chain` — the **geometric** Remark-7.55 chain-decomposition of an arbitrary
  `U ⊆ V` into basic-Laurent steps (the inductive `Xᵢ`-chain object; `cor_7_32_dominating_unit`
  supplies `X₀`, but `laurent_cover_from_dominating_unit` and the inductive chain are not yet built).
* `presheafValue_isStronglyNoetherian_faithful` — strong-noetherianity of `B = O_X(V)` (Example 6.38,
  faithful, replacing the retired-false `noeth + Tate ⟹ strongly-noeth`); its single residual is the
  relative surjection `presheafValue_mvRestricted_surjection` (`A⟨X₁..Xₙ₊ₘ⟩ ↠ B⟨Y₁..Yₘ⟩`). The
  *noetherian* half `presheafValue_isNoetherianRing_faithful` is sorry-free (the multivariate
  Example 6.38 surjection `example638_evalHom_surjective` is proven, `#print axioms`-clean). -/
theorem prop_8_30_restriction_flat (D D' : RationalLocData A)
    (h : rationalOpen D'.T D'.s ⊆ rationalOpen D.T D.s)
    (hD : D.IsRational) (hD' : D'.IsRational) :
    @Module.Flat (presheafValue D) (presheafValue D') _ _
      (restrictionMapHom D D' h).toModule :=
  -- Step 1 (Example 6.38): `B := presheafValue D` is again complete strongly noetherian Tate.
  -- Steps 2–4 (Remark 7.55 + Example 6.38 over `B` + Lemma 8.31): the relative reduction.
  prop_8_30_flat_of_faithful_base D D' h hD hD'
    (presheafValue_isTateRing_faithful D)
    (presheafValue_isNoetherianRing_faithful D)

omit [CompatiblePlusSubring A] in
/-- **Cor 8.32 — Wedhorn-faithful maximals route (geometric leaf).**

Wedhorn states Cor 8.32 as *immediate* from flatness (Prop 8.30) + the covering.
Mathlib's `Module.FaithfullyFlat` is **defined** by the maximals criterion
(`submodule_ne_top`: flat + `∀ maximal m, m • M ≠ ⊤`), so the only geometric
content is: for every **maximal** ideal `m` of the base `O_X(C.base)`, some cover
piece `D` has `m · O_X(D) ≠ ⊤`.

This is the *correct* faithful target. It avoids two dead ends:
* the exact prime-surjection criterion (`q.comap = p` for **all** primes — the now-deleted
  `cor_8_32_prime_surjection`) needs `supp x = p`, i.e. Bourbaki rank-1 domination — absent
  (Lemma745 gives only `supp ⊇ p`); and
* the lifted-ideal route (`hSpa_points_nonOpen_via_lifted_ideal_proper`) lifts a
  prime of `A` to `presheafValue C.base`, which forces the residual
  `liftedIdeal ≠ ⊤` (= the Stacks-00MA / OMT analytic input).

Working with a **maximal `m` of the base directly**: `m` is non-open (proper in a
Tate ring), so `exists_spa_point_supp_ge_in_presheafValue` (Lemma 7.45 on the
completion, T-SUM-1, noeth-`A₀`-free) gives a Spa point `w` with `m ≤ supp w`; the
`A`-shadow `v = comap C.base.canonicalMap w` lies in `rationalOpen C.base`, so the
covering places it in some piece `D` (`C.hcover`); `cor_8_32_spaExtendsAlongRestriction`
extends `w` to a point `w'` of `O_X(D)` with `comap (restrictionMapHom C.base D) w' = w`,
so `m ≤ supp w = comap(restrictionMapHom) supp w'`, giving
`Ideal.map (restrictionMapHom C.base D) m ⊆ supp w' ≠ ⊤`. No Bourbaki, no `liftedIdeal ≠ ⊤`,
no OMT, and (crucially) **no** `restrictionMap_isLocalization` (the mathematically-false
algebraic-localization predicate). The sole deep input is the isolated
`cor_8_32_spaExtendsAlongRestriction` (Wedhorn 7.46/7.48/8.2). -/
theorem cor_8_32_maximal_liftedIdeal_ne_top (C : RationalCoveringData A) :
    ∀ (m : Ideal (presheafValue C.base)), m.IsMaximal →
      ∃ (D : { D // D ∈ C.covers }),
        Ideal.map (restrictionMapHom C.base D.1 (C.hsubset D.1 D.2)) m ≠ ⊤ := by
  intro m hm
  haveI : m.IsPrime := hm.isPrime
  -- `presheafValue C.base` is a Tate ring (noeth-A₀-free faithful pair).
  haveI : IsTateRing (presheafValue C.base) := presheafValue_isTateRing_faithful C.base
  -- A maximal (hence proper) ideal of a Tate ring is non-open.
  have hm_notOpen : ¬IsOpen (m : Set (presheafValue C.base)) :=
    tate_proper_ideal_not_open hm.ne_top
  -- Lemma 7.45 on the completion (T-SUM-1, noeth-A₀-free): a Spa point `w` with `m ≤ w.supp`.
  obtain ⟨w, hw_spa, hw_supp⟩ :=
    exists_spa_point_supp_ge_in_presheafValue C hm_notOpen
  -- The `A`-shadow `v = comap C.base.canonicalMap w` lies in the base rational open.
  have hv_rat_base : comap C.base.canonicalMap w ∈ rationalOpen C.base.T C.base.s :=
    comap_canonicalMap_mem_rationalOpen C.base (canonicalMap_continuous C.base) hw_spa
  -- The covering places `v` in some piece `D`.
  obtain ⟨D, hD, hv_D⟩ := C.hcover _ hv_rat_base
  -- Extend `w` along the restriction `O_X(C.base) → O_X(D)`: a point `w'` of `O_X(D)`
  -- with `comap (restrictionMapHom C.base D) w' = w` (Wedhorn 7.46/7.48/8.2 geometric leaf).
  obtain ⟨w', hw'_eq⟩ :=
    cor_8_32_spaExtendsAlongRestriction C D hD hw_spa hv_D
  refine ⟨⟨D, hD⟩, ?_⟩
  -- `Ideal.map (restrictionMapHom) m ⊆ w'.supp`, and `w'.supp` is a (proper) prime.
  intro htop
  -- From `htop : Ideal.map (restrictionMapHom) m = ⊤`, `1 ∈ w'.supp`, contradiction.
  have hmap_le : Ideal.map (restrictionMapHom C.base D (C.hsubset D hD)) m ≤ w'.supp := by
    rw [Ideal.map_le_iff_le_comap]
    intro a ha
    -- Goal: `restrictionMapHom a ∈ w'.supp`, i.e. `w'.vle (restrictionMapHom a) 0`.
    rw [Ideal.mem_comap, ValuationSpectrum.mem_supp_iff]
    -- `a ∈ m ≤ w.supp` and `w = comap (restrictionMapHom) w'`, so `w'.vle (restrictionMapHom a) 0`.
    have ha_w : a ∈ w.supp := hw_supp ha
    rw [← hw'_eq, ValuationSpectrum.mem_supp_iff, ValuationSpectrum.comap_vle, map_zero] at ha_w
    exact ha_w
  rw [htop, top_le_iff] at hmap_le
  exact (ValuationSpectrum.instIsPrimeSupp w').ne_top hmap_le

omit [CompatiblePlusSubring A] in
theorem cor_8_32_productRestriction_faithfullyFlat (C : RationalCoveringData A)
    (hC : C.IsRational) :
    letI : ∀ D : { D // D ∈ C.covers }, Algebra (presheafValue C.base) (presheafValue D.1) :=
      fun D => (restrictionMapHom C.base D.1 (C.hsubset D.1 D.2)).toAlgebra
    Module.FaithfullyFlat (presheafValue C.base)
      (∀ D : { D // D ∈ C.covers }, presheafValue D.1) := by
  -- Compose Prop 8.30 flatness with the Wedhorn-faithful MAXIMALS criterion
  -- (`faithfullyFlat_pi_of_maximal_ne_top`, axiom-clean, `Cor832.lean`): mathlib *defines*
  -- `FaithfullyFlat` by the maximals field, so the geometric input is exactly T-SUM-2
  -- (`cor_8_32_maximal_liftedIdeal_ne_top`: some cover piece has `m · O_X(D) ≠ ⊤`). The
  -- `algebraMap (presheafValue C.base) (presheafValue D.1)` under `(restrictionMapHom …).toAlgebra`
  -- is `rfl`-equal to `restrictionMapHom …`, so T-SUM-2 supplies `hmax` directly. No
  -- prime-surjection / `supp = p` / Bourbaki domination.
  exact @faithfullyFlat_pi_of_maximal_ne_top (presheafValue C.base) _
    { D // D ∈ C.covers } (Finite.of_fintype _)
    (fun D => presheafValue D.1)
    (fun _ => inferInstance)
    (fun D => (restrictionMapHom C.base D.1 (C.hsubset D.1 D.2)).toAlgebra)
    (fun D => prop_8_30_restriction_flat C.base D.1 (C.hsubset D.1 D.2)
      hC.base (hC.piece D.2))
    (cor_8_32_maximal_liftedIdeal_ne_top C)

omit [CompatiblePlusSubring A] in
/-- **Corollary 8.32, injectivity consequence** (the separation half of `IsSheafy`): the
product restriction `O_X(X) → ∏ O_X(Uᵢ)` is injective. Faithfully flat ⇒ injective.

**Discharged** (Wedhorn-faithful, MAXIMALS route): faithful flatness of the product restriction
(`cor_8_32_productRestriction_faithfullyFlat`, via Prop 8.30 flatness + T-SUM-2's maximals
criterion) gives `FaithfulSMul`, hence `algebraMap` injectivity, hence injectivity of the
subtype-indexed product restriction. No noeth-`A₀`, no prime-surjection. -/
theorem cor_8_32_productRestrictionSub_injective (C : RationalCoveringData A)
    (hC : C.IsRational) :
    Function.Injective (productRestrictionSub A C) := by
  letI : ∀ D : { D // D ∈ C.covers }, Algebra (presheafValue C.base) (presheafValue D.1) :=
    fun D => (restrictionMapHom C.base D.1 (C.hsubset D.1 D.2)).toAlgebra
  haveI := cor_8_32_productRestriction_faithfullyFlat C hC
  -- The product's `algebraMap` is injective (faithfully flat ⇒ `FaithfulSMul`), and it
  -- agrees componentwise with `productRestrictionSub` (each factor's algebraMap is the
  -- restriction ring hom).
  have hinj : Function.Injective
      (algebraMap (presheafValue C.base) (∀ D : { D // D ∈ C.covers }, presheafValue D.1)) :=
    FaithfulSMul.algebraMap_injective _ _
  intro x y hxy
  apply hinj
  funext D
  change restrictionMapHom C.base D.1 (C.hsubset D.1 D.2) x =
    restrictionMapHom C.base D.1 (C.hsubset D.1 D.2) y
  exact congr_fun hxy D

/-- **Cor 8.32, topological inducing half**: `productRestrictionSub` carries the subspace
topology of its image inside `∏ O_X(Uᵢ)`. This is the open-mapping / strictness content
behind Wedhorn's "sheaf of **complete topological** rings" — supplied in the repo by the
Tate-absorbing Banach OMT (`productRestrictionSubToEqualizer_isOpenMap`, `BanachOMT.lean`,
Wedhorn Prop 6.18). Delegates to the single canonical inducing residual
`productRestrictionSub_isInducing_tate` (`StructureSheaf.lean`, the 6.18-OMT leaf); inducing
is purely topological, so the Def-7.29 hypothesis `hC` is not needed. -/
theorem cor_8_32_productRestrictionSub_isInducing (C : RationalCoveringData A)
    (hC : C.IsRational) :
    Topology.IsInducing (productRestrictionSub A C) :=
  productRestrictionSub_isInducing_tate (A := A) C

/-- **Corollary 8.32, topological strengthening** (the full `embedding` field of `IsSheafy`):
the product restriction is a topological embedding = topological inducing + injectivity. -/
theorem cor_8_32_productRestrictionSub_isEmbedding (C : RationalCoveringData A)
    (hC : C.IsRational) :
    Topology.IsEmbedding (productRestrictionSub A C) :=
  ⟨cor_8_32_productRestrictionSub_isInducing C hC,
    cor_8_32_productRestrictionSub_injective C hC⟩

end Wedhorn828Tail

end ValuationSpectrum
