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
public import LeanPool.UniformSheafyTateDomains.AdicSpaces.FJP.TateBallResidue
public import LeanPool.UniformSheafyTateDomains.AdicSpaces.FJP.CDVFNoetherian
public import LeanPool.UniformSheafyTateDomains.AdicSpaces.NoetherianGDomain
public import LeanPool.UniformSheafyTateDomains.AdicSpaces.GeometricSeries
public import Mathlib.RingTheory.Jacobson.Artinian
public import LeanPool.UniformSheafyTateDomains.AdicSpaces.Bounded

/-!
# The affinoid Nullstellensatz for Tate algebras over a noetherian unit ball

([hrw-decomposition] "THE TATE LEAF DECOMPOSED", leaves 3/6/8/9/11.)  For
`K` with noetherian unit ball and a uniformizer `ϖ`, every maximal ideal `𝔪`
of `K⟨T₁,…,T_m⟩ = P K m` has residue field finite over `K`.  The route is the
DVR integral model: `B := T°/(𝔪 ∩ T°)` is a noetherian domain with `B[1/ϖ]`
the residue field; the G-domain lemma makes `B/ϖB` zero-dimensional and of
finite type over the residue ring of `𝒪_K`, hence finite; topological
Nakayama lifts finiteness to `B`, and localization finishes.
-/

@[expose] public section

@[expose] public section

open scoped Classical NormedField Valued

namespace FiniteJet.GraphKoszul

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
  [CompleteSpace K]
variable (ϖ : FiniteJetOver.Uniformizer K) {m : ℕ}

/-- The scaling constant of the integral Tate algebra at a uniformizer. -/
noncomputable abbrev piBall : ↥(unitBall (P K m)) :=
  tConstBall (E := K) (m := m) ϖ.val ϖ.norm_val_lt_one

theorem piBall_coe :
    ((piBall (m := m) ϖ) : P K m) = polyToP (MvPolynomial.C ϖ.val) := by
  show polyBall (tConstPoly (E := K) (m := m) ϖ.val ϖ.norm_val_lt_one) = _
  rw [tConstPoly, polyBall, RingHom.comp_apply, MvPolynomial.map_C]
  rfl

/-- **Leaf 3 (extracted from `Uniformizer.isNoetherianRing_P`)**: the Tate
algebra is the localization of its unit ball at the powers of the scaling
constant. -/
theorem isLocalization_powers_piBall :
    letI : Algebra ↥(unitBall (P K m)) (P K m) :=
      (unitBall (P K m)).subtype.toAlgebra
    IsLocalization (Submonoid.powers (piBall (m := m) ϖ)) (P K m) := by
  letI : Algebra ↥(unitBall (P K m)) (P K m) :=
    (unitBall (P K m)).subtype.toAlgebra
  refine ⟨⟨?_, ?_, ?_⟩⟩
  · rintro ⟨y, k, rfl⟩
    show IsUnit ((((piBall (m := m) ϖ) ^ k : ↥(unitBall (P K m)))) : P K m)
    rw [SubmonoidClass.coe_pow, piBall_coe]
    exact (isUnit_tP ϖ.val ϖ.isUnit_val).pow k
  · intro F
    obtain ⟨n, hn⟩ : ∃ n : ℕ, ‖ϖ.val‖ ^ n * ‖F‖ ≤ 1 := by
      rcases eq_or_ne ‖F‖ 0 with h0 | h0
      · exact ⟨0, by rw [h0, mul_zero]; exact zero_le_one⟩
      · have hpos : 0 < ‖F‖ := lt_of_le_of_ne (norm_nonneg F) (Ne.symm h0)
        obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (inv_pos.mpr hpos)
          ϖ.norm_val_lt_one
        exact ⟨n, by
          calc ‖ϖ.val‖ ^ n * ‖F‖ ≤ ‖F‖⁻¹ * ‖F‖ :=
                mul_le_mul_of_nonneg_right hn.le (norm_nonneg _)
            _ = 1 := inv_mul_cancel₀ (ne_of_gt hpos)⟩
    have hmem : ‖polyToP (MvPolynomial.C ϖ.val) ^ n * F‖ ≤ 1 := by
      rw [norm_pow_mul_of_scale (E := P K m)
        (fun G => by
          rw [norm_tP ϖ.val ϖ.norm_val_mul]
          exact norm_tP_mul ϖ.val ϖ.norm_val_mul G) n,
        norm_tP ϖ.val ϖ.norm_val_mul]
      exact hn
    refine ⟨(⟨polyToP (MvPolynomial.C ϖ.val) ^ n * F, hmem⟩,
      ⟨(piBall (m := m) ϖ) ^ n, n, rfl⟩), ?_⟩
    show F * ((((piBall (m := m) ϖ) ^ n : ↥(unitBall (P K m)))) : P K m) =
      polyToP (MvPolynomial.C ϖ.val) ^ n * F
    rw [SubmonoidClass.coe_pow, piBall_coe]
    exact mul_comm F _
  · intro x y h
    refine ⟨1, ?_⟩
    have hinj : Function.Injective ((unitBall (P K m)).subtype) :=
      Subtype.val_injective
    rw [hinj h]

section MaximalIdeal

variable (𝔪 : Ideal (P K m)) [h𝔪 : 𝔪.IsMaximal]

/-- The integral contraction of a maximal ideal. -/
noncomputable abbrev ballContraction : Ideal ↥(unitBall (P K m)) :=
  𝔪.comap (unitBall (P K m)).subtype

/-- The integral model of the residue field. -/
noncomputable abbrev IntegralModel : Type _ :=
  ↥(unitBall (P K m)) ⧸ ballContraction (m := m) 𝔪

instance : (ballContraction (m := m) 𝔪).IsPrime :=
  Ideal.comap_isPrime _ _

noncomputable instance : CommRing (IntegralModel (m := m) 𝔪) :=
  Ideal.Quotient.commRing _

instance : IsDomain (IntegralModel (m := m) 𝔪) :=
  Ideal.Quotient.isDomain _

include ϖ in
theorem isNoetherianRing_integralModel
    (hK₀ : IsNoetherianRing (unitBall K)) :
    IsNoetherianRing (IntegralModel (m := m) 𝔪) := by
  haveI hball : IsNoetherianRing ↥(unitBall (P K m)) :=
    FiniteJetOver.Uniformizer.isNoetherianRing_unitBall_P ϖ hK₀ m
  exact isNoetherianRing_of_surjective _ _
    (Ideal.Quotient.mk (ballContraction (m := m) 𝔪))
    Ideal.Quotient.mk_surjective

/-- A ring isomorphic to a field is a field. -/
theorem isField_of_ringEquiv {A B : Type*} [CommRing A] [CommRing B]
    (e : A ≃+* B) (hB : IsField B) : IsField A := by
  refine ⟨?_, mul_comm, ?_⟩
  · obtain ⟨x, y, hxy⟩ := hB.exists_pair_ne
    exact ⟨e.symm x, e.symm y, fun h => hxy (by
      have := congrArg e h
      simpa using this)⟩
  · intro a ha
    have hea : e a ≠ 0 := fun h0 => ha (by
      have := congrArg e.symm h0
      simpa using this)
    obtain ⟨b, hb⟩ := hB.mul_inv_cancel hea
    refine ⟨e.symm b, ?_⟩
    have h1 : e (a * e.symm b) = 1 := by
      rw [map_mul, RingEquiv.apply_symm_apply, hb]
    have := congrArg e.symm h1
    simpa using this

theorem piBall_notMem_ballContraction :
    piBall (m := m) ϖ ∉ ballContraction (m := m) 𝔪 := by
  intro hmem
  have hmem' : (unitBall (P K m)).subtype (piBall (m := m) ϖ) ∈ 𝔪 := hmem
  have hunit : IsUnit ((unitBall (P K m)).subtype (piBall (m := m) ϖ)) := by
    show IsUnit ((piBall (m := m) ϖ) : P K m)
    rw [piBall_coe]
    exact isUnit_tP ϖ.val ϖ.isUnit_val
  exact h𝔪.ne_top (Ideal.eq_top_of_isUnit_mem _ hmem' hunit)

/-- The scaling constant in the integral model. -/
noncomputable abbrev piBar : IntegralModel (m := m) 𝔪 :=
  Ideal.Quotient.mk _ (piBall (m := m) ϖ)

theorem piBar_ne_zero : piBar (m := m) ϖ 𝔪 ≠ 0 := by
  rw [Ne, Ideal.Quotient.eq_zero_iff_mem]
  exact piBall_notMem_ballContraction ϖ 𝔪

/-- The scaling constant is not a unit of the integral model: an inverse would
exhibit `1 - ϖ·g ∈ 𝔪` with `‖ϖ·g‖ < 1`, contradicting the Neumann series. -/
theorem not_isUnit_piBar : ¬ IsUnit (piBar (m := m) ϖ 𝔪) := by
  rintro ⟨u, hu⟩
  obtain ⟨g, hg⟩ := Ideal.Quotient.mk_surjective
    ((↑u⁻¹ : IntegralModel (m := m) 𝔪))
  have h1 : Ideal.Quotient.mk (ballContraction (m := m) 𝔪)
      (1 - piBall (m := m) ϖ * g) = 0 := by
    rw [map_sub, map_one, map_mul, hg]
    rw [show Ideal.Quotient.mk (ballContraction (m := m) 𝔪)
        (piBall (m := m) ϖ) = piBar (m := m) ϖ 𝔪 from rfl, ← hu]
    rw [Units.mul_inv]
    exact sub_self 1
  have h2 : (1 - piBall (m := m) ϖ * g) ∈ ballContraction (m := m) 𝔪 :=
    Ideal.Quotient.eq_zero_iff_mem.mp h1
  have h2' : (unitBall (P K m)).subtype (1 - piBall (m := m) ϖ * g) ∈ 𝔪 := h2
  have h3 : IsUnit ((unitBall (P K m)).subtype
      (1 - piBall (m := m) ϖ * g)) := by
    have h4 : (unitBall (P K m)).subtype (1 - piBall (m := m) ϖ * g) =
        1 - ((piBall (m := m) ϖ : P K m)) * ((g : ↥(unitBall (P K m))) :
          P K m) := rfl
    rw [h4]
    have hnorm : ‖((piBall (m := m) ϖ : P K m)) * ((g :
        ↥(unitBall (P K m))) : P K m)‖ < 1 := by
      refine lt_of_le_of_lt (norm_mul_le _ _) ?_
      have hπ : ‖((piBall (m := m) ϖ : P K m))‖ = ‖ϖ.val‖ := by
        rw [piBall_coe]
        exact norm_tP ϖ.val ϖ.norm_val_mul
      have hgle : ‖((g : ↥(unitBall (P K m))) : P K m)‖ ≤ 1 :=
        (mem_unitBall_iff _ _).mp g.2
      calc ‖((piBall (m := m) ϖ : P K m))‖ *
            ‖((g : ↥(unitBall (P K m))) : P K m)‖
          ≤ ‖((piBall (m := m) ϖ : P K m))‖ * 1 :=
            mul_le_mul_of_nonneg_left hgle (norm_nonneg _)
        _ = ‖ϖ.val‖ := by rw [mul_one, hπ]
        _ < 1 := ϖ.norm_val_lt_one
    have hnil : IsTopologicallyNilpotent
        (((piBall (m := m) ϖ : P K m)) * ((g : ↥(unitBall (P K m))) :
          P K m)) :=
      tendsto_pow_atTop_nhds_zero_of_norm_lt_one hnorm
    exact hnil.isUnit_one_sub
  exact h𝔪.ne_top (Ideal.eq_top_of_isUnit_mem _ h2' h3)

/-- The integral model maps to the residue field. -/
noncomputable def modelToResidue :
    IntegralModel (m := m) 𝔪 →+* (P K m ⧸ 𝔪) :=
  Ideal.quotientMap 𝔪 (unitBall (P K m)).subtype le_rfl

theorem modelToResidue_mk (b : ↥(unitBall (P K m))) :
    modelToResidue (m := m) 𝔪 (Ideal.Quotient.mk _ b) =
      Ideal.Quotient.mk 𝔪 ((unitBall (P K m)).subtype b) := rfl

/-- **The residue field is the localization of the integral model at the
scaling constant** ([hrw-decomposition] Tate leaf 6): units, surjectivity via
the ball localization, and injectivity mod the contraction. -/
theorem isLocalization_residue :
    letI : Algebra (IntegralModel (m := m) 𝔪) (P K m ⧸ 𝔪) :=
      (modelToResidue (m := m) 𝔪).toAlgebra
    IsLocalization (Submonoid.powers (piBar (m := m) ϖ 𝔪))
      (P K m ⧸ 𝔪) := by
  letI : Algebra (IntegralModel (m := m) 𝔪) (P K m ⧸ 𝔪) :=
    (modelToResidue (m := m) 𝔪).toAlgebra
  letI : Algebra ↥(unitBall (P K m)) (P K m) :=
    (unitBall (P K m)).subtype.toAlgebra
  haveI hloc : IsLocalization (Submonoid.powers (piBall (m := m) ϖ))
      (P K m) := isLocalization_powers_piBall ϖ
  refine ⟨⟨?_, ?_, ?_⟩⟩
  · rintro ⟨y, k, rfl⟩
    have h5 : algebraMap (IntegralModel (m := m) 𝔪) (P K m ⧸ 𝔪)
        ((piBar (m := m) ϖ 𝔪) ^ k) =
        Ideal.Quotient.mk 𝔪
          (((piBall (m := m) ϖ) ^ k : ↥(unitBall (P K m))) : P K m) := by
      rw [map_pow]
      rw [show algebraMap (IntegralModel (m := m) 𝔪) (P K m ⧸ 𝔪)
          (piBar (m := m) ϖ 𝔪) =
        Ideal.Quotient.mk 𝔪 ((piBall (m := m) ϖ : ↥(unitBall (P K m))) :
          P K m) from rfl]
      rw [← map_pow]
      rw [show ((((piBall (m := m) ϖ) : ↥(unitBall (P K m))) : P K m)) ^ k =
        (((piBall (m := m) ϖ) ^ k : ↥(unitBall (P K m))) : P K m) from
        (SubmonoidClass.coe_pow _ _).symm]
    rw [h5]
    refine IsUnit.map _ ?_
    rw [SubmonoidClass.coe_pow, piBall_coe]
    exact (isUnit_tP ϖ.val ϖ.isUnit_val).pow k
  · intro z
    obtain ⟨F, rfl⟩ := Ideal.Quotient.mk_surjective z
    obtain ⟨⟨b, sPow⟩, hb⟩ := IsLocalization.surj
      (Submonoid.powers (piBall (m := m) ϖ)) (S := P K m) F
    obtain ⟨n, hn⟩ := sPow.2
    refine ⟨(Ideal.Quotient.mk _ b, ⟨(piBar (m := m) ϖ 𝔪) ^ n, n, rfl⟩), ?_⟩
    have h6 : algebraMap (IntegralModel (m := m) 𝔪) (P K m ⧸ 𝔪)
        ((piBar (m := m) ϖ 𝔪) ^ n) =
        Ideal.Quotient.mk 𝔪 ((sPow : ↥(unitBall (P K m))) : P K m) := by
      rw [map_pow]
      rw [show algebraMap (IntegralModel (m := m) 𝔪) (P K m ⧸ 𝔪)
          (piBar (m := m) ϖ 𝔪) =
        Ideal.Quotient.mk 𝔪 ((piBall (m := m) ϖ : ↥(unitBall (P K m))) :
          P K m) from rfl]
      rw [← map_pow, ← hn]
      rw [show ((((piBall (m := m) ϖ) : ↥(unitBall (P K m))) : P K m)) ^ n =
        (((piBall (m := m) ϖ) ^ n : ↥(unitBall (P K m))) : P K m) from
        (SubmonoidClass.coe_pow _ _).symm]
    have h7 : algebraMap (IntegralModel (m := m) 𝔪) (P K m ⧸ 𝔪)
        (Ideal.Quotient.mk _ b) =
        Ideal.Quotient.mk 𝔪 ((b : ↥(unitBall (P K m))) : P K m) := rfl
    rw [h6, h7]
    show Ideal.Quotient.mk 𝔪 F * Ideal.Quotient.mk 𝔪 _ = _
    rw [← map_mul]
    have hb' : F * ((sPow : ↥(unitBall (P K m))) : P K m) =
        ((b : ↥(unitBall (P K m))) : P K m) := hb
    rw [hb']
  · intro x y h
    obtain ⟨bx, rfl⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨by', rfl⟩ := Ideal.Quotient.mk_surjective y
    refine ⟨1, ?_⟩
    have h8 : Ideal.Quotient.mk 𝔪 ((bx : ↥(unitBall (P K m))) : P K m) =
        Ideal.Quotient.mk 𝔪 ((by' : ↥(unitBall (P K m))) : P K m) := h
    have h9 : ((bx : ↥(unitBall (P K m))) : P K m) -
        ((by' : ↥(unitBall (P K m))) : P K m) ∈ 𝔪 :=
      Ideal.Quotient.eq.mp h8
    have h10 : bx - by' ∈ ballContraction (m := m) 𝔪 := h9
    rw [OneMemClass.coe_one, one_mul, one_mul]
    exact Ideal.Quotient.eq.mpr h10

/-- **The localization of the integral model away from the scaling constant is
a field** — it is the residue field of the maximal ideal. -/
theorem isField_localization_away_piBar :
    IsField (Localization.Away (piBar (m := m) ϖ 𝔪)) := by
  letI : Algebra (IntegralModel (m := m) 𝔪) (P K m ⧸ 𝔪) :=
    (modelToResidue (m := m) 𝔪).toAlgebra
  haveI hres := isLocalization_residue (m := m) ϖ 𝔪
  letI : Field (P K m ⧸ 𝔪) := Ideal.Quotient.field 𝔪
  have e := IsLocalization.algEquiv
    (Submonoid.powers (piBar (m := m) ϖ 𝔪))
    (Localization.Away (piBar (m := m) ϖ 𝔪)) (P K m ⧸ 𝔪)
  exact isField_of_ringEquiv e.toRingEquiv (Field.toIsField _)

/-- The special fibre of the integral model. -/
noncomputable abbrev SpecialFibre : Type _ :=
  IntegralModel (m := m) 𝔪 ⧸
    Ideal.span {piBar (m := m) ϖ 𝔪}

noncomputable instance : CommRing (SpecialFibre (m := m) ϖ 𝔪) :=
  Ideal.Quotient.commRing _

/-- **Leaf 8a (the G-domain payoff)**: the special fibre is zero-dimensional —
every prime of `B` over `ϖ` is nonzero, hence maximal. -/
theorem krullDimLE_zero_specialFibre
    (hK₀ : IsNoetherianRing (unitBall K)) :
    Ring.KrullDimLE 0 (SpecialFibre (m := m) ϖ 𝔪) := by
  haveI hBnoeth : IsNoetherianRing (IntegralModel (m := m) 𝔪) :=
    isNoetherianRing_integralModel ϖ 𝔪 hK₀
  rw [Ring.krullDimLE_zero_iff]
  intro q hq
  haveI := hq
  set J : Ideal (IntegralModel (m := m) 𝔪) :=
    q.comap (Ideal.Quotient.mk (Ideal.span {piBar (m := m) ϖ 𝔪})) with hJ
  haveI hJprime : J.IsPrime := Ideal.comap_isPrime _ _
  have hπJ : piBar (m := m) ϖ 𝔪 ∈ J := by
    rw [hJ, Ideal.mem_comap]
    rw [show Ideal.Quotient.mk (Ideal.span {piBar (m := m) ϖ 𝔪})
        (piBar (m := m) ϖ 𝔪) = 0 from
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self _)]
    exact q.zero_mem
  have hJ0 : J ≠ ⊥ := fun h0 => piBar_ne_zero ϖ 𝔪 (by
    rw [h0] at hπJ
    simpa using hπJ)
  have hJmax : J.IsMaximal :=
    Ideal.isMaximal_of_isPrime_of_ne_bot_of_isField_away
      (piBar_ne_zero ϖ 𝔪) (not_isUnit_piBar ϖ 𝔪)
      (isField_localization_away_piBar ϖ 𝔪) J hJprime hJ0
  -- transport maximality through the surjective quotient correspondence
  have hqmap : q = J.map (Ideal.Quotient.mk
      (Ideal.span {piBar (m := m) ϖ 𝔪})) := by
    rw [hJ]
    exact (Ideal.map_comap_of_surjective _
      Ideal.Quotient.mk_surjective q).symm
  rw [hqmap]
  haveI := hJmax
  refine Ideal.IsMaximal.map_of_surjective_of_ker_le
    Ideal.Quotient.mk_surjective (m := J) ?_
  rw [Ideal.mk_ker, hJ]
  intro x hx
  rw [Ideal.mem_comap]
  rw [Ideal.Quotient.eq_zero_iff_mem.mpr hx]
  exact q.zero_mem

end MaximalIdeal

section Residue

variable [IsDiscreteValuationRing ↥(Valued.integer K)]

/-- The uniformizer as a unit-ball element, in the residue-equivalence's
membership form. -/
noncomputable abbrev piUnitBall : ↥(unitBall K) :=
  ⟨ϖ.val, (mem_unitBall_iff (E := K) ϖ.val).mpr ϖ.norm_val_lt_one.le⟩

/-- The uniformizer span is maximal in the unit ball (transport of the DVR
maximal ideal along `unitBallEquivInteger`). -/
theorem span_piUnitBall_isMaximal :
    (Ideal.span {piUnitBall ϖ}).IsMaximal := by
  have hmax : (Ideal.span {ϖ.elem}).IsMaximal := by
    have h1 : IsLocalRing.maximalIdeal ↥(Valued.integer K) =
        Ideal.span {ϖ.elem} :=
      (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ.elem).mp
        ϖ.irreducible
    rw [← h1]
    exact IsLocalRing.maximalIdeal.isMaximal _
  haveI := hmax
  have hmap : Ideal.map (FiniteJetOver.unitBallEquivInteger K).toRingHom
      (Ideal.span {piUnitBall ϖ}) = Ideal.span {ϖ.elem} := by
    rw [Ideal.map_span, Set.image_singleton]
    refine congrArg (fun z => Ideal.span {z}) ?_
    refine Subtype.ext ?_
    show ((FiniteJetOver.unitBallEquivInteger K) (piUnitBall ϖ) :
      Valued.integer K).1 = (ϖ.elem : K)
    rfl
  have h2 : Ideal.span {piUnitBall ϖ} =
      Ideal.comap (FiniteJetOver.unitBallEquivInteger K).toRingHom
        (Ideal.span {ϖ.elem}) := by
    rw [← hmap, Ideal.comap_map_of_bijective
      (f := (FiniteJetOver.unitBallEquivInteger K).toRingHom)
      ((FiniteJetOver.unitBallEquivInteger K).bijective)]
  rw [h2]
  exact Ideal.comap_isMaximal_of_surjective _
    (FiniteJetOver.unitBallEquivInteger K).surjective

/-- The residue field of the base. -/
noncomputable abbrev ResidueK : Type _ :=
  ↥(unitBall K) ⧸ Ideal.span {piUnitBall ϖ}

noncomputable instance : CommRing (ResidueK ϖ) := Ideal.Quotient.commRing _

noncomputable instance : Field (ResidueK ϖ) :=
  haveI := span_piUnitBall_isMaximal ϖ
  Ideal.Quotient.field _

/-- Norm characterization of the uniformizer-power submodules of the unit
ball: divisibility is a norm bound (the field norm divides exactly). -/
theorem mem_span_piUnitBall_pow_iff (k : ℕ) (x : ↥(unitBall K)) :
    x ∈ ((Ideal.span {piUnitBall ϖ}) ^ k • ⊤ :
      Submodule ↥(unitBall K) ↥(unitBall K)) ↔
    ‖(x : K)‖ ≤ ‖ϖ.val‖ ^ k := by
  rw [ideal_smul_top_self, Ideal.span_singleton_pow]
  constructor
  · intro hx
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp hx
    rw [← hc]
    have h1 : ((c * piUnitBall ϖ ^ k : ↥(unitBall K)) : K) =
        (c : K) * ϖ.val ^ k := rfl
    rw [h1, norm_mul, norm_pow]
    calc ‖(c : K)‖ * ‖ϖ.val‖ ^ k ≤ 1 * ‖ϖ.val‖ ^ k :=
          mul_le_mul_of_nonneg_right ((mem_unitBall_iff _ _).mp c.2)
            (by positivity)
      _ = ‖ϖ.val‖ ^ k := one_mul _
  · intro hx
    have hπk : (ϖ.val : K) ^ k ≠ 0 := pow_ne_zero _ ϖ.val_ne_zero
    have hc1 : ‖(x : K) / ϖ.val ^ k‖ ≤ 1 := by
      rw [norm_div, norm_pow, div_le_one (pow_pos ϖ.norm_val_pos k)]
      exact hx
    refine Ideal.mem_span_singleton'.mpr
      ⟨⟨(x : K) / ϖ.val ^ k, (mem_unitBall_iff _ _).mpr hc1⟩, ?_⟩
    refine Subtype.ext ?_
    show ((x : K) / ϖ.val ^ k) * (ϖ.val ^ k) = (x : K)
    rw [div_mul_cancel₀ _ hπk]

/-- **Leaf 11a: the unit ball is precomplete at the uniformizer** — adic
Cauchy sequences are norm Cauchy sequences, which converge by completeness of
`K`, with limits in the closed ball and adically close to the tail. -/
theorem isPrecomplete_span_piUnitBall :
    IsPrecomplete (Ideal.span {piUnitBall ϖ}) ↥(unitBall K) := by
  constructor
  intro f hf
  have hdiff : ∀ {a b : ℕ}, a ≤ b →
      ‖((f a : ↥(unitBall K)) : K) - ((f b : ↥(unitBall K)) : K)‖ ≤
        ‖ϖ.val‖ ^ a := by
    intro a b hab
    have h1 := hf hab
    rw [SModEq.sub_mem] at h1
    have h2 := (mem_span_piUnitBall_pow_iff ϖ a (f a - f b)).mp h1
    exact h2
  have hcauchy : CauchySeq (fun n => ((f n : ↥(unitBall K)) : K)) := by
    refine cauchySeq_of_le_geometric ‖ϖ.val‖ 1 ϖ.norm_val_lt_one fun n => ?_
    rw [dist_eq_norm, one_mul]
    exact hdiff (Nat.le_succ n)
  obtain ⟨L, hL⟩ := cauchySeq_tendsto_of_complete hcauchy
  have hLball : ‖L‖ ≤ 1 := by
    refine le_of_tendsto (hL.norm) ?_
    filter_upwards with n
    exact (mem_unitBall_iff _ _).mp (f n).2
  refine ⟨⟨L, (mem_unitBall_iff _ _).mpr hLball⟩, fun n => ?_⟩
  rw [SModEq.sub_mem]
  rw [mem_span_piUnitBall_pow_iff]
  have htail : Filter.Tendsto
      (fun j => ‖((f n : ↥(unitBall K)) : K) -
        ((f j : ↥(unitBall K)) : K)‖) Filter.atTop
      (nhds ‖((f n : ↥(unitBall K)) : K) - L‖) := by
    exact ((tendsto_const_nhds.sub hL).norm)
  refine le_of_tendsto htail ?_
  filter_upwards [Filter.eventually_ge_atTop n] with j hj
  exact hdiff hj

variable (𝔪 : Ideal (P K m)) [h𝔪 : 𝔪.IsMaximal]

/-- The factor map from the Tate residue ring onto the special fibre. -/
noncomputable def toSpecialFibre :
    (↥(unitBall (P K m)) ⧸ Ideal.span {piBall (m := m) ϖ}) →+*
      SpecialFibre (m := m) ϖ 𝔪 :=
  Ideal.Quotient.lift (Ideal.span {piBall (m := m) ϖ})
    ((Ideal.Quotient.mk (Ideal.span {piBar (m := m) ϖ 𝔪})).comp
      (Ideal.Quotient.mk (ballContraction (m := m) 𝔪)))
    (by
      intro a ha
      obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp ha
      rw [← hc]
      rw [RingHom.comp_apply, map_mul]
      rw [show Ideal.Quotient.mk (ballContraction (m := m) 𝔪)
          (piBall (m := m) ϖ) = piBar (m := m) ϖ 𝔪 from rfl]
      rw [map_mul]
      rw [show Ideal.Quotient.mk (Ideal.span {piBar (m := m) ϖ 𝔪})
          (piBar (m := m) ϖ 𝔪) = 0 from
        Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self _)]
      rw [mul_zero])

theorem toSpecialFibre_surjective :
    Function.Surjective (toSpecialFibre (m := m) ϖ 𝔪) := by
  intro z
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective z
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective b
  exact ⟨Ideal.Quotient.mk _ x, rfl⟩

/-- The polynomial presentation of the special fibre over the residue field. -/
noncomputable def fibreFromPoly :
    MvPolynomial (Fin m) (ResidueK ϖ) →+* SpecialFibre (m := m) ϖ 𝔪 :=
  (toSpecialFibre (m := m) ϖ 𝔪).comp
    (unitBallPResidueEquiv (E := K) (m := m) ϖ.val ϖ.isUnit_val
      ϖ.norm_val_lt_one ϖ.norm_val_pos ϖ.norm_val_mul).symm.toRingHom

theorem fibreFromPoly_surjective :
    Function.Surjective (fibreFromPoly (m := m) ϖ 𝔪) :=
  (toSpecialFibre_surjective (m := m) ϖ 𝔪).comp
    (unitBallPResidueEquiv (E := K) (m := m) ϖ.val ϖ.isUnit_val
      ϖ.norm_val_lt_one ϖ.norm_val_pos ϖ.norm_val_mul).symm.surjective

/-- **Leaf 9: the special fibre is a finite module over the residue field**
(finite type via the polynomial presentation, zero-dimensional by the
G-domain lemma, hence finite by the Artinian criterion). -/
theorem module_finite_specialFibre (hK₀ : IsNoetherianRing (unitBall K)) :
    letI : Algebra (ResidueK ϖ) (SpecialFibre (m := m) ϖ 𝔪) :=
      ((fibreFromPoly (m := m) ϖ 𝔪).comp
        (MvPolynomial.C : ResidueK ϖ →+* MvPolynomial (Fin m)
          (ResidueK ϖ))).toAlgebra
    Module.Finite (ResidueK ϖ) (SpecialFibre (m := m) ϖ 𝔪) := by
  letI : Algebra (ResidueK ϖ) (SpecialFibre (m := m) ϖ 𝔪) :=
    ((fibreFromPoly (m := m) ϖ 𝔪).comp
      (MvPolynomial.C : ResidueK ϖ →+* MvPolynomial (Fin m)
        (ResidueK ϖ))).toAlgebra
  haveI hft : Algebra.FiniteType (ResidueK ϖ)
      (SpecialFibre (m := m) ϖ 𝔪) :=
    Algebra.FiniteType.of_surjective
      (⟨fibreFromPoly (m := m) ϖ 𝔪, fun c => rfl⟩ :
        MvPolynomial (Fin m) (ResidueK ϖ) →ₐ[ResidueK ϖ]
          SpecialFibre (m := m) ϖ 𝔪)
      (fibreFromPoly_surjective (m := m) ϖ 𝔪)
  exact (Module.finite_iff_krullDimLE_zero (ResidueK ϖ)
    (SpecialFibre (m := m) ϖ 𝔪)).mpr
    (krullDimLE_zero_specialFibre (m := m) ϖ 𝔪 hK₀)

/-- **The constants compatibility**: the polynomial presentation of the
special fibre restricts on constants to the reduction of the unit-ball
constants. -/
theorem fibreFromPoly_C_mk (d : ↥(unitBall K)) :
    fibreFromPoly (m := m) ϖ 𝔪
      (MvPolynomial.C (Ideal.Quotient.mk (Ideal.span {piUnitBall ϖ}) d)) =
    Ideal.Quotient.mk (Ideal.span {piBar (m := m) ϖ 𝔪})
      (Ideal.Quotient.mk (ballContraction (m := m) 𝔪)
        (polyBallRes (E := K) (m := m) (MvPolynomial.C d))) := by
  have hfwd := unitBallPResidueEquiv_mk_C (E := K) (m := m) ϖ.val
    ϖ.isUnit_val ϖ.norm_val_lt_one ϖ.norm_val_pos ϖ.norm_val_mul d
  have hsymm : (unitBallPResidueEquiv (E := K) (m := m) ϖ.val ϖ.isUnit_val
      ϖ.norm_val_lt_one ϖ.norm_val_pos ϖ.norm_val_mul).symm
      (MvPolynomial.C (Ideal.Quotient.mk (Ideal.span {piUnitBall ϖ}) d)) =
      Ideal.Quotient.mk _ (polyBallRes (E := K) (m := m)
        (MvPolynomial.C d)) := by
    rw [RingEquiv.symm_apply_eq]
    exact hfwd.symm
  show toSpecialFibre (m := m) ϖ 𝔪
      ((unitBallPResidueEquiv (E := K) (m := m) ϖ.val ϖ.isUnit_val
        ϖ.norm_val_lt_one ϖ.norm_val_pos ϖ.norm_val_mul).symm
        (MvPolynomial.C (Ideal.Quotient.mk (Ideal.span {piUnitBall ϖ}) d))) =
    _
  rw [hsymm]
  rfl

/-- The unit-ball constants hom into the integral model. -/
noncomputable def ballToModel : ↥(unitBall K) →+* IntegralModel (m := m) 𝔪 :=
  (Ideal.Quotient.mk (ballContraction (m := m) 𝔪)).comp
    ((polyBallRes (E := K) (m := m)).comp
      (MvPolynomial.C : ↥(unitBall K) →+*
        MvPolynomial (Fin m) ↥(unitBall K)))

theorem ballToModel_piUnitBall :
    ballToModel (m := m) 𝔪 (piUnitBall ϖ) = piBar (m := m) ϖ 𝔪 := rfl

/-- **The scalar coherence**: the uniformizer-power submodules of the integral
model over the unit ball are the powers of the reduced scaling ideal. -/
theorem span_smul_top_model (n : ℕ) :
    letI : Algebra ↥(unitBall K) (IntegralModel (m := m) 𝔪) :=
      (ballToModel (m := m) 𝔪).toAlgebra
    ((Ideal.span {piUnitBall ϖ}) ^ n • ⊤ :
      Submodule ↥(unitBall K) (IntegralModel (m := m) 𝔪)) =
    (((Ideal.span {piBar (m := m) ϖ 𝔪}) ^ n :
      Ideal (IntegralModel (m := m) 𝔪))).restrictScalars ↥(unitBall K) := by
  letI : Algebra ↥(unitBall K) (IntegralModel (m := m) 𝔪) :=
    (ballToModel (m := m) 𝔪).toAlgebra
  refine le_antisymm (Submodule.smul_le.mpr fun a ha x _ => ?_) fun x hx => ?_
  · rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton'] at ha
    obtain ⟨c, hc⟩ := ha
    rw [Submodule.restrictScalars_mem, Ideal.span_singleton_pow,
      Ideal.mem_span_singleton']
    refine ⟨ballToModel (m := m) 𝔪 c * x, ?_⟩
    have h1 : a • x = ballToModel (m := m) 𝔪 a * x := rfl
    rw [h1, ← hc, map_mul, map_pow, ballToModel_piUnitBall]
    ring
  · rw [Submodule.restrictScalars_mem, Ideal.span_singleton_pow,
      Ideal.mem_span_singleton'] at hx
    obtain ⟨y, hy⟩ := hx
    rw [← hy]
    have h2 : y * piBar (m := m) ϖ 𝔪 ^ n = (piUnitBall ϖ ^ n) • y := by
      have h3 : (piUnitBall ϖ ^ n) • y =
          ballToModel (m := m) 𝔪 (piUnitBall ϖ ^ n) * y := rfl
      rw [h3, map_pow, ballToModel_piUnitBall]
      ring
    rw [h2]
    exact Submodule.smul_mem_smul (Ideal.pow_mem_pow
      (Ideal.mem_span_singleton_self _) n) Submodule.mem_top

/-- **Leaf 11c: the integral model is uniformizer-adically Hausdorff** (Krull
intersection in the noetherian domain). -/
theorem isHausdorff_model (hK₀ : IsNoetherianRing (unitBall K)) :
    letI : Algebra ↥(unitBall K) (IntegralModel (m := m) 𝔪) :=
      (ballToModel (m := m) 𝔪).toAlgebra
    IsHausdorff (Ideal.span {piUnitBall ϖ}) (IntegralModel (m := m) 𝔪) := by
  letI : Algebra ↥(unitBall K) (IntegralModel (m := m) 𝔪) :=
    (ballToModel (m := m) 𝔪).toAlgebra
  haveI := isNoetherianRing_integralModel ϖ 𝔪 hK₀
  constructor
  intro x hx
  have hall : ∀ n : ℕ, x ∈ ((Ideal.span {piBar (m := m) ϖ 𝔪}) ^ n :
      Ideal (IntegralModel (m := m) 𝔪)) := by
    intro n
    have h1 := hx n
    rw [SModEq.zero, span_smul_top_model (m := m) ϖ 𝔪 n,
      Submodule.restrictScalars_mem] at h1
    exact h1
  have hne : (Ideal.span {piBar (m := m) ϖ 𝔪} :
      Ideal (IntegralModel (m := m) 𝔪)) ≠ ⊤ := by
    rw [Ne, Ideal.span_singleton_eq_top]
    exact not_isUnit_piBar ϖ 𝔪
  have hbot := Ideal.iInf_pow_eq_bot_of_isDomain
    (I := Ideal.span {piBar (m := m) ϖ 𝔪}) hne
  have hmem : x ∈ (⨅ n : ℕ, (Ideal.span {piBar (m := m) ϖ 𝔪}) ^ n :
      Ideal (IntegralModel (m := m) 𝔪)) :=
    Ideal.mem_iInf.mpr hall
  rw [hbot] at hmem
  simpa using hmem

include ϖ in
/-- **Leaf 11d: the integral model is a finite module over the unit ball**
(topological Nakayama over the finite special fibre). -/
theorem module_finite_integralModel
    (hK₀ : IsNoetherianRing (unitBall K)) :
    letI : Algebra ↥(unitBall K) (IntegralModel (m := m) 𝔪) :=
      (ballToModel (m := m) 𝔪).toAlgebra
    Module.Finite ↥(unitBall K) (IntegralModel (m := m) 𝔪) := by
  letI : Algebra ↥(unitBall K) (IntegralModel (m := m) 𝔪) :=
    (ballToModel (m := m) 𝔪).toAlgebra
  haveI := isPrecomplete_span_piUnitBall ϖ
  haveI := isHausdorff_model (m := m) ϖ 𝔪 hK₀
  refine Module.Finite.of_finite_quotient_smul_top_of_isPrecomplete
    (Ideal.span {piUnitBall ϖ}) ?_
  -- identify the quotient with the special fibre as unit-ball modules
  have hEq : ((Ideal.span {piUnitBall ϖ}) • ⊤ :
      Submodule ↥(unitBall K) (IntegralModel (m := m) 𝔪)) =
      (((Ideal.span {piBar (m := m) ϖ 𝔪}) :
        Ideal (IntegralModel (m := m) 𝔪))).restrictScalars ↥(unitBall K) := by
    have h4 := span_smul_top_model (m := m) ϖ 𝔪 1
    rw [pow_one, pow_one] at h4
    exact h4
  let e1 := Submodule.quotEquivOfEq _ _ hEq
  let e2 := Submodule.Quotient.restrictScalarsEquiv ↥(unitBall K)
    ((Ideal.span {piBar (m := m) ϖ 𝔪}) :
      Ideal (IntegralModel (m := m) 𝔪))
  -- finiteness of the special fibre over the unit ball, elementwise
  have hfin : Module.Finite ↥(unitBall K)
      (IntegralModel (m := m) 𝔪 ⧸
        ((Ideal.span {piBar (m := m) ϖ 𝔪}) :
          Ideal (IntegralModel (m := m) 𝔪))) := by
    haveI hfinK := module_finite_specialFibre (m := m) ϖ 𝔪 hK₀
    -- pull generators: k-span-⊤ + k = unit-ball image ⇒ unit-ball span-⊤
    letI : Algebra (ResidueK ϖ) (SpecialFibre (m := m) ϖ 𝔪) :=
      ((fibreFromPoly (m := m) ϖ 𝔪).comp
        (MvPolynomial.C : ResidueK ϖ →+* MvPolynomial (Fin m)
          (ResidueK ϖ))).toAlgebra
    obtain ⟨T, hT⟩ := hfinK.fg_top
    refine ⟨⟨T, ?_⟩⟩
    rw [eq_top_iff]
    intro z _
    have hz : z ∈ Submodule.span (ResidueK ϖ) (T : Set _) := by
      rw [hT]; exact Submodule.mem_top
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hz
    · intro t ht
      exact Submodule.subset_span ht
    · exact Submodule.zero_mem _
    · intro a b _ _ ha hb
      exact Submodule.add_mem _ ha hb
    · intro c a _ ha
      -- a k-scalar is the image of a unit-ball scalar
      obtain ⟨d, hd⟩ := Ideal.Quotient.mk_surjective c
      have hsc : c • a = d • a := by
        obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective a
        have h5 : c • (Ideal.Quotient.mk
            (Ideal.span {piBar (m := m) ϖ 𝔪}) b) =
            fibreFromPoly (m := m) ϖ 𝔪 (MvPolynomial.C c) *
              Ideal.Quotient.mk (Ideal.span {piBar (m := m) ϖ 𝔪}) b := rfl
        have h6 : d • (Ideal.Quotient.mk
            (Ideal.span {piBar (m := m) ϖ 𝔪}) b) =
            Ideal.Quotient.mk (Ideal.span {piBar (m := m) ϖ 𝔪})
              (d • b) := rfl
        have h7 : (d • b : IntegralModel (m := m) 𝔪) =
            ballToModel (m := m) 𝔪 d * b := rfl
        rw [h5, h6, h7, ← hd, fibreFromPoly_C_mk, map_mul]
        rfl
      rw [hsc]
      exact Submodule.smul_mem _ _ ha
  exact Module.Finite.equiv (e1.trans e2).symm

/-- The Tate residue ring as a `K`-algebra through the constants. -/
noncomputable def constantsToResidue : K →+* (P K m ⧸ 𝔪) :=
  (Ideal.Quotient.mk 𝔪).comp
    ((polyToP (E := K) (m := m)).comp
      (MvPolynomial.C : K →+* MvPolynomial (Fin m) K))

include ϖ in
/-- **The affinoid Nullstellensatz** ([hrw-decomposition] Tate leaf 11,
endpoint): the residue ring of the Tate algebra at a maximal ideal is a
finite `K`-module — the localization unit is absorbed into the `K`-scalars.
-/
theorem module_finite_residue (hK₀ : IsNoetherianRing (unitBall K)) :
    letI : Algebra K (P K m ⧸ 𝔪) :=
      (constantsToResidue (m := m) 𝔪).toAlgebra
    Module.Finite K (P K m ⧸ 𝔪) := by
  letI : Algebra K (P K m ⧸ 𝔪) :=
    (constantsToResidue (m := m) 𝔪).toAlgebra
  letI : Algebra ↥(unitBall K) (IntegralModel (m := m) 𝔪) :=
    (ballToModel (m := m) 𝔪).toAlgebra
  letI : Algebra (IntegralModel (m := m) 𝔪) (P K m ⧸ 𝔪) :=
    (modelToResidue (m := m) 𝔪).toAlgebra
  haveI hloc := isLocalization_residue (m := m) ϖ 𝔪
  haveI hfinB := module_finite_integralModel (m := m) ϖ 𝔪 hK₀
  obtain ⟨T, hT⟩ := hfinB.fg_top
  -- every image of the integral model lies in the K-span of the generators
  have hmem : ∀ b : IntegralModel (m := m) 𝔪,
      modelToResidue (m := m) 𝔪 b ∈
        Submodule.span K ((T.image
          (fun b => modelToResidue (m := m) 𝔪 b) : Finset _) : Set _) := by
    intro b
    have hb0 : b ∈ (⊤ : Submodule ↥(unitBall K)
        (IntegralModel (m := m) 𝔪)) := Submodule.mem_top
    rw [← hT] at hb0
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hb0
    · intro t ht
      exact Submodule.subset_span (Finset.mem_coe.mpr
        (Finset.mem_image_of_mem _ ht))
    · rw [_root_.map_zero]
      exact Submodule.zero_mem _
    · intro a b _ _ ha hb'
      rw [map_add]
      exact Submodule.add_mem _ ha hb'
    · intro c x _ hx
      have h8 : modelToResidue (m := m) 𝔪 (c • x) =
          (c : K) • modelToResidue (m := m) 𝔪 x := by
        have h9 : c • x = ballToModel (m := m) 𝔪 c * x := rfl
        rw [h9, map_mul]
        have h10 : modelToResidue (m := m) 𝔪 (ballToModel (m := m) 𝔪 c) =
            constantsToResidue (m := m) 𝔪 (c : K) := by
          rw [show ballToModel (m := m) 𝔪 c = Ideal.Quotient.mk _
            (polyBallRes (E := K) (m := m) (MvPolynomial.C c)) from rfl,
            modelToResidue_mk]
          rw [show (unitBall (P K m)).subtype
              (polyBallRes (E := K) (m := m) (MvPolynomial.C c)) =
            polyBall (E := K) (m := m) (MvPolynomial.C c) from rfl]
          rw [show polyBall (E := K) (m := m) (MvPolynomial.C c) =
            polyToP (E := K) (m := m) (MvPolynomial.C (c : K)) from by
              rw [polyBall, RingHom.comp_apply, MvPolynomial.map_C]
              rfl]
          rfl
        rw [h10]
        rfl
      rw [h8]
      exact Submodule.smul_mem _ _ hx
  refine ⟨⟨T.image (fun b => modelToResidue (m := m) 𝔪 b), ?_⟩⟩
  rw [eq_top_iff]
  intro z _
  obtain ⟨⟨b, sPow⟩, hb⟩ := IsLocalization.surj
    (Submonoid.powers (piBar (m := m) ϖ 𝔪)) (S := P K m ⧸ 𝔪) z
  obtain ⟨n, hn⟩ := sPow.2
  have hn' : (piBar (m := m) ϖ 𝔪) ^ n =
      (sPow : IntegralModel (m := m) 𝔪) := hn
  have h11 : algebraMap (IntegralModel (m := m) 𝔪) (P K m ⧸ 𝔪)
      (sPow : IntegralModel (m := m) 𝔪) =
      constantsToResidue (m := m) 𝔪 (ϖ.val ^ n) := by
    rw [← hn']
    rw [show (algebraMap (IntegralModel (m := m) 𝔪) (P K m ⧸ 𝔪) :
      IntegralModel (m := m) 𝔪 →+* (P K m ⧸ 𝔪)) =
      modelToResidue (m := m) 𝔪 from rfl]
    rw [map_pow, map_pow]
    refine congrArg (· ^ n) ?_
    rw [show piBar (m := m) ϖ 𝔪 = Ideal.Quotient.mk _
      (piBall (m := m) ϖ) from rfl, modelToResidue_mk]
    rw [show (unitBall (P K m)).subtype (piBall (m := m) ϖ) =
      ((piBall (m := m) ϖ : ↥(unitBall (P K m))) : P K m) from rfl,
      piBall_coe]
    rfl
  have hne : (ϖ.val ^ n : K) ≠ 0 := pow_ne_zero _ ϖ.val_ne_zero
  have hz : z = ((ϖ.val ^ n)⁻¹ : K) •
      (modelToResidue (m := m) 𝔪 b) := by
    have h12 : ((ϖ.val ^ n)⁻¹ : K) • (modelToResidue (m := m) 𝔪 b) =
        constantsToResidue (m := m) 𝔪 ((ϖ.val ^ n)⁻¹) *
          modelToResidue (m := m) 𝔪 b := rfl
    rw [h12]
    have h13 : modelToResidue (m := m) 𝔪 b =
        algebraMap (IntegralModel (m := m) 𝔪) (P K m ⧸ 𝔪) b := rfl
    rw [h13, ← hb, h11]
    rw [← mul_assoc, mul_comm (constantsToResidue (m := m) 𝔪 _) z,
      mul_assoc, ← map_mul, inv_mul_cancel₀ hne, map_one, mul_one]
  rw [hz]
  exact Submodule.smul_mem _ _ (hmem b)

end Residue

section Descent

variable {K A S : Type*} [Field K] [CommRing A] [CommRing S]
variable [Algebra K A] [Algebra K S]

/-- **Contractions of finite-residue maximals are maximal**: if the residue
ring at a maximal ideal is module-finite over the base field, the
contraction along any algebra map is maximal (the finite-dimensional domain
quotient is a field). -/
theorem comap_isMaximal_of_finite_residue (f : A →ₐ[K] S)
    (𝔫 : Ideal S) [h𝔫 : 𝔫.IsMaximal] [hfin : Module.Finite K (S ⧸ 𝔫)] :
    (𝔫.comap (f : A →+* S)).IsMaximal := by
  haveI hcp : (𝔫.comap (f : A →+* S)).IsPrime := 𝔫.comap_isPrime _
  have hinj : Function.Injective (Ideal.quotientMapₐ 𝔫 f le_rfl) :=
    Ideal.quotientMap_injective
  haveI : Module.Finite K (A ⧸ 𝔫.comap (f : A →+* S)) :=
    Module.Finite.of_injective
      (Ideal.quotientMapₐ 𝔫 f le_rfl).toLinearMap hinj
  haveI : Algebra.IsIntegral K (A ⧸ 𝔫.comap (f : A →+* S)) :=
    Algebra.IsIntegral.of_finite _ _
  have hfield : IsField (A ⧸ 𝔫.comap (f : A →+* S)) :=
    isField_of_isIntegral_of_isField' (Field.toIsField K)
  exact Ideal.Quotient.maximal_of_isField _ hfield

/-- **Residue finiteness descends along module-finite extensions** (lying
over): if every maximal residue of `S` is finite over `K` and `S` is a
module-finite faithful `A`-algebra, every maximal residue of `A` is finite
over `K`. -/
theorem module_finite_residue_of_finite_extension
    [Algebra A S] [Module.Finite A S] [FaithfulSMul A S]
    [IsScalarTower K A S]
    (hres : ∀ (𝔫 : Ideal S), 𝔫.IsMaximal → Module.Finite K (S ⧸ 𝔫))
    (𝔪 : Ideal A) (h𝔪 : 𝔪.IsMaximal) : Module.Finite K (A ⧸ 𝔪) := by
  haveI := h𝔪
  haveI : Algebra.IsIntegral A S := Algebra.IsIntegral.of_finite A S
  obtain ⟨𝔫, h𝔫, h𝔫c⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral 𝔪
    (by
      rw [(RingHom.injective_iff_ker_eq_bot _).mp
        (FaithfulSMul.algebraMap_injective A S)]
      exact bot_le)
  haveI := h𝔫
  haveI := hres 𝔫 h𝔫
  have h1 : (𝔪 : Ideal A) =
      𝔫.comap ((IsScalarTower.toAlgHom K A S : A →ₐ[K] S) : A →+* S) :=
    h𝔫c.symm
  rw [h1]
  have hinj : Function.Injective
      (Ideal.quotientMapₐ 𝔫 (IsScalarTower.toAlgHom K A S) le_rfl) :=
    Ideal.quotientMap_injective
  exact Module.Finite.of_injective
    (Ideal.quotientMapₐ 𝔫 (IsScalarTower.toAlgHom K A S) le_rfl).toLinearMap
    hinj



end Descent

section IntegralRelations

variable (ϖ : FiniteJetOver.Uniformizer K)
variable [IsDiscreteValuationRing 𝒪[K]]
variable (𝔮 : Ideal (P K m)) [h𝔮 : 𝔮.IsMaximal]

/-- The variables lie in the unit ball of the Tate algebra. -/
theorem norm_polyToP_X_le_one (i : Fin m) :
    ‖(polyToP (MvPolynomial.X i) : P K m)‖ ≤ 1 := by
  have h1 : (polyToP (MvPolynomial.X i) : P K m) =
      polyBall (E := K) (m := m) (MvPolynomial.X i) := by
    rw [show polyBall (E := K) (m := m) (MvPolynomial.X i) =
      polyToP (MvPolynomial.map (FiniteJet.unitBall K).subtype
        (MvPolynomial.X i)) from rfl, MvPolynomial.map_X]
  rw [h1]
  exact norm_polyBall_le_one _

/-- The composite of the model maps is the constants map. -/
theorem modelToResidue_comp_ballToModel :
    (modelToResidue (m := m) 𝔮).comp (ballToModel (m := m) 𝔮) =
      (constantsToResidue 𝔮 : K →+* (P K m ⧸ 𝔮)).comp
        (FiniteJet.unitBall K).subtype := by
  refine RingHom.ext fun c => ?_
  show modelToResidue (m := m) 𝔮 (ballToModel (m := m) 𝔮 c) = _
  rw [show ballToModel (m := m) 𝔮 c = Ideal.Quotient.mk _
    (polyBallRes (E := K) (m := m) (MvPolynomial.C c)) from rfl,
    modelToResidue_mk]
  rw [show (FiniteJet.unitBall (P K m)).subtype
      (polyBallRes (E := K) (m := m) (MvPolynomial.C c)) =
    polyBall (E := K) (m := m) (MvPolynomial.C c) from rfl]
  rw [show polyBall (E := K) (m := m) (MvPolynomial.C c) =
    polyToP (E := K) (m := m) (MvPolynomial.C (c : K)) from by
      rw [show polyBall (E := K) (m := m) (MvPolynomial.C c) =
        polyToP (MvPolynomial.map (FiniteJet.unitBall K).subtype
          (MvPolynomial.C c)) from rfl, MvPolynomial.map_C]
      rfl]
  rfl

include ϖ in
/-- **The integral-model monic relations for the variables**: each variable
image in the residue field satisfies a monic relation over the unit ball. -/
theorem exists_monic_ball_relation_X
    (hK₀ : IsNoetherianRing (FiniteJet.unitBall K)) (i : Fin m) :
    ∃ p : Polynomial ↥(FiniteJet.unitBall K), p.Monic ∧
      Polynomial.eval₂
        (((constantsToResidue 𝔮 : K →+* (P K m ⧸ 𝔮))).comp
          (FiniteJet.unitBall K).subtype)
        (Ideal.Quotient.mk 𝔮 (polyToP (MvPolynomial.X i))) p = 0 := by
  letI : Algebra ↥(FiniteJet.unitBall K) (IntegralModel (m := m) 𝔮) :=
    (ballToModel (m := m) 𝔮).toAlgebra
  haveI hfinB := module_finite_integralModel (m := m) ϖ 𝔮 hK₀
  haveI : Algebra.IsIntegral ↥(FiniteJet.unitBall K)
      (IntegralModel (m := m) 𝔮) := Algebra.IsIntegral.of_finite _ _
  set XB : ↥(FiniteJet.unitBall (P K m)) :=
    ⟨polyToP (MvPolynomial.X i),
      (FiniteJet.mem_unitBall_iff _ _).mpr (norm_polyToP_X_le_one i)⟩
    with hXB
  set b : IntegralModel (m := m) 𝔮 := Ideal.Quotient.mk _ XB with hb
  have hint : IsIntegral ↥(FiniteJet.unitBall K) b :=
    Algebra.IsIntegral.isIntegral b
  obtain ⟨p, hpmonic, hpev⟩ := hint
  refine ⟨p, hpmonic, ?_⟩
  -- push the relation along the residue map
  have hpush : modelToResidue (m := m) 𝔮
      (Polynomial.eval₂ (ballToModel (m := m) 𝔮) b p) = 0 := by
    have h2 : Polynomial.eval₂ (ballToModel (m := m) 𝔮) b p =
        Polynomial.eval₂ (algebraMap ↥(FiniteJet.unitBall K)
          (IntegralModel (m := m) 𝔮)) b p := rfl
    rw [h2, hpev, _root_.map_zero]
  have h3 : modelToResidue (m := m) 𝔮
      (Polynomial.eval₂ (ballToModel (m := m) 𝔮) b p) =
      Polynomial.eval₂ ((modelToResidue (m := m) 𝔮).comp
        (ballToModel (m := m) 𝔮)) (modelToResidue (m := m) 𝔮 b) p :=
    Polynomial.hom_eval₂ _ _ _ _
  rw [h3, modelToResidue_comp_ballToModel] at hpush
  have h4 : modelToResidue (m := m) 𝔮 b =
      Ideal.Quotient.mk 𝔮 (polyToP (MvPolynomial.X i)) := by
    rw [hb, modelToResidue_mk]
    rfl
  rwa [h4] at hpush

end IntegralRelations

end FiniteJet.GraphKoszul
