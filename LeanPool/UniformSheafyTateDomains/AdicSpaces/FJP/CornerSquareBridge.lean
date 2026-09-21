/-
Copyright (c) 2026 Christopher Birkbeck, Alex Torzewski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Birkbeck, Alex Torzewski
-/

/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanPool.UniformSheafyTateDomains.AdicSpaces.CornerSquareDatum
import LeanPool.UniformSheafyTateDomains.AdicSpaces.FJP.CornerSquareLocalization
import LeanPool.UniformSheafyTateDomains.AdicSpaces.FJP.FiniteJetFunctoriality

/-!
# The graph bridge over a single abstract corner (T625, campaign B)

[FJP] §4 (4.4)/(4.19)–(4.21), the completion identification, over ONE normed
ultrametric Huber corner `E`: for a rational datum `D` on `E` with enumeration
`e`, the completed rational localization `𝒪_E(D)` is topologically the Banach
graph quotient `E_α = P_E ⧸ I_E`:

* forward `bridgeFwd : 𝒪_E(D) →+* E_α` (completion extension of the
  localization lift at the unit `s̄`);
* reverse `bridgeRev : E_α →+* 𝒪_E(D)` (evaluation `X̄ᵢ ↦ fᵢ/s`, convergent by
  the [FJP] (1.3) bound);
* `graphBridge : 𝒪_E(D) ≃+* E_α`, continuous in both directions.

This is the single-corner generalization of the `JetA`-side bridge of
`FJP/FiniteJetFunctoriality.lean` (:207–:733). Because the `Pinch` relations are
in graph-polynomial form, instantiating `E` at each vertex of a pinch square
(with the pushed datum and pushed enumeration at `B`, `C`, `D`) yields the four
vertex bridges of the localized Milnor row **definitionally** — the ideals
`Pinch.IB/IC/ID` are the `IA`-ideals of the pushed data.

The closedness of the graph ideal enters as an explicit argument `hIcl` (at the
`B`/`C`/`D`-corners it is `isClosed_graphIdeal`; at the base corner of a pinch
it is `Pinch.isClosed_IA`, which needs the square).
-/

@[expose] public section

noncomputable section

open Filter Topology

namespace FiniteJet

open RestrictedLaurent GraphKoszul ValuationSpectrum Pinch

variable {E : Type*} [NormedCommRing E] [IsUltrametricDist E] [NormOneClass E]
  [CompleteSpace E] [PlusSubring E] [IsTateRing E]
  [HasLocLiftPowerBounded E]

/-- An indexed enumeration of a `RationalLocData`: `f` lists `T`, `g = s`
(the generic form of the Jet-concrete `DatumEnum`). -/
structure CornerEnum (D : RationalLocData E) where
  /-- The arity. -/
  m : ℕ
  /-- The enumeration of `T`. -/
  f : Fin m → E
  /-- Enumeration covers `T`. -/
  hf : ∀ t ∈ D.T, ∃ i, f i = t
  /-- Enumeration lands in `T`. -/
  hf' : ∀ i, f i ∈ D.T

/-- The canonical enumeration of a rational datum (via `Finset.equivFin`). -/
noncomputable def cornerEnum (D : RationalLocData E) : CornerEnum D where
  m := D.T.card
  f := fun i => (D.T.equivFin.symm i : E)
  hf := fun t ht => ⟨D.T.equivFin ⟨t, ht⟩, by rw [Equiv.symm_apply_apply]⟩
  hf' := fun i => (D.T.equivFin.symm i).2

namespace CornerEnum

variable (D : RationalLocData E) (e : CornerEnum D)

omit [IsUltrametricDist E] [NormOneClass E] [CompleteSpace E] [PlusSubring E] [HasLocLiftPowerBounded E] in
/-- The enumerated datum spans `({s} ∪ range f) = ⊤` (rationality + covering). -/
theorem span_eq_top (hD : D.IsRational) :
    Ideal.span ({D.s} ∪ Set.range e.f) = ⊤ := by
  rw [← top_le_iff, ← hD.span_eq_top]
  refine Ideal.span_mono fun t ht => ?_
  obtain ⟨i, rfl⟩ := e.hf t ht
  exact Set.mem_union_right _ ⟨i, rfl⟩

end CornerEnum

namespace CornerBridge

section Bridge

variable (D : RationalLocData E) (e : CornerEnum D)

/-- Scalars into `P_E` (constant restricted series). -/
noncomputable def bridgeConst (m : ℕ) : E →+* P E m :=
  polyToP.comp MvPolynomial.C

/-- The base map `E → E_α = P_E ⧸ I_E` (constants, then the graph quotient). -/
noncomputable def bridgeBase : E →+* locA e.m D.s e.f :=
  (Ideal.Quotient.mk (IA e.m D.s e.f)).comp (bridgeConst e.m)

/-- The variable images `X̄ᵢ ∈ E_α`. -/
noncomputable def bridgeX (i : Fin e.m) : locA e.m D.s e.f :=
  Ideal.Quotient.mk (IA e.m D.s e.f) (polyToP (MvPolynomial.X i))

omit [NormOneClass E] [CompleteSpace E] [PlusSubring E] [HasLocLiftPowerBounded E] in
/-- The graph relation in the quotient: `s̄ · X̄ᵢ = f̄ᵢ` ([FJP] (4.6)). -/
theorem bridgeBase_s_mul_X (i : Fin e.m) :
    bridgeBase D e D.s * bridgeX D e i = bridgeBase D e (e.f i) := by
  have hmem : polyToP (MvPolynomial.C D.s) * polyToP (MvPolynomial.X i) -
      polyToP (MvPolynomial.C (e.f i)) ∈ IA e.m D.s e.f := by
    have hrw : rA e.m D.s e.f i =
        polyToP (MvPolynomial.C D.s) * polyToP (MvPolynomial.X i) -
          polyToP (MvPolynomial.C (e.f i)) := by
      rw [rA, map_sub, map_mul]
    rw [← hrw]
    exact Ideal.subset_span ⟨i, rfl⟩
  show Ideal.Quotient.mk (IA e.m D.s e.f) (polyToP (MvPolynomial.C D.s)) *
      Ideal.Quotient.mk (IA e.m D.s e.f) (polyToP (MvPolynomial.X i)) =
    Ideal.Quotient.mk (IA e.m D.s e.f) (polyToP (MvPolynomial.C (e.f i)))
  rw [← RingHom.map_mul (Ideal.Quotient.mk (IA e.m D.s e.f))]
  exact Ideal.Quotient.eq.mpr hmem

omit [NormOneClass E] [CompleteSpace E] [PlusSubring E] [HasLocLiftPowerBounded E] in
/-- `s̄` is a unit in `E_α` ([FJP] (4.3)). -/
theorem isUnit_bridgeBase_s (hD : D.IsRational) :
    IsUnit (bridgeBase D e D.s) := by
  have h1 : (1 : E) ∈ Ideal.span ({D.s} ∪ Set.range e.f) := by
    rw [e.span_eq_top D hD]; trivial
  rw [Ideal.span_union, Submodule.mem_sup] at h1
  obtain ⟨x, hx, y, hy, hxy⟩ := h1
  obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp hx
  rw [Ideal.mem_span_range_iff_exists_fun] at hy
  obtain ⟨d, rfl⟩ := hy
  have hterm : ∀ i, bridgeBase D e (d i * e.f i) =
      bridgeBase D e (d i) * (bridgeBase D e D.s * bridgeX D e i) := fun i => by
    rw [RingHom.map_mul (bridgeBase D e), bridgeBase_s_mul_X]
  have happ : bridgeBase D e c * bridgeBase D e D.s +
      ∑ i, bridgeBase D e (d i) * (bridgeBase D e D.s * bridgeX D e i) = 1 := by
    have h0 := congrArg (bridgeBase D e) hxy
    rw [RingHom.map_one (bridgeBase D e), RingHom.map_add (bridgeBase D e),
      RingHom.map_mul (bridgeBase D e),
      show (bridgeBase D e) (∑ i, d i * e.f i) = ∑ i, bridgeBase D e (d i * e.f i) from
        map_sum (bridgeBase D e) _ _,
      Finset.sum_congr rfl fun i _ => hterm i] at h0
    exact h0
  have hmul : bridgeBase D e D.s *
      (bridgeBase D e c + ∑ i, bridgeBase D e (d i) * bridgeX D e i) = 1 := by
    rw [mul_add, Finset.mul_sum]
    calc bridgeBase D e D.s * bridgeBase D e c +
        ∑ i, bridgeBase D e D.s * (bridgeBase D e (d i) * bridgeX D e i)
        = bridgeBase D e c * bridgeBase D e D.s +
          ∑ i, bridgeBase D e (d i) * (bridgeBase D e D.s * bridgeX D e i) := by
          rw [mul_comm (bridgeBase D e D.s) (bridgeBase D e c)]
          congr 1
          exact Finset.sum_congr rfl fun i _ => by ring
      _ = 1 := happ
  exact IsUnit.of_mul_eq_one _ hmul

omit [CompleteSpace E] [PlusSubring E] [HasLocLiftPowerBounded E] in
/-- `‖X̄ᵢ‖ ≤ 1` in the graph quotient. -/
theorem norm_bridgeX_le_one (i : Fin e.m) : ‖bridgeX D e i‖ ≤ 1 := by
  refine (Ideal.Quotient.norm_mk_le _ _).trans ?_
  rw [MvRestricted.norm_eq]
  exact FiniteJet.gaussNorm_X_le_one (S := E) i

omit [NormOneClass E] [CompleteSpace E] [PlusSubring E] [HasLocLiftPowerBounded E] in
/-- `bridgeBase` is norm-nonincreasing. -/
theorem norm_bridgeBase_le (a : E) : ‖bridgeBase D e a‖ ≤ ‖a‖ := by
  refine (Ideal.Quotient.norm_mk_le _ _).trans ?_
  show ‖(polyToP (E := E) (m := e.m) (MvPolynomial.C a) : P E e.m)‖ ≤ ‖a‖
  rw [MvRestricted.norm_eq,
    show (polyToP (E := E) (m := e.m) (MvPolynomial.C a)).1 =
      MvPowerSeries.C (σ := Fin e.m) (R := E) a from MvPolynomial.coe_C a]
  exact le_of_eq (UnitDiscExample.gaussNorm_C_norm _ a)

/-- The loc-level forward map `E_s → E_α` (`IsLocalization.Away.lift` at `s̄`). -/
noncomputable def bridgeLocHom (hD : D.IsRational) :
    Localization.Away D.s →+* locA e.m D.s e.f :=
  IsLocalization.Away.lift D.s (isUnit_bridgeBase_s D e hD)

omit [NormOneClass E] [CompleteSpace E] [PlusSubring E] [HasLocLiftPowerBounded E] in
theorem bridgeLocHom_algebraMap (hD : D.IsRational) (a : E) :
    bridgeLocHom D e hD (algebraMap E (Localization.Away D.s) a) =
      bridgeBase D e a :=
  IsLocalization.Away.lift_eq _ _ a

omit [NormOneClass E] [CompleteSpace E] [PlusSubring E] [HasLocLiftPowerBounded E] in
/-- The forward map sends the rational generator `fᵢ/s` to the variable `X̄ᵢ`. -/
theorem bridgeLocHom_divByS (hD : D.IsRational) (i : Fin e.m) :
    bridgeLocHom D e hD (divByS (e.f i) D.s) = bridgeX D e i := by
  have hu := isUnit_bridgeBase_s D e hD
  have hspec : divByS (e.f i) D.s * algebraMap E (Localization.Away D.s) D.s =
      algebraMap E (Localization.Away D.s) (e.f i) := by
    rw [divByS, IsLocalization.mk'_spec]
  have happ := congrArg (bridgeLocHom D e hD) hspec
  rw [RingHom.map_mul (bridgeLocHom D e hD), bridgeLocHom_algebraMap,
    bridgeLocHom_algebraMap, ← bridgeBase_s_mul_X] at happ
  refine hu.mul_left_cancel ?_
  rw [mul_comm (bridgeBase D e D.s) (bridgeLocHom D e hD (divByS (e.f i) D.s))]
  exact happ

omit [CompleteSpace E] [PlusSubring E] [HasLocLiftPowerBounded E] in
/-- Continuity of the loc-level forward map (universal property; the generators
map to the norm-≤-1 variables `X̄ᵢ`, which are power-bounded). -/
theorem bridgeLocHom_continuous (hD : D.IsRational) :
    @Continuous _ _ D.topology _ (bridgeLocHom D e hD) := by
  refine locTopology_continuous_lift D.P D.T D.s D.hopen _ ?_ ?_
  · have h_eq : (bridgeLocHom D e hD).comp
        (algebraMap E (Localization.Away D.s)) = bridgeBase D e := by
      ext a; exact bridgeLocHom_algebraMap D e hD a
    rw [show ⇑((bridgeLocHom D e hD).comp
        (algebraMap E (Localization.Away D.s)))
        = ⇑(bridgeBase D e) from congrArg _ h_eq]
    exact AddMonoidHomClass.continuous_of_bound (bridgeBase D e) 1 fun a => by
      rw [one_mul]; exact norm_bridgeBase_le D e a
  · intro t ht
    obtain ⟨i, rfl⟩ := e.hf t ht
    rw [bridgeLocHom_divByS]
    exact FiniteJet.isPowerBounded_of_norm_le_one (norm_bridgeX_le_one D e i)

omit [NormOneClass E] [CompleteSpace E] [PlusSubring E] [HasLocLiftPowerBounded E] in
/-- `E_α` is Hausdorff when the graph ideal is closed. -/
theorem locE_t2 (hIcl : IsClosed ((IA e.m D.s e.f : Set (P E e.m)))) :
    T2Space (locA e.m D.s e.f) :=
  locA_t2_of_isClosed e.m D.s e.f hIcl

/-- Forward: `𝒪_E(D) → E_α` (completion extension of the localization lift;
the target is complete Hausdorff since `I_E` is closed, [FJP] (4.21)). -/
noncomputable def bridgeFwd (hD : D.IsRational)
    (hIcl : IsClosed ((IA e.m D.s e.f : Set (P E e.m)))) :
    presheafValue D →+* locA e.m D.s e.f := by
  have : T2Space (locA e.m D.s e.f) := locE_t2 D e hIcl
  have : CompleteSpace (locA e.m D.s e.f) :=
    locA_completeSpace_of_isClosed e.m D.s e.f hIcl
  letI := D.uniformSpace
  letI : IsTopologicalRing (Localization.Away D.s) := D.isTopologicalRing
  letI : IsUniformAddGroup (Localization.Away D.s) := D.isUniformAddGroup
  exact UniformSpace.Completion.extensionHom (bridgeLocHom D e hD)
    (bridgeLocHom_continuous D e hD)

omit [PlusSubring E] [HasLocLiftPowerBounded E] in
theorem bridgeFwd_coe (hD : D.IsRational)
    (hIcl : IsClosed ((IA e.m D.s e.f : Set (P E e.m))))
    (a : Localization.Away D.s) :
    bridgeFwd D e hD hIcl (D.coeRingHom a) = bridgeLocHom D e hD a := by
  have : T2Space (locA e.m D.s e.f) := locE_t2 D e hIcl
  have : CompleteSpace (locA e.m D.s e.f) :=
    locA_completeSpace_of_isClosed e.m D.s e.f hIcl
  let _i := D.uniformSpace
  have : IsTopologicalRing (Localization.Away D.s) := D.isTopologicalRing
  have : IsUniformAddGroup (Localization.Away D.s) := D.isUniformAddGroup
  exact UniformSpace.Completion.extensionHom_coe (bridgeLocHom D e hD)
    (bridgeLocHom_continuous D e hD) a

omit [PlusSubring E] [HasLocLiftPowerBounded E] in
theorem bridgeFwd_canonicalMap (hD : D.IsRational)
    (hIcl : IsClosed ((IA e.m D.s e.f : Set (P E e.m)))) (a : E) :
    bridgeFwd D e hD hIcl (D.canonicalMap a) = bridgeBase D e a := by
  rw [show D.canonicalMap a =
      D.coeRingHom (algebraMap E (Localization.Away D.s) a) from rfl,
    bridgeFwd_coe, bridgeLocHom_algebraMap]

omit [PlusSubring E] [HasLocLiftPowerBounded E] in
theorem bridgeFwd_continuous (hD : D.IsRational)
    (hIcl : IsClosed ((IA e.m D.s e.f : Set (P E e.m)))) :
    Continuous (bridgeFwd D e hD hIcl) := by
  have : T2Space (locA e.m D.s e.f) := locE_t2 D e hIcl
  have : CompleteSpace (locA e.m D.s e.f) :=
    locA_completeSpace_of_isClosed e.m D.s e.f hIcl
  let _i := D.uniformSpace
  exact UniformSpace.Completion.continuous_extension

end Bridge

/-! #### The reverse direction: evaluation `P_E → 𝒪_E(D)` ([FJP] Lemma 1.1, (1.3)) -/

/-- Norm-decay restricted series are topologically restricted. -/
noncomputable def bridgeToRestricted (m : ℕ) :
    P E m →+* ↥(restrictedMvPowerSeriesSubring m E) where
  toFun p := ⟨p.1, by
    have hp : MvPowerSeries.IsRestrictedGauss (fun _ : Fin m => (1 : ℝ)) p.1 := p.2
    rw [MvPowerSeries.IsRestrictedGauss] at hp
    have hprod : ∀ t : Fin m →₀ ℕ, (t.prod fun _ k => (1 : ℝ) ^ k) = 1 := fun t => by simp
    simp only [hprod, mul_one] at hp
    show Filter.Tendsto (fun t : Fin m →₀ ℕ => MvPowerSeries.coeff t p.1)
      Filter.cofinite (nhds 0)
    rwa [tendsto_zero_iff_norm_tendsto_zero]⟩
  map_one' := Subtype.ext rfl
  map_mul' _ _ := Subtype.ext rfl
  map_zero' := Subtype.ext rfl
  map_add' _ _ := Subtype.ext rfl

section Eval

variable (D : RationalLocData E) (e : CornerEnum D)

/-- The rational generators `fᵢ/s ∈ 𝒪_E(D)`. -/
noncomputable def bridgeGen (i : Fin e.m) : presheafValue D :=
  D.coeRingHom (divByS (e.f i) D.s)

omit [IsUltrametricDist E] [NormOneClass E] [CompleteSpace E] [PlusSubring E] [HasLocLiftPowerBounded E] in
/-- Each generator is power-bounded. -/
theorem bridgeGen_isBounded (i : Fin e.m) :
    TopologicalRing.IsBounded (Set.range (bridgeGen D e i ^ · : ℕ → presheafValue D)) := by
  have hmem : divByS (e.f i) D.s ∈ locSubring D.P D.T D.s :=
    divByS_mem_locSubring D.P D.T D.s (e.hf' i)
  have hbdd := CompletionLocalization.coeRingHom_image_locSubring_isBounded D
  apply hbdd.subset
  rintro _ ⟨n, rfl⟩
  exact ⟨divByS (e.f i) D.s ^ n, pow_mem hmem n, by
    rw [map_pow]; rfl⟩

/-- The evaluation `P_E →+* 𝒪_E(D)`: `Σ a_v X^v ↦ Σ ρ(a_v)·(f/s)^v`. -/
noncomputable def bridgeEval : P E e.m →+* presheafValue D :=
  (mvEvalHomBounded D.canonicalMap (canonicalMap_continuous D)
    (bridgeGen D e) (bridgeGen_isBounded D e)).comp (bridgeToRestricted e.m)

omit [NormOneClass E] [CompleteSpace E] [PlusSubring E] [HasLocLiftPowerBounded E] in
theorem bridgeEval_const (a : E) :
    bridgeEval D e (polyToP (MvPolynomial.C a)) = D.canonicalMap a := by
  have hcast : bridgeToRestricted (E := E) e.m (polyToP (MvPolynomial.C a)) =
      algebraMap E ↥(restrictedMvPowerSeriesSubring e.m E) a := by
    refine Subtype.ext ?_
    show ((polyToP (E := E) (m := e.m) (MvPolynomial.C a)).1 :
      MvPowerSeries (Fin e.m) E) = _
    rw [show (polyToP (E := E) (m := e.m) (MvPolynomial.C a)).1 =
      MvPowerSeries.C (σ := Fin e.m) (R := E) a from MvPolynomial.coe_C a]
    rfl
  rw [bridgeEval, RingHom.comp_apply, hcast]
  exact mvEvalHomBounded_algebraMap _ _ _ _ a

omit [NormOneClass E] [CompleteSpace E] [PlusSubring E] [HasLocLiftPowerBounded E] in
theorem bridgeEval_X (i : Fin e.m) :
    bridgeEval D e (polyToP (MvPolynomial.X i)) = bridgeGen D e i := by
  have hcast : bridgeToRestricted (E := E) e.m (polyToP (MvPolynomial.X i)) =
      ⟨MvPowerSeries.X i, MvPowerSeries.X_isRestricted i⟩ := by
    refine Subtype.ext ?_
    show ((polyToP (E := E) (m := e.m) (MvPolynomial.X i)).1 :
      MvPowerSeries (Fin e.m) E) = _
    exact MvPolynomial.coe_X i
  rw [bridgeEval, RingHom.comp_apply, hcast]
  exact mvEvalHomBounded_X _ _ _ _ i

omit [NormOneClass E] [CompleteSpace E] [PlusSubring E] [HasLocLiftPowerBounded E] in
/-- The evaluation kills the graph ideal. -/
theorem IA_le_ker_bridgeEval : IA e.m D.s e.f ≤ RingHom.ker (bridgeEval D e) := by
  rw [IA, Ideal.span_le]
  rintro _ ⟨i, rfl⟩
  rw [SetLike.mem_coe, RingHom.mem_ker]
  have hval : bridgeEval D e (rA e.m D.s e.f i) =
      D.canonicalMap D.s * bridgeGen D e i - D.canonicalMap (e.f i) :=
    (map_sub ((bridgeEval D e).comp polyToP)
        (MvPolynomial.C D.s * MvPolynomial.X i) (MvPolynomial.C (e.f i))).trans
      (congrArg₂ (· - ·)
        ((map_mul ((bridgeEval D e).comp polyToP)
            (MvPolynomial.C D.s) (MvPolynomial.X i)).trans
          (congrArg₂ (· * ·) (bridgeEval_const D e D.s) (bridgeEval_X D e i)))
        (bridgeEval_const D e (e.f i)))
  rw [hval, sub_eq_zero, bridgeGen]
  rw [show D.canonicalMap D.s = D.coeRingHom (algebraMap E
      (Localization.Away D.s) D.s) from rfl, ← RingHom.map_mul D.coeRingHom,
    show algebraMap E (Localization.Away D.s) D.s * divByS (e.f i) D.s =
      algebraMap E (Localization.Away D.s) (e.f i) from by
    rw [mul_comm, divByS, IsLocalization.mk'_spec]]
  rfl

/-- Reverse: `E_α → 𝒪_E(D)` (the evaluation factors through the graph quotient). -/
noncomputable def bridgeRev : locA e.m D.s e.f →+* presheafValue D :=
  Ideal.Quotient.lift (IA e.m D.s e.f) (bridgeEval D e)
    (fun _ ha => RingHom.mem_ker.mp (IA_le_ker_bridgeEval D e ha))

omit [NormOneClass E] [CompleteSpace E] [PlusSubring E] [HasLocLiftPowerBounded E] in
theorem bridgeRev_mk (p : P E e.m) :
    bridgeRev D e (Ideal.Quotient.mk (IA e.m D.s e.f) p) = bridgeEval D e p := rfl

omit [NormOneClass E] [CompleteSpace E] [PlusSubring E] [HasLocLiftPowerBounded E] in
theorem bridgeRev_bridgeBase (a : E) :
    bridgeRev D e (bridgeBase D e a) = D.canonicalMap a :=
  bridgeEval_const D e a

omit [NormOneClass E] [CompleteSpace E] [PlusSubring E] [HasLocLiftPowerBounded E] in
theorem bridgeRev_bridgeX (i : Fin e.m) :
    bridgeRev D e (bridgeX D e i) = bridgeGen D e i :=
  bridgeEval_X D e i

/-- Sums of open-subgroup members stay in the subgroup. -/
private theorem tsum_mem_of_isOpen_addSubgroup' {ι G₀ : Type*} [AddCommGroup G₀]
    [TopologicalSpace G₀] [IsTopologicalAddGroup G₀] {f : ι → G₀}
    (hf : Summable f) {G : AddSubgroup G₀} (hG : IsOpen (G : Set G₀))
    (hmem : ∀ i, f i ∈ G) : ∑' i, f i ∈ G := by
  have hclosed : IsClosed (G : Set G₀) := AddSubgroup.isClosed_of_isOpen G hG
  refine hclosed.mem_of_tendsto hf.hasSum (Filter.Eventually.of_forall ?_)
  intro s
  exact G.sum_mem fun i _ => hmem i

omit [IsUltrametricDist E] [NormOneClass E] [CompleteSpace E] [PlusSubring E]
  [HasLocLiftPowerBounded E] in
/-- The range of the generator product powers is bounded. -/
private theorem bridgeRangeProd_isBounded :
    TopologicalRing.IsBounded
      (Set.range (fun v : Fin e.m →₀ ℕ => ∏ i, bridgeGen D e i ^ (v i))) := by
  classical
  suffices h : ∀ s : Finset (Fin e.m), TopologicalRing.IsBounded
      (Set.range (fun v : Fin e.m →₀ ℕ => ∏ i ∈ s, bridgeGen D e i ^ (v i))) from
    h Finset.univ
  intro s
  induction s using Finset.induction with
  | empty => simpa using TopologicalRing.isBounded_singleton (1 : presheafValue D)
  | insert a s ha ih =>
      refine ((bridgeGen_isBounded D e a).mul ih).subset ?_
      rintro _ ⟨v, rfl⟩
      change ∏ i ∈ insert a s, bridgeGen D e i ^ (v i) ∈ _
      rw [Finset.prod_insert ha]
      exact Set.mul_mem_mul ⟨v a, rfl⟩ ⟨v, rfl⟩

omit [PlusSubring E] [HasLocLiftPowerBounded E] in
/-- **Continuity of the evaluation** from the norm topology on `P_E`
([FJP] (1.3) bound). -/
theorem bridgeEval_continuous : Continuous (bridgeEval D e) := by
  classical
  refine continuous_of_continuousAt_zero (bridgeEval D e).toAddMonoidHom ?_
  rw [ContinuousAt, map_zero, Filter.tendsto_def]
  intro U hU
  obtain ⟨W, hWU⟩ := NonarchimedeanRing.is_nonarchimedean U hU
  obtain ⟨V, hV, hVR⟩ := bridgeRangeProd_isBounded D e (W : Set (presheafValue D))
    (W.isOpen.mem_nhds W.zero_mem)
  have hpre : D.canonicalMap ⁻¹' V ∈ nhds (0 : E) :=
    (canonicalMap_continuous D).continuousAt.preimage_mem_nhds (by rwa [map_zero])
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp hpre
  refine Filter.mem_of_superset (Metric.ball_mem_nhds (0 : P E e.m) hδ) ?_
  intro p hp
  rw [Metric.mem_ball, dist_zero_right] at hp
  apply hWU
  change (∑' v, mvEvalTerm D.canonicalMap (bridgeGen D e)
    (bridgeToRestricted e.m p) v) ∈ (W : Set (presheafValue D))
  refine tsum_mem_of_isOpen_addSubgroup'
    (mvEvalTerm_summable D.canonicalMap (canonicalMap_continuous D)
      (bridgeGen D e) (bridgeGen_isBounded D e) (bridgeToRestricted e.m p))
    W.isOpen fun v => ?_
  have hcoeff : ‖MvPowerSeries.coeff v p.1‖ < δ :=
    lt_of_le_of_lt (norm_coeff_le_gauss p v) hp
  have hVmem : D.canonicalMap (MvPowerSeries.coeff v p.1) ∈ V :=
    hball (by rwa [Metric.mem_ball, dist_zero_right])
  change mvEvalTerm D.canonicalMap (bridgeGen D e) (bridgeToRestricted e.m p) v ∈ W
  rw [show mvEvalTerm D.canonicalMap (bridgeGen D e) (bridgeToRestricted e.m p) v =
      (∏ i, bridgeGen D e i ^ (v i)) *
        D.canonicalMap (MvPowerSeries.coeff v p.1) from by
    rw [mvEvalTerm]; exact mul_comm _ _]
  exact hVR (Set.mul_mem_mul ⟨v, rfl⟩ hVmem)

omit [PlusSubring E] [HasLocLiftPowerBounded E] in
/-- Continuity of the reverse map (quotient topology). -/
theorem bridgeRev_continuous : Continuous (bridgeRev D e) := by
  rw [(QuotientRing.isOpenQuotientMap_mk (IA e.m D.s e.f)).isQuotientMap.continuous_iff]
  exact bridgeEval_continuous D e

/-! #### Round trips (density + Hausdorff equalizers) -/

omit [PlusSubring E] [IsTateRing E] [HasLocLiftPowerBounded E] in
/-- Polynomials are dense in `P_E`. -/
theorem polyToP_denseRange (m : ℕ) :
    DenseRange (polyToP : MvPolynomial (Fin m) E → P E m) := by
  classical
  rw [Metric.denseRange_iff]
  intro p ε hε
  refine ⟨∑ s ∈ (finite_setOf_le_norm_coeff p (half_pos hε)).toFinset,
    MvPolynomial.monomial s (MvPowerSeries.coeff s p.1), ?_⟩
  rw [dist_eq_norm, MvRestricted.norm_eq, MvPowerSeries.gaussNorm]
  refine lt_of_le_of_lt (Real.iSup_le (fun s => ?_) (half_pos hε).le) (half_lt_self hε)
  rw [finsupp_prod_one, mul_one]
  show ‖MvPowerSeries.coeff s ((p - polyToP _ : P E m)).1‖ ≤ ε / 2
  rw [show ((p - polyToP (∑ s ∈ (finite_setOf_le_norm_coeff p (half_pos hε)).toFinset,
      MvPolynomial.monomial s (MvPowerSeries.coeff s p.1)) : P E m)).1 =
    p.1 - (polyToP (∑ s ∈ (finite_setOf_le_norm_coeff p (half_pos hε)).toFinset,
      MvPolynomial.monomial s (MvPowerSeries.coeff s p.1) : MvPolynomial (Fin m)
        E)).1 from rfl, map_sub, coeff_polyToP, MvPolynomial.coeff_sum]
  by_cases hs : ε / 2 ≤ ‖MvPowerSeries.coeff s p.1‖
  · rw [Finset.sum_eq_single s
      (fun b _ hb => by rw [MvPolynomial.coeff_monomial, if_neg hb])
      (fun hns => absurd ((finite_setOf_le_norm_coeff p (half_pos hε)).mem_toFinset.mpr hs)
        hns), MvPolynomial.coeff_monomial, if_pos rfl, sub_self, norm_zero]
    exact (half_pos hε).le
  · rw [Finset.sum_eq_zero fun b hb => ?_, sub_zero]
    · exact (not_le.mp hs).le
    · rw [MvPolynomial.coeff_monomial, if_neg]
      intro hbs
      rw [hbs] at hb
      exact hs ((finite_setOf_le_norm_coeff p (half_pos hε)).mem_toFinset.mp hb)

omit [PlusSubring E] [HasLocLiftPowerBounded E] in
/-- `rev ∘ fwd = id` on `𝒪_E(D)`. -/
theorem bridgeRev_bridgeFwd (hD : D.IsRational)
    (hIcl : IsClosed ((IA e.m D.s e.f : Set (P E e.m)))) (x : presheafValue D) :
    bridgeRev D e (bridgeFwd D e hD hIcl x) = x := by
  let _i := D.uniformSpace
  have : IsTopologicalRing (Localization.Away D.s) := D.isTopologicalRing
  have : IsUniformAddGroup (Localization.Away D.s) := D.isUniformAddGroup
  have : RegularSpace (presheafValue D) := UniformSpace.to_regularSpace
  have hcomp : (bridgeRev D e).comp (bridgeLocHom D e hD) = D.coeRingHom := by
    refine IsLocalization.ringHom_ext (Submonoid.powers D.s) ?_
    ext a
    simp only [RingHom.comp_apply]
    rw [bridgeLocHom_algebraMap, bridgeRev_bridgeBase]
    rfl
  have hdense : DenseRange (D.coeRingHom :
      Localization.Away D.s → presheafValue D) :=
    UniformSpace.Completion.denseRange_coe
  have hagree : (fun y => bridgeRev D e (bridgeFwd D e hD hIcl y)) ∘ D.coeRingHom =
      (fun y => y) ∘ (D.coeRingHom : Localization.Away D.s → presheafValue D) := by
    funext a
    show bridgeRev D e (bridgeFwd D e hD hIcl (D.coeRingHom a)) = D.coeRingHom a
    rw [bridgeFwd_coe]
    exact DFunLike.congr_fun hcomp a
  have h_eq : (fun y => bridgeRev D e (bridgeFwd D e hD hIcl y)) = fun y => y :=
    hdense.equalizer ((bridgeRev_continuous D e).comp (bridgeFwd_continuous D e hD hIcl))
      continuous_id hagree
  exact congrFun h_eq x

omit [NormOneClass E] [CompleteSpace E] [PlusSubring E] [HasLocLiftPowerBounded E] in
/-- The graph-quotient projection is continuous. -/
theorem mkIA_continuous :
    Continuous (Ideal.Quotient.mk (IA e.m D.s e.f)) :=
  AddMonoidHomClass.continuous_of_bound (Ideal.Quotient.mk (IA e.m D.s e.f)) 1
    fun a => by rw [one_mul]; exact Ideal.Quotient.norm_mk_le _ a

omit [PlusSubring E] [HasLocLiftPowerBounded E] in
/-- `fwd ∘ rev = id` on `E_α`. -/
theorem bridgeFwd_bridgeRev (hD : D.IsRational)
    (hIcl : IsClosed ((IA e.m D.s e.f : Set (P E e.m)))) (y : locA e.m D.s e.f) :
    bridgeFwd D e hD hIcl (bridgeRev D e y) = y := by
  have : T2Space (locA e.m D.s e.f) := locE_t2 D e hIcl
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective y
  have hmkcont : Continuous (Ideal.Quotient.mk (IA e.m D.s e.f)) :=
    mkIA_continuous D e
  have hpoly : ∀ q : MvPolynomial (Fin e.m) E,
      bridgeFwd D e hD hIcl (bridgeEval D e (polyToP q)) =
        Ideal.Quotient.mk (IA e.m D.s e.f) (polyToP q) := by
    have hhomeq : ((bridgeFwd D e hD hIcl).comp ((bridgeEval D e).comp polyToP)) =
        (Ideal.Quotient.mk (IA e.m D.s e.f)).comp
          (polyToP : MvPolynomial (Fin e.m) E →+* P E e.m) := by
      refine MvPolynomial.ringHom_ext (fun a => ?_) (fun i => ?_)
      · show bridgeFwd D e hD hIcl (bridgeEval D e (polyToP (MvPolynomial.C a))) =
          Ideal.Quotient.mk (IA e.m D.s e.f) (polyToP (MvPolynomial.C a))
        rw [bridgeEval_const, bridgeFwd_canonicalMap]
        rfl
      · show bridgeFwd D e hD hIcl (bridgeEval D e (polyToP (MvPolynomial.X i))) =
          Ideal.Quotient.mk (IA e.m D.s e.f) (polyToP (MvPolynomial.X i))
        rw [bridgeEval_X, bridgeGen, bridgeFwd_coe, bridgeLocHom_divByS]
        rfl
    intro q
    exact DFunLike.congr_fun hhomeq q
  have h_eq : (fun z : P E e.m => bridgeFwd D e hD hIcl (bridgeEval D e z)) =
      fun z : P E e.m => Ideal.Quotient.mk (IA e.m D.s e.f) z := by
    refine (polyToP_denseRange e.m).equalizer
      ((bridgeFwd_continuous D e hD hIcl).comp (bridgeEval_continuous D e)) hmkcont ?_
    funext q
    exact hpoly q
  exact congrFun h_eq p

/-- **The graph bridge** ([FJP] (4.19)/(4.21)): the completed rational
localization is the Banach graph quotient, as topological rings. -/
noncomputable def graphBridge (hD : D.IsRational)
    (hIcl : IsClosed ((IA e.m D.s e.f : Set (P E e.m)))) :
    presheafValue D ≃+* locA e.m D.s e.f where
  toFun := bridgeFwd D e hD hIcl
  invFun := bridgeRev D e
  left_inv := bridgeRev_bridgeFwd D e hD hIcl
  right_inv := bridgeFwd_bridgeRev D e hD hIcl
  map_mul' := map_mul (bridgeFwd D e hD hIcl)
  map_add' := map_add (bridgeFwd D e hD hIcl)

omit [PlusSubring E] [HasLocLiftPowerBounded E] in
theorem graphBridge_continuous (hD : D.IsRational)
    (hIcl : IsClosed ((IA e.m D.s e.f : Set (P E e.m)))) :
    Continuous (graphBridge D e hD hIcl) :=
  bridgeFwd_continuous D e hD hIcl

omit [PlusSubring E] [HasLocLiftPowerBounded E] in
theorem graphBridge_symm_continuous (hD : D.IsRational)
    (hIcl : IsClosed ((IA e.m D.s e.f : Set (P E e.m)))) :
    Continuous (graphBridge D e hD hIcl).symm :=
  bridgeRev_continuous D e

end Eval

end CornerBridge

/-! ### The square-level bridges: pushed enumerations and naturality (stage 4c)

Instantiating the single-corner bridge at the four vertices of a pinch square:
the pushed data (`pushDatumOfHom`) carry pushed enumerations of the SAME arity,
and by the polyToP-form of the `Pinch` relations the pushed graph ideals are the
`Pinch.IB/IC/ID` ideals definitionally, so the vertex bridges land in
`Pinch.locB/locC/locD`. The naturality squares (N1)–(N4) identify the
value-level square with the localized Milnor square. -/

namespace Pinch

section Square

variable {A B C D : Type*}
  [NormedCommRing A] [IsUltrametricDist A] [NormOneClass A] [CompleteSpace A]
  [PlusSubring A] [IsTateRing A] [HasLocLiftPowerBounded A]
  [NormedCommRing B] [IsUltrametricDist B] [NormOneClass B] [CompleteSpace B]
  [PlusSubring B] [IsTateRing B] [HasLocLiftPowerBounded B]
  [NormedCommRing C] [IsUltrametricDist C] [NormOneClass C] [CompleteSpace C]
  [PlusSubring C] [IsTateRing C] [HasLocLiftPowerBounded C]
  [NormedCommRing D] [IsUltrametricDist D] [NormOneClass D] [CompleteSpace D]
  [PlusSubring D] [IsTateRing D] [HasLocLiftPowerBounded D]
  [DecidableEq B] [DecidableEq C] [DecidableEq D]

variable (S : Pinch A B C D)

omit [NormOneClass B] [CompleteSpace B] in
omit [NormOneClass A] [CompleteSpace A] [PlusSubring A] [IsTateRing A] [HasLocLiftPowerBounded A] [PlusSubring B] [IsTateRing B] [HasLocLiftPowerBounded B] [NormOneClass C] [CompleteSpace C] [PlusSubring C] [IsTateRing C] [HasLocLiftPowerBounded C] [NormOneClass D] [CompleteSpace D] [PlusSubring D] [IsTateRing D] [HasLocLiftPowerBounded D] [DecidableEq B] [DecidableEq C] [DecidableEq D] in
/-- Continuity of `φB` from its norm bound. -/
theorem φB_continuous : Continuous S.φB :=
  AddMonoidHomClass.continuous_of_bound S.φB 1 fun a => by
    rw [one_mul]; exact S.norm_φB_le a

omit [NormOneClass C] [CompleteSpace C] [NormOneClass A] [CompleteSpace A] [PlusSubring A] [IsTateRing A] [HasLocLiftPowerBounded A] [NormOneClass B] [CompleteSpace B] [PlusSubring B] [IsTateRing B] [HasLocLiftPowerBounded B] [PlusSubring C] [IsTateRing C] [HasLocLiftPowerBounded C] [NormOneClass D] [CompleteSpace D] [PlusSubring D] [IsTateRing D] [HasLocLiftPowerBounded D] [DecidableEq B] [DecidableEq C] [DecidableEq D] in
theorem φC_continuous : Continuous S.φC :=
  AddMonoidHomClass.continuous_of_bound S.φC 1 fun a => by
    rw [one_mul]; exact le_of_eq (S.norm_φC a)

omit [NormOneClass B] [CompleteSpace B] [NormOneClass D] [CompleteSpace D] [NormOneClass A] [CompleteSpace A] [PlusSubring A] [IsTateRing A] [HasLocLiftPowerBounded A] [PlusSubring B] [IsTateRing B] [HasLocLiftPowerBounded B] [NormOneClass C] [CompleteSpace C] [PlusSubring C] [IsTateRing C] [HasLocLiftPowerBounded C] [PlusSubring D] [IsTateRing D] [HasLocLiftPowerBounded D] [DecidableEq B] [DecidableEq C] [DecidableEq D] in
theorem ψB_continuous : Continuous S.ψB :=
  AddMonoidHomClass.continuous_of_bound S.ψB 1 fun b => by
    rw [one_mul]; exact le_of_eq (S.norm_ψB b)

omit [NormOneClass C] [CompleteSpace C] [NormOneClass D] [CompleteSpace D] [NormOneClass A] [CompleteSpace A] [PlusSubring A] [IsTateRing A] [HasLocLiftPowerBounded A] [NormOneClass B] [CompleteSpace B] [PlusSubring B] [IsTateRing B] [HasLocLiftPowerBounded B] [PlusSubring C] [IsTateRing C] [HasLocLiftPowerBounded C] [PlusSubring D] [IsTateRing D] [HasLocLiftPowerBounded D] [DecidableEq B] [DecidableEq C] [DecidableEq D] in
theorem ψC_continuous : Continuous S.ψC :=
  AddMonoidHomClass.continuous_of_bound S.ψC 1 fun c => by
    rw [one_mul]; exact S.norm_ψC_le c

variable (PB : PairOfDefinition B) (PC : PairOfDefinition C) (PD : PairOfDefinition D)
variable (D₀ : RationalLocData A) (e : CornerEnum D₀) (hD₀ : D₀.IsRational)

/-- The pushed enumeration at the `B`-vertex. -/
noncomputable def pushEnumB : CornerEnum (pushDatumOfHom S.φB PB D₀ hD₀) where
  m := e.m
  f := fun i => S.φB (e.f i)
  hf := by
    intro t ht
    obtain ⟨t₀, ht₀, rfl⟩ := Finset.mem_image.mp ht
    obtain ⟨i, rfl⟩ := e.hf t₀ ht₀
    exact ⟨i, rfl⟩
  hf' := fun i => Finset.mem_image_of_mem _ (e.hf' i)

/-- The pushed enumeration at the `C`-vertex. -/
noncomputable def pushEnumC : CornerEnum (pushDatumOfHom S.φC PC D₀ hD₀) where
  m := e.m
  f := fun i => S.φC (e.f i)
  hf := by
    intro t ht
    obtain ⟨t₀, ht₀, rfl⟩ := Finset.mem_image.mp ht
    obtain ⟨i, rfl⟩ := e.hf t₀ ht₀
    exact ⟨i, rfl⟩
  hf' := fun i => Finset.mem_image_of_mem _ (e.hf' i)

/-- The pushed enumeration at the `D`-vertex (along the composite leg). -/
noncomputable def pushEnumD :
    CornerEnum (pushDatumOfHom (S.ψC.comp S.φC) PD D₀ hD₀) where
  m := e.m
  f := fun i => S.ψC (S.φC (e.f i))
  hf := by
    intro t ht
    obtain ⟨t₀, ht₀, rfl⟩ := Finset.mem_image.mp ht
    obtain ⟨i, rfl⟩ := e.hf t₀ ht₀
    exact ⟨i, rfl⟩
  hf' := fun i => Finset.mem_image_of_mem _ (e.hf' i)

omit [NormOneClass A] [CompleteSpace A] [PlusSubring A] [HasLocLiftPowerBounded A] [PlusSubring B] [IsTateRing B] [HasLocLiftPowerBounded B] [NormOneClass C] [CompleteSpace C] [PlusSubring C] [IsTateRing C] [HasLocLiftPowerBounded C] [NormOneClass D] [CompleteSpace D] [PlusSubring D] [IsTateRing D] [HasLocLiftPowerBounded D] [DecidableEq B] [DecidableEq C] [DecidableEq D] in
/-- Closedness of the pushed `B`-graph ideal (Koszul, corner-intrinsic). -/
theorem isClosed_pushB (hPB : IsNoetherianRing (P B e.m))
    (hPBball : IsNoetherianRing (unitBall (P B e.m))) :
    IsClosed ((IA e.m (S.φB D₀.s) (fun i => S.φB (e.f i)) : Set (P B e.m))) := by
  have := hPB
  exact isClosed_graphIdeal S.tB S.tB_isUnit S.norm_tB_lt_one S.norm_tB_pos
    S.norm_tB_mul hPBball _

omit [NormOneClass A] [CompleteSpace A] [PlusSubring A] [HasLocLiftPowerBounded A] [NormOneClass B] [CompleteSpace B] [PlusSubring B] [IsTateRing B] [HasLocLiftPowerBounded B] [PlusSubring C] [IsTateRing C] [HasLocLiftPowerBounded C] [NormOneClass D] [CompleteSpace D] [PlusSubring D] [IsTateRing D] [HasLocLiftPowerBounded D] [DecidableEq B] [DecidableEq C] [DecidableEq D] in
/-- Closedness of the pushed `C`-graph ideal. -/
theorem isClosed_pushC (hPC : IsNoetherianRing (P C e.m))
    (hPCball : IsNoetherianRing (unitBall (P C e.m))) :
    IsClosed ((IA e.m (S.φC D₀.s) (fun i => S.φC (e.f i)) : Set (P C e.m))) := by
  have := hPC
  exact isClosed_graphIdeal S.tC S.tC_isUnit S.norm_tC_lt_one S.norm_tC_pos
    S.norm_tC_mul hPCball _

omit [NormOneClass A] [CompleteSpace A] [PlusSubring A] [HasLocLiftPowerBounded A] [NormOneClass B] [CompleteSpace B] [PlusSubring B] [IsTateRing B] [HasLocLiftPowerBounded B] [NormOneClass C] [CompleteSpace C] [PlusSubring C] [IsTateRing C] [HasLocLiftPowerBounded C] [PlusSubring D] [IsTateRing D] [HasLocLiftPowerBounded D] [DecidableEq B] [DecidableEq C] [DecidableEq D] in
/-- Closedness of the pushed `D`-graph ideal. -/
theorem isClosed_pushD (hPD : IsNoetherianRing (P D e.m))
    (hPDball : IsNoetherianRing (unitBall (P D e.m))) :
    IsClosed ((IA e.m (S.ψC (S.φC D₀.s)) (fun i => S.ψC (S.φC (e.f i))) :
      Set (P D e.m))) := by
  have := hPD
  exact isClosed_graphIdeal S.tD S.tD_isUnit S.norm_tD_lt_one S.norm_tD_pos
    S.norm_tD_mul hPDball _

omit [PlusSubring A] [HasLocLiftPowerBounded A] [PlusSubring B] [HasLocLiftPowerBounded B] [NormOneClass C] [CompleteSpace C] [PlusSubring C] [IsTateRing C] [HasLocLiftPowerBounded C] [NormOneClass D] [CompleteSpace D] [PlusSubring D] [IsTateRing D] [HasLocLiftPowerBounded D] [DecidableEq C] [DecidableEq D] in
/-- `locφB` carries the `A`-bridge base to the `B`-bridge base. -/
theorem locφB_bridgeBase (a : A) :
    S.locφB e.m D₀.s e.f (CornerBridge.bridgeBase D₀ e a) =
      CornerBridge.bridgeBase (pushDatumOfHom S.φB PB D₀ hD₀)
        (S.pushEnumB PB D₀ e hD₀) (S.φB a) := by
  show Ideal.Quotient.mk (S.IB e.m D₀.s e.f)
      (S.extB e.m (polyToP (MvPolynomial.C a))) =
    Ideal.Quotient.mk (S.IB e.m D₀.s e.f) (polyToP (MvPolynomial.C (S.φB a)))
  congr 1
  show mapRestricted S.φB S.norm_φB_le _ (polyToP _) = _
  rw [StrictLoc.mapRestricted_polyToP, MvPolynomial.map_C]

omit [PlusSubring A] [HasLocLiftPowerBounded A] [NormOneClass B] [CompleteSpace B] [PlusSubring B] [IsTateRing B] [HasLocLiftPowerBounded B] [PlusSubring C] [HasLocLiftPowerBounded C] [NormOneClass D] [CompleteSpace D] [PlusSubring D] [IsTateRing D] [HasLocLiftPowerBounded D] [DecidableEq B] [DecidableEq D] in
/-- `locφC` carries the `A`-bridge base to the `C`-bridge base. -/
theorem locφC_bridgeBase (a : A) :
    S.locφC e.m D₀.s e.f (CornerBridge.bridgeBase D₀ e a) =
      CornerBridge.bridgeBase (pushDatumOfHom S.φC PC D₀ hD₀)
        (S.pushEnumC PC D₀ e hD₀) (S.φC a) := by
  show Ideal.Quotient.mk (S.IC e.m D₀.s e.f)
      (S.extC e.m (polyToP (MvPolynomial.C a))) =
    Ideal.Quotient.mk (S.IC e.m D₀.s e.f) (polyToP (MvPolynomial.C (S.φC a)))
  congr 1
  show mapRestricted S.φC (fun x => le_of_eq (S.norm_φC x)) _ (polyToP _) = _
  rw [StrictLoc.mapRestricted_polyToP, MvPolynomial.map_C]

omit [PlusSubring A] [HasLocLiftPowerBounded A] [PlusSubring B] [HasLocLiftPowerBounded B] [PlusSubring C] [IsTateRing C] [HasLocLiftPowerBounded C] [PlusSubring D] [HasLocLiftPowerBounded D] [DecidableEq C] in
/-- `locψB` carries the `B`-bridge base to the `D`-bridge base. -/
theorem locψB_bridgeBase (b : B) :
    S.locψB e.m D₀.s e.f
      (CornerBridge.bridgeBase (pushDatumOfHom S.φB PB D₀ hD₀)
        (S.pushEnumB PB D₀ e hD₀) b) =
      CornerBridge.bridgeBase (pushDatumOfHom (S.ψC.comp S.φC) PD D₀ hD₀)
        (S.pushEnumD PD D₀ e hD₀) (S.ψB b) := by
  show Ideal.Quotient.mk (S.ID e.m D₀.s e.f)
      (S.extDB e.m (polyToP (MvPolynomial.C b))) =
    Ideal.Quotient.mk (S.ID e.m D₀.s e.f) (polyToP (MvPolynomial.C (S.ψB b)))
  congr 1
  show mapRestricted S.ψB (fun x => le_of_eq (S.norm_ψB x)) _ (polyToP _) = _
  rw [StrictLoc.mapRestricted_polyToP, MvPolynomial.map_C]

omit [NormOneClass A] [CompleteSpace A] [PlusSubring A] [HasLocLiftPowerBounded A] [NormOneClass B] [CompleteSpace B] [PlusSubring B] [IsTateRing B] [HasLocLiftPowerBounded B] [PlusSubring C] [HasLocLiftPowerBounded C] [PlusSubring D] [HasLocLiftPowerBounded D] [DecidableEq B] in
/-- `locψC` carries the `C`-bridge base to the `D`-bridge base. -/
theorem locψC_bridgeBase (c : C) :
    S.locψC e.m D₀.s e.f
      (CornerBridge.bridgeBase (pushDatumOfHom S.φC PC D₀ hD₀)
        (S.pushEnumC PC D₀ e hD₀) c) =
      CornerBridge.bridgeBase (pushDatumOfHom (S.ψC.comp S.φC) PD D₀ hD₀)
        (S.pushEnumD PD D₀ e hD₀) (S.ψC c) := by
  show Ideal.Quotient.mk (S.ID e.m D₀.s e.f)
      (S.extDC e.m (polyToP (MvPolynomial.C c))) =
    Ideal.Quotient.mk (S.ID e.m D₀.s e.f) (polyToP (MvPolynomial.C (S.ψC c)))
  congr 1
  show mapRestricted S.ψC S.norm_ψC_le _ (polyToP _) = _
  rw [StrictLoc.mapRestricted_polyToP, MvPolynomial.map_C]

omit [PlusSubring A] [HasLocLiftPowerBounded A] [PlusSubring B] [HasLocLiftPowerBounded B] [NormOneClass C] [CompleteSpace C] [PlusSubring C] [IsTateRing C] [HasLocLiftPowerBounded C] [NormOneClass D] [CompleteSpace D] [PlusSubring D] [IsTateRing D] [HasLocLiftPowerBounded D] [DecidableEq C] [DecidableEq D] in
/-- **(N1) Push naturality at `B`**: the `B`-vertex bridge intertwines the
value-level push with the localized `locφB` ([FJP] Lemma 5.1's square, bridged). -/
theorem bridgeFwd_natural_B
    (hIclA : IsClosed ((IA e.m D₀.s e.f : Set (P A e.m))))
    (hIclB : IsClosed ((IA e.m (S.φB D₀.s) (fun i => S.φB (e.f i)) : Set (P B e.m))))
    (hφ : Continuous S.φB)
    (hs : (pushDatumOfHom S.φB PB D₀ hD₀).s = S.φB D₀.s)
    (hT : ∀ t ∈ D₀.T, S.φB t ∈ (pushDatumOfHom S.φB PB D₀ hD₀).T)
    (x : presheafValue D₀) :
    CornerBridge.bridgeFwd (pushDatumOfHom S.φB PB D₀ hD₀)
        (S.pushEnumB PB D₀ e hD₀) (pushDatumOfHom_isRational S.φB PB hD₀) hIclB
      (presheafValueMapOfHom S.φB hφ D₀ (pushDatumOfHom S.φB PB D₀ hD₀) hs hT x) =
    S.locφB e.m D₀.s e.f (CornerBridge.bridgeFwd D₀ e hD₀ hIclA x) := by
  let _i := D₀.uniformSpace
  have : IsTopologicalRing (Localization.Away D₀.s) := D₀.isTopologicalRing
  have : IsUniformAddGroup (Localization.Away D₀.s) := D₀.isUniformAddGroup
  have hT2 := CornerBridge.locE_t2 (pushDatumOfHom S.φB PB D₀ hD₀)
    (S.pushEnumB PB D₀ e hD₀) hIclB
  have hcomp :
      ((CornerBridge.bridgeFwd (pushDatumOfHom S.φB PB D₀ hD₀)
          (S.pushEnumB PB D₀ e hD₀)
          (pushDatumOfHom_isRational S.φB PB hD₀) hIclB).comp
        (presheafValueMapOfHom S.φB hφ D₀ (pushDatumOfHom S.φB PB D₀ hD₀)
          hs hT)).comp D₀.coeRingHom =
      ((S.locφB e.m D₀.s e.f).comp
        (CornerBridge.bridgeFwd D₀ e hD₀ hIclA)).comp D₀.coeRingHom := by
    refine IsLocalization.ringHom_ext (Submonoid.powers D₀.s) ?_
    refine RingHom.ext fun a => ?_
    show CornerBridge.bridgeFwd (pushDatumOfHom S.φB PB D₀ hD₀)
        (S.pushEnumB PB D₀ e hD₀) (pushDatumOfHom_isRational S.φB PB hD₀) hIclB
        (presheafValueMapOfHom S.φB hφ D₀ (pushDatumOfHom S.φB PB D₀ hD₀) hs hT
          (D₀.canonicalMap a)) =
      S.locφB e.m D₀.s e.f (CornerBridge.bridgeFwd D₀ e hD₀ hIclA
        (D₀.canonicalMap a))
    rw [presheafValueMapOfHom_canonicalMap S.φB hφ D₀ _ hs hT a,
      CornerBridge.bridgeFwd_canonicalMap,
      CornerBridge.bridgeFwd_canonicalMap,
      S.locφB_bridgeBase PB D₀ e hD₀ a]
  have hdense : DenseRange (D₀.coeRingHom :
      Localization.Away D₀.s → presheafValue D₀) :=
    UniformSpace.Completion.denseRange_coe
  have h_eq : (fun y => CornerBridge.bridgeFwd (pushDatumOfHom S.φB PB D₀ hD₀)
      (S.pushEnumB PB D₀ e hD₀) (pushDatumOfHom_isRational S.φB PB hD₀) hIclB
      (presheafValueMapOfHom S.φB hφ D₀ (pushDatumOfHom S.φB PB D₀ hD₀) hs hT y)) =
      fun y => S.locφB e.m D₀.s e.f (CornerBridge.bridgeFwd D₀ e hD₀ hIclA y) :=
    hdense.equalizer
      ((CornerBridge.bridgeFwd_continuous _ _ _ hIclB).comp
        (presheafValueMapOfHom_continuous S.φB hφ D₀ _ hs hT))
      (((S.locφB_lipschitz e.m D₀.s e.f).continuous).comp
        (CornerBridge.bridgeFwd_continuous _ _ _ hIclA))
      (by funext a; exact DFunLike.congr_fun hcomp a)
  exact congrFun h_eq x

omit [PlusSubring A] [HasLocLiftPowerBounded A] [NormOneClass B] [CompleteSpace B] [PlusSubring B] [IsTateRing B] [HasLocLiftPowerBounded B] [PlusSubring C] [HasLocLiftPowerBounded C] [NormOneClass D] [CompleteSpace D] [PlusSubring D] [IsTateRing D] [HasLocLiftPowerBounded D] [DecidableEq B] [DecidableEq D] in
/-- **(N2) Push naturality at `C`**. -/
theorem bridgeFwd_natural_C
    (hIclA : IsClosed ((IA e.m D₀.s e.f : Set (P A e.m))))
    (hIclC : IsClosed ((IA e.m (S.φC D₀.s) (fun i => S.φC (e.f i)) : Set (P C e.m))))
    (hφ : Continuous S.φC)
    (hs : (pushDatumOfHom S.φC PC D₀ hD₀).s = S.φC D₀.s)
    (hT : ∀ t ∈ D₀.T, S.φC t ∈ (pushDatumOfHom S.φC PC D₀ hD₀).T)
    (x : presheafValue D₀) :
    CornerBridge.bridgeFwd (pushDatumOfHom S.φC PC D₀ hD₀)
        (S.pushEnumC PC D₀ e hD₀) (pushDatumOfHom_isRational S.φC PC hD₀) hIclC
      (presheafValueMapOfHom S.φC hφ D₀ (pushDatumOfHom S.φC PC D₀ hD₀) hs hT x) =
    S.locφC e.m D₀.s e.f (CornerBridge.bridgeFwd D₀ e hD₀ hIclA x) := by
  let _i := D₀.uniformSpace
  have : IsTopologicalRing (Localization.Away D₀.s) := D₀.isTopologicalRing
  have : IsUniformAddGroup (Localization.Away D₀.s) := D₀.isUniformAddGroup
  have hT2 := CornerBridge.locE_t2 (pushDatumOfHom S.φC PC D₀ hD₀)
    (S.pushEnumC PC D₀ e hD₀) hIclC
  have hcomp :
      ((CornerBridge.bridgeFwd (pushDatumOfHom S.φC PC D₀ hD₀)
          (S.pushEnumC PC D₀ e hD₀)
          (pushDatumOfHom_isRational S.φC PC hD₀) hIclC).comp
        (presheafValueMapOfHom S.φC hφ D₀ (pushDatumOfHom S.φC PC D₀ hD₀)
          hs hT)).comp D₀.coeRingHom =
      ((S.locφC e.m D₀.s e.f).comp
        (CornerBridge.bridgeFwd D₀ e hD₀ hIclA)).comp D₀.coeRingHom := by
    refine IsLocalization.ringHom_ext (Submonoid.powers D₀.s) ?_
    refine RingHom.ext fun a => ?_
    show CornerBridge.bridgeFwd (pushDatumOfHom S.φC PC D₀ hD₀)
        (S.pushEnumC PC D₀ e hD₀) (pushDatumOfHom_isRational S.φC PC hD₀) hIclC
        (presheafValueMapOfHom S.φC hφ D₀ (pushDatumOfHom S.φC PC D₀ hD₀) hs hT
          (D₀.canonicalMap a)) =
      S.locφC e.m D₀.s e.f (CornerBridge.bridgeFwd D₀ e hD₀ hIclA
        (D₀.canonicalMap a))
    rw [presheafValueMapOfHom_canonicalMap S.φC hφ D₀ _ hs hT a,
      CornerBridge.bridgeFwd_canonicalMap,
      CornerBridge.bridgeFwd_canonicalMap,
      S.locφC_bridgeBase PC D₀ e hD₀ a]
  have hdense : DenseRange (D₀.coeRingHom :
      Localization.Away D₀.s → presheafValue D₀) :=
    UniformSpace.Completion.denseRange_coe
  have h_eq : (fun y => CornerBridge.bridgeFwd (pushDatumOfHom S.φC PC D₀ hD₀)
      (S.pushEnumC PC D₀ e hD₀) (pushDatumOfHom_isRational S.φC PC hD₀) hIclC
      (presheafValueMapOfHom S.φC hφ D₀ (pushDatumOfHom S.φC PC D₀ hD₀) hs hT y)) =
      fun y => S.locφC e.m D₀.s e.f (CornerBridge.bridgeFwd D₀ e hD₀ hIclA y) :=
    hdense.equalizer
      ((CornerBridge.bridgeFwd_continuous _ _ _ hIclC).comp
        (presheafValueMapOfHom_continuous S.φC hφ D₀ _ hs hT))
      (((S.locφC_lipschitz e.m D₀.s e.f).continuous).comp
        (CornerBridge.bridgeFwd_continuous _ _ _ hIclA))
      (by funext a; exact DFunLike.congr_fun hcomp a)
  exact congrFun h_eq x

omit [PlusSubring A] [HasLocLiftPowerBounded A] [PlusSubring B] [HasLocLiftPowerBounded B] [PlusSubring C] [IsTateRing C] [HasLocLiftPowerBounded C] [PlusSubring D] [HasLocLiftPowerBounded D] [DecidableEq C] in
/-- **(N3) Leg naturality at `B → D`**: `locψB` intertwines the vertex bridges
with the value-level leg map. -/
theorem bridgeFwd_natural_legB
    (hIclB : IsClosed ((IA e.m (S.φB D₀.s) (fun i => S.φB (e.f i)) : Set (P B e.m))))
    (hIclD : IsClosed ((IA e.m (S.ψC (S.φC D₀.s)) (fun i => S.ψC (S.φC (e.f i))) :
      Set (P D e.m))))
    (hψ : Continuous S.ψB)
    (hs : (pushDatumOfHom (S.ψC.comp S.φC) PD D₀ hD₀).s =
      S.ψB (pushDatumOfHom S.φB PB D₀ hD₀).s)
    (hT : ∀ t ∈ (pushDatumOfHom S.φB PB D₀ hD₀).T,
      S.ψB t ∈ (pushDatumOfHom (S.ψC.comp S.φC) PD D₀ hD₀).T)
    (b : presheafValue (pushDatumOfHom S.φB PB D₀ hD₀)) :
    CornerBridge.bridgeFwd (pushDatumOfHom (S.ψC.comp S.φC) PD D₀ hD₀)
        (S.pushEnumD PD D₀ e hD₀)
        (pushDatumOfHom_isRational (S.ψC.comp S.φC) PD hD₀) hIclD
      (presheafValueMapOfHom S.ψB hψ (pushDatumOfHom S.φB PB D₀ hD₀)
        (pushDatumOfHom (S.ψC.comp S.φC) PD D₀ hD₀) hs hT b) =
    S.locψB e.m D₀.s e.f
      (CornerBridge.bridgeFwd (pushDatumOfHom S.φB PB D₀ hD₀)
        (S.pushEnumB PB D₀ e hD₀)
        (pushDatumOfHom_isRational S.φB PB hD₀) hIclB b) := by
  let _i := (pushDatumOfHom S.φB PB D₀ hD₀).uniformSpace
  have : IsTopologicalRing (Localization.Away (pushDatumOfHom S.φB PB D₀ hD₀).s) :=
    (pushDatumOfHom S.φB PB D₀ hD₀).isTopologicalRing
  have : IsUniformAddGroup (Localization.Away (pushDatumOfHom S.φB PB D₀ hD₀).s) :=
    (pushDatumOfHom S.φB PB D₀ hD₀).isUniformAddGroup
  have hT2 := CornerBridge.locE_t2 (pushDatumOfHom (S.ψC.comp S.φC) PD D₀ hD₀)
    (S.pushEnumD PD D₀ e hD₀) hIclD
  have hcomp :
      ((CornerBridge.bridgeFwd (pushDatumOfHom (S.ψC.comp S.φC) PD D₀ hD₀)
          (S.pushEnumD PD D₀ e hD₀)
          (pushDatumOfHom_isRational (S.ψC.comp S.φC) PD hD₀) hIclD).comp
        (presheafValueMapOfHom S.ψB hψ (pushDatumOfHom S.φB PB D₀ hD₀)
          (pushDatumOfHom (S.ψC.comp S.φC) PD D₀ hD₀) hs hT)).comp
        (pushDatumOfHom S.φB PB D₀ hD₀).coeRingHom =
      ((S.locψB e.m D₀.s e.f).comp
        (CornerBridge.bridgeFwd (pushDatumOfHom S.φB PB D₀ hD₀)
          (S.pushEnumB PB D₀ e hD₀)
          (pushDatumOfHom_isRational S.φB PB hD₀) hIclB)).comp
        (pushDatumOfHom S.φB PB D₀ hD₀).coeRingHom := by
    refine IsLocalization.ringHom_ext
      (Submonoid.powers (pushDatumOfHom S.φB PB D₀ hD₀).s) ?_
    refine RingHom.ext fun b₀ => ?_
    show CornerBridge.bridgeFwd (pushDatumOfHom (S.ψC.comp S.φC) PD D₀ hD₀)
        (S.pushEnumD PD D₀ e hD₀)
        (pushDatumOfHom_isRational (S.ψC.comp S.φC) PD hD₀) hIclD
        (presheafValueMapOfHom S.ψB hψ (pushDatumOfHom S.φB PB D₀ hD₀)
          (pushDatumOfHom (S.ψC.comp S.φC) PD D₀ hD₀) hs hT
          ((pushDatumOfHom S.φB PB D₀ hD₀).canonicalMap b₀)) =
      S.locψB e.m D₀.s e.f
        (CornerBridge.bridgeFwd (pushDatumOfHom S.φB PB D₀ hD₀)
          (S.pushEnumB PB D₀ e hD₀)
          (pushDatumOfHom_isRational S.φB PB hD₀) hIclB
          ((pushDatumOfHom S.φB PB D₀ hD₀).canonicalMap b₀))
    rw [presheafValueMapOfHom_canonicalMap S.ψB hψ _ _ hs hT b₀,
      CornerBridge.bridgeFwd_canonicalMap,
      CornerBridge.bridgeFwd_canonicalMap,
      S.locψB_bridgeBase PB PD D₀ e hD₀ b₀]
  have hdense : DenseRange ((pushDatumOfHom S.φB PB D₀ hD₀).coeRingHom :
      Localization.Away (pushDatumOfHom S.φB PB D₀ hD₀).s →
        presheafValue (pushDatumOfHom S.φB PB D₀ hD₀)) :=
    UniformSpace.Completion.denseRange_coe
  have h_eq : (fun y => CornerBridge.bridgeFwd
      (pushDatumOfHom (S.ψC.comp S.φC) PD D₀ hD₀) (S.pushEnumD PD D₀ e hD₀)
      (pushDatumOfHom_isRational (S.ψC.comp S.φC) PD hD₀) hIclD
      (presheafValueMapOfHom S.ψB hψ (pushDatumOfHom S.φB PB D₀ hD₀)
        (pushDatumOfHom (S.ψC.comp S.φC) PD D₀ hD₀) hs hT y)) =
      fun y => S.locψB e.m D₀.s e.f
        (CornerBridge.bridgeFwd (pushDatumOfHom S.φB PB D₀ hD₀)
          (S.pushEnumB PB D₀ e hD₀)
          (pushDatumOfHom_isRational S.φB PB hD₀) hIclB y) :=
    hdense.equalizer
      ((CornerBridge.bridgeFwd_continuous _ _ _ hIclD).comp
        (presheafValueMapOfHom_continuous S.ψB hψ _ _ hs hT))
      (((S.locψB_lipschitz e.m D₀.s e.f).continuous).comp
        (CornerBridge.bridgeFwd_continuous _ _ _ hIclB))
      (by funext a; exact DFunLike.congr_fun hcomp a)
  exact congrFun h_eq b

omit [NormOneClass A] [CompleteSpace A] [PlusSubring A] [HasLocLiftPowerBounded A] [NormOneClass B] [CompleteSpace B] [PlusSubring B] [IsTateRing B] [HasLocLiftPowerBounded B] [PlusSubring C] [HasLocLiftPowerBounded C] [PlusSubring D] [HasLocLiftPowerBounded D] [DecidableEq B] in
/-- **(N4) Leg naturality at `C → D`**. -/
theorem bridgeFwd_natural_legC
    (hIclC : IsClosed ((IA e.m (S.φC D₀.s) (fun i => S.φC (e.f i)) : Set (P C e.m))))
    (hIclD : IsClosed ((IA e.m (S.ψC (S.φC D₀.s)) (fun i => S.ψC (S.φC (e.f i))) :
      Set (P D e.m))))
    (hψ : Continuous S.ψC)
    (hs : (pushDatumOfHom (S.ψC.comp S.φC) PD D₀ hD₀).s =
      S.ψC (pushDatumOfHom S.φC PC D₀ hD₀).s)
    (hT : ∀ t ∈ (pushDatumOfHom S.φC PC D₀ hD₀).T,
      S.ψC t ∈ (pushDatumOfHom (S.ψC.comp S.φC) PD D₀ hD₀).T)
    (c : presheafValue (pushDatumOfHom S.φC PC D₀ hD₀)) :
    CornerBridge.bridgeFwd (pushDatumOfHom (S.ψC.comp S.φC) PD D₀ hD₀)
        (S.pushEnumD PD D₀ e hD₀)
        (pushDatumOfHom_isRational (S.ψC.comp S.φC) PD hD₀) hIclD
      (presheafValueMapOfHom S.ψC hψ (pushDatumOfHom S.φC PC D₀ hD₀)
        (pushDatumOfHom (S.ψC.comp S.φC) PD D₀ hD₀) hs hT c) =
    S.locψC e.m D₀.s e.f
      (CornerBridge.bridgeFwd (pushDatumOfHom S.φC PC D₀ hD₀)
        (S.pushEnumC PC D₀ e hD₀)
        (pushDatumOfHom_isRational S.φC PC hD₀) hIclC c) := by
  let _i := (pushDatumOfHom S.φC PC D₀ hD₀).uniformSpace
  have : IsTopologicalRing (Localization.Away (pushDatumOfHom S.φC PC D₀ hD₀).s) :=
    (pushDatumOfHom S.φC PC D₀ hD₀).isTopologicalRing
  have : IsUniformAddGroup (Localization.Away (pushDatumOfHom S.φC PC D₀ hD₀).s) :=
    (pushDatumOfHom S.φC PC D₀ hD₀).isUniformAddGroup
  have hT2 := CornerBridge.locE_t2 (pushDatumOfHom (S.ψC.comp S.φC) PD D₀ hD₀)
    (S.pushEnumD PD D₀ e hD₀) hIclD
  have hcomp :
      ((CornerBridge.bridgeFwd (pushDatumOfHom (S.ψC.comp S.φC) PD D₀ hD₀)
          (S.pushEnumD PD D₀ e hD₀)
          (pushDatumOfHom_isRational (S.ψC.comp S.φC) PD hD₀) hIclD).comp
        (presheafValueMapOfHom S.ψC hψ (pushDatumOfHom S.φC PC D₀ hD₀)
          (pushDatumOfHom (S.ψC.comp S.φC) PD D₀ hD₀) hs hT)).comp
        (pushDatumOfHom S.φC PC D₀ hD₀).coeRingHom =
      ((S.locψC e.m D₀.s e.f).comp
        (CornerBridge.bridgeFwd (pushDatumOfHom S.φC PC D₀ hD₀)
          (S.pushEnumC PC D₀ e hD₀)
          (pushDatumOfHom_isRational S.φC PC hD₀) hIclC)).comp
        (pushDatumOfHom S.φC PC D₀ hD₀).coeRingHom := by
    refine IsLocalization.ringHom_ext
      (Submonoid.powers (pushDatumOfHom S.φC PC D₀ hD₀).s) ?_
    refine RingHom.ext fun c₀ => ?_
    show CornerBridge.bridgeFwd (pushDatumOfHom (S.ψC.comp S.φC) PD D₀ hD₀)
        (S.pushEnumD PD D₀ e hD₀)
        (pushDatumOfHom_isRational (S.ψC.comp S.φC) PD hD₀) hIclD
        (presheafValueMapOfHom S.ψC hψ (pushDatumOfHom S.φC PC D₀ hD₀)
          (pushDatumOfHom (S.ψC.comp S.φC) PD D₀ hD₀) hs hT
          ((pushDatumOfHom S.φC PC D₀ hD₀).canonicalMap c₀)) =
      S.locψC e.m D₀.s e.f
        (CornerBridge.bridgeFwd (pushDatumOfHom S.φC PC D₀ hD₀)
          (S.pushEnumC PC D₀ e hD₀)
          (pushDatumOfHom_isRational S.φC PC hD₀) hIclC
          ((pushDatumOfHom S.φC PC D₀ hD₀).canonicalMap c₀))
    rw [presheafValueMapOfHom_canonicalMap S.ψC hψ _ _ hs hT c₀,
      CornerBridge.bridgeFwd_canonicalMap,
      CornerBridge.bridgeFwd_canonicalMap,
      S.locψC_bridgeBase PC PD D₀ e hD₀ c₀]
  have hdense : DenseRange ((pushDatumOfHom S.φC PC D₀ hD₀).coeRingHom :
      Localization.Away (pushDatumOfHom S.φC PC D₀ hD₀).s →
        presheafValue (pushDatumOfHom S.φC PC D₀ hD₀)) :=
    UniformSpace.Completion.denseRange_coe
  have h_eq : (fun y => CornerBridge.bridgeFwd
      (pushDatumOfHom (S.ψC.comp S.φC) PD D₀ hD₀) (S.pushEnumD PD D₀ e hD₀)
      (pushDatumOfHom_isRational (S.ψC.comp S.φC) PD hD₀) hIclD
      (presheafValueMapOfHom S.ψC hψ (pushDatumOfHom S.φC PC D₀ hD₀)
        (pushDatumOfHom (S.ψC.comp S.φC) PD D₀ hD₀) hs hT y)) =
      fun y => S.locψC e.m D₀.s e.f
        (CornerBridge.bridgeFwd (pushDatumOfHom S.φC PC D₀ hD₀)
          (S.pushEnumC PC D₀ e hD₀)
          (pushDatumOfHom_isRational S.φC PC hD₀) hIclC y) :=
    hdense.equalizer
      ((CornerBridge.bridgeFwd_continuous _ _ _ hIclD).comp
        (presheafValueMapOfHom_continuous S.ψC hψ _ _ hs hT))
      (((S.locψC_lipschitz e.m D₀.s e.f).continuous).comp
        (CornerBridge.bridgeFwd_continuous _ _ _ hIclC))
      (by funext a; exact DFunLike.congr_fun hcomp a)
  exact congrFun h_eq c


/-! ### The value-level Milnor row (T625 output; T626/T627 consumables) -/

omit [PlusSubring A] [HasLocLiftPowerBounded A] [PlusSubring B] [HasLocLiftPowerBounded B] [PlusSubring C] [HasLocLiftPowerBounded C] [PlusSubring D] [IsTateRing D] [HasLocLiftPowerBounded D] [DecidableEq D] in
/-- **Value-row injectivity** (prop:localized-milnor left exactness at values):
the pair of value-level pushes out of `𝒪_A(D₀)` is jointly injective. -/
theorem valueRow_injective
    (hN : NoethPack B C D e.m)
    (hIclA : IsClosed ((IA e.m D₀.s e.f : Set (P A e.m))))
    (hIclB : IsClosed ((IA e.m (S.φB D₀.s) (fun i => S.φB (e.f i)) : Set (P B e.m))))
    (hIclC : IsClosed ((IA e.m (S.φC D₀.s) (fun i => S.φC (e.f i)) : Set (P C e.m))))
    (hφB : Continuous S.φB) (hφC : Continuous S.φC)
    (hsB : (pushDatumOfHom S.φB PB D₀ hD₀).s = S.φB D₀.s)
    (hTB : ∀ t ∈ D₀.T, S.φB t ∈ (pushDatumOfHom S.φB PB D₀ hD₀).T)
    (hsC : (pushDatumOfHom S.φC PC D₀ hD₀).s = S.φC D₀.s)
    (hTC : ∀ t ∈ D₀.T, S.φC t ∈ (pushDatumOfHom S.φC PC D₀ hD₀).T)
    (x y : presheafValue D₀)
    (hB : presheafValueMapOfHom S.φB hφB D₀ (pushDatumOfHom S.φB PB D₀ hD₀) hsB hTB x =
      presheafValueMapOfHom S.φB hφB D₀ (pushDatumOfHom S.φB PB D₀ hD₀) hsB hTB y)
    (hC : presheafValueMapOfHom S.φC hφC D₀ (pushDatumOfHom S.φC PC D₀ hD₀) hsC hTC x =
      presheafValueMapOfHom S.φC hφC D₀ (pushDatumOfHom S.φC PC D₀ hD₀) hsC hTC y) :
    x = y := by
  have hinj : Function.Injective (CornerBridge.bridgeFwd D₀ e hD₀ hIclA) :=
    (CornerBridge.graphBridge D₀ e hD₀ hIclA).injective
  refine hinj ?_
  refine S.loc_pair_injective e.m D₀.s e.f hN (e.span_eq_top D₀ hD₀) ?_
  refine Prod.ext ?_ ?_
  · show S.locφB e.m D₀.s e.f (CornerBridge.bridgeFwd D₀ e hD₀ hIclA x) =
      S.locφB e.m D₀.s e.f (CornerBridge.bridgeFwd D₀ e hD₀ hIclA y)
    rw [← S.bridgeFwd_natural_B PB D₀ e hD₀ hIclA hIclB hφB hsB hTB x, hB,
      S.bridgeFwd_natural_B PB D₀ e hD₀ hIclA hIclB hφB hsB hTB y]
  · show S.locφC e.m D₀.s e.f (CornerBridge.bridgeFwd D₀ e hD₀ hIclA x) =
      S.locφC e.m D₀.s e.f (CornerBridge.bridgeFwd D₀ e hD₀ hIclA y)
    rw [← S.bridgeFwd_natural_C PC D₀ e hD₀ hIclA hIclC hφC hsC hTC x, hC,
      S.bridgeFwd_natural_C PC D₀ e hD₀ hIclA hIclC hφC hsC hTC y]

omit [PlusSubring A] [HasLocLiftPowerBounded A] [PlusSubring B] [HasLocLiftPowerBounded B] [PlusSubring C] [HasLocLiftPowerBounded C] [PlusSubring D] [HasLocLiftPowerBounded D] in
/-- **Value-row gluing** (prop:localized-milnor middle exactness at values):
a `D`-matching pair of local sections at the pushed `B`/`C`-data descends to
`𝒪_A(D₀)`. -/
theorem valueRow_glue
    (hN : NoethPack B C D e.m)
    (hIclA : IsClosed ((IA e.m D₀.s e.f : Set (P A e.m))))
    (hIclB : IsClosed ((IA e.m (S.φB D₀.s) (fun i => S.φB (e.f i)) : Set (P B e.m))))
    (hIclC : IsClosed ((IA e.m (S.φC D₀.s) (fun i => S.φC (e.f i)) : Set (P C e.m))))
    (hIclD : IsClosed ((IA e.m (S.ψC (S.φC D₀.s)) (fun i => S.ψC (S.φC (e.f i))) :
      Set (P D e.m))))
    (hφB : Continuous S.φB) (hφC : Continuous S.φC)
    (hψB : Continuous S.ψB) (hψC : Continuous S.ψC)
    (hsB : (pushDatumOfHom S.φB PB D₀ hD₀).s = S.φB D₀.s)
    (hTB : ∀ t ∈ D₀.T, S.φB t ∈ (pushDatumOfHom S.φB PB D₀ hD₀).T)
    (hsC : (pushDatumOfHom S.φC PC D₀ hD₀).s = S.φC D₀.s)
    (hTC : ∀ t ∈ D₀.T, S.φC t ∈ (pushDatumOfHom S.φC PC D₀ hD₀).T)
    (hsDB : (pushDatumOfHom (S.ψC.comp S.φC) PD D₀ hD₀).s =
      S.ψB (pushDatumOfHom S.φB PB D₀ hD₀).s)
    (hTDB : ∀ t ∈ (pushDatumOfHom S.φB PB D₀ hD₀).T,
      S.ψB t ∈ (pushDatumOfHom (S.ψC.comp S.φC) PD D₀ hD₀).T)
    (hsDC : (pushDatumOfHom (S.ψC.comp S.φC) PD D₀ hD₀).s =
      S.ψC (pushDatumOfHom S.φC PC D₀ hD₀).s)
    (hTDC : ∀ t ∈ (pushDatumOfHom S.φC PC D₀ hD₀).T,
      S.ψC t ∈ (pushDatumOfHom (S.ψC.comp S.φC) PD D₀ hD₀).T)
    (b : presheafValue (pushDatumOfHom S.φB PB D₀ hD₀))
    (c : presheafValue (pushDatumOfHom S.φC PC D₀ hD₀))
    (hbc : presheafValueMapOfHom S.ψB hψB (pushDatumOfHom S.φB PB D₀ hD₀)
        (pushDatumOfHom (S.ψC.comp S.φC) PD D₀ hD₀) hsDB hTDB b =
      presheafValueMapOfHom S.ψC hψC (pushDatumOfHom S.φC PC D₀ hD₀)
        (pushDatumOfHom (S.ψC.comp S.φC) PD D₀ hD₀) hsDC hTDC c) :
    ∃ x : presheafValue D₀,
      presheafValueMapOfHom S.φB hφB D₀ (pushDatumOfHom S.φB PB D₀ hD₀) hsB hTB x = b ∧
      presheafValueMapOfHom S.φC hφC D₀ (pushDatumOfHom S.φC PC D₀ hD₀) hsC hTC x = c := by
  have hloc : S.locψB e.m D₀.s e.f
      (CornerBridge.bridgeFwd (pushDatumOfHom S.φB PB D₀ hD₀)
        (S.pushEnumB PB D₀ e hD₀) (pushDatumOfHom_isRational S.φB PB hD₀) hIclB b) =
      S.locψC e.m D₀.s e.f
      (CornerBridge.bridgeFwd (pushDatumOfHom S.φC PC D₀ hD₀)
        (S.pushEnumC PC D₀ e hD₀) (pushDatumOfHom_isRational S.φC PC hD₀) hIclC c) := by
    rw [← S.bridgeFwd_natural_legB PB PD D₀ e hD₀ hIclB hIclD hψB hsDB hTDB b,
      ← S.bridgeFwd_natural_legC PC PD D₀ e hD₀ hIclC hIclD hψC hsDC hTDC c, hbc]
  obtain ⟨w, ⟨hwB, hwC⟩, -⟩ := S.loc_row_exact e.m D₀.s e.f hN
    (e.span_eq_top D₀ hD₀) _ _ hloc
  refine ⟨(CornerBridge.graphBridge D₀ e hD₀ hIclA).symm w, ?_, ?_⟩
  · have hinjB : Function.Injective
        (CornerBridge.bridgeFwd (pushDatumOfHom S.φB PB D₀ hD₀)
          (S.pushEnumB PB D₀ e hD₀) (pushDatumOfHom_isRational S.φB PB hD₀) hIclB) :=
      (CornerBridge.graphBridge (pushDatumOfHom S.φB PB D₀ hD₀)
        (S.pushEnumB PB D₀ e hD₀) (pushDatumOfHom_isRational S.φB PB hD₀)
        hIclB).injective
    refine hinjB ?_
    rw [S.bridgeFwd_natural_B PB D₀ e hD₀ hIclA hIclB hφB hsB hTB,
      show CornerBridge.bridgeFwd D₀ e hD₀ hIclA
          ((CornerBridge.graphBridge D₀ e hD₀ hIclA).symm w) = w from
        (CornerBridge.graphBridge D₀ e hD₀ hIclA).apply_symm_apply w]
    exact hwB
  · have hinjC : Function.Injective
        (CornerBridge.bridgeFwd (pushDatumOfHom S.φC PC D₀ hD₀)
          (S.pushEnumC PC D₀ e hD₀) (pushDatumOfHom_isRational S.φC PC hD₀) hIclC) :=
      (CornerBridge.graphBridge (pushDatumOfHom S.φC PC D₀ hD₀)
        (S.pushEnumC PC D₀ e hD₀) (pushDatumOfHom_isRational S.φC PC hD₀)
        hIclC).injective
    refine hinjC ?_
    rw [S.bridgeFwd_natural_C PC D₀ e hD₀ hIclA hIclC hφC hsC hTC,
      show CornerBridge.bridgeFwd D₀ e hD₀ hIclA
          ((CornerBridge.graphBridge D₀ e hD₀ hIclA).symm w) = w from
        (CornerBridge.graphBridge D₀ e hD₀ hIclA).apply_symm_apply w]
    exact hwC

omit [PlusSubring A] [HasLocLiftPowerBounded A] [PlusSubring B] [HasLocLiftPowerBounded B] [PlusSubring C] [HasLocLiftPowerBounded C] [PlusSubring D] [IsTateRing D] [HasLocLiftPowerBounded D] [DecidableEq D] in
/-- **Value-row embedding** (prop:localized-milnor topological strictness at
values): the value-level pair map is a topological embedding. -/
theorem valueRow_embedding
    (hN : NoethPack B C D e.m)
    (hIclA : IsClosed ((IA e.m D₀.s e.f : Set (P A e.m))))
    (hIclB : IsClosed ((IA e.m (S.φB D₀.s) (fun i => S.φB (e.f i)) : Set (P B e.m))))
    (hIclC : IsClosed ((IA e.m (S.φC D₀.s) (fun i => S.φC (e.f i)) : Set (P C e.m))))
    (hφB : Continuous S.φB) (hφC : Continuous S.φC)
    (hsB : (pushDatumOfHom S.φB PB D₀ hD₀).s = S.φB D₀.s)
    (hTB : ∀ t ∈ D₀.T, S.φB t ∈ (pushDatumOfHom S.φB PB D₀ hD₀).T)
    (hsC : (pushDatumOfHom S.φC PC D₀ hD₀).s = S.φC D₀.s)
    (hTC : ∀ t ∈ D₀.T, S.φC t ∈ (pushDatumOfHom S.φC PC D₀ hD₀).T) :
    Topology.IsEmbedding (fun x : presheafValue D₀ =>
      (presheafValueMapOfHom S.φB hφB D₀ (pushDatumOfHom S.φB PB D₀ hD₀) hsB hTB x,
       presheafValueMapOfHom S.φC hφC D₀ (pushDatumOfHom S.φC PC D₀ hD₀) hsC hTC x)) := by
  have hpair := S.loc_pair_isEmbedding e.m D₀.s e.f hN (e.span_eq_top D₀ hD₀)
  have hbr : Topology.IsEmbedding ⇑(CornerBridge.graphBridge D₀ e hD₀ hIclA) :=
    (Homeomorph.mk (CornerBridge.graphBridge D₀ e hD₀ hIclA).toEquiv
      (CornerBridge.graphBridge_continuous D₀ e hD₀ hIclA)
      (CornerBridge.graphBridge_symm_continuous D₀ e hD₀ hIclA)).isEmbedding
  have hcomp : (fun p : presheafValue (pushDatumOfHom S.φB PB D₀ hD₀) ×
        presheafValue (pushDatumOfHom S.φC PC D₀ hD₀) =>
        (CornerBridge.bridgeFwd (pushDatumOfHom S.φB PB D₀ hD₀)
          (S.pushEnumB PB D₀ e hD₀) (pushDatumOfHom_isRational S.φB PB hD₀)
          hIclB p.1,
         CornerBridge.bridgeFwd (pushDatumOfHom S.φC PC D₀ hD₀)
          (S.pushEnumC PC D₀ e hD₀) (pushDatumOfHom_isRational S.φC PC hD₀)
          hIclC p.2)) ∘
      (fun x : presheafValue D₀ =>
        (presheafValueMapOfHom S.φB hφB D₀ (pushDatumOfHom S.φB PB D₀ hD₀) hsB hTB x,
         presheafValueMapOfHom S.φC hφC D₀ (pushDatumOfHom S.φC PC D₀ hD₀) hsC hTC x)) =
      (fun w : locA e.m D₀.s e.f =>
        (S.locφB e.m D₀.s e.f w, S.locφC e.m D₀.s e.f w)) ∘
        ⇑(CornerBridge.graphBridge D₀ e hD₀ hIclA) := by
    funext x
    exact Prod.ext (S.bridgeFwd_natural_B PB D₀ e hD₀ hIclA hIclB hφB hsB hTB x)
      (S.bridgeFwd_natural_C PC D₀ e hD₀ hIclA hIclC hφC hsC hTC x)
  refine Topology.IsEmbedding.of_comp ?_ ?_ (by rw [hcomp]; exact hpair.comp hbr)
  · exact (presheafValueMapOfHom_continuous S.φB hφB D₀ _ hsB hTB).prodMk
      (presheafValueMapOfHom_continuous S.φC hφC D₀ _ hsC hTC)
  · exact ((CornerBridge.bridgeFwd_continuous _ _ _ hIclB).comp continuous_fst).prodMk
      ((CornerBridge.bridgeFwd_continuous _ _ _ hIclC).comp continuous_snd)

end Square

end Pinch

end FiniteJet
