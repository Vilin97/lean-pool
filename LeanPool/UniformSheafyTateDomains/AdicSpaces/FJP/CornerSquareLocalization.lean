/-
Copyright (c) 2026 Christopher Birkbeck, Alex Torzewski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Birkbeck, Alex Torzewski
-/

/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanPool.UniformSheafyTateDomains.AdicSpaces.FJP.FiniteJetStrictLocalization

/-!
# Strict localization over an abstract pinched corner square (T625, campaign B)

[FJP] §4 parametrized: the strict-localization chain (Lemmas 4.1, 4.3, 4.4, Prop 4.5)
over an **abstract strict Milnor pinch** of four normed ultrametric complete corners

`A = B ×_D C` : `φB : A →+* B`, `φC : A →+* C`, `ψB : B →+* D`, `ψC : C →+* D`

carrying the [FJP] §2 package: the norm identities (`φC`, `ψB` isometric; `φB`, `ψC`
1-Lipschitz; pullback max-norm identity), the exact row with uniqueness
(`milnorRow`), the additive κ=1 coefficient section of `ψC`, per-corner scaling
pseudouniformizers, and noetherianity of the corner and `P`-ring unit balls.

The paper states §4 for the finite-jet square but the proofs use only this package
([FJP] Lemma 4.1: "restricted Tate extension carries a strict Milnor square to a
strict Milnor square"); `FiniteJetStrictLocalization.lean` is its transcription at
the Jet corners. This parametrized version exists so the SAME chain instantiates at
the `⟨V⟩`-extended corners `P (Jet• F) n` (whose package facts are the `ext•` lemmas
of `FiniteJetStrictLocalization` at arity `n`) — the reviewer §5.1 strengthening.

The Koszul layer (`exists_d1_lift`, `exists_d2_lift`, `syzygy_graph_restricted`) is
already generic over a normed corner `E` and is consumed as-is.
-/

@[expose] public section

noncomputable section

open Filter Topology

namespace FiniteJet

open RestrictedLaurent GraphKoszul

variable {A B C D : Type*}
  [NormedCommRing A] [IsUltrametricDist A]
  [NormedCommRing B] [IsUltrametricDist B]
  [NormedCommRing C] [IsUltrametricDist C]
  [NormedCommRing D] [IsUltrametricDist D]

/-- **The abstract strict Milnor pinch** ([FJP] SS2's package for the square
`A = B x_D C`): homs, norm identities, the exact row with uniqueness, the kappa=1
coefficient section of `psiC`, per-corner scaling pseudouniformizers, and the
noetherianity inputs consumed by the graph-Koszul layer. -/
structure Pinch (A B C D : Type*)
    [NormedCommRing A] [IsUltrametricDist A] [NormedCommRing B] [IsUltrametricDist B]
    [NormedCommRing C] [IsUltrametricDist C] [NormedCommRing D] [IsUltrametricDist D] :
    Type _ where
  φB : A →+* B
  φC : A →+* C
  ψB : B →+* D
  ψC : C →+* D
  norm_φB_le : ∀ a, ‖φB a‖ ≤ ‖a‖
  norm_φC : ∀ a, ‖φC a‖ = ‖a‖
  norm_ψB : ∀ b, ‖ψB b‖ = ‖b‖
  norm_ψC_le : ∀ c, ‖ψC c‖ ≤ ‖c‖
  square : ∀ a, ψB (φB a) = ψC (φC a)
  row : ∀ (b : B) (c : C), ψB b = ψC c → ∃! a : A, φB a = b ∧ φC a = c
  max_norm : ∀ a : A, max ‖φB a‖ ‖φC a‖ = ‖a‖
  secD : D → C
  ψC_secD : ∀ x, ψC (secD x) = x
  norm_secD : ∀ x, ‖secD x‖ = ‖x‖
  tB : B
  tB_isUnit : IsUnit tB
  norm_tB_lt_one : ‖tB‖ < 1
  norm_tB_pos : 0 < ‖tB‖
  norm_tB_mul : ∀ x, ‖tB * x‖ = ‖tB‖ * ‖x‖
  tC : C
  tC_isUnit : IsUnit tC
  norm_tC_lt_one : ‖tC‖ < 1
  norm_tC_pos : 0 < ‖tC‖
  norm_tC_mul : ∀ x, ‖tC * x‖ = ‖tC‖ * ‖x‖
  tD : D
  tD_isUnit : IsUnit tD
  norm_tD_lt_one : ‖tD‖ < 1
  norm_tD_pos : 0 < ‖tD‖
  norm_tD_mul : ∀ x, ‖tD * x‖ = ‖tD‖ * ‖x‖

/-- The noetherianity inputs consumed by the graph-Koszul layer at arity `m`
(discharged per instance: at the Jet corners from the concrete tower lemmas, at the
`⟨V⟩`-extended corners through the restricted Fubini). -/
structure NoethPack (B C D : Type*)
    [NormedCommRing B] [IsUltrametricDist B] [NormOneClass B] [CompleteSpace B]
    [NormedCommRing C] [IsUltrametricDist C] [NormOneClass C] [CompleteSpace C]
    [NormedCommRing D] [IsUltrametricDist D] [NormOneClass D] [CompleteSpace D]
    (m : ℕ) : Prop where
  hPB : IsNoetherianRing (P B m)
  hPC : IsNoetherianRing (P C m)
  hPD : IsNoetherianRing (P D m)
  hPBball : IsNoetherianRing (unitBall (P B m))
  hPCball : IsNoetherianRing (unitBall (P C m))
  hPDball : IsNoetherianRing (unitBall (P D m))
  hDball : IsNoetherianRing (unitBall D)

namespace Pinch

variable (S : Pinch A B C D) (m : ℕ)
/-- Coefficientwise `φB : P_A → P_B`. -/
noncomputable def extB : P A m →+* P B m :=
  mapRestricted S.φB S.norm_φB_le _

/-- Coefficientwise `φC : P_A → P_C`. -/
noncomputable def extC : P A m →+* P C m :=
  mapRestricted S.φC (fun a => le_of_eq (S.norm_φC a)) _

/-- Coefficientwise `ψB : P_B → P_D`. -/
noncomputable def extDB : P B m →+* P D m :=
  mapRestricted S.ψB (fun b => le_of_eq (S.norm_ψB b)) _

/-- Coefficientwise `ψC : P_C → P_D`. -/
noncomputable def extDC : P C m →+* P D m :=
  mapRestricted S.ψC S.norm_ψC_le _


theorem ext_square_commutes (p : P A m) :
    S.extDB m (S.extB m p) = S.extDC m (S.extC m p) := by
  refine Subtype.ext ?_
  show MvPowerSeries.map S.ψB (MvPowerSeries.map S.φB p.1) =
    MvPowerSeries.map S.ψC (MvPowerSeries.map S.φC p.1)
  refine MvPowerSeries.ext fun s => ?_
  rw [MvPowerSeries.coeff_map, MvPowerSeries.coeff_map, MvPowerSeries.coeff_map,
    MvPowerSeries.coeff_map]
  exact S.square _



/-- Coefficientwise sectioning: the extended `ψC` is strictly surjective with
constant 1 ([FJP] Lemma 4.1's κ=1 section, abstractly). -/
theorem extDC_strict_surjective (d : P D m) :
    ∃ c : P C m, S.extDC m c = d ∧ ‖c‖ = ‖d‖ := by
  classical
  have hmem : MvPowerSeries.IsRestrictedGauss (fun _ : Fin m => (1 : ℝ))
      (fun s => S.secD (MvPowerSeries.coeff s d.1)) := by
    have hd : MvPowerSeries.IsRestrictedGauss (fun _ : Fin m => (1 : ℝ)) d.1 := d.2
    unfold MvPowerSeries.IsRestrictedGauss at hd ⊢
    refine hd.congr fun s => ?_
    show ‖MvPowerSeries.coeff s d.1‖ * _ =
      ‖MvPowerSeries.coeff s (fun s => S.secD (MvPowerSeries.coeff s d.1))‖ * _
    rw [show MvPowerSeries.coeff s (fun s => S.secD (MvPowerSeries.coeff s d.1)) =
      S.secD (MvPowerSeries.coeff s d.1) from rfl, S.norm_secD]
  refine ⟨⟨fun s => S.secD (MvPowerSeries.coeff s d.1), hmem⟩, ?_, ?_⟩
  · refine Subtype.ext ?_
    show MvPowerSeries.map S.ψC (fun s => S.secD (MvPowerSeries.coeff s d.1)) = d.1
    refine MvPowerSeries.ext fun s => ?_
    rw [MvPowerSeries.coeff_map]
    show S.ψC (S.secD (MvPowerSeries.coeff s d.1)) = MvPowerSeries.coeff s d.1
    rw [S.ψC_secD]
  · rw [MvRestricted.norm_eq, MvRestricted.norm_eq, MvPowerSeries.gaussNorm,
      MvPowerSeries.gaussNorm]
    refine iSup_congr fun s => ?_
    show ‖MvPowerSeries.coeff s (fun s => S.secD (MvPowerSeries.coeff s d.1))‖ * _ = _
    rw [show MvPowerSeries.coeff s (fun s => S.secD (MvPowerSeries.coeff s d.1)) =
      S.secD (MvPowerSeries.coeff s d.1) from rfl, S.norm_secD]




/-- The extended square is cartesian ([FJP] Lemma 4.1, abstractly): a compatible
pair comes from a unique element of `P_A`, coefficientwise via the base row and the
pullback max-norm identity. -/
theorem ext_milnorRow_exact (b : P B m) (c : P C m)
    (h : S.extDB m b = S.extDC m c) :
    ∃! p : P A m, S.extB m p = b ∧ S.extC m p = c := by
  classical
  have hcoeff : ∀ s : Fin m →₀ ℕ, S.ψB (MvPowerSeries.coeff s b.1) =
      S.ψC (MvPowerSeries.coeff s c.1) := fun s => by
    have h0 := congrArg (fun x : P D m => MvPowerSeries.coeff s x.1) h
    have h1 : MvPowerSeries.coeff s (MvPowerSeries.map S.ψB b.1) =
        MvPowerSeries.coeff s (MvPowerSeries.map S.ψC c.1) := h0
    rwa [MvPowerSeries.coeff_map, MvPowerSeries.coeff_map] at h1
  choose a ha using fun s => (S.row _ _ (hcoeff s)).exists
  have hanorm : ∀ s, ‖a s‖ =
      max ‖MvPowerSeries.coeff s b.1‖ ‖MvPowerSeries.coeff s c.1‖ := fun s => by
    rw [← S.max_norm (a s), (ha s).1, (ha s).2]
  have hres : MvPowerSeries.IsRestrictedGauss (fun _ : Fin m => (1 : ℝ))
      (fun s => a s) := by
    have hb : MvPowerSeries.IsRestrictedGauss (fun _ : Fin m => (1 : ℝ)) b.1 := b.2
    have hc : MvPowerSeries.IsRestrictedGauss (fun _ : Fin m => (1 : ℝ)) c.1 := c.2
    unfold MvPowerSeries.IsRestrictedGauss at hb hc ⊢
    have hmaxlim := hb.max hc
    rw [max_self (0 : ℝ)] at hmaxlim
    refine hmaxlim.congr fun s => ?_
    show max (‖MvPowerSeries.coeff s b.1‖ * _) (‖MvPowerSeries.coeff s c.1‖ * _) = _
    simp only [finsupp_prod_one, mul_one]
    rw [show ‖MvPowerSeries.coeff s (fun s => a s)‖ = ‖a s‖ from rfl, hanorm s]
  refine ⟨⟨fun s => a s, hres⟩, ⟨?_, ?_⟩, ?_⟩
  · refine Subtype.ext ?_
    show MvPowerSeries.map S.φB (fun s => a s) = b.1
    refine MvPowerSeries.ext fun s => ?_
    rw [MvPowerSeries.coeff_map]
    exact (ha s).1
  · refine Subtype.ext ?_
    show MvPowerSeries.map S.φC (fun s => a s) = c.1
    refine MvPowerSeries.ext fun s => ?_
    rw [MvPowerSeries.coeff_map]
    exact (ha s).2
  · rintro q ⟨hqb, hqc⟩
    refine Subtype.ext (MvPowerSeries.ext fun s => ?_)
    have h1 : S.φB (MvPowerSeries.coeff s q.1) = MvPowerSeries.coeff s b.1 := by
      have := congrArg (fun x : P B m => MvPowerSeries.coeff s x.1) hqb
      show S.φB (MvPowerSeries.coeff s q.1) = MvPowerSeries.coeff s b.1
      have h2 : MvPowerSeries.coeff s (MvPowerSeries.map S.φB q.1) =
          MvPowerSeries.coeff s b.1 := this
      rwa [MvPowerSeries.coeff_map] at h2
    have h2 : S.φC (MvPowerSeries.coeff s q.1) = MvPowerSeries.coeff s c.1 := by
      have := congrArg (fun x : P C m => MvPowerSeries.coeff s x.1) hqc
      have h3 : MvPowerSeries.coeff s (MvPowerSeries.map S.φC q.1) =
          MvPowerSeries.coeff s c.1 := this
      rwa [MvPowerSeries.coeff_map] at h3
    exact (S.row _ _ (hcoeff s)).unique ⟨h1, h2⟩ ⟨(ha s).1, (ha s).2⟩

/-- Pullback-norm identity for the extended square (constants 1). -/
theorem ext_max_norm_eq (p : P A m) :
    max ‖S.extB m p‖ ‖S.extC m p‖ = ‖p‖ := by
  have h1 : ‖S.extC m p‖ = ‖p‖ := by
    rw [MvRestricted.norm_eq, MvRestricted.norm_eq]
    show MvPowerSeries.gaussNorm _ _ (MvPowerSeries.map S.φC p.1) = _
    rw [MvPowerSeries.gaussNorm, MvPowerSeries.gaussNorm]
    refine iSup_congr fun s => ?_
    rw [MvPowerSeries.coeff_map, S.norm_φC]
  have h2 : ‖S.extB m p‖ ≤ ‖p‖ := norm_mapRestricted_le _ _ _ p
  rw [h1]
  exact max_eq_right h2

/-- `P_A → P_B ⊕ P_C` is injective (left exactness of the extended row),
from the base row's uniqueness. -/
theorem ext_pair_injective :
    Function.Injective (fun p : P A m =>
      (S.extB m p, S.extC m p)) := by
  intro p q h
  have hB := congrArg Prod.fst h
  have hC := congrArg Prod.snd h
  refine Subtype.ext (MvPowerSeries.ext fun s => ?_)
  have h1 : S.φB (MvPowerSeries.coeff s p.1) = S.φB (MvPowerSeries.coeff s q.1) := by
    have := congrArg (fun x : P B m => MvPowerSeries.coeff s x.1) hB
    have h2 : MvPowerSeries.coeff s (MvPowerSeries.map S.φB p.1) =
        MvPowerSeries.coeff s (MvPowerSeries.map S.φB q.1) := this
    rwa [MvPowerSeries.coeff_map, MvPowerSeries.coeff_map] at h2
  have h2 : S.φC (MvPowerSeries.coeff s p.1) = S.φC (MvPowerSeries.coeff s q.1) := by
    have := congrArg (fun x : P C m => MvPowerSeries.coeff s x.1) hC
    have h3 : MvPowerSeries.coeff s (MvPowerSeries.map S.φC p.1) =
        MvPowerSeries.coeff s (MvPowerSeries.map S.φC q.1) := this
    rwa [MvPowerSeries.coeff_map, MvPowerSeries.coeff_map] at h3
  have hsqp : S.ψB (S.φB (MvPowerSeries.coeff s p.1)) =
      S.ψC (S.φC (MvPowerSeries.coeff s p.1)) := S.square _
  exact (S.row (S.φB (MvPowerSeries.coeff s p.1)) (S.φC (MvPowerSeries.coeff s p.1))
    hsqp).unique ⟨rfl, rfl⟩ ⟨h1.symm, h2.symm⟩



/-! ### The graph data ([FJP] (4.6)) -/

section Graph

variable [NormOneClass A] [CompleteSpace A] [NormOneClass B] [CompleteSpace B]
  [NormOneClass C] [CompleteSpace C] [NormOneClass D] [CompleteSpace D]

variable (g : A) (f : Fin m → A)

/-- The graph relations `r_i = gT_i − f_i` in `P_A` ([FJP] (4.6)). -/
noncomputable def rA : Fin m → P A m := fun i =>
  polyToP (MvPolynomial.C g * MvPolynomial.X i - MvPolynomial.C (f i))

/-- The pushed relations at the vertices, in graph-polynomial form (so the
single-corner bridge stack instantiates at each vertex definitionally). -/
noncomputable def rB : Fin m → P B m := fun i =>
  polyToP (MvPolynomial.C (S.φB g) * MvPolynomial.X i - MvPolynomial.C (S.φB (f i)))
noncomputable def rC : Fin m → P C m := fun i =>
  polyToP (MvPolynomial.C (S.φC g) * MvPolynomial.X i - MvPolynomial.C (S.φC (f i)))
noncomputable def rD : Fin m → P D m := fun i =>
  polyToP (MvPolynomial.C (S.ψC (S.φC g)) * MvPolynomial.X i -
    MvPolynomial.C (S.ψC (S.φC (f i))))

/-- Graph ideals `I_E = im(d₁) = (r₁, …, r_m)` ([FJP] (4.6)). -/
noncomputable def IA : Ideal (P A m) := Ideal.span (Set.range (rA m g f))
noncomputable def IB : Ideal (P B m) := Ideal.span (Set.range (S.rB m g f))
noncomputable def IC : Ideal (P C m) := Ideal.span (Set.range (S.rC m g f))
noncomputable def ID : Ideal (P D m) := Ideal.span (Set.range (S.rD m g f))

omit [NormOneClass A] [CompleteSpace A] [NormOneClass B] [CompleteSpace B] [NormOneClass C] [CompleteSpace C] [NormOneClass D] [CompleteSpace D] in
/-- The pushed data generate the unit ideal at each vertex ([FJP] §4 after (4.6)). -/
theorem span_pushed_B (hspan : Ideal.span ({g} ∪ Set.range f) = ⊤) :
    Ideal.span ({S.φB g} ∪ Set.range (fun i => S.φB (f i))) = ⊤ := by
  have h := congrArg (Ideal.map S.φB) hspan
  rw [Ideal.map_span, Ideal.map_top] at h
  rw [← h]
  congr 1
  rw [Set.image_union, Set.image_singleton, ← Set.range_comp]
  rfl

omit [NormOneClass A] [CompleteSpace A] [NormOneClass B] [CompleteSpace B] [NormOneClass C] [CompleteSpace C] [NormOneClass D] [CompleteSpace D] in
theorem span_pushed_C (hspan : Ideal.span ({g} ∪ Set.range f) = ⊤) :
    Ideal.span ({S.φC g} ∪ Set.range (fun i => S.φC (f i))) = ⊤ := by
  have h := congrArg (Ideal.map S.φC) hspan
  rw [Ideal.map_span, Ideal.map_top] at h
  rw [← h]
  congr 1
  rw [Set.image_union, Set.image_singleton, ← Set.range_comp]
  rfl

omit [NormOneClass A] [CompleteSpace A] [NormOneClass B] [CompleteSpace B] [NormOneClass C] [CompleteSpace C] [NormOneClass D] [CompleteSpace D] in
theorem span_pushed_D (hspan : Ideal.span ({g} ∪ Set.range f) = ⊤) :
    Ideal.span ({S.ψC (S.φC g)} ∪
      Set.range (fun i => S.ψC (S.φC (f i)))) = ⊤ := by
  have h := congrArg (Ideal.map (S.ψC.comp S.φC)) hspan
  rw [Ideal.map_span, Ideal.map_top] at h
  rw [← h]
  congr 1
  rw [Set.image_union, Set.image_singleton, ← Set.range_comp]
  rfl

omit [NormOneClass C] [CompleteSpace C] [NormOneClass D] [CompleteSpace D] in
/-- The `B`-relations are the pushes of the base relations. -/
theorem extB_rA (i : Fin m) : S.extB m (rA m g f i) = S.rB m g f i := by
  show mapRestricted S.φB S.norm_φB_le _ (polyToP _) = _
  rw [StrictLoc.mapRestricted_polyToP]
  congr 1
  rw [map_sub, map_mul, MvPolynomial.map_C, MvPolynomial.map_X, MvPolynomial.map_C]

omit [NormOneClass B] [CompleteSpace B] [NormOneClass D] [CompleteSpace D] in
/-- The `C`-relations are the pushes of the base relations. -/
theorem extC_rA (i : Fin m) : S.extC m (rA m g f i) = S.rC m g f i := by
  show mapRestricted S.φC (fun a => le_of_eq (S.norm_φC a)) _ (polyToP _) = _
  rw [StrictLoc.mapRestricted_polyToP]
  congr 1
  rw [map_sub, map_mul, MvPolynomial.map_C, MvPolynomial.map_X, MvPolynomial.map_C]

omit [NormOneClass A] [CompleteSpace A] [NormOneClass B] [CompleteSpace B] [NormOneClass C] [CompleteSpace C] [NormOneClass D] [CompleteSpace D] in
/-- The `D`-relations in graph-polynomial form (definitional; the
`exists_d2_lift` interface). -/
theorem rD_eq (i : Fin m) : S.rD m g f i =
    polyToP (MvPolynomial.C (S.ψC (S.φC g)) * MvPolynomial.X i -
      MvPolynomial.C (S.ψC (S.φC (f i)))) := rfl

omit [NormOneClass A] [CompleteSpace A] [NormOneClass B] [CompleteSpace B] in
/-- The `D`-relations are the `ψC`-pushes of the `C`-relations. -/
theorem extDC_rC (i : Fin m) : S.extDC m (S.rC m g f i) = S.rD m g f i := by
  show mapRestricted S.ψC S.norm_ψC_le _ (polyToP _) = _
  rw [StrictLoc.mapRestricted_polyToP]
  congr 1
  rw [map_sub, map_mul, MvPolynomial.map_C, MvPolynomial.map_X, MvPolynomial.map_C]

/-- The pushed generators are compatible across the square. -/
theorem extDB_rB (i : Fin m) : S.extDB m (S.rB m g f i) = S.rD m g f i := by
  rw [← S.extB_rA m g f i, ← S.extDC_rC m g f i, ← S.extC_rA m g f i]
  exact S.ext_square_commutes m (rA m g f i)

/-! ### Lemma 4.3 — controlled graph-ideal pullback ([FJP] (4.11)–(4.16)) -/

omit [NormOneClass A] [CompleteSpace A] in
/-- Right strict surjectivity of the ideal row ([FJP] (4.11)). -/
theorem ideal_row_surjective (hN : NoethPack B C D m)
    (_hspan : Ideal.span ({g} ∪ Set.range f) = ⊤) :
    ∃ Cs : ℝ, 1 ≤ Cs ∧ ∀ y ∈ S.ID m g f,
      ∃ xc ∈ S.IC m g f, S.extDC m xc = y ∧ ‖xc‖ ≤ Cs * ‖y‖ := by
  classical
  have := hN.hPD
  obtain ⟨h, hh1, hlift⟩ := exists_d1_lift (E := D) S.tD S.tD_isUnit
    S.norm_tD_lt_one S.norm_tD_pos S.norm_tD_mul hN.hPDball (S.rD m g f)
  set Cr : ℝ := 1 + ∑ i, ‖S.rC m g f i‖ with hCr
  have hCr1 : 1 ≤ Cr := le_add_of_nonneg_right (Finset.sum_nonneg fun i _ => norm_nonneg _)
  refine ⟨h * Cr, ?_, fun y hy => ?_⟩
  · calc (1 : ℝ) ≤ h := hh1
      _ = h * 1 := (mul_one h).symm
      _ ≤ h * Cr := mul_le_mul_of_nonneg_left hCr1 (zero_le_one.trans hh1)
  · obtain ⟨u, hu, hun⟩ := hlift y hy
    have hsec : ∀ i, ∃ c : P C m, S.extDC m c = u i ∧ ‖c‖ = ‖u i‖ := fun i =>
      S.extDC_strict_surjective m (u i)
    choose cc hcc hccn using hsec
    refine ⟨d1 (S.rC m g f) cc, ?_, ?_, ?_⟩
    · show d1 (S.rC m g f) cc ∈ Ideal.span (Set.range (S.rC m g f))
      unfold d1
      exact Ideal.sum_mem _ fun i _ => Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨i, rfl⟩)
    · rw [show S.extDC m (d1 (S.rC m g f) cc) =
        d1 (fun i => S.extDC m (S.rC m g f i)) (fun i => S.extDC m (cc i)) from
          d1_map (S.extDC m) _ cc,
        show (fun i => S.extDC m (S.rC m g f i)) = S.rD m g f from
          funext fun i => S.extDC_rC m g f i,
        show (fun i => S.extDC m (cc i)) = u from funext hcc]
      exact hu
    · have hterm : ∀ i : Fin m, ‖cc i * S.rC m g f i‖ ≤ ‖u‖ * Cr := fun i => by
        calc ‖cc i * S.rC m g f i‖ ≤ ‖cc i‖ * ‖S.rC m g f i‖ := norm_mul_le _ _
          _ = ‖u i‖ * ‖S.rC m g f i‖ := by rw [hccn i]
          _ ≤ ‖u‖ * Cr := by
              refine mul_le_mul (norm_le_pi_norm u i) ?_ (norm_nonneg _) (norm_nonneg u)
              rw [hCr]
              refine le_add_of_nonneg_of_le zero_le_one ?_
              exact Finset.single_le_sum (fun j _ => norm_nonneg _) (Finset.mem_univ i)
      have hpartial : ∀ s : Finset (Fin m),
          ‖∑ i ∈ s, cc i * S.rC m g f i‖ ≤ ‖u‖ * Cr := by
        intro s
        induction s using Finset.induction_on with
        | empty =>
          rw [Finset.sum_empty, norm_zero]
          exact mul_nonneg (norm_nonneg u) (zero_le_one.trans hCr1)
        | insert a s ha ih =>
          rw [Finset.sum_insert ha]
          exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (hterm a) ih)
      show ‖d1 (S.rC m g f) cc‖ ≤ h * Cr * ‖y‖
      unfold d1
      refine (hpartial Finset.univ).trans ?_
      calc ‖u‖ * Cr ≤ h * ‖y‖ * Cr :=
            mul_le_mul_of_nonneg_right hun (zero_le_one.trans hCr1)
        _ = h * Cr * ‖y‖ := by ring

/-- The controlled pullback ([FJP] (4.12)–(4.16)): a matching pair of graph-ideal
elements comes from an element of `I_A` with a uniformly bounded representative.
This is where the `d₂`-syzygy correction (`exists_d2_lift` at the `D`-vertex)
enters. -/
theorem ideal_pullback_controlled (hN : NoethPack B C D m)
    (hspan : Ideal.span ({g} ∪ Set.range f) = ⊤) :
    ∃ Cs : ℝ, 1 ≤ Cs ∧
      ∀ xb ∈ S.IB m g f, ∀ xc ∈ S.IC m g f,
        S.extDB m xb = S.extDC m xc →
        ∃ xa ∈ IA m g f,
          S.extB m xa = xb ∧ S.extC m xa = xc ∧ ‖xa‖ ≤ Cs * max ‖xb‖ ‖xc‖ := by
  classical
  have := hN.hPB
  have := hN.hPC
  have := hN.hPD
  obtain ⟨hB, hB1, hliftB⟩ := exists_d1_lift (E := B) S.tB S.tB_isUnit
    S.norm_tB_lt_one S.norm_tB_pos S.norm_tB_mul hN.hPBball (S.rB m g f)
  obtain ⟨hC, hC1, hliftC⟩ := exists_d1_lift (E := C) S.tC S.tC_isUnit
    S.norm_tC_lt_one S.norm_tC_pos S.norm_tC_mul hN.hPCball (S.rC m g f)
  obtain ⟨z, hz1, hliftD⟩ := exists_d2_lift (E := D)
    hN.hDball S.tD S.tD_isUnit
    S.norm_tD_lt_one S.norm_tD_pos
    S.norm_tD_mul (S.ψC (S.φC g)) (fun i => S.ψC (S.φC (f i)))
    (S.span_pushed_D m g f hspan) (S.rD m g f) (S.rD_eq m g f)
  set CrC : ℝ := 1 + ∑ i, ‖S.rC m g f i‖ with hCrC
  set CrA : ℝ := 1 + ∑ i, ‖rA m g f i‖ with hCrA
  have hCrC1 : 1 ≤ CrC := le_add_of_nonneg_right (Finset.sum_nonneg fun i _ => norm_nonneg _)
  have hCrA1 : 1 ≤ CrA := le_add_of_nonneg_right (Finset.sum_nonneg fun i _ => norm_nonneg _)
  have hB0 : 0 ≤ hB := zero_le_one.trans hB1
  have hC0 : 0 ≤ hC := zero_le_one.trans hC1
  have hz0 : 0 ≤ z := zero_le_one.trans hz1
  set Bs : ℝ := hB + hC + z * (hB + hC) * CrC with hBs
  have hBs0 : 0 ≤ Bs := add_nonneg (add_nonneg hB0 hC0)
    (mul_nonneg (mul_nonneg hz0 (add_nonneg hB0 hC0)) (zero_le_one.trans hCrC1))
  have hprod0 : 0 ≤ z * (hB + hC) * CrC :=
    mul_nonneg (mul_nonneg hz0 (add_nonneg hB0 hC0)) (zero_le_one.trans hCrC1)
  have hBsB : hB ≤ Bs := by
    rw [hBs]
    linarith
  have hBsC : hC ≤ Bs := by
    rw [hBs]
    linarith
  have hBszC : z * (hB + hC) * CrC ≤ Bs := by
    rw [hBs]
    linarith
  refine ⟨1 + Bs * CrA, le_add_of_nonneg_right (mul_nonneg hBs0
    (zero_le_one.trans hCrA1)), fun xb hxb xc hxc hcompat => ?_⟩
  set M : ℝ := max ‖xb‖ ‖xc‖ with hM
  have hM0 : (0 : ℝ) ≤ M := le_max_of_le_left (norm_nonneg xb)
  obtain ⟨u, hu, hun⟩ := hliftB xb hxb
  obtain ⟨v, hv, hvn⟩ := hliftC xc hxc
  have hun' : ‖u‖ ≤ hB * M :=
    hun.trans (mul_le_mul_of_nonneg_left (le_max_left _ _) hB0)
  have hvn' : ‖v‖ ≤ hC * M :=
    hvn.trans (mul_le_mul_of_nonneg_left (le_max_right _ _) hC0)
  set w : Fin m → P D m := fun i => S.extDB m (u i) - S.extDC m (v i) with hw
  have hd1sub : ∀ {T : Type _} [inst : CommRing T] (r a b : Fin m → T),
      d1 r (fun i => a i - b i) = d1 r a - d1 r b := by
    intro T _ r a b
    unfold d1
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  have hwd1 : d1 (S.rD m g f) w = 0 := by
    have h1 : d1 (S.rD m g f) (fun i => S.extDB m (u i)) = S.extDB m xb := by
      rw [← hu, d1_map (S.extDB m)]
      congr 1
      exact (funext fun i => (S.extDB_rB m g f i)).symm
    have h2 : d1 (S.rD m g f) (fun i => S.extDC m (v i)) = S.extDC m xc := by
      rw [← hv, d1_map (S.extDC m)]
      congr 1
      exact (funext fun i => S.extDC_rC m g f i).symm
    rw [hw, hd1sub, h1, h2, hcompat, sub_self]
  obtain ⟨sD, hsD, hsDn⟩ := hliftD w hwd1
  have hwn : ‖w‖ ≤ (hB + hC) * M := by
    refine pi_norm_le_iff_of_nonneg (mul_nonneg (add_nonneg hB0 hC0) hM0) |>.mpr fun i => ?_
    show ‖S.extDB m (u i) - S.extDC m (v i)‖ ≤ _
    have hsub : ‖S.extDB m (u i) - S.extDC m (v i)‖ ≤
        max ‖S.extDB m (u i)‖ ‖S.extDC m (v i)‖ := by
      have h := IsUltrametricDist.norm_add_le_max (S.extDB m (u i))
        (-(S.extDC m (v i)))
      rwa [← sub_eq_add_neg, norm_neg] at h
    refine hsub.trans (max_le ?_ ?_)
    · calc ‖S.extDB m (u i)‖ ≤ ‖u i‖ := norm_mapRestricted_le _ _ _ _
        _ ≤ ‖u‖ := norm_le_pi_norm u i
        _ ≤ hB * M := hun'
        _ ≤ (hB + hC) * M := mul_le_mul_of_nonneg_right (by linarith) hM0
    · calc ‖S.extDC m (v i)‖ ≤ ‖v i‖ := norm_mapRestricted_le _ _ _ _
        _ ≤ ‖v‖ := norm_le_pi_norm v i
        _ ≤ hC * M := hvn'
        _ ≤ (hB + hC) * M := mul_le_mul_of_nonneg_right (by linarith) hM0
  have hzM0 : 0 ≤ z * (hB + hC) * M :=
    mul_nonneg (mul_nonneg hz0 (add_nonneg hB0 hC0)) hM0
  have hsDn' : ‖sD‖ ≤ z * (hB + hC) * M := by
    refine hsDn.trans ?_
    calc z * ‖w‖ ≤ z * ((hB + hC) * M) := mul_le_mul_of_nonneg_left hwn hz0
      _ = z * (hB + hC) * M := by ring
  have hsec : ∀ p : Pairs m, ∃ c : P C m, S.extDC m c = sD p ∧ ‖c‖ = ‖sD p‖ := fun p =>
    S.extDC_strict_surjective m (sD p)
  choose sC hsC hsCn using hsec
  have hsCn' : ∀ p, ‖sC p‖ ≤ z * (hB + hC) * M := fun p => by
    rw [hsCn p]
    exact (norm_le_pi_norm sD p).trans hsDn'
  set v' : Fin m → P C m := fun i => v i + d2 (S.rC m g f) sC i with hv'def
  have hd1add : ∀ {T : Type _} [inst : CommRing T] (r a b : Fin m → T),
      d1 r (fun i => a i + b i) = d1 r a + d1 r b := by
    intro T _ r a b
    unfold d1
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  have hv'd1 : d1 (S.rC m g f) v' = xc := by
    rw [hv'def, hd1add, hv,
      show d1 (S.rC m g f) (fun i => d2 (S.rC m g f) sC i) = 0 from d1_d2 _ sC, add_zero]
  have hv'compat : ∀ i, S.extDB m (u i) = S.extDC m (v' i) := fun i => by
    rw [hv'def]
    show _ = S.extDC m (v i + d2 (S.rC m g f) sC i)
    rw [map_add, d2_map (S.extDC m)]
    have heq : d2 (fun j => S.extDC m (S.rC m g f j)) (fun p => S.extDC m (sC p)) i =
        d2 (S.rD m g f) sD i := by
      congr 1
      · exact funext fun j => S.extDC_rC m g f j
      · exact funext hsC
    rw [heq, congrFun hsD i, hw]
    show S.extDB m (u i) =
      S.extDC m (v i) + (S.extDB m (u i) - S.extDC m (v i))
    ring
  have hpull := fun i => (S.ext_milnorRow_exact m (u i) (v' i) (hv'compat i)).exists
  choose a ha using hpull
  refine ⟨d1 (rA m g f) a, ?_, ?_, ?_, ?_⟩
  · show d1 (rA m g f) a ∈ Ideal.span (Set.range (rA m g f))
    unfold d1
    exact Ideal.sum_mem _ fun i _ => Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨i, rfl⟩)
  · rw [show S.extB m (d1 (rA m g f) a) =
      d1 (fun i => S.extB m (rA m g f i)) (fun i => S.extB m (a i)) from
        d1_map (S.extB m) _ a,
      show (fun i => S.extB m (rA m g f i)) = S.rB m g f from
        funext fun i => S.extB_rA m g f i,
      show (fun i => S.extB m (a i)) = u from funext fun i => (ha i).1]
    exact hu
  · rw [show S.extC m (d1 (rA m g f) a) =
      d1 (fun i => S.extC m (rA m g f i)) (fun i => S.extC m (a i)) from
        d1_map (S.extC m) _ a,
      show (fun i => S.extC m (rA m g f i)) = S.rC m g f from
        funext fun i => S.extC_rA m g f i,
      show (fun i => S.extC m (a i)) = v' from funext fun i => (ha i).2]
    exact hv'd1
  · have hsum : ∀ (C0 : ℝ), 0 ≤ C0 → ∀ (T : Finset (Fin m)) (G : Fin m → P C m),
        (∀ j ∈ T, ‖G j‖ ≤ C0) → ‖∑ j ∈ T, G j‖ ≤ C0 := by
      intro C0 hC00 T G hG
      induction T using Finset.induction_on with
      | empty =>
        rw [Finset.sum_empty, norm_zero]
        exact hC00
      | insert b T hb ih =>
        rw [Finset.sum_insert hb]
        exact (IsUltrametricDist.norm_add_le_max _ _).trans
          (max_le (hG b (Finset.mem_insert_self _ _))
            (ih fun j hj => hG j (Finset.mem_insert_of_mem hj)))
    have hd2bound : ∀ i, ‖d2 (S.rC m g f) sC i‖ ≤ z * (hB + hC) * M * CrC := fun i => by
      have hterm : ∀ (p : Pairs m) (j : Fin m), ‖sC p * S.rC m g f j‖ ≤
          z * (hB + hC) * M * CrC := fun p j => by
        calc ‖sC p * S.rC m g f j‖ ≤ ‖sC p‖ * ‖S.rC m g f j‖ := norm_mul_le _ _
          _ ≤ (z * (hB + hC) * M) * CrC := by
              refine mul_le_mul (hsCn' p) ?_ (norm_nonneg _) hzM0
              rw [hCrC]
              exact le_add_of_nonneg_of_le zero_le_one
                (Finset.single_le_sum (fun k _ => norm_nonneg _) (Finset.mem_univ j))
      have hCrCM0 : 0 ≤ z * (hB + hC) * M * CrC :=
        mul_nonneg hzM0 (zero_le_one.trans hCrC1)
      show ‖d2 (S.rC m g f) sC i‖ ≤ _
      unfold d2
      have h1 : ‖(∑ j, if h : j < i then sC ⟨(j, i), h⟩ * S.rC m g f j else 0)‖ ≤
          z * (hB + hC) * M * CrC := by
        refine hsum _ hCrCM0 Finset.univ _ fun j _ => ?_
        by_cases hji : j < i
        · rw [dif_pos hji]
          exact hterm _ _
        · rw [dif_neg hji, norm_zero]
          exact hCrCM0
      have h2 : ‖(∑ j, if h : i < j then sC ⟨(i, j), h⟩ * S.rC m g f j else 0)‖ ≤
          z * (hB + hC) * M * CrC := by
        refine hsum _ hCrCM0 Finset.univ _ fun j _ => ?_
        by_cases hji : i < j
        · rw [dif_pos hji]
          exact hterm _ _
        · rw [dif_neg hji, norm_zero]
          exact hCrCM0
      have hd : ‖(∑ j, if h : j < i then sC ⟨(j, i), h⟩ * S.rC m g f j else 0) -
          (∑ j, if h : i < j then sC ⟨(i, j), h⟩ * S.rC m g f j else 0)‖ ≤
          max ‖(∑ j, if h : j < i then sC ⟨(j, i), h⟩ * S.rC m g f j else 0)‖
            ‖(∑ j, if h : i < j then sC ⟨(i, j), h⟩ * S.rC m g f j else 0)‖ := by
        have h := IsUltrametricDist.norm_add_le_max
          (∑ j, if h : j < i then sC ⟨(j, i), h⟩ * S.rC m g f j else 0)
          (-(∑ j, if h : i < j then sC ⟨(i, j), h⟩ * S.rC m g f j else 0))
        rwa [← sub_eq_add_neg, norm_neg] at h
      exact hd.trans (max_le h1 h2)
    have hv'n : ‖v'‖ ≤ Bs * M := by
      refine pi_norm_le_iff_of_nonneg (mul_nonneg hBs0 hM0) |>.mpr fun i => ?_
      show ‖v i + d2 (S.rC m g f) sC i‖ ≤ _
      refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
      · calc ‖v i‖ ≤ ‖v‖ := norm_le_pi_norm v i
          _ ≤ hC * M := hvn'
          _ ≤ Bs * M := mul_le_mul_of_nonneg_right hBsC hM0
      · refine (hd2bound i).trans ?_
        calc z * (hB + hC) * M * CrC = (z * (hB + hC) * CrC) * M := by ring
          _ ≤ Bs * M := mul_le_mul_of_nonneg_right hBszC hM0
    have han : ‖a‖ ≤ Bs * M := by
      refine pi_norm_le_iff_of_nonneg (mul_nonneg hBs0 hM0) |>.mpr fun i => ?_
      have hmax := S.ext_max_norm_eq m (a i)
      rw [(ha i).1, (ha i).2] at hmax
      rw [← hmax]
      refine max_le ?_ ?_
      · exact (norm_le_pi_norm u i).trans (hun'.trans
          (mul_le_mul_of_nonneg_right hBsB hM0))
      · exact (norm_le_pi_norm v' i).trans hv'n
    have hfinal : ∀ (T : Finset (Fin m)), ‖∑ j ∈ T, a j * rA m g f j‖ ≤ Bs * M * CrA := by
      have hBMC0 : 0 ≤ Bs * M * CrA :=
        mul_nonneg (mul_nonneg hBs0 hM0) (zero_le_one.trans hCrA1)
      intro T
      induction T using Finset.induction_on with
      | empty =>
        rw [Finset.sum_empty, norm_zero]
        exact hBMC0
      | insert b T hb ih =>
        rw [Finset.sum_insert hb]
        refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ih)
        calc ‖a b * rA m g f b‖ ≤ ‖a b‖ * ‖rA m g f b‖ := norm_mul_le _ _
          _ ≤ (Bs * M) * CrA := by
              refine mul_le_mul ((norm_le_pi_norm a b).trans han) ?_ (norm_nonneg _)
                (mul_nonneg hBs0 hM0)
              rw [hCrA]
              exact le_add_of_nonneg_of_le zero_le_one
                (Finset.single_le_sum (fun k _ => norm_nonneg _) (Finset.mem_univ b))
    show ‖d1 (rA m g f) a‖ ≤ (1 + Bs * CrA) * M
    unfold d1
    refine (hfinal Finset.univ).trans ?_
    calc Bs * M * CrA = Bs * CrA * M := by ring
      _ ≤ (1 + Bs * CrA) * M := by
          refine mul_le_mul_of_nonneg_right ?_ hM0
          linarith [mul_nonneg hBs0 (zero_le_one.trans hCrA1)]

include S in
/-- `I_A` is closed in `P_A` ([FJP] Lemma 4.3: "Consequently `I_R` is closed"). -/
theorem isClosed_IA (hN : NoethPack B C D m)
    (hspan : Ideal.span ({g} ∪ Set.range f) = ⊤) :
    IsClosed ((IA m g f : Set (P A m))) := by
  classical
  have := hN.hPB
  have := hN.hPC
  have hIBclosed : IsClosed ((S.IB m g f : Set (P B m))) :=
    isClosed_graphIdeal S.tB S.tB_isUnit
      S.norm_tB_lt_one S.norm_tB_pos
      S.norm_tB_mul (hN.hPBball) (S.rB m g f)
  have hICclosed : IsClosed ((S.IC m g f : Set (P C m))) :=
    isClosed_graphIdeal S.tC S.tC_isUnit
      S.norm_tC_lt_one S.norm_tC_pos
      S.norm_tC_mul (hN.hPCball) (S.rC m g f)
  obtain ⟨Cs, hCs1, hpull⟩ := S.ideal_pullback_controlled m g f hN hspan
  refine isClosed_of_closure_subset fun x hx => ?_
  have hcontB : Continuous (S.extB m) := by
    have hlip : LipschitzWith 1 (S.extB m) := LipschitzWith.of_dist_le_mul fun a b => by
      rw [NNReal.coe_one, one_mul, dist_eq_norm, dist_eq_norm, ← map_sub]
      exact norm_mapRestricted_le _ _ _ _
    exact hlip.continuous
  have hcontC : Continuous (S.extC m) := by
    have hlip : LipschitzWith 1 (S.extC m) := LipschitzWith.of_dist_le_mul fun a b => by
      rw [NNReal.coe_one, one_mul, dist_eq_norm, dist_eq_norm, ← map_sub]
      exact norm_mapRestricted_le _ _ _ _
    exact hlip.continuous
  have hsubB : S.extB m '' (IA m g f : Set (P A m)) ⊆ (S.IB m g f : Set (P B m)) := by
    rintro _ ⟨y, hy, rfl⟩
    have hmap : Ideal.map (S.extB m) (IA m g f) ≤ S.IB m g f := by
      rw [show IA m g f = Ideal.span (Set.range (rA m g f)) from rfl, Ideal.map_span]
      refine Ideal.span_le.mpr ?_
      rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
      exact Ideal.subset_span ⟨i, (S.extB_rA m g f i).symm⟩
    exact hmap (Ideal.mem_map_of_mem _ hy)
  have hsubC : S.extC m '' (IA m g f : Set (P A m)) ⊆ (S.IC m g f : Set (P C m)) := by
    rintro _ ⟨y, hy, rfl⟩
    have hmap : Ideal.map (S.extC m) (IA m g f) ≤ S.IC m g f := by
      rw [show IA m g f = Ideal.span (Set.range (rA m g f)) from rfl, Ideal.map_span]
      refine Ideal.span_le.mpr ?_
      rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
      exact Ideal.subset_span ⟨i, (S.extC_rA m g f i).symm⟩
    exact hmap (Ideal.mem_map_of_mem _ hy)
  have hxB : S.extB m x ∈ (S.IB m g f : Set (P B m)) := by
    have h1 : S.extB m x ∈ closure (S.extB m '' (IA m g f : Set (P A m))) :=
      image_closure_subset_closure_image hcontB ⟨x, hx, rfl⟩
    exact hIBclosed.closure_eq ▸ closure_mono hsubB h1
  have hxC : S.extC m x ∈ (S.IC m g f : Set (P C m)) := by
    have h1 : S.extC m x ∈ closure (S.extC m '' (IA m g f : Set (P A m))) :=
      image_closure_subset_closure_image hcontC ⟨x, hx, rfl⟩
    exact hICclosed.closure_eq ▸ closure_mono hsubC h1
  obtain ⟨xa, hxa, hJ, hI, -⟩ := hpull (S.extB m x) hxB (S.extC m x) hxC
    (S.ext_square_commutes m x)
  have heq : xa = x := S.ext_pair_injective m (Prod.ext hJ hI)
  rw [← heq]
  exact hxa

/-! ### Proposition 4.5 — strict Milnor localization

Since all four graph ideals are closed ([FJP] (4.21)), we take the plain ring
quotients with their quotient topologies; the strict quotient lemma ([FJP]
Lemma 4.4) is consumed inside the proofs below. -/

/-- `A_α = P_A ⧸ I_A` and companions, as topological rings with the quotient
topology. -/
abbrev locA : Type _ := P A m ⧸ IA m g f
abbrev locB : Type _ := P B m ⧸ S.IB m g f
abbrev locC : Type _ := P C m ⧸ S.IC m g f
abbrev locD : Type _ := P D m ⧸ S.ID m g f

omit [NormOneClass C] [CompleteSpace C] [NormOneClass D] [CompleteSpace D] in
/-- Graph ideals push forward along the square's maps. -/
theorem extB_mem_IB {y : P A m} (hy : y ∈ IA m g f) : S.extB m y ∈ S.IB m g f := by
  have hmap : Ideal.map (S.extB m) (IA m g f) ≤ S.IB m g f := by
    rw [show IA m g f = Ideal.span (Set.range (rA m g f)) from rfl, Ideal.map_span]
    refine Ideal.span_le.mpr ?_
    rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
    exact Ideal.subset_span ⟨i, (S.extB_rA m g f i).symm⟩
  exact hmap (Ideal.mem_map_of_mem _ hy)

omit [NormOneClass B] [CompleteSpace B] [NormOneClass D] [CompleteSpace D] in
theorem extC_mem_IC {y : P A m} (hy : y ∈ IA m g f) :
    S.extC m y ∈ S.IC m g f := by
  have hmap : Ideal.map (S.extC m) (IA m g f) ≤ S.IC m g f := by
    rw [show IA m g f = Ideal.span (Set.range (rA m g f)) from rfl, Ideal.map_span]
    refine Ideal.span_le.mpr ?_
    rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
    exact Ideal.subset_span ⟨i, (S.extC_rA m g f i).symm⟩
  exact hmap (Ideal.mem_map_of_mem _ hy)

theorem extDB_mem_ID {y : P B m} (hy : y ∈ S.IB m g f) :
    S.extDB m y ∈ S.ID m g f := by
  have hmap : Ideal.map (S.extDB m) (S.IB m g f) ≤ S.ID m g f := by
    rw [show S.IB m g f = Ideal.span (Set.range (S.rB m g f)) from rfl, Ideal.map_span]
    refine Ideal.span_le.mpr ?_
    rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
    exact Ideal.subset_span ⟨i, (S.extDB_rB m g f i).symm⟩
  exact hmap (Ideal.mem_map_of_mem _ hy)

omit [NormOneClass A] [CompleteSpace A] [NormOneClass B] [CompleteSpace B] in
theorem extDC_mem_ID {y : P C m} (hy : y ∈ S.IC m g f) :
    S.extDC m y ∈ S.ID m g f := by
  have hmap : Ideal.map (S.extDC m) (S.IC m g f) ≤ S.ID m g f := by
    rw [show S.IC m g f = Ideal.span (Set.range (S.rC m g f)) from rfl, Ideal.map_span]
    refine Ideal.span_le.mpr ?_
    rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
    exact Ideal.subset_span ⟨i, (S.extDC_rC m g f i).symm⟩
  exact hmap (Ideal.mem_map_of_mem _ hy)

/-- The induced maps of the localized square ([FJP] (4.19)). -/
noncomputable def locφB : locA m g f →+* S.locB m g f :=
  Ideal.Quotient.lift (IA m g f)
    ((Ideal.Quotient.mk (S.IB m g f)).comp (S.extB m)) (fun a ha => by
      rw [RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem]
      exact S.extB_mem_IB m g f ha)

noncomputable def locφC : locA m g f →+* S.locC m g f :=
  Ideal.Quotient.lift (IA m g f)
    ((Ideal.Quotient.mk (S.IC m g f)).comp (S.extC m)) (fun a ha => by
      rw [RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem]
      exact S.extC_mem_IC m g f ha)

noncomputable def locψB : S.locB m g f →+* S.locD m g f :=
  Ideal.Quotient.lift (S.IB m g f)
    ((Ideal.Quotient.mk (S.ID m g f)).comp (S.extDB m)) (fun a ha => by
      rw [RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem]
      exact S.extDB_mem_ID m g f ha)

noncomputable def locψC : S.locC m g f →+* S.locD m g f :=
  Ideal.Quotient.lift (S.IC m g f)
    ((Ideal.Quotient.mk (S.ID m g f)).comp (S.extDC m)) (fun a ha => by
      rw [RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem]
      exact S.extDC_mem_ID m g f ha)

omit [NormOneClass C] [CompleteSpace C] [NormOneClass D] [CompleteSpace D] in
theorem locφB_mk (p : P A m) :
    S.locφB m g f (Ideal.Quotient.mk (IA m g f) p) =
      Ideal.Quotient.mk (S.IB m g f) (S.extB m p) := rfl

omit [NormOneClass B] [CompleteSpace B] [NormOneClass D] [CompleteSpace D] in
theorem locφC_mk (p : P A m) :
    S.locφC m g f (Ideal.Quotient.mk (IA m g f) p) =
      Ideal.Quotient.mk (S.IC m g f) (S.extC m p) := rfl

theorem locψB_mk (p : P B m) :
    S.locψB m g f (Ideal.Quotient.mk (S.IB m g f) p) =
      Ideal.Quotient.mk (S.ID m g f) (S.extDB m p) := rfl

omit [NormOneClass A] [CompleteSpace A] [NormOneClass B] [CompleteSpace B] in
theorem locψC_mk (p : P C m) :
    S.locψC m g f (Ideal.Quotient.mk (S.IC m g f) p) =
      Ideal.Quotient.mk (S.ID m g f) (S.extDC m p) := rfl

theorem loc_square_commutes (x : locA m g f) :
    S.locψB m g f (S.locφB m g f x) = S.locψC m g f (S.locφC m g f x) := by
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [locφB_mk, locφC_mk, locψB_mk, locψC_mk, S.ext_square_commutes]

/-- Left exactness of the localized row: the pullback description of `A_α`
([FJP] (4.20)). -/
theorem loc_pair_injective (hN : NoethPack B C D m)
    (hspan : Ideal.span ({g} ∪ Set.range f) = ⊤) :
    Function.Injective
      (fun x : locA m g f => (S.locφB m g f x, S.locφC m g f x)) := by
  obtain ⟨Cs, hCs1, hpull⟩ := S.ideal_pullback_controlled m g f hN hspan
  have hker : ∀ y : locA m g f,
      S.locφB m g f y = 0 → S.locφC m g f y = 0 → y = 0 := by
    intro y hyB hyC
    obtain ⟨q, rfl⟩ := Ideal.Quotient.mk_surjective y
    rw [locφB_mk, Ideal.Quotient.eq_zero_iff_mem] at hyB
    rw [locφC_mk, Ideal.Quotient.eq_zero_iff_mem] at hyC
    obtain ⟨qa, hqa, hJ, hI, -⟩ := hpull (S.extB m q) hyB (S.extC m q) hyC
      (S.ext_square_commutes m q)
    have heq : qa = q := S.ext_pair_injective m (Prod.ext hJ hI)
    rw [Ideal.Quotient.eq_zero_iff_mem, ← heq]
    exact hqa
  intro x y hxy
  have hxy' : (S.locφB m g f x, S.locφC m g f x) =
      (S.locφB m g f y, S.locφC m g f y) := hxy
  rw [Prod.mk.injEq] at hxy'
  have h1 : S.locφB m g f (x - y) = 0 := by
    rw [map_sub, hxy'.1, sub_self]
  have h2 : S.locφC m g f (x - y) = 0 := by
    rw [map_sub, hxy'.2, sub_self]
  have := hker (x - y) h1 h2
  rwa [sub_eq_zero] at this

/-- Middle exactness of the localized row ([FJP] (4.20)): a `D_α`-matching pair
comes from a unique element of `A_α`. -/
theorem loc_row_exact (hN : NoethPack B C D m)
    (hspan : Ideal.span ({g} ∪ Set.range f) = ⊤)
    (b : S.locB m g f) (c : S.locC m g f)
    (h : S.locψB m g f b = S.locψC m g f c) :
    ∃! x : locA m g f, S.locφB m g f x = b ∧ S.locφC m g f x = c := by
  obtain ⟨pb, rfl⟩ := Ideal.Quotient.mk_surjective b
  obtain ⟨pc, rfl⟩ := Ideal.Quotient.mk_surjective c
  rw [locψB_mk, locψC_mk, Ideal.Quotient.mk_eq_mk_iff_sub_mem] at h
  obtain ⟨Cs, hCs1, hrow⟩ := S.ideal_row_surjective m g f hN hspan
  obtain ⟨xc, hxc, hxcρ, -⟩ := hrow (S.extDB m pb - S.extDC m pc) h
  set pc' : P C m := pc + xc with hpc'
  have hcompat : S.extDB m pb = S.extDC m pc' := by
    rw [hpc', map_add, hxcρ]
    ring
  obtain ⟨p, hpb, hpc⟩ := (S.ext_milnorRow_exact m pb pc' hcompat).exists
  refine ⟨Ideal.Quotient.mk _ p, ⟨?_, ?_⟩, ?_⟩
  · rw [locφB_mk, hpb]
  · rw [locφC_mk, hpc, hpc', Ideal.Quotient.mk_eq_mk_iff_sub_mem, add_sub_cancel_left]
    exact hxc
  · rintro x' ⟨hx'B, hx'C⟩
    refine S.loc_pair_injective m g f hN hspan ?_
    rw [Prod.ext_iff]
    constructor
    · show S.locφB m g f x' = S.locφB m g f (Ideal.Quotient.mk _ p)
      rw [hx'B, locφB_mk, hpb]
    · show S.locφC m g f x' = S.locφC m g f (Ideal.Quotient.mk _ p)
      rw [hx'C, locφC_mk, hpc, hpc', Ideal.Quotient.mk_eq_mk_iff_sub_mem,
        sub_add_cancel_left]
      exact (S.IC m g f).neg_mem hxc

omit [NormOneClass C] [CompleteSpace C] [NormOneClass D] [CompleteSpace D] in
/-- The quotient maps are 1-Lipschitz for the quotient seminorms. -/
theorem locφB_lipschitz : LipschitzWith 1 (S.locφB m g f) :=
  LipschitzWith.of_dist_le_mul fun a b => by
    rw [NNReal.coe_one, one_mul, dist_eq_norm, dist_eq_norm, ← map_sub]
    obtain ⟨p, hp⟩ := Ideal.Quotient.mk_surjective (a - b)
    rw [← hp, locφB_mk]
    refine le_of_forall_pos_le_add fun ε hε => ?_
    obtain ⟨q, hq, hqn⟩ := Ideal.Quotient.norm_mk_lt (Ideal.Quotient.mk (IA m g f) p) hε
    have hmkeq : Ideal.Quotient.mk (S.IB m g f) (S.extB m p) =
        Ideal.Quotient.mk (S.IB m g f) (S.extB m q) := by
      rw [Ideal.Quotient.mk_eq_mk_iff_sub_mem, ← map_sub]
      exact S.extB_mem_IB m g f (by
        have h := hq.symm
        rwa [Ideal.Quotient.mk_eq_mk_iff_sub_mem] at h)
    rw [hmkeq]
    calc ‖Ideal.Quotient.mk (S.IB m g f) (S.extB m q)‖
        ≤ ‖S.extB m q‖ := Ideal.Quotient.norm_mk_le _ (S.extB m q)
      _ ≤ ‖q‖ := norm_mapRestricted_le _ _ _ _
      _ ≤ ‖Ideal.Quotient.mk (IA m g f) p‖ + ε := hqn.le

omit [NormOneClass B] [CompleteSpace B] [NormOneClass D] [CompleteSpace D] in
theorem locφC_lipschitz : LipschitzWith 1 (S.locφC m g f) :=
  LipschitzWith.of_dist_le_mul fun a b => by
    rw [NNReal.coe_one, one_mul, dist_eq_norm, dist_eq_norm, ← map_sub]
    obtain ⟨p, hp⟩ := Ideal.Quotient.mk_surjective (a - b)
    rw [← hp, locφC_mk]
    refine le_of_forall_pos_le_add fun ε hε => ?_
    obtain ⟨q, hq, hqn⟩ := Ideal.Quotient.norm_mk_lt (Ideal.Quotient.mk (IA m g f) p) hε
    have hmkeq : Ideal.Quotient.mk (S.IC m g f) (S.extC m p) =
        Ideal.Quotient.mk (S.IC m g f) (S.extC m q) := by
      rw [Ideal.Quotient.mk_eq_mk_iff_sub_mem, ← map_sub]
      exact S.extC_mem_IC m g f (by
        have h := hq.symm
        rwa [Ideal.Quotient.mk_eq_mk_iff_sub_mem] at h)
    rw [hmkeq]
    calc ‖Ideal.Quotient.mk (S.IC m g f) (S.extC m q)‖
        ≤ ‖S.extC m q‖ := Ideal.Quotient.norm_mk_le _ (S.extC m q)
      _ ≤ ‖q‖ := norm_mapRestricted_le _ _ _ _
      _ ≤ ‖Ideal.Quotient.mk (IA m g f) p‖ + ε := hqn.le

theorem locψB_lipschitz : LipschitzWith 1 (S.locψB m g f) :=
  LipschitzWith.of_dist_le_mul fun a b => by
    rw [NNReal.coe_one, one_mul, dist_eq_norm, dist_eq_norm, ← map_sub]
    obtain ⟨p, hp⟩ := Ideal.Quotient.mk_surjective (a - b)
    rw [← hp, locψB_mk]
    refine le_of_forall_pos_le_add fun ε hε => ?_
    obtain ⟨q, hq, hqn⟩ := Ideal.Quotient.norm_mk_lt
      (Ideal.Quotient.mk (S.IB m g f) p) hε
    have hmkeq : Ideal.Quotient.mk (S.ID m g f) (S.extDB m p) =
        Ideal.Quotient.mk (S.ID m g f) (S.extDB m q) := by
      rw [Ideal.Quotient.mk_eq_mk_iff_sub_mem, ← map_sub]
      exact S.extDB_mem_ID m g f (by
        have h := hq.symm
        rwa [Ideal.Quotient.mk_eq_mk_iff_sub_mem] at h)
    rw [hmkeq]
    calc ‖Ideal.Quotient.mk (S.ID m g f) (S.extDB m q)‖
        ≤ ‖S.extDB m q‖ := Ideal.Quotient.norm_mk_le _ (S.extDB m q)
      _ ≤ ‖q‖ := norm_mapRestricted_le _ _ _ _
      _ ≤ ‖Ideal.Quotient.mk (S.IB m g f) p‖ + ε := hqn.le

omit [NormOneClass A] [CompleteSpace A] [NormOneClass B] [CompleteSpace B] in
theorem locψC_lipschitz : LipschitzWith 1 (S.locψC m g f) :=
  LipschitzWith.of_dist_le_mul fun a b => by
    rw [NNReal.coe_one, one_mul, dist_eq_norm, dist_eq_norm, ← map_sub]
    obtain ⟨p, hp⟩ := Ideal.Quotient.mk_surjective (a - b)
    rw [← hp, locψC_mk]
    refine le_of_forall_pos_le_add fun ε hε => ?_
    obtain ⟨q, hq, hqn⟩ := Ideal.Quotient.norm_mk_lt
      (Ideal.Quotient.mk (S.IC m g f) p) hε
    have hmkeq : Ideal.Quotient.mk (S.ID m g f) (S.extDC m p) =
        Ideal.Quotient.mk (S.ID m g f) (S.extDC m q) := by
      rw [Ideal.Quotient.mk_eq_mk_iff_sub_mem, ← map_sub]
      exact S.extDC_mem_ID m g f (by
        have h := hq.symm
        rwa [Ideal.Quotient.mk_eq_mk_iff_sub_mem] at h)
    rw [hmkeq]
    calc ‖Ideal.Quotient.mk (S.ID m g f) (S.extDC m q)‖
        ≤ ‖S.extDC m q‖ := Ideal.Quotient.norm_mk_le _ (S.extDC m q)
      _ ≤ ‖q‖ := norm_mapRestricted_le _ _ _ _
      _ ≤ ‖Ideal.Quotient.mk (S.IC m g f) p‖ + ε := hqn.le

/-- The quantitative Lemma 4.4 estimate: the quotient pullback norm is controlled
by the component norms. -/
theorem loc_norm_le (hN : NoethPack B C D m)
    (hspan : Ideal.span ({g} ∪ Set.range f) = ⊤) (x : locA m g f) :
    ‖x‖ ≤ (1 + Classical.choose (S.ideal_row_surjective m g f hN hspan)) *
      max ‖S.locφB m g f x‖ ‖S.locφC m g f x‖ := by
  classical
  obtain ⟨hC₁1, hrow⟩ := Classical.choose_spec (S.ideal_row_surjective m g f hN hspan)
  set C₁ := Classical.choose (S.ideal_row_surjective m g f hN hspan) with hC₁def
  have hC₁0 : (0 : ℝ) ≤ C₁ := zero_le_one.trans hC₁1
  set M : ℝ := max ‖S.locφB m g f x‖ ‖S.locφC m g f x‖ with hMdef
  have hM0 : 0 ≤ M := le_max_of_le_left (norm_nonneg _)
  refine le_of_forall_pos_le_add fun ε hε => ?_
  set δ : ℝ := ε / (2 * (1 + C₁)) with hδdef
  have hδ0 : 0 < δ := by positivity
  obtain ⟨pb, hpb, hpbn⟩ := Ideal.Quotient.norm_mk_lt (S.locφB m g f x) hδ0
  obtain ⟨pc, hpc, hpcn⟩ := Ideal.Quotient.norm_mk_lt (S.locφC m g f x) hδ0
  have hpbM : ‖pb‖ < M + δ := by
    refine hpbn.trans_le ?_
    have h := le_max_left ‖S.locφB m g f x‖ ‖S.locφC m g f x‖
    linarith
  have hpcM : ‖pc‖ < M + δ := by
    refine hpcn.trans_le ?_
    have h := le_max_right ‖S.locφB m g f x‖ ‖S.locφC m g f x‖
    linarith
  have hdefect : S.extDB m pb - S.extDC m pc ∈ S.ID m g f := by
    rw [← Ideal.Quotient.mk_eq_mk_iff_sub_mem, ← locψB_mk, ← locψC_mk, hpb, hpc]
    exact S.loc_square_commutes m g f x
  obtain ⟨xc, hxcIC, hxcρ, hxcn⟩ := hrow _ hdefect
  have hdn : ‖S.extDB m pb - S.extDC m pc‖ < M + δ := by
    have hsub : ‖S.extDB m pb - S.extDC m pc‖ ≤
        max ‖S.extDB m pb‖ ‖S.extDC m pc‖ := by
      have h := IsUltrametricDist.norm_add_le_max (S.extDB m pb) (-(S.extDC m pc))
      rwa [← sub_eq_add_neg, norm_neg] at h
    refine lt_of_le_of_lt hsub (max_lt ?_ ?_)
    · exact lt_of_le_of_lt (norm_mapRestricted_le _ _ _ _) hpbM
    · exact lt_of_le_of_lt (norm_mapRestricted_le _ _ _ _) hpcM
  have hxcn' : ‖xc‖ ≤ C₁ * (M + δ) :=
    hxcn.trans (mul_le_mul_of_nonneg_left hdn.le hC₁0)
  set pc' : P C m := pc + xc with hpc'def
  have hcompat : S.extDB m pb = S.extDC m pc' := by
    rw [hpc'def, map_add, hxcρ]
    ring
  obtain ⟨p', hp'b, hp'c⟩ := (S.ext_milnorRow_exact m pb pc' hcompat).exists
  have hmkp' : Ideal.Quotient.mk (IA m g f) p' = x := by
    refine S.loc_pair_injective m g f hN hspan ?_
    show (S.locφB m g f _, S.locφC m g f _) = (S.locφB m g f x, S.locφC m g f x)
    rw [Prod.mk.injEq]
    constructor
    · rw [locφB_mk, hp'b, hpb]
    · rw [locφC_mk, hp'c, hpc'def, ← hpc]
      rw [Ideal.Quotient.mk_eq_mk_iff_sub_mem, add_sub_cancel_left]
      exact hxcIC
  have hnormp' : ‖p'‖ ≤ (1 + C₁) * (M + δ) := by
    have hmax := S.ext_max_norm_eq m p'
    rw [hp'b, hp'c] at hmax
    rw [← hmax]
    refine max_le ?_ ?_
    · nlinarith [hpbM.le, hM0, hδ0.le, hC₁0]
    · show ‖pc'‖ ≤ _
      rw [hpc'def]
      refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
      · nlinarith [hpcM.le, hM0, hδ0.le, hC₁0]
      · nlinarith [hxcn', hM0, hδ0.le, hC₁0]
  calc ‖x‖ = ‖Ideal.Quotient.mk (IA m g f) p'‖ := by rw [hmkp']
    _ ≤ ‖p'‖ := Ideal.Quotient.norm_mk_le _ p'
    _ ≤ (1 + C₁) * (M + δ) := hnormp'
    _ = (1 + C₁) * M + (1 + C₁) * δ := by ring
    _ ≤ (1 + C₁) * M + ε := by
        have hδval : (1 + C₁) * δ ≤ ε := by
          have h2 : (0 : ℝ) < 2 * (1 + C₁) := by linarith
          calc (1 + C₁) * δ = (1 + C₁) * (ε / (2 * (1 + C₁))) := by rw [hδdef]
            _ = ε / 2 := by
                field_simp
            _ ≤ ε := by linarith
        linarith

/-- Topological strictness on the left ([FJP] (4.19)/(4.20)): `A_α` carries the
subspace topology of `B_α × C_α`. -/
theorem loc_pair_isEmbedding (hN : NoethPack B C D m)
    (hspan : Ideal.span ({g} ∪ Set.range f) = ⊤) :
    Topology.IsEmbedding
      (fun x : locA m g f => (S.locφB m g f x, S.locφC m g f x)) := by
  classical
  have hclA : IsClosed ((IA m g f : Set (P A m))) := S.isClosed_IA m g f hN hspan
  have : NormedAddCommGroup (P A m ⧸ IA m g f) :=
    Submodule.Quotient.normedAddCommGroup _
  set C₁ := Classical.choose (S.ideal_row_surjective m g f hN hspan) with hC₁def
  have hC₁1 := (Classical.choose_spec (S.ideal_row_surjective m g f hN hspan)).1
  have hK0 : (0 : ℝ) ≤ 1 + C₁ := by linarith
  have hcont : Continuous (fun x : locA m g f =>
      (S.locφB m g f x, S.locφC m g f x)) :=
    Continuous.prodMk (S.locφB_lipschitz m g f).continuous
      (S.locφC_lipschitz m g f).continuous
  have hanti : AntilipschitzWith ⟨1 + C₁, hK0⟩
      (fun x : locA m g f => (S.locφB m g f x, S.locφC m g f x)) := by
    refine AntilipschitzWith.of_le_mul_dist fun x y => ?_
    have hest := S.loc_norm_le m g f hN hspan (x - y)
    rw [map_sub, map_sub] at hest
    rw [dist_eq_norm, Prod.dist_eq]
    dsimp only
    rw [dist_eq_norm, dist_eq_norm]
    exact hest
  exact hanti.isEmbedding hcont

omit [NormOneClass A] [CompleteSpace A] [NormOneClass B] [CompleteSpace B] in
/-- `C_α → D_α` is surjective ([FJP] Prop 4.5). -/
theorem locψC_surjective :
    Function.Surjective (S.locψC m g f) := by
  intro d
  obtain ⟨pd, rfl⟩ := Ideal.Quotient.mk_surjective d
  obtain ⟨c, hc, -⟩ := S.extDC_strict_surjective m pd
  exact ⟨Ideal.Quotient.mk _ c, by rw [locψC_mk, hc]⟩

omit [NormOneClass A] [CompleteSpace A] [NormOneClass B] [CompleteSpace B] [NormOneClass C] [CompleteSpace C] [NormOneClass D] [CompleteSpace D] in
/-- `extDC` is open (constant-1 sections). -/
theorem extDC_isOpenMap : IsOpenMap (S.extDC m) := by
  intro U hU
  rw [Metric.isOpen_iff] at hU ⊢
  rintro _ ⟨x, hxU, rfl⟩
  obtain ⟨ε, hε, hball⟩ := hU x hxU
  refine ⟨ε, hε, fun d hd => ?_⟩
  rw [Metric.mem_ball, dist_eq_norm] at hd
  obtain ⟨c, hc, hcn⟩ := S.extDC_strict_surjective m (d - S.extDC m x)
  refine ⟨x + c, hball ?_, ?_⟩
  · rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, hcn]
    exact hd
  · rw [map_add, hc]
    ring

omit [NormOneClass A] [CompleteSpace A] [NormOneClass B] [CompleteSpace B] in
theorem locψC_isOpenMap :
    IsOpenMap (S.locψC m g f) := by
  intro U hU
  have hmkC_cont : Continuous (Ideal.Quotient.mk (S.IC m g f)) := by
    have hlip : LipschitzWith 1 (Ideal.Quotient.mk (S.IC m g f)) :=
      LipschitzWith.of_dist_le_mul fun a b => by
        rw [NNReal.coe_one, one_mul, dist_eq_norm, dist_eq_norm, ← map_sub]
        exact Ideal.Quotient.norm_mk_le _ _
    exact hlip.continuous
  have hmkD_open : IsOpenMap (Ideal.Quotient.mk (S.ID m g f)) := by
    intro V hV
    rw [Metric.isOpen_iff] at hV ⊢
    rintro _ ⟨v, hvV, rfl⟩
    obtain ⟨ε, hε, hball⟩ := hV v hvV
    refine ⟨ε, hε, fun d hd => ?_⟩
    rw [Metric.mem_ball, dist_eq_norm] at hd
    have hpos : 0 < ε - ‖d - Ideal.Quotient.mk (S.ID m g f) v‖ := by linarith
    obtain ⟨y, hy, hyn⟩ := Ideal.Quotient.norm_mk_lt
      (d - Ideal.Quotient.mk (S.ID m g f) v) hpos
    refine ⟨v + y, hball ?_, ?_⟩
    · rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left]
      linarith
    · have hadd := RingHom.map_add (Ideal.Quotient.mk (S.ID m g f)) v y
      rw [hadd, hy]
      ring
  have himg : S.locψC m g f '' U =
      Ideal.Quotient.mk (S.ID m g f) ''
        (S.extDC m '' (Ideal.Quotient.mk (S.IC m g f) ⁻¹' U)) := by
    ext d
    constructor
    · rintro ⟨u, hu, rfl⟩
      obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective u
      exact ⟨S.extDC m p, ⟨p, hu, rfl⟩, (S.locψC_mk m g f p).symm⟩
    · rintro ⟨_, ⟨p, hp, rfl⟩, rfl⟩
      exact ⟨Ideal.Quotient.mk _ p, hp, S.locψC_mk m g f p⟩
  rw [himg]
  exact hmkD_open _ (S.extDC_isOpenMap m _ (hU.preimage hmkC_cont))

include S in
/-- `A_α` is Hausdorff (quotient by a closed ideal; [FJP] (4.21)). -/
theorem locA_t2 (hN : NoethPack B C D m)
    (hspan : Ideal.span ({g} ∪ Set.range f) = ⊤) :
    T2Space (locA m g f) := by
  have hclA : IsClosed ((IA m g f : Set (P A m))) := S.isClosed_IA m g f hN hspan
  have : NormedAddCommGroup (P A m ⧸ IA m g f) :=
    Submodule.Quotient.normedAddCommGroup _
  infer_instance

include S in
/-- `A_α` is complete (Banach quotient; [FJP] (4.21)). -/
theorem locA_completeSpace (hN : NoethPack B C D m)
    (hspan : Ideal.span ({g} ∪ Set.range f) = ⊤) :
    @CompleteSpace (locA m g f)
      (IsTopologicalAddGroup.rightUniformSpace (locA m g f)) := by
  have hclA : IsClosed ((IA m g f : Set (P A m))) := S.isClosed_IA m g f hN hspan
  have : NormedAddCommGroup (P A m ⧸ IA m g f) :=
    Submodule.Quotient.normedAddCommGroup _
  have : IsUniformAddGroup (locA m g f) := SeminormedAddCommGroup.to_isUniformAddGroup
  rw [IsUniformAddGroup.rightUniformSpace_eq]
  infer_instance

/-- The quotient norm structure on a single-corner graph quotient, packaged for
importers (the two `P`-ring core paths are defeq only at default transparency —
the established v4.33 pattern). -/
@[instance_reducible]
noncomputable def locANormedAddCommGroup (hIcl : IsClosed ((IA m g f : Set (P A m)))) :
    NormedAddCommGroup (locA m g f) := by
  have hclA : IsClosed ((IA m g f : Set (P A m))) := hIcl
  exact Submodule.Quotient.normedAddCommGroup _

omit [NormOneClass A] [CompleteSpace A] in
/-- Single-corner Hausdorffness of the graph quotient from ideal closedness. -/
theorem locA_t2_of_isClosed (hIcl : IsClosed ((IA m g f : Set (P A m)))) :
    T2Space (locA m g f) := by
  have hclA : IsClosed ((IA m g f : Set (P A m))) := hIcl
  have : NormedAddCommGroup (P A m ⧸ IA m g f) :=
    Submodule.Quotient.normedAddCommGroup _
  infer_instance

omit [NormOneClass A] in
/-- Single-corner completeness of the graph quotient (Banach quotient). -/
theorem locA_completeSpace_of_isClosed
    (hIcl : IsClosed ((IA m g f : Set (P A m)))) :
    CompleteSpace (locA m g f) := by
  have hclA : IsClosed ((IA m g f : Set (P A m))) := hIcl
  have : NormedAddCommGroup (P A m ⧸ IA m g f) :=
    Submodule.Quotient.normedAddCommGroup _
  infer_instance

end Graph

end Pinch

end FiniteJet
