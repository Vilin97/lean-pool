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
public import Mathlib.Topology.Algebra.Valued.NormedValued
public import Mathlib.Data.Int.WithZero
public import LeanPool.UniformSheafyTateDomains.AdicSpaces.ExampleLaurentSeries
public import LeanPool.UniformSheafyTateDomains.AdicSpaces.Vendored.CoramRestrictedIso

/-!
# The closed unit disc over `F⸨X⸩` is sheafy (Wedhorn 8.28(b), second example)

Let `K := F⸨X⸩` (Laurent series, `X`-adically valued) and
`D := K⟨Y⟩ = MvPowerSeries.Restricted K 1` the ring of restricted power series in one
variable — the ring of functions on the **closed unit disc** over `K`. We equip `K`
with the rank-one norm (`Valued.toNormedField`, whose uniformity *is* the valued one),
and `D` with the Gauss norm (vendored Coram stack). Then `D` is a complete, strongly
noetherian Tate ring, `(D, 𝒪_D)` with `𝒪_D` the closed unit ball is an affinoid ring,
and `IsSheafy D` follows from `isSheafy_of_stronglyNoetherian_828b`.

Strong noetherianity comes from the **flattening isometry**
`K⟨Y⟩⟨X₁,…,Xₘ⟩ ≃ K⟨Y, X₁,…,Xₘ⟩` (induction on `m` over the vendored restricted Fubini
`MvRestricted.finSuccEquiv`), transported to the topological restricted rings by the
norm/topology bridge, and then discharged by `IsStronglyNoetherian K` from
`ExampleLaurentSeries`.
-/

@[expose] public section

noncomputable section

open scoped LaurentSeries PowerSeries
open WithZero ValuationSpectrum Filter
open scoped NNReal

namespace UnitDiscExample

open LaurentSeriesExample

variable (F : Type*) [Field F]

local notation "K" => LaurentSeries F

/-! ### The rank-one norm on `K` -/

/-- The `X`-adic valuation of `K` embeds in `ℝ≥0` (rank at most one), via `2^(-ord)`. -/
noncomputable instance : Valuation.RankLeOne (Valued.v : Valuation K ℤᵐ⁰) where
  hom' := (WithZeroMulInt.toNNReal (by norm_num : (2 : ℝ≥0) ≠ 0)).comp
    (MonoidWithZeroHom.ValueGroup₀.embedding)
  strictMono' := (WithZeroMulInt.toNNReal_strictMono (by norm_num : (1 : ℝ≥0) < 2)).comp
    MonoidWithZeroHom.ValueGroup₀.embedding_strictMono

/-- The `X`-adic valuation of `K` has rank one (nontriviality witnessed by `t`). -/
noncomputable instance : Valuation.RankOne (Valued.v : Valuation K ℤᵐ⁰) :=
  Valuation.RankLeOne.rankOne_of_exists (Valued.v : Valuation K ℤᵐ⁰) ⟨t F, t_ne_zero F, by
    rw [valuation_t]
    intro h
    have h2 := exp_lt_exp.mpr (show (-1 : ℤ) < 0 by omega)
    rw [h, exp_zero] at h2
    exact absurd h2 (lt_irrefl _)⟩

open scoped Valued in
noncomputable instance : NormedField K := Valued.toNormedField K ℤᵐ⁰

/-- `K` with the rank-one norm is an ultrametric space. -/
instance : IsUltrametricDist K := by
  refine IsUltrametricDist.isUltrametricDist_of_isNonarchimedean_norm fun x y => ?_
  rcases le_total ‖x‖ ‖y‖ with h | h
  · refine le_trans ?_ (le_max_right ‖x‖ ‖y‖)
    rw [Valued.toNormedField.norm_le_iff] at h ⊢
    exact le_trans (Valuation.map_add _ _ _) (max_le h le_rfl)
  · refine le_trans ?_ (le_max_left ‖x‖ ‖y‖)
    rw [Valued.toNormedField.norm_le_iff] at h ⊢
    exact le_trans (Valuation.map_add _ _ _) (max_le le_rfl h)

/-! ### The norm/topology bridge for restricted power series -/

section Bridge

variable (R : Type*) [NormedCommRing R] [IsUltrametricDist R] (k : ℕ)

/-- `CommRing` on the (vendored, normed) restricted subring over a commutative base. -/
noncomputable instance (priority := 50) :
    CommRing (MvPowerSeries.Restricted R (fun _ : Fin k => (1 : ℝ))) :=
  inferInstance

/-- Radius-one Gauss restrictedness is the topological restrictedness over a normed
ultrametric base. -/
theorem isRestrictedGauss_one_iff (f : MvPowerSeries (Fin k) R) :
    MvPowerSeries.IsRestrictedGauss (fun _ : Fin k => (1 : ℝ)) f ↔
      MvPowerSeries.IsRestricted f := by
  rw [MvPowerSeries.IsRestrictedGauss, MvPowerSeries.IsRestricted]
  constructor
  · intro h
    rw [tendsto_zero_iff_norm_tendsto_zero]
    refine h.congr fun t => ?_
    simp [Finsupp.prod_pow]
  · intro h
    rw [tendsto_zero_iff_norm_tendsto_zero] at h
    refine h.congr fun t => ?_
    simp [Finsupp.prod_pow]

/-- The two restricted subrings coincide. -/
theorem restrictedGauss_eq_restricted :
    MvPowerSeries.isSubring (R := R) (fun _ : Fin k => (1 : ℝ)) =
      (restrictedMvPowerSeriesSubring k R : Subring (MvPowerSeries (Fin k) R)) := by
  ext f
  show MvPowerSeries.IsRestrictedGauss _ f ↔ MvPowerSeries.IsRestricted f
  exact isRestrictedGauss_one_iff R k f

/-- Transport between the (vendored) Gauss-restricted ring and this project's
topological restricted ring. -/
noncomputable def restrictedGaussEquiv :
    MvPowerSeries.Restricted R (fun _ : Fin k => (1 : ℝ)) ≃+*
      ↥(restrictedMvPowerSeriesSubring k R) :=
  RingEquiv.subringCongr (restrictedGauss_eq_restricted R k)

end Bridge

/-! ### Base change for univariate restricted rings along a norm-preserving equivalence -/

section CongrBase

variable {R S : Type*} [NormedCommRing R] [NormedCommRing S]
  [IsUltrametricDist R] [IsUltrametricDist S]

/-- The coefficientwise ring equivalence of power series rings. -/
noncomputable def psCongr (e : R ≃+* S) : PowerSeries R ≃+* PowerSeries S :=
  (MvPowerSeries.congrRingEquiv Unit e : MvPowerSeries Unit R ≃+* MvPowerSeries Unit S)

theorem psCongr_coeff (e : R ≃+* S) (f : PowerSeries R) (n : ℕ) :
    PowerSeries.coeff n (psCongr e f) = e (PowerSeries.coeff n f) := by
  show MvPowerSeries.coeff _ (MvPowerSeries.map (e : R →+* S) f) = _
  rw [MvPowerSeries.coeff_map]
  rfl

theorem psCongr_image (c : ℝ) (e : R ≃+* S) (he : ∀ x, ‖e x‖ = ‖x‖) :
    (PowerSeries.isSubring (R := R) c).map (psCongr e).toRingHom =
      PowerSeries.isSubring (R := S) c := by
  ext g
  constructor
  · rintro ⟨f, hf, rfl⟩
    show PowerSeries.IsRestricted c ((psCongr e).toRingHom f)
    rw [Restricted.isRestricted_iff_cofinite]
    refine ((Restricted.isRestricted_iff_cofinite c).mp hf).congr fun n => ?_
    rw [show (psCongr e).toRingHom f = psCongr e f from rfl, psCongr_coeff, he]
  · intro hg
    refine ⟨(psCongr e).symm g, ?_, by simp⟩
    show PowerSeries.IsRestricted c ((psCongr e).symm g)
    rw [Restricted.isRestricted_iff_cofinite]
    refine ((Restricted.isRestricted_iff_cofinite c).mp hg).congr fun n => ?_
    have : e (PowerSeries.coeff n ((psCongr e).symm g)) = PowerSeries.coeff n g := by
      rw [← psCongr_coeff e, RingEquiv.apply_symm_apply]
    rw [← he (PowerSeries.coeff n ((psCongr e).symm g)), this]

/-- Base change of the restricted ring along a norm-preserving ring equivalence. -/
noncomputable def congrBase (c : ℝ) (e : R ≃+* S) (he : ∀ x, ‖e x‖ = ‖x‖) :
    PowerSeries.Restricted R c ≃+* PowerSeries.Restricted S c :=
  (RingEquiv.subringMap (s := PowerSeries.isSubring (R := R) c) (psCongr e)).trans
    (RingEquiv.subringCongr (psCongr_image c e he))

theorem congrBase_val (c : ℝ) (e : R ≃+* S) (he : ∀ x, ‖e x‖ = ‖x‖)
    (f : PowerSeries.Restricted R c) :
    ((congrBase c e he f : PowerSeries.Restricted S c)).1 = psCongr e f.1 := rfl

theorem congrBase_norm (c : ℝ) [StrongPos (fun _ : Unit => c)]
    (e : R ≃+* S) (he : ∀ x, ‖e x‖ = ‖x‖)
    (f : PowerSeries.Restricted R c) : ‖congrBase c e he f‖ = ‖f‖ := by
  rw [Restricted.norm_eq, Restricted.norm_eq, congrBase_val]
  rw [PowerSeries.gaussNorm_eq, PowerSeries.gaussNorm_eq]
  refine iSup_congr fun n => ?_
  rw [show (psCongr e f.1).coeff n = e (f.1.coeff n) from psCongr_coeff e f.1 n, he]

end CongrBase

/-! ### The flattening isometry `R⟨X⃗⟩⟨Y⃗⟩ ≃ R⟨X⃗,Y⃗⟩` (constant radius `1`) -/

section Flatten

instance strongPos_one_fin (n : ℕ) : StrongPos (fun _ : Fin n => (1 : ℝ)) :=
  ⟨fun _ => one_pos⟩

instance strongPos_one_unit : StrongPos (fun _ : Unit => (1 : ℝ)) :=
  ⟨fun _ => one_pos⟩

/-- The Gauss-norm ring of restricted series over a normed *commutative* ring is a
normed commutative ring (the vendored stack only registers `NormedRing`). -/
noncomputable instance MvRestricted.isNormedCommRing (S : Type*) {σ : Type*} (c : σ → ℝ)
    [NormedCommRing S] [IsUltrametricDist S] [StrongPos c] :
    NormedCommRing (MvPowerSeries.Restricted S c) :=
  { MvRestricted.isNormedRing S c with
    mul_comm := fun a b => Subtype.ext (mul_comm a.1 b.1) }

/-- `MvRestricted.finSuccEquiv` retyped with syntactically uniform radius functions
(`fun _ => 1` everywhere, no `Fin.tail`). -/
noncomputable def finSuccOne (S : Type*) [NormedCommRing S] [IsUltrametricDist S] (m : ℕ) :
    MvPowerSeries.Restricted S (fun _ : Fin (m + 1) => (1 : ℝ)) ≃+*
      PowerSeries.Restricted
        (MvPowerSeries.Restricted S (fun _ : Fin m => (1 : ℝ))) (1 : ℝ) :=
  MvRestricted.finSuccEquiv S m (fun _ : Fin (m + 1) => (1 : ℝ))

theorem finSuccOne_norm (S : Type*) [NormedCommRing S] [IsUltrametricDist S] (m : ℕ)
    (f : MvPowerSeries.Restricted S (fun _ : Fin (m + 1) => (1 : ℝ))) :
    ‖finSuccOne S m f‖ = ‖f‖ :=
  (MvRestricted.finSuccIsometry' S (n := m)
    (c := fun _ : Fin (m + 1) => (1 : ℝ))).norm_map (x := f)

theorem finSuccOne_symm_norm (S : Type*) [NormedCommRing S] [IsUltrametricDist S] (m : ℕ)
    (g : PowerSeries.Restricted
      (MvPowerSeries.Restricted S (fun _ : Fin m => (1 : ℝ))) (1 : ℝ)) :
    ‖(finSuccOne S m).symm g‖ = ‖g‖ := by
  conv_rhs => rw [← RingEquiv.apply_symm_apply (finSuccOne S m) g]
  rw [finSuccOne_norm]

attribute [local irreducible] finSuccOne congrBase psCongr

/-- Gauss norm of a zero-variable power series is the norm of its only coefficient. -/
theorem gaussNorm_fin_zero {S : Type*} [NormedRing S] (g : MvPowerSeries (Fin 0) S) :
    MvPowerSeries.gaussNorm (norm : S → ℝ) (fun _ : Fin 0 => (1 : ℝ)) g =
      ‖MvPowerSeries.coeff (0 : Fin 0 →₀ ℕ) g‖ := by
  show (⨆ t : Fin 0 →₀ ℕ,
    ‖MvPowerSeries.coeff t g‖ * t.prod ((fun _ : Fin 0 => (1 : ℝ)) · ^ ·)) = _
  rw [ciSup_subsingleton (0 : Fin 0 →₀ ℕ), Finsupp.prod_zero_index, mul_one]

variable (R : Type*) [NormedCommRing R] [IsUltrametricDist R]

/-- **Flattening** (generic form): if `B` is norm-isomorphic to one-variable restricted
series over `R`, then `m`-variable restricted series over `B` are `(m+1)`-variable
restricted series over `R`, norm-preservingly.  Stated over an abstract normed ring `B`
so that all defeq checks happen over a free variable (the concrete instantiation
`B := MvPowerSeries.Restricted R _` makes elaboration explode). -/
theorem exists_flatten' (B : Type*) [NormedCommRing B] [IsUltrametricDist B]
    (HB : B ≃+* MvPowerSeries.Restricted R (fun _ : Fin 1 => (1 : ℝ)))
    (hHB : ∀ x, ‖HB x‖ = ‖x‖) (m : ℕ) :
    ∃ e : (MvPowerSeries.Restricted B (fun _ : Fin m => (1 : ℝ)) ≃+*
      MvPowerSeries.Restricted R (fun _ : Fin (m + 1) => (1 : ℝ))),
      ∀ f, ‖e f‖ = ‖f‖ := by
  induction m with
  | zero =>
    refine ⟨(restrictedFinZeroEquiv B (fun _ : Fin 0 => (1 : ℝ))).trans HB, fun f => ?_⟩
    rw [RingEquiv.trans_apply, hHB]
    exact (restrictedFinZeroRingHomIsometric B (fun _ : Fin 0 => (1 : ℝ))).norm_map (x := f)
  | succ m ih =>
    obtain ⟨eIH, hIH⟩ := ih
    refine ⟨(finSuccOne B m).trans
      ((congrBase 1 eIH hIH).trans (finSuccOne R (m + 1)).symm), fun f => ?_⟩
    rw [RingEquiv.trans_apply, RingEquiv.trans_apply, finSuccOne_symm_norm,
      congrBase_norm, finSuccOne_norm]

end Flatten

/-! ### The disc ring `D = K⟨Y⟩` and its strong noetherianity -/

section Disc

/-- The ring of the closed unit disc over `K = F((X))`: one-variable power series over `K`
whose coefficients tend to `0`, normed by the Gauss (sup) norm. -/
abbrev D : Type _ :=
  MvPowerSeries.Restricted (LaurentSeries F) (fun _ : Fin 1 => (1 : ℝ))

/-- Any normed ring with ultrametric distance is a nonarchimedean topological ring. -/
instance nonarchimedeanRing_ofUltrametric (S : Type*) [NormedRing S] [IsUltrametricDist S] :
    NonarchimedeanRing S where
  is_nonarchimedean := NonarchimedeanAddGroup.is_nonarchimedean

/-- The Gauss norm of a constant series is the norm of the constant. -/
theorem gaussNorm_C_norm {S : Type*} [NormedRing S] {σ : Type*} (c : σ → ℝ) (a : S) :
    MvPowerSeries.gaussNorm (norm : S → ℝ) c (MvPowerSeries.C a) = ‖a‖ := by
  classical
  have hpt : ∀ t : σ →₀ ℕ, ‖MvPowerSeries.coeff t (MvPowerSeries.C (σ := σ) a)‖ *
      t.prod (c · ^ ·) ≤ ‖a‖ := by
    intro t
    by_cases ht : t = 0
    · subst ht
      simp [MvPowerSeries.coeff_zero_C]
    · rw [MvPowerSeries.coeff_C, if_neg ht, norm_zero, zero_mul]
      exact norm_nonneg a
  have hbd : MvPowerSeries.HasGaussNorm (norm : S → ℝ) c (MvPowerSeries.C a) := by
    refine ⟨‖a‖, ?_⟩
    rintro - ⟨t, rfl⟩
    exact hpt t
  refine le_antisymm (Real.iSup_le hpt (norm_nonneg a)) ?_
  simpa [MvPowerSeries.coeff_zero_C] using
    MvPowerSeries.le_gaussNorm (norm : S → ℝ) c (MvPowerSeries.C a) hbd 0

/-- The constant embedding `K →+* D`. -/
noncomputable def constD : LaurentSeries F →+* D F where
  toFun a := ⟨MvPowerSeries.C a, MvPowerSeries.isRestrictedGauss_C _ a⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' a b := Subtype.ext (map_mul _ a b)
  map_zero' := Subtype.ext (map_zero _)
  map_add' a b := Subtype.ext (map_add _ a b)

theorem norm_constD (a : LaurentSeries F) : ‖constD F a‖ = ‖a‖ := by
  rw [MvRestricted.norm_eq]
  exact gaussNorm_C_norm _ a

/-- The Gauss norm on `D` is multiplicative (the base is a nonarchimedean field). -/
theorem normD_mul (f g : D F) : ‖f * g‖ = ‖f‖ * ‖g‖ :=
  (MvRestricted.isAbsoluteValue (R := LaurentSeries F)
    (c := fun _ : Fin 1 => (1 : ℝ)) norm_mul).abv_mul' f g

theorem normD_one : ‖(1 : D F)‖ = 1 := by
  rw [← map_one (constD F), norm_constD, norm_one]

theorem normD_pow (f : D F) (n : ℕ) : ‖f ^ n‖ = ‖f‖ ^ n := by
  induction n with
  | zero => simpa using normD_one F
  | succ n ih => rw [pow_succ, pow_succ, normD_mul, ih]

/-- The closed unit ball `𝒪_D = {‖f‖ ≤ 1}` — the Gauss-norm integers of `D`. -/
def OD : Subring (D F) where
  carrier := {f | ‖f‖ ≤ 1}
  one_mem' := le_of_eq (normD_one F)
  mul_mem' := fun {a b} ha hb =>
    le_trans (norm_mul_le a b) (mul_le_one₀ ha (norm_nonneg b) hb)
  zero_mem' := by simp
  add_mem' := fun {a b} ha hb =>
    le_trans (IsUltrametricDist.norm_add_le_max a b) (max_le ha hb)
  neg_mem' := fun {a} ha => by
    show ‖-a‖ ≤ 1
    rwa [norm_neg]

theorem mem_OD_iff (f : D F) : f ∈ OD F ↔ ‖f‖ ≤ 1 := Iff.rfl

/-- The pseudouniformizer of `D`: the constant `t`. -/
noncomputable def tD : D F := constD F (t F)

theorem norm_tD_lt_one : ‖tD F‖ < 1 := by
  rw [tD, norm_constD, Valued.toNormedField.norm_lt_one_iff, valuation_t, ← exp_zero,
    exp_lt_exp]
  omega

theorem norm_tD_pos : 0 < ‖tD F‖ := by
  rw [tD, norm_constD, norm_pos_iff]
  exact t_ne_zero F

theorem isUnit_tD : IsUnit (tD F) :=
  isUnit_iff_exists_inv.mpr ⟨constD F (t F)⁻¹, by
    rw [tD, ← map_mul, mul_inv_cancel₀ (t_ne_zero F), map_one]⟩

theorem isTopologicallyNilpotent_tD : IsTopologicallyNilpotent (tD F) := by
  rw [IsTopologicallyNilpotent, tendsto_zero_iff_norm_tendsto_zero]
  simp_rw [normD_pow]
  exact tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg _) (norm_tD_lt_one F)

/-- `tD` as an element of `𝒪_D`. -/
noncomputable def tD₀ : OD F := ⟨tD F, le_of_lt (norm_tD_lt_one F)⟩

theorem norm_tD_inv_mul : ‖constD F (t F)⁻¹‖ * ‖tD F‖ = 1 := by
  rw [← normD_mul, tD, ← map_mul, inv_mul_cancel₀ (t_ne_zero F), map_one, normD_one]

/-- Divisibility by `tDⁿ` in the unit ball is the Gauss-norm bound `‖·‖ ≤ ‖tD‖ⁿ`. -/
theorem tD₀_pow_dvd_iff (n : ℕ) (x : OD F) :
    (tD₀ F) ^ n ∣ x ↔ ‖(x : D F)‖ ≤ ‖tD F‖ ^ n := by
  constructor
  · rintro ⟨y, rfl⟩
    push_cast
    rw [normD_mul, normD_pow]
    calc ‖tD F‖ ^ n * ‖(y : D F)‖ ≤ ‖tD F‖ ^ n * 1 := by
          gcongr
          exact y.2
      _ = ‖tD F‖ ^ n := mul_one _
  · intro hx
    have hy : ‖(constD F (t F)⁻¹) ^ n * (x : D F)‖ ≤ 1 := by
      rw [normD_mul, normD_pow]
      calc ‖constD F (t F)⁻¹‖ ^ n * ‖(x : D F)‖
          ≤ ‖constD F (t F)⁻¹‖ ^ n * ‖tD F‖ ^ n :=
            mul_le_mul_of_nonneg_left hx (pow_nonneg (norm_nonneg _) n)
        _ = (‖constD F (t F)⁻¹‖ * ‖tD F‖) ^ n := (mul_pow _ _ n).symm
        _ = 1 := by rw [norm_tD_inv_mul, one_pow]
    refine ⟨⟨(constD F (t F)⁻¹) ^ n * (x : D F), hy⟩, ?_⟩
    apply Subtype.ext
    push_cast
    rw [show ((tD₀ F : OD F) : D F) = tD F from rfl]
    rw [show (tD F) ^ n * ((constD F (t F)⁻¹) ^ n * (x : D F)) =
      ((tD F) * constD F (t F)⁻¹) ^ n * (x : D F) by ring]
    rw [tD, ← map_mul, mul_inv_cancel₀ (t_ne_zero F), map_one, one_pow, one_mul]

/-- Membership in `(tD)ⁿ ⊆ 𝒪_D` is the norm bound `‖·‖ ≤ ‖tD‖ⁿ`. -/
theorem mem_span_tD₀_pow_iff (n : ℕ) (x : OD F) :
    x ∈ (Ideal.span {tD₀ F} ^ n : Ideal (OD F)) ↔ ‖(x : D F)‖ ≤ ‖tD F‖ ^ n := by
  rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton, tD₀_pow_dvd_iff]

/-- The closed unit ball is open (ultrametric). -/
theorem isOpen_OD : IsOpen ((OD F : Set (D F))) := by
  rw [isOpen_iff_mem_nhds]
  intro x hx
  rw [Metric.mem_nhds_iff]
  refine ⟨1, one_pos, fun y hy => ?_⟩
  rw [Metric.mem_ball, dist_eq_norm] at hy
  have hyx : y = (y - x) + x := by ring
  rw [SetLike.mem_coe, mem_OD_iff, hyx]
  exact le_trans (IsUltrametricDist.norm_add_le_max _ _) (max_le (le_of_lt hy) hx)

/-- The closed unit ball is a bounded subset of `D`. -/
theorem isBounded_OD : TopologicalRing.IsBounded ((OD F : Subring (D F)) : Set (D F)) := by
  intro U hU
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hU
  refine ⟨Metric.ball 0 ε, Metric.ball_mem_nhds 0 hε, ?_⟩
  rintro z ⟨s, hs, y, hy, rfl⟩
  rw [Metric.mem_ball, dist_zero_right] at hy
  refine hball ?_
  rw [Metric.mem_ball, dist_zero_right]
  calc ‖s * y‖ ≤ ‖s‖ * ‖y‖ := norm_mul_le s y
    _ ≤ 1 * ‖y‖ := by
        gcongr
        exact hs
    _ = ‖y‖ := one_mul _
    _ < ε := hy

/-- The power-bounded subring of `D` contains `𝒪_D`. -/
theorem OD_subset_powerBounded :
    ((OD F : Subring (D F)) : Set (D F)) ⊆ TopologicalRing.powerBoundedSubring (D F) := by
  intro x hx
  refine (isBounded_OD F).subset ?_
  rintro - ⟨k, rfl⟩
  rw [SetLike.mem_coe, mem_OD_iff, normD_pow]
  exact pow_le_one₀ (norm_nonneg _) hx

/-- Power-bounded elements of `D` lie in the unit ball (multiplicativity of the norm). -/
theorem norm_le_one_of_isPowerBounded {a : D F}
    (h : TopologicalRing.IsPowerBounded a) : ‖a‖ ≤ 1 := by
  by_contra hlt
  push_neg at hlt
  obtain ⟨V, hV, hVsub⟩ := h (Metric.ball 0 1) (Metric.ball_mem_nhds 0 one_pos)
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp hV
  obtain ⟨m, hm⟩ := exists_pow_lt_of_lt_one hδ (norm_tD_lt_one F)
  have hwV : (tD F) ^ m ∈ V := by
    refine hball ?_
    rw [Metric.mem_ball, dist_zero_right, normD_pow]
    exact hm
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (((‖tD F‖) ^ m)⁻¹) hlt
  have hmem : a ^ n * (tD F) ^ m ∈ Metric.ball (0 : D F) 1 :=
    hVsub ⟨a ^ n, ⟨n, rfl⟩, (tD F) ^ m, hwV, rfl⟩
  rw [Metric.mem_ball, dist_zero_right, normD_mul, normD_pow, normD_pow] at hmem
  have hge : (1 : ℝ) ≤ ‖a‖ ^ n * ‖tD F‖ ^ m := by
    have hpos : (0 : ℝ) < ‖tD F‖ ^ m := pow_pos (norm_tD_pos F) m
    calc (1 : ℝ) = (‖tD F‖ ^ m)⁻¹ * ‖tD F‖ ^ m := (inv_mul_cancel₀ (ne_of_gt hpos)).symm
      _ ≤ ‖a‖ ^ n * ‖tD F‖ ^ m := by gcongr
  exact absurd hmem (not_lt.mpr hge)

-- v4.33: the subtype algebra for `OD F ≤ D F` is no longer found by instance synthesis
-- (cf. the wave-4 `letI` hoists in HuberLocLift/FaithfulLocLift); register it locally for
-- the `IsIntegral` statement below and its `IsRingOfIntegralElements` consumer.
noncomputable local instance : Algebra ↥(OD F) (D F) := (OD F).subtype.toAlgebra

/-- `𝒪_D` is integrally closed in `D` (via power-boundedness, Wedhorn Prop 5.30(4)). -/
theorem OD_isIntegrallyClosed (a : D F) (ha : IsIntegral (OD F) a) : a ∈ OD F :=
  norm_le_one_of_isPowerBounded F ((isBounded_OD F).isPowerBounded_of_isIntegral ha)

/-- The pair of definition `(𝒪_D, (tD))` for `D`: the `tD`-adic topology on the unit ball
is the Gauss-norm topology. -/
noncomputable def podD : PairOfDefinition (D F) where
  A₀ := OD F
  I := Ideal.span {tD₀ F}
  isOpen := isOpen_OD F
  fg := ⟨{tD₀ F}, by simp⟩
  isAdic := by
    rw [isAdic_iff]
    refine ⟨fun n => ?_, fun s hs => ?_⟩
    · rw [isOpen_iff_mem_nhds]
      intro x hx
      rw [SetLike.mem_coe, mem_span_tD₀_pow_iff] at hx
      rw [mem_nhds_subtype]
      refine ⟨Metric.ball (x : D F) (‖tD F‖ ^ n),
        Metric.ball_mem_nhds _ (pow_pos (norm_tD_pos F) n), ?_⟩
      intro y hy
      rw [Set.mem_preimage, Metric.mem_ball, dist_eq_norm] at hy
      rw [SetLike.mem_coe, mem_span_tD₀_pow_iff]
      have hdecomp : ((y : D F)) = (((y : D F)) - ((x : D F))) + ((x : D F)) := by ring
      rw [hdecomp]
      exact le_trans (IsUltrametricDist.norm_add_le_max _ _) (max_le (le_of_lt hy) hx)
    · rw [mem_nhds_subtype] at hs
      obtain ⟨U, hU, hUs⟩ := hs
      obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp (by simpa using hU)
      obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hε (norm_tD_lt_one F)
      refine ⟨n, fun x hx => hUs ?_⟩
      rw [SetLike.mem_coe, mem_span_tD₀_pow_iff] at hx
      rw [Set.mem_preimage]
      refine hball ?_
      rw [Metric.mem_ball, dist_zero_right]
      exact lt_of_le_of_lt hx hn

instance : IsHuberRing (D F) := ⟨⟨podD F⟩⟩

instance : IsTateRing (D F) :=
  ⟨⟨(isUnit_tD F).unit, by simpa using isTopologicallyNilpotent_tD F⟩⟩

instance : ValuationSpectrum.PlusSubring (D F) := ⟨OD F⟩

instance : IsRingOfIntegralElements
    ((ValuationSpectrum.ringPlus (D F) : Subring (D F))) where
  isOpen := isOpen_OD F
  isIntegrallyClosed := OD_isIntegrallyClosed F
  subset_powerBounded := OD_subset_powerBounded F

instance : @CompleteSpace (D F) (IsTopologicalAddGroup.rightUniformSpace (D F)) := by
  haveI : IsUniformAddGroup (D F) := SeminormedAddCommGroup.to_isUniformAddGroup
  rw [IsUniformAddGroup.rightUniformSpace_eq]
  infer_instance

/-- **The disc ring is strongly noetherian**: `D⟨X₁,…,Xₘ⟩ ≅ K⟨Y,X₁,…,Xₘ⟩` by the flattening
isometry, and the right side is noetherian because `K` is strongly noetherian. -/
instance : IsStronglyNoetherian (D F) where
  isNoetherianRing_restricted := fun m => by
    obtain ⟨e₂, -⟩ := exists_flatten' (LaurentSeries F) (D F) (RingEquiv.refl _)
      (fun _ => rfl) m
    have h : IsNoetherianRing
        (restrictedMvPowerSeriesSubring (m + 1) (LaurentSeries F)) :=
      IsStronglyNoetherian.isNoetherianRing_restricted (m + 1)
    exact isNoetherianRing_of_surjective _ _
      (((restrictedGaussEquiv (LaurentSeries F) (m + 1)).symm.trans e₂.symm).trans
        (restrictedGaussEquiv (D F) m)).toRingHom
      (((restrictedGaussEquiv (LaurentSeries F) (m + 1)).symm.trans e₂.symm).trans
        (restrictedGaussEquiv (D F) m)).surjective

/-- `K⟨Y⟩` is a noetherian ring (the `k = 0` instance of strong noetherianity). -/
instance : IsNoetherianRing (D F) := IsStronglyNoetherian.isNoetherianRing (D F)

/-! ### The payoff: the closed unit disc is sheafy -/

/-- **The closed unit disc over `F((X))` is sheafy**: the structure presheaf of
`Spa(K⟨Y⟩, 𝒪_D)` satisfies the sheaf condition on rational covers — Wedhorn
Theorem 8.28(b) applied to the strongly noetherian complete Tate ring `K⟨Y⟩`. -/
theorem isSheafy_unitDisc : ValuationSpectrum.IsSheafy (D F) :=
  ValuationSpectrum.isSheafy_of_stronglyNoetherian_828b

end Disc

end UnitDiscExample
