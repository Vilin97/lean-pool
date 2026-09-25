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
public import LeanPool.UniformSheafyTateDomains.AdicSpaces.WP.HeadReducedMaximal
public import LeanPool.UniformSheafyTateDomains.AdicSpaces.WP.KappaResidue
public import LeanPool.UniformSheafyTateDomains.AdicSpaces.FJP.SpectralExtension
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import LeanPool.UniformSheafyTateDomains.AdicSpaces.WedhornBanachTheorem

/-!
# The trivial special fibre of the graph model (BETA)

([hrw-decomposition] BETA, adjudicated route R1′.)  This file builds the
bricks for the level-one bijectivity `A/𝔭 ≅ Q/𝔭Q` of the graph model at a
maximal contraction: closedness of ideals in normed noetherian Tate rings
(the faithful Wedhorn 6.17 engine), the residue-field package, the bounded
evaluation, and the closed-plus-dense argument.
-/

@[expose] public section

@[expose] public section

namespace WeightedParity

open FiniteJetOver

/-- **Wedhorn 6.17, faithful, normed form**: every ideal of a complete
normed noetherian Tate ring is closed. -/
theorem isClosed_ideal_of_noetherian_normed {C : Type*} [NormedCommRing C]
    [CompleteSpace C] [IsTateRing C] [IsNoetherianRing C]
    (J : Ideal C) : IsClosed (J : Set C) := by
  haveI : ContinuousSMul C C := ⟨continuous_mul⟩
  refine ValuationSpectrum.fg_topologicalClosure_isClosed J ?_
  have hfg : (Submodule.topologicalClosure J).FG :=
    IsNoetherian.noetherian _
  exact Module.Finite.iff_fg.mpr hfg

/-- A set of uniformly bounded norm is bounded. -/
theorem isBounded_of_forall_norm_le {L : Type*} [NormedCommRing L] {C : ℝ}
    {S : Set L} (hS : ∀ y ∈ S, ‖y‖ ≤ C) : TopologicalRing.IsBounded S := by
  intro U hU
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hU
  set C' : ℝ := max C 1 with hC'
  have hC'pos : 0 < C' := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  refine ⟨Metric.ball 0 (ε / C'), Metric.ball_mem_nhds 0 (by positivity), ?_⟩
  rintro z ⟨y, hy, v, hv, rfl⟩
  refine hball ?_
  rw [Metric.mem_ball, dist_zero_right] at hv ⊢
  calc ‖y * v‖ ≤ ‖y‖ * ‖v‖ := norm_mul_le y v
    _ ≤ C' * ‖v‖ := mul_le_mul_of_nonneg_right
        (le_trans (hS y hy) (le_max_left _ _)) (norm_nonneg v)
    _ < C' * (ε / C') := by
        exact mul_lt_mul_of_pos_left hv hC'pos
    _ = ε := mul_div_cancel₀ _ (ne_of_gt hC'pos)

/-- Bounded sets push forward along continuous open ring homomorphisms. -/
theorem isBounded_image_of_isOpenMap {A B : Type*}
    [CommRing A] [TopologicalSpace A] [CommRing B] [TopologicalSpace B]
    (φ : A →+* B) (hcont : Continuous φ) (hopen : IsOpenMap φ)
    {S : Set A} (hS : TopologicalRing.IsBounded S) :
    TopologicalRing.IsBounded (⇑φ '' S) := by
  intro U' hU'
  have hpre : φ ⁻¹' U' ∈ nhds (0 : A) := by
    have h0 : φ 0 = 0 := map_zero φ
    exact ContinuousAt.preimage_mem_nhds hcont.continuousAt (h0 ▸ hU')
  obtain ⟨V, hV, hSV⟩ := hS (φ ⁻¹' U') hpre
  refine ⟨⇑φ '' V, ?_, ?_⟩
  · have h1 := hopen.image_mem_nhds hV
    rwa [map_zero φ] at h1
  · rintro z hz
    obtain ⟨y, ⟨x, hxS, rfl⟩, w, ⟨v, hvV, rfl⟩, rfl⟩ := Set.mem_mul.mp hz
    have h2 : x * v ∈ φ ⁻¹' U' := hSV (Set.mul_mem_mul hxS hvV)
    rw [← map_mul]
    exact h2

/-- Power-bounded elements push forward along continuous open ring
homomorphisms. -/
theorem isPowerBounded_image_of_isOpenMap {A B : Type*}
    [CommRing A] [TopologicalSpace A] [CommRing B] [TopologicalSpace B]
    (φ : A →+* B) (hcont : Continuous φ) (hopen : IsOpenMap φ)
    {x : A} (hx : TopologicalRing.IsPowerBounded x) :
    TopologicalRing.IsPowerBounded (φ x) := by
  have hrange : Set.range ((φ x) ^ · : ℕ → B) =
      ⇑φ '' Set.range (x ^ · : ℕ → A) := by
    ext y
    constructor
    · rintro ⟨n, rfl⟩
      exact ⟨x ^ n, ⟨n, rfl⟩, map_pow φ x n⟩
    · rintro ⟨-, ⟨n, rfl⟩, rfl⟩
      exact ⟨n, (map_pow φ x n).symm⟩
  show TopologicalRing.IsBounded (Set.range ((φ x) ^ · : ℕ → B))
  rw [hrange]
  exact isBounded_image_of_isOpenMap φ hcont hopen hx

section KappaBridge

open FiniteJet.SpectralExtension

open scoped NormedField Valued

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
  [CompleteSpace K]
variable (w : ℕ → ℕ) (N : ℕ)

/-- **BETA brick (ii), the continuity bridge**: the residue map of the head
onto the spectral residue field `κ(𝔭)` is continuous.  (Factor through the
quotient topology: the projection is continuous, and the identity onto the
spectral side is `K`-linear from a finite-dimensional Hausdorff space.) -/
theorem continuous_mkKappaP (ϖ : Uniformizer K)
    [hdvr : IsDiscreteValuationRing 𝒪[K]]
    (hK₀ : IsNoetherianRing (FiniteJet.unitBall K))
    (𝔭 : Ideal (WPHead K w N)) [h𝔭 : 𝔭.IsMaximal] :
    haveI : FiniteDimensional K (KappaP w N 𝔭) :=
      module_finite_residue_head w N ϖ hK₀ 𝔭
    letI := extNormedField K (KappaP w N 𝔭)
    Continuous (mkKappaP w N 𝔭) := by
  haveI hfd : FiniteDimensional K (KappaP w N 𝔭) :=
    module_finite_residue_head w N ϖ hK₀ 𝔭
  letI nfκ : NormedField (KappaP w N 𝔭) := extNormedField K (KappaP w N 𝔭)
  classical
  haveI hNoeth : IsNoetherianRing (WPHead K w N) :=
    isNoetherianRing_WPHead w N ϖ hK₀
  haveI hclosed : IsClosed ((𝔭 : Ideal (WPHead K w N)) : Set (WPHead K w N)) :=
    isClosed_ideal_of_noetherian_normed 𝔭
  letI : Algebra K (WPHead K w N ⧸ 𝔭) :=
    ((Ideal.Quotient.mk 𝔭).comp (constHead K w N)).toAlgebra
  have hconst : Continuous (⇑(constHead K w N)) :=
    AddMonoidHomClass.continuous_of_bound (constHead K w N) 1
      fun c => by rw [one_mul]; exact norm_constHead_le w N c
  haveI hsmulQ : ContinuousSMul K (WPHead K w N ⧸ 𝔭) := by
    refine ⟨?_⟩
    have halg : Continuous (fun c : K =>
        ((Ideal.Quotient.mk 𝔭) (constHead K w N c) : WPHead K w N ⧸ 𝔭)) :=
      continuous_quot_mk.comp hconst
    have hmul : (fun p : K × (WPHead K w N ⧸ 𝔭) => p.1 • p.2) =
        fun p : K × (WPHead K w N ⧸ 𝔭) =>
          (Ideal.Quotient.mk 𝔭) (constHead K w N p.1) * p.2 := by
      funext p
      exact Algebra.smul_def p.1 p.2
    rw [hmul]
    exact (halg.comp continuous_fst).mul continuous_snd
  haveI hug : IsUniformAddGroup (KappaP w N 𝔭) :=
    SeminormedAddCommGroup.to_isUniformAddGroup
  haveI htag : IsTopologicalAddGroup (KappaP w N 𝔭) :=
    SeminormedAddCommGroup.toIsTopologicalAddGroup
  haveI hcs : ContinuousSMul K (KappaP w N 𝔭) :=
    extContinuousSMul K (KappaP w N 𝔭)
  haveI hfd' : FiniteDimensional K (WPHead K w N ⧸ 𝔭) := hfd
  set ι : (WPHead K w N ⧸ 𝔭) →ₗ[K] KappaP w N 𝔭 :=
    { toFun := fun x => x
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl } with hιdef
  have hbridge : Continuous ι := LinearMap.continuous_of_finiteDimensional ι
  have hmk : Continuous (fun a : WPHead K w N =>
      ((Ideal.Quotient.mk 𝔭) a : WPHead K w N ⧸ 𝔭)) := continuous_quot_mk
  exact hbridge.comp hmk

end KappaBridge

section BPoint

open ValuationSpectrum FiniteJet.SpectralExtension FiniteJet.GraphKoszul

open scoped NormedField Valued

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
  [CompleteSpace K]
variable {w : ℕ → ℕ} {N : ℕ}

/-- **The evaluation point** of a head datum at a maximal ideal of the head:
the residue `bᵢ = t̄ᵢ / s̄` of the `i`-th graph coordinate. -/
noncomputable def bPoint (DH : RationalLocData (WPHead K w N))
    (𝔭 : Ideal (WPHead K w N)) [h𝔭 : 𝔭.IsMaximal] (i : Fin DH.T.card) :
    KappaP w N 𝔭 :=
  mkKappaP w N 𝔭 ((datumEnum DH i : ↥DH.T) : WPHead K w N) *
    (mkKappaP w N 𝔭 DH.s)⁻¹

theorem bPoint_mul_s (DH : RationalLocData (WPHead K w N))
    (𝔭 : Ideal (WPHead K w N)) [h𝔭 : 𝔭.IsMaximal] (hs : DH.s ∉ 𝔭)
    (i : Fin DH.T.card) :
    bPoint DH 𝔭 i * mkKappaP w N 𝔭 DH.s =
      mkKappaP w N 𝔭 ((datumEnum DH i : ↥DH.T) : WPHead K w N) := by
  have hne : mkKappaP w N 𝔭 DH.s ≠ 0 := by
    show (Ideal.Quotient.mk 𝔭 DH.s : WPHead K w N ⧸ 𝔭) ≠ 0
    rw [Ne, Ideal.Quotient.eq_zero_iff_mem]
    exact hs
  rw [bPoint, mul_assoc, inv_mul_cancel₀ hne, mul_one]

/-- **BETA brick (iii)**: the evaluation point is power-bounded in the spectral
residue field.  The graph variables are power-bounded in the graph model, hence
in its residue field at `𝔮`; the residue field of the head at the contraction
embeds there, and a continuous injection out of a finite-dimensional normed
space is anti-Lipschitz, so the bound reflects. -/
theorem isBounded_range_bPoint_pow (ϖ : Uniformizer K)
    [hdvr : IsDiscreteValuationRing 𝒪[K]]
    (hK₀ : IsNoetherianRing (FiniteJet.unitBall K))
    (DH : RationalLocData (WPHead K w N)) (hDH : DH.IsRational)
    (𝔮 : Ideal (QHead DH)) (h𝔮 : 𝔮.IsMaximal) (i : Fin DH.T.card) :
    haveI h𝔭 : (𝔮.comap (headToQ DH)).IsMaximal :=
      comap_headToQ_isMaximal w N ϖ hK₀ DH hDH 𝔮 h𝔮
    haveI : FiniteDimensional K (KappaP w N (𝔮.comap (headToQ DH))) :=
      module_finite_residue_head w N ϖ hK₀ (𝔮.comap (headToQ DH))
    letI := extNormedField K (KappaP w N (𝔮.comap (headToQ DH)))
    TopologicalRing.IsBounded
      (Set.range (bPoint DH (𝔮.comap (headToQ DH)) i ^ · : ℕ → _)) := by
  haveI h𝔭 : (𝔮.comap (headToQ DH)).IsMaximal :=
    comap_headToQ_isMaximal w N ϖ hK₀ DH hDH 𝔮 h𝔮
  haveI hfd : FiniteDimensional K (KappaP w N (𝔮.comap (headToQ DH))) :=
    module_finite_residue_head w N ϖ hK₀ (𝔮.comap (headToQ DH))
  letI nfκ : NormedField (KappaP w N (𝔮.comap (headToQ DH))) :=
    extNormedField K (KappaP w N (𝔮.comap (headToQ DH)))
  letI nsκ : NormedSpace K (KappaP w N (𝔮.comap (headToQ DH))) :=
    extNormedSpace K (KappaP w N (𝔮.comap (headToQ DH)))
  haveI hfd2 : FiniteDimensional K (KappaP w N (𝔮.comap (headToQ DH))) := hfd
  haveI hprime : 𝔮.IsPrime := h𝔮.isPrime
  haveI hnt : Nontrivial (QHead DH ⧸ 𝔮) := by
    letI := Ideal.Quotient.field 𝔮
    infer_instance
  -- the head's residue map into the residue ring of the graph model at `𝔮`
  set ρ : WPHead K w N →+* QHead DH ⧸ 𝔮 :=
    (Ideal.Quotient.mk 𝔮).comp (headToQ DH) with hρdef
  have hkill : ∀ a ∈ 𝔮.comap (headToQ DH), ρ a = 0 := by
    intro a ha
    show Ideal.Quotient.mk 𝔮 (headToQ DH a) = 0
    rw [Ideal.Quotient.eq_zero_iff_mem]
    exact ha
  set ι : KappaP w N (𝔮.comap (headToQ DH)) →+* QHead DH ⧸ 𝔮 :=
    Ideal.Quotient.lift _ ρ hkill with hιdef
  have hιmk : ∀ a : WPHead K w N,
      ι (mkKappaP w N (𝔮.comap (headToQ DH)) a) = ρ a := fun _ => rfl
  have hinj : Function.Injective ι := ι.injective
  -- the `K`-structures on the target
  letI algL : Algebra K (QHead DH ⧸ 𝔮) :=
    (ρ.comp (constHead K w N)).toAlgebra
  have hnormconst : ∀ c : K, ‖ρ (constHead K w N c)‖ ≤ ‖c‖ := by
    intro c
    refine le_trans (Ideal.Quotient.norm_mk_le _ _) ?_
    show ‖headToQ DH (constHead K w N c)‖ ≤ ‖c‖
    refine le_trans (Ideal.Quotient.norm_mk_le _ _) ?_
    show ‖(polyToP (MvPolynomial.C (constHead K w N c)) :
      P (WPHead K w N) DH.T.card)‖ ≤ ‖c‖
    have h1 := norm_tP_mul (E := WPHead K w N) (m := DH.T.card)
      (constHead K w N c) (fun x => norm_wphead_mul _ x) 1
    rw [mul_one, norm_one, mul_one, norm_constHead] at h1
    exact le_of_eq h1
  have hM : ∀ (c : K) (x : QHead DH ⧸ 𝔮),
      ‖algebraMap K (QHead DH ⧸ 𝔮) c * x‖ ≤ ‖c‖ * ‖x‖ := fun c x =>
    le_trans (norm_mul_le _ _)
      (mul_le_mul_of_nonneg_right (hnormconst c) (norm_nonneg x))
  have hfc : ∀ c : K,
      ι (algebraMap K (KappaP w N (𝔮.comap (headToQ DH))) c) =
        algebraMap K (QHead DH ⧸ 𝔮) c := fun _ => rfl
  obtain ⟨C, hCpos, hbound⟩ :=
    @exists_norm_le_mul_norm_map K _ _ _
      (KappaP w N (𝔮.comap (headToQ DH))) _ _ hfd
      (QHead DH ⧸ 𝔮) _ algL hM ι hfc hinj
  -- the evaluation point maps to the graph variable
  have hs : DH.s ∉ 𝔮.comap (headToQ DH) :=
    s_notMem_comap_headToQ ϖ hK₀ DH hDH 𝔮 hprime
  have h2 : ι (bPoint DH (𝔮.comap (headToQ DH)) i) * ρ DH.s =
      ρ ((datumEnum DH i : ↥DH.T) : WPHead K w N) := by
    rw [← hιmk, ← hιmk, ← map_mul, bPoint_mul_s DH _ hs i]
  have hrel : ρ ((datumEnum DH i : ↥DH.T) : WPHead K w N) =
      ρ DH.s * Ideal.Quotient.mk 𝔮 (qX DH i) := by
    show Ideal.Quotient.mk 𝔮 (headToQ DH _) = _
    rw [show headToQ DH ((datumEnum DH i : ↥DH.T) : WPHead K w N) =
      headConst DH ((datumEnum DH i : ↥DH.T) : WPHead K w N) from rfl,
      headConst_datumEnum DH i, map_mul]
    rfl
  have hρs : ρ DH.s ≠ 0 := by
    rw [← hιmk]
    refine fun hzero => ?_
    have hmk : mkKappaP w N (𝔮.comap (headToQ DH)) DH.s = 0 :=
      hinj (by rw [hzero, map_zero])
    have hmk' : (Ideal.Quotient.mk (𝔮.comap (headToQ DH)) DH.s :
        WPHead K w N ⧸ 𝔮.comap (headToQ DH)) = 0 := hmk
    rw [Ideal.Quotient.eq_zero_iff_mem] at hmk'
    exact hs hmk'
  have hval : ι (bPoint DH (𝔮.comap (headToQ DH)) i) =
      Ideal.Quotient.mk 𝔮 (qX DH i) :=
    mul_right_cancel₀ hρs (by rw [h2, hrel, mul_comm])
  have hnormι : ‖ι (bPoint DH (𝔮.comap (headToQ DH)) i)‖ ≤ 1 := by
    rw [hval]
    exact le_trans (Ideal.Quotient.norm_mk_le _ _) (norm_qX_le_one DH i)
  have hone : ‖(1 : QHead DH ⧸ 𝔮)‖ ≤ 1 := by
    have h1 : ‖(1 : QHead DH ⧸ 𝔮)‖ ≤ ‖(1 : QHead DH)‖ := by
      have hx := Ideal.Quotient.norm_mk_le 𝔮 1
      rwa [map_one] at hx
    have h2 : ‖(1 : QHead DH)‖ ≤ ‖(1 : P (WPHead K w N) DH.T.card)‖ := by
      have hx := Ideal.Quotient.norm_mk_le (headGraphIdeal DH) 1
      rwa [map_one] at hx
    calc ‖(1 : QHead DH ⧸ 𝔮)‖ ≤ ‖(1 : QHead DH)‖ := h1
      _ ≤ ‖(1 : P (WPHead K w N) DH.T.card)‖ := h2
      _ = 1 := norm_one
  have hpow : ∀ n : ℕ, ‖ι (bPoint DH (𝔮.comap (headToQ DH)) i) ^ n‖ ≤ 1 := by
    intro n
    induction n with
    | zero => rw [pow_zero]; exact hone
    | succ k ih =>
        rw [pow_succ]
        refine le_trans (norm_mul_le _ _) ?_
        calc ‖ι (bPoint DH (𝔮.comap (headToQ DH)) i) ^ k‖ *
              ‖ι (bPoint DH (𝔮.comap (headToQ DH)) i)‖
            ≤ 1 * 1 := mul_le_mul ih hnormι (norm_nonneg _) zero_le_one
          _ = 1 := one_mul 1
  refine isBounded_of_forall_norm_le (C := C) ?_
  rintro y ⟨n, rfl⟩
  calc ‖bPoint DH (𝔮.comap (headToQ DH)) i ^ n‖
      ≤ C * ‖ι (bPoint DH (𝔮.comap (headToQ DH)) i ^ n)‖ := hbound _
    _ = C * ‖ι (bPoint DH (𝔮.comap (headToQ DH)) i) ^ n‖ := by rw [map_pow]
    _ ≤ C * 1 := mul_le_mul_of_nonneg_left (hpow n) (le_of_lt hCpos)
    _ = C := mul_one _

end BPoint

section QTate

open ValuationSpectrum FiniteJet.GraphKoszul

open scoped NormedField Valued

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
  [CompleteSpace K]
variable {w : ℕ → ℕ} {N : ℕ}

/-- In a nontrivial graph model the unit has norm one: a lift of `1` of norm
`< 1` would make `1` minus that lift — an element of the graph ideal — a unit. -/
theorem norm_one_qHead (DH : RationalLocData (WPHead K w N))
    [hnt : Nontrivial (QHead DH)] : ‖(1 : QHead DH)‖ = 1 := by
  have hntq : Nontrivial
      (P (WPHead K w N) DH.T.card ⧸ headGraphIdeal DH) := hnt
  show ‖(1 : P (WPHead K w N) DH.T.card ⧸ headGraphIdeal DH)‖ = 1
  set r : ℝ := ‖(1 : P (WPHead K w N) DH.T.card ⧸ headGraphIdeal DH)‖ with hr
  have hle : r ≤ 1 := by
    rw [hr]
    calc ‖(1 : P (WPHead K w N) DH.T.card ⧸ headGraphIdeal DH)‖
        = ‖Ideal.Quotient.mk (headGraphIdeal DH)
            (1 : P (WPHead K w N) DH.T.card)‖ := by rw [map_one]
      _ ≤ ‖(1 : P (WPHead K w N) DH.T.card)‖ := Ideal.Quotient.norm_mk_le _ _
      _ = 1 := norm_one
  refine le_antisymm hle ?_
  by_contra hlt
  push_neg at hlt
  obtain ⟨a, ha, han⟩ :=
    Ideal.Quotient.norm_mk_lt
      (1 : P (WPHead K w N) DH.T.card ⧸ headGraphIdeal DH)
      (by linarith : (0 : ℝ) < 1 - r)
  have ha1 : ‖a‖ < 1 := by
    have : r + (1 - r) = 1 := by ring
    rw [← hr, this] at han
    exact han
  have hmem : (1 : P (WPHead K w N) DH.T.card) - a ∈ headGraphIdeal DH := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_one, ha]
    exact sub_self _
  have hunit : IsUnit ((1 : P (WPHead K w N) DH.T.card) - a) :=
    (Units.oneSub a ha1).isUnit
  have htop : headGraphIdeal DH = ⊤ :=
    Ideal.eq_top_of_isUnit_mem _ hmem hunit
  have hzero : (1 : P (WPHead K w N) DH.T.card ⧸ headGraphIdeal DH) = 0 := by
    rw [show (1 : P (WPHead K w N) DH.T.card ⧸ headGraphIdeal DH) =
      Ideal.Quotient.mk (headGraphIdeal DH) 1 from (map_one _).symm,
      Ideal.Quotient.eq_zero_iff_mem, htop]
    trivial
  exact one_ne_zero hzero

/-- Multiplication by a nonzero constant scales the norm of the graph model:
the constant is a unit upstairs, so it permutes the lifts of an element. -/
theorem norm_headToQ_const_mul (DH : RationalLocData (WPHead K w N)) {c : K}
    (hc : c ≠ 0) (x : QHead DH) :
    ‖headToQ DH (constHead K w N c) * x‖ = ‖c‖ * ‖x‖ := by
  have hcpos : 0 < ‖c‖ := norm_pos_iff.mpr hc
  set tP : P (WPHead K w N) DH.T.card :=
    polyToP (MvPolynomial.C (constHead K w N c)) with htP
  set tP' : P (WPHead K w N) DH.T.card :=
    polyToP (MvPolynomial.C (constHead K w N c⁻¹)) with htP'
  have hscale : ∀ y : P (WPHead K w N) DH.T.card, ‖tP * y‖ = ‖c‖ * ‖y‖ := by
    intro y
    rw [htP, norm_tP_mul (constHead K w N c) (fun z => norm_wphead_mul _ z) y,
      norm_constHead]
  have hscale' : ∀ y : P (WPHead K w N) DH.T.card,
      ‖tP' * y‖ = ‖c‖⁻¹ * ‖y‖ := by
    intro y
    rw [htP', norm_tP_mul (constHead K w N c⁻¹)
      (fun z => norm_wphead_mul _ z) y, norm_constHead, norm_inv]
  have hinv : tP' * tP = 1 := by
    rw [htP, htP', ← map_mul, ← map_mul, ← map_mul, inv_mul_cancel₀ hc,
      map_one, map_one, map_one]
  set y : P (WPHead K w N) DH.T.card ⧸ headGraphIdeal DH := x with hy
  show ‖Ideal.Quotient.mk (headGraphIdeal DH) tP * y‖ = ‖c‖ * ‖y‖
  refine le_antisymm ?_ ?_
  · refine le_of_forall_pos_le_add fun ε hε => ?_
    obtain ⟨a, ha, han⟩ := Ideal.Quotient.norm_mk_lt y (div_pos hε hcpos)
    have hlift : Ideal.Quotient.mk (headGraphIdeal DH) (tP * a) =
        Ideal.Quotient.mk (headGraphIdeal DH) tP * y := by rw [map_mul, ha]
    calc ‖Ideal.Quotient.mk (headGraphIdeal DH) tP * y‖
        ≤ ‖tP * a‖ := by rw [← hlift]; exact Ideal.Quotient.norm_mk_le _ _
      _ = ‖c‖ * ‖a‖ := hscale a
      _ ≤ ‖c‖ * (‖y‖ + ε / ‖c‖) :=
          mul_le_mul_of_nonneg_left han.le (norm_nonneg c)
      _ = ‖c‖ * ‖y‖ + ε := by field_simp
  · refine le_of_forall_pos_le_add fun ε hε => ?_
    obtain ⟨z, hz, hzn⟩ := Ideal.Quotient.norm_mk_lt
      (Ideal.Quotient.mk (headGraphIdeal DH) tP * y) hε
    have hlift : Ideal.Quotient.mk (headGraphIdeal DH) (tP' * z) = y := by
      rw [map_mul, hz, ← mul_assoc, ← map_mul, hinv, map_one, one_mul]
    have hxle : ‖y‖ ≤ ‖c‖⁻¹ * ‖z‖ := by
      rw [← hscale' z, ← hlift]
      exact Ideal.Quotient.norm_mk_le _ _
    calc ‖c‖ * ‖y‖ ≤ ‖c‖ * (‖c‖⁻¹ * ‖z‖) :=
          mul_le_mul_of_nonneg_left hxle (norm_nonneg c)
      _ = ‖z‖ := by field_simp
      _ ≤ ‖Ideal.Quotient.mk (headGraphIdeal DH) tP * y‖ + ε := hzn.le

/-- **The graph model is a Tate ring**: scaling by a constant pseudo-uniformizer
is exact on the quotient norm. -/
theorem isTateRing_qHead (DH : RationalLocData (WPHead K w N))
    [hnt : Nontrivial (QHead DH)] : IsTateRing (QHead DH) := by
  obtain ⟨c, hcu, hc1, hc0⟩ := exists_norm_window' K
  have hcne : c ≠ 0 := by
    intro h
    rw [h, norm_zero] at hc0
    exact lt_irrefl 0 hc0
  haveI hnoc : NormOneClass (QHead DH) := ⟨norm_one_qHead DH⟩
  have hnormt : ‖headToQ DH (constHead K w N c)‖ = ‖c‖ := by
    have h := norm_headToQ_const_mul DH hcne (1 : QHead DH)
    rwa [mul_one, norm_one, mul_one] at h
  exact FiniteJet.isTateRing_of_scale (headToQ DH (constHead K w N c))
    ((hcu.map (constHead K w N)).map (headToQ DH))
    (by rw [hnormt]; exact hc1) (by rw [hnormt]; exact hc0)
    (fun x => by rw [hnormt]; exact norm_headToQ_const_mul DH hcne x)

/-- Residue maps of normed rings are continuous. -/
theorem continuous_quotient_mk_normed {R : Type*} [SeminormedCommRing R]
    (I : Ideal R) : Continuous (Ideal.Quotient.mk I) :=
  AddMonoidHomClass.continuous_of_bound (Ideal.Quotient.mk I) 1 fun x => by
    rw [one_mul]
    exact Ideal.Quotient.norm_mk_le I x

end QTate

section BetaMain

open ValuationSpectrum FiniteJet.SpectralExtension FiniteJet.GraphKoszul

open scoped NormedField Valued

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
  [CompleteSpace K]
variable {w : ℕ → ℕ} {N : ℕ}

/-- **BETA**: the special fibre of the graph model at the contraction of a
maximal ideal is trivial — the head surjects onto `Q/𝔭Q`.

The residue field `κ(𝔭)` is finite over `K`, so its image in the (Hausdorff,
because `𝔭Q` is closed) normed ring `Q/𝔭Q` is a finite-dimensional subspace,
hence closed; and it contains the images of all polynomials, which are dense.
The graph relation `s̄·T̄ᵢ = t̄ᵢ` with `s̄` invertible in `κ(𝔭)` is what puts the
graph variables into that image. -/
theorem headToQ_surjective_mod_map (ϖ : Uniformizer K)
    [hdvr : IsDiscreteValuationRing 𝒪[K]]
    (hK₀ : IsNoetherianRing (FiniteJet.unitBall K))
    (DH : RationalLocData (WPHead K w N)) (hDH : DH.IsRational)
    (𝔮 : Ideal (QHead DH)) (h𝔮 : 𝔮.IsMaximal) :
    Function.Surjective
      ((Ideal.Quotient.mk
        (Ideal.map (headToQ DH) (𝔮.comap (headToQ DH)))).comp (headToQ DH)) := by
  classical
  haveI h𝔭 : (𝔮.comap (headToQ DH)).IsMaximal :=
    comap_headToQ_isMaximal w N ϖ hK₀ DH hDH 𝔮 h𝔮
  haveI hfd : FiniteDimensional K (KappaP w N (𝔮.comap (headToQ DH))) :=
    module_finite_residue_head w N ϖ hK₀ (𝔮.comap (headToQ DH))
  haveI hnt : Nontrivial (QHead DH) :=
    ⟨⟨1, 0, fun h => h𝔮.ne_top (Ideal.eq_top_iff_one 𝔮 |>.mpr (h ▸ 𝔮.zero_mem))⟩⟩
  haveI hTate : IsTateRing (QHead DH) := isTateRing_qHead DH
  haveI hNoeth : IsNoetherianRing (QHead DH) := isNoetherianRing_qHead ϖ hK₀ hDH
  haveI hclosed : IsClosed
      ((Ideal.map (headToQ DH) (𝔮.comap (headToQ DH)) : Ideal (QHead DH)) :
        Set (QHead DH)) :=
    isClosed_ideal_of_noetherian_normed _
  -- the residue field of the head maps into the special fibre
  have hkill : ∀ a ∈ 𝔮.comap (headToQ DH),
      (Ideal.Quotient.mk (Ideal.map (headToQ DH) (𝔮.comap (headToQ DH))))
        (headToQ DH a) = 0 := by
    intro a ha
    rw [Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.mem_map_of_mem _ ha
  set j : KappaP w N (𝔮.comap (headToQ DH)) →+*
      QHead DH ⧸ Ideal.map (headToQ DH) (𝔮.comap (headToQ DH)) :=
    Ideal.Quotient.lift _
      ((Ideal.Quotient.mk _).comp (headToQ DH)) hkill with hjdef
  have hjmk : ∀ a : WPHead K w N,
      j (mkKappaP w N (𝔮.comap (headToQ DH)) a) =
        Ideal.Quotient.mk _ (headToQ DH a) := fun _ => rfl
  -- the `K`-structures on the special fibre
  letI algF : Algebra K (QHead DH ⧸
      Ideal.map (headToQ DH) (𝔮.comap (headToQ DH))) :=
    (((Ideal.Quotient.mk _).comp (headToQ DH)).comp (constHead K w N)).toAlgebra
  have hnormconst : ∀ c : K,
      ‖algebraMap K (QHead DH ⧸ Ideal.map (headToQ DH)
        (𝔮.comap (headToQ DH))) c‖ ≤ ‖c‖ := by
    intro c
    refine le_trans (Ideal.Quotient.norm_mk_le _ _) ?_
    show ‖headToQ DH (constHead K w N c)‖ ≤ ‖c‖
    refine le_trans (Ideal.Quotient.norm_mk_le _ _) ?_
    show ‖(polyToP (MvPolynomial.C (constHead K w N c)) :
      P (WPHead K w N) DH.T.card)‖ ≤ ‖c‖
    have h1 := norm_tP_mul (E := WPHead K w N) (m := DH.T.card)
      (constHead K w N c) (fun x => norm_wphead_mul _ x) 1
    rw [mul_one, norm_one, mul_one, norm_constHead] at h1
    exact le_of_eq h1
  letI nsF : NormedSpace K (QHead DH ⧸
      Ideal.map (headToQ DH) (𝔮.comap (headToQ DH))) :=
    { norm_smul_le := fun c x => by
        rw [Algebra.smul_def]
        exact le_trans (norm_mul_le _ _)
          (mul_le_mul_of_nonneg_right (hnormconst c) (norm_nonneg x)) }
  haveI : IsBoundedSMul K (QHead DH ⧸
      Ideal.map (headToQ DH) (𝔮.comap (headToQ DH))) :=
    IsBoundedSMul.of_norm_smul_le NormedSpace.norm_smul_le
  haveI : ContinuousSMul K (QHead DH ⧸
      Ideal.map (headToQ DH) (𝔮.comap (headToQ DH))) :=
    IsBoundedSMul.continuousSMul
  -- the image of the residue field is a finite-dimensional, hence closed, subspace
  letI nfκ : NormedField (KappaP w N (𝔮.comap (headToQ DH))) :=
    extNormedField K (KappaP w N (𝔮.comap (headToQ DH)))
  letI nsκ : NormedSpace K (KappaP w N (𝔮.comap (headToQ DH))) :=
    extNormedSpace K (KappaP w N (𝔮.comap (headToQ DH)))
  set jₗ : KappaP w N (𝔮.comap (headToQ DH)) →ₗ[K]
      (QHead DH ⧸ Ideal.map (headToQ DH) (𝔮.comap (headToQ DH))) :=
    { toFun := j
      map_add' := map_add j
      map_smul' := fun c x => by
        show j (algebraMap K (KappaP w N (𝔮.comap (headToQ DH))) c * x) =
          algebraMap K _ c * j x
        rw [map_mul]
        rfl } with hjₗdef
  haveI hfdr : FiniteDimensional K ↥(LinearMap.range jₗ) := by
    haveI : FiniteDimensional K (KappaP w N (𝔮.comap (headToQ DH))) := hfd
    exact FiniteDimensional.of_surjective (jₗ.rangeRestrict)
      (LinearMap.surjective_rangeRestrict jₗ)
  have hrangeClosed : IsClosed ((LinearMap.range jₗ :
      Submodule K (QHead DH ⧸ Ideal.map (headToQ DH) (𝔮.comap (headToQ DH)))) :
      Set (QHead DH ⧸ Ideal.map (headToQ DH) (𝔮.comap (headToQ DH)))) :=
    Submodule.closed_of_finiteDimensional _
  -- the polynomial images are dense and land in that subspace
  set π : P (WPHead K w N) DH.T.card →+*
      (QHead DH ⧸ Ideal.map (headToQ DH) (𝔮.comap (headToQ DH))) :=
    (Ideal.Quotient.mk _).comp (Ideal.Quotient.mk (headGraphIdeal DH))
    with hπdef
  have hπcont : Continuous π :=
    (continuous_quotient_mk_normed _).comp (continuous_quotient_mk_normed _)
  have hπsurj : Function.Surjective ⇑π := by
    rw [hπdef]
    show Function.Surjective (⇑(Ideal.Quotient.mk (Ideal.map (headToQ DH)
        (𝔮.comap (headToQ DH)))) ∘
      ⇑(Ideal.Quotient.mk (headGraphIdeal DH)))
    exact Function.Surjective.comp Ideal.Quotient.mk_surjective
      Ideal.Quotient.mk_surjective
  have hpoly : ∀ p : MvPolynomial (Fin DH.T.card) (WPHead K w N),
      π (polyToP p) ∈ LinearMap.range jₗ := by
    have hs : DH.s ∉ 𝔮.comap (headToQ DH) :=
      s_notMem_comap_headToQ ϖ hK₀ DH hDH 𝔮 h𝔮.isPrime
    have hsne : mkKappaP w N (𝔮.comap (headToQ DH)) DH.s ≠ 0 := by
      show (Ideal.Quotient.mk (𝔮.comap (headToQ DH)) DH.s :
        WPHead K w N ⧸ 𝔮.comap (headToQ DH)) ≠ 0
      rw [Ne, Ideal.Quotient.eq_zero_iff_mem]
      exact hs
    have hunit : IsUnit (j (mkKappaP w N (𝔮.comap (headToQ DH)) DH.s)) :=
      (isUnit_iff_ne_zero.mpr hsne).map j
    have hX : ∀ i : Fin DH.T.card,
        π (polyToP (MvPolynomial.X i)) =
          j (bPoint DH (𝔮.comap (headToQ DH)) i) := by
      intro i
      refine hunit.mul_left_cancel ?_
      have h1 : j (mkKappaP w N (𝔮.comap (headToQ DH)) DH.s) *
          π (polyToP (MvPolynomial.X i)) =
          Ideal.Quotient.mk _ (headToQ DH DH.s * qX DH i) := by
        rw [hjmk, map_mul]
        rfl
      have h2 : j (mkKappaP w N (𝔮.comap (headToQ DH)) DH.s) *
          j (bPoint DH (𝔮.comap (headToQ DH)) i) =
          Ideal.Quotient.mk _ (headToQ DH
            ((datumEnum DH i : ↥DH.T) : WPHead K w N)) := by
        rw [← map_mul, mul_comm,
          bPoint_mul_s DH (𝔮.comap (headToQ DH)) hs i, hjmk]
      rw [h1, h2, show headToQ DH DH.s * qX DH i =
        headToQ DH ((datumEnum DH i : ↥DH.T) : WPHead K w N) from
        (headConst_datumEnum DH i).symm]
    intro p
    have hext : π.comp (polyToP (E := WPHead K w N) (m := DH.T.card)) =
        j.comp (MvPolynomial.eval₂Hom
          (mkKappaP w N (𝔮.comap (headToQ DH)))
          (fun i => bPoint DH (𝔮.comap (headToQ DH)) i)) := by
      refine MvPolynomial.ringHom_ext (fun a => ?_) (fun i => ?_)
      · rw [RingHom.comp_apply, RingHom.comp_apply, MvPolynomial.eval₂Hom_C,
          hjmk]
        rfl
      · rw [RingHom.comp_apply, RingHom.comp_apply, MvPolynomial.eval₂Hom_X']
        exact hX i
    have hp : π (polyToP p) =
        j (MvPolynomial.eval₂Hom (mkKappaP w N (𝔮.comap (headToQ DH)))
          (fun i => bPoint DH (𝔮.comap (headToQ DH)) i) p) := by
      have := congrArg
        (fun f : MvPolynomial (Fin DH.T.card) (WPHead K w N) →+* _ => f p) hext
      simpa only [RingHom.comp_apply] using this
    exact ⟨_, hp.symm⟩

  -- closed + dense
  have hdense : Dense (⇑π '' Set.range (polyToP (E := WPHead K w N)
      (m := DH.T.card))) := by
    rw [dense_iff_closure_eq]
    refine Set.eq_univ_of_univ_subset ?_
    calc (Set.univ : Set (QHead DH ⧸ Ideal.map (headToQ DH)
            (𝔮.comap (headToQ DH))))
        = ⇑π '' Set.univ := (Set.image_univ_of_surjective hπsurj).symm
      _ = ⇑π '' closure (Set.range (polyToP (E := WPHead K w N)
            (m := DH.T.card))) := by rw [denseRange_polyToP.closure_eq]
      _ ⊆ closure (⇑π '' Set.range (polyToP (E := WPHead K w N)
            (m := DH.T.card))) := image_closure_subset_closure_image hπcont
  have hsub : ⇑π '' Set.range (polyToP (E := WPHead K w N) (m := DH.T.card)) ⊆
      ((LinearMap.range jₗ : Submodule K (QHead DH ⧸ Ideal.map (headToQ DH)
        (𝔮.comap (headToQ DH)))) : Set (QHead DH ⧸ Ideal.map (headToQ DH)
          (𝔮.comap (headToQ DH)))) := by
    rintro y ⟨-, ⟨p, rfl⟩, rfl⟩
    exact hpoly p
  have htop : ((LinearMap.range jₗ : Submodule K (QHead DH ⧸
      Ideal.map (headToQ DH) (𝔮.comap (headToQ DH)))) :
      Set (QHead DH ⧸ Ideal.map (headToQ DH) (𝔮.comap (headToQ DH)))) =
      Set.univ := by
    refine Set.eq_univ_of_univ_subset ?_
    rw [← hdense.closure_eq]
    exact hrangeClosed.closure_subset_iff.mpr hsub
  -- conclude
  intro y
  have hy : y ∈ ((LinearMap.range jₗ : Submodule K (QHead DH ⧸
      Ideal.map (headToQ DH) (𝔮.comap (headToQ DH)))) :
      Set (QHead DH ⧸ Ideal.map (headToQ DH) (𝔮.comap (headToQ DH)))) :=
    htop ▸ Set.mem_univ y
  obtain ⟨u, hu⟩ := hy
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective u
  exact ⟨a, by rw [← hu]; rfl⟩

end BetaMain

end WeightedParity
