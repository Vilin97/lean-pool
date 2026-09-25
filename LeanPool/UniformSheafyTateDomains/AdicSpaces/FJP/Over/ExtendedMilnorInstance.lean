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
public import LeanPool.UniformSheafyTateDomains.AdicSpaces.FJP.Over.ExtendedCornerPackage
public import LeanPool.UniformSheafyTateDomains.AdicSpaces.FJP.MilnorSquareInstance

/-!
# The `⟨V⟩`-extended square as a `MilnorSquareData` (T627, campaign B)

Instantiates the abstract strict-Milnor-descent criterion at the extended
finite-jet square `StrictLoc.PA K n = StrictLoc.PB K n ×_{StrictLoc.PD K n} StrictLoc.PC K n` (T626's `extPinch`),
following the `jetSquare` template (T620) with the generic datum layer (T624),
the generic naturality/composition lemmas (T623), and the value-level Milnor
row of the abstract pinch (T625's `valueRow_*`).

Output: `isSheafy_extJetA n : IsSheafy (StrictLoc.PA K n)` — the sheafiness of the
Gauss-normed Tate extension of the pinching algebra, for every `n`
([Reviewer] §5.1; the normed half of the B-headline).
-/

@[expose] public section

@[expose] public section

noncomputable section

namespace FiniteJetOver

open FiniteJet ValuationSpectrum TopologicalRing GraphKoszul StrictLoc

variable (K : Type*) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  (ϖ : Uniformizer K) (hK₀ : IsNoetherianRing (FiniteJet.unitBall K)) (n : ℕ)

/-! ### Pods and the power-bounded transport -/

/-- Pair of definition for `StrictLoc.PA K n` (unit ball at the constant-series scale). -/
noncomputable def podPA : PairOfDefinition (StrictLoc.PA K n) :=
  unitBallPod (polyToP (MvPolynomial.C (piA ϖ)))
    (isUnit_tP _ (isUnit_piA ϖ))
    (by rw [norm_tP _ (norm_piA_mul ϖ)]; exact norm_piA_lt_one ϖ)
    (by rw [norm_tP _ (norm_piA_mul ϖ)]; exact norm_piA_pos ϖ)
    (fun x => by rw [norm_tP _ (norm_piA_mul ϖ)]
                 exact norm_tP_mul _ (norm_piA_mul ϖ) x)

/-- Pair of definition for `StrictLoc.PB K n`. -/
noncomputable def podPB : PairOfDefinition (StrictLoc.PB K n) :=
  unitBallPod (polyToP (MvPolynomial.C (piB ϖ)))
    (isUnit_tP _ (isUnit_piB ϖ))
    (by rw [norm_tP _ (norm_piB_mul ϖ), norm_piB]; exact ϖ.norm_val_lt_one)
    (by rw [norm_tP _ (norm_piB_mul ϖ), norm_piB]; exact ϖ.norm_val_pos)
    (fun x => by rw [norm_tP _ (norm_piB_mul ϖ)]
                 exact norm_tP_mul _ (norm_piB_mul ϖ) x)

/-- Pair of definition for `StrictLoc.PC K n`. -/
noncomputable def podPC : PairOfDefinition (StrictLoc.PC K n) :=
  unitBallPod (polyToP (MvPolynomial.C (piC ϖ)))
    (isUnit_tP _ (isUnit_piC ϖ))
    (by rw [norm_tP _ (norm_piC_mul ϖ), norm_piC]; exact ϖ.norm_val_lt_one)
    (by rw [norm_tP _ (norm_piC_mul ϖ), norm_piC]; exact ϖ.norm_val_pos)
    (fun x => by rw [norm_tP _ (norm_piC_mul ϖ)]
                 exact norm_tP_mul _ (norm_piC_mul ϖ) x)

/-- Pair of definition for `StrictLoc.PD K n`. -/
noncomputable def podPD : PairOfDefinition (StrictLoc.PD K n) :=
  unitBallPod (polyToP (MvPolynomial.C (piD ϖ)))
    (isUnit_tP _ (isUnit_piD ϖ))
    (by rw [norm_tP _ (norm_piD_mul ϖ), norm_piD]; exact ϖ.norm_val_lt_one)
    (by rw [norm_tP _ (norm_piD_mul ϖ), norm_piD]; exact ϖ.norm_val_pos)
    (fun x => by rw [norm_tP _ (norm_piD_mul ϖ)]
                 exact norm_tP_mul _ (norm_piD_mul ϖ) x)

section Transport

variable {A' B' : Type*}
  [NormedCommRing A'] [IsUltrametricDist A']
  [NormedCommRing B'] [IsUltrametricDist B']

omit [IsUltrametricDist A'] in
/-- Norm-bounded sets are Huber-bounded in a seminormed ring
(submultiplicativity shrinks the ball). -/
theorem isBounded_of_norm_le {S : Set A'} {M : ℝ} (hM : 0 ≤ M)
    (hS : ∀ x ∈ S, ‖x‖ ≤ M) : TopologicalRing.IsBounded S := by
  intro U hU
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hU
  refine ⟨Metric.ball 0 (ε / (M + 1)), Metric.ball_mem_nhds 0 (by positivity), ?_⟩
  rintro _ ⟨s, hs, v, hv, rfl⟩
  rw [Metric.mem_ball, dist_zero_right] at hv
  refine hball ?_
  rw [Metric.mem_ball, dist_zero_right]
  calc ‖s * v‖ ≤ ‖s‖ * ‖v‖ := norm_mul_le _ _
    _ ≤ M * ‖v‖ := mul_le_mul_of_nonneg_right (hS s hs) (norm_nonneg v)
    _ ≤ (M + 1) * ‖v‖ :=
        mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg v)
    _ < (M + 1) * (ε / (M + 1)) := by
        have hM1 : (0 : ℝ) < M + 1 := by linarith
        exact mul_lt_mul_of_pos_left hv hM1
    _ = ε := by
        have hM1 : (M + 1 : ℝ) ≠ 0 := by linarith
        field_simp

omit [IsUltrametricDist A'] in
/-- In a normed ring with a multiplicative scale, Huber-bounded sets are
norm-bounded (`t`-power division). -/
theorem exists_norm_le_of_isBounded (t : A') (ht1 : ‖t‖ < 1) (ht0 : 0 < ‖t‖)
    (hscale : ∀ x : A', ‖t * x‖ = ‖t‖ * ‖x‖)
    {S : Set A'} (hS : TopologicalRing.IsBounded S) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ x ∈ S, ‖x‖ ≤ M := by
  obtain ⟨V, hV, hVS⟩ := hS (Metric.ball 0 1) (Metric.ball_mem_nhds 0 one_pos)
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp hV
  obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one hδ ht1
  have hpow : ∀ (y : A') (j : ℕ), ‖y * t ^ j‖ = ‖t‖ ^ j * ‖y‖ := by
    intro y j
    induction j with
    | zero => simp
    | succ i ih =>
      calc ‖y * t ^ (i + 1)‖ = ‖t * (y * t ^ i)‖ := by
            rw [show y * t ^ (i + 1) = t * (y * t ^ i) from by ring]
        _ = ‖t‖ * ‖y * t ^ i‖ := hscale _
        _ = ‖t‖ * (‖t‖ ^ i * ‖y‖) := by rw [ih]
        _ = ‖t‖ ^ (i + 1) * ‖y‖ := by ring
  refine ⟨(‖t‖ ^ (k + 1))⁻¹, by positivity, fun x hx => ?_⟩
  have htk : t ^ (k + 1) ∈ V := by
    refine hball ?_
    rw [Metric.mem_ball, dist_zero_right]
    calc ‖t ^ (k + 1)‖ ≤ ‖t‖ ^ (k + 1) := norm_pow_le' t (Nat.succ_pos k)
      _ = ‖t‖ ^ k * ‖t‖ := pow_succ _ _
      _ < δ * 1 := by
          refine mul_lt_mul'' hk ht1 (by positivity) (norm_nonneg t)
      _ = δ := mul_one δ
  have hmem : x * t ^ (k + 1) ∈ Metric.ball (0 : A') 1 :=
    hVS (Set.mul_mem_mul hx htk)
  rw [Metric.mem_ball, dist_zero_right, hpow x (k + 1)] at hmem
  rw [← one_div, le_div_iff₀ (by positivity), mul_comm]
  exact hmem.le

omit [IsUltrametricDist A'] [IsUltrametricDist B'] in
/-- **Power-bounded transport along a 1-Lipschitz hom** out of a scaled corner:
the generic `A⁺ ≤ (B⁺).comap φ` input for the pushed-datum comap iffs. -/
theorem powerBounded_le_comap (t : A') (ht1 : ‖t‖ < 1) (ht0 : 0 < ‖t‖)
    (hscale : ∀ x : A', ‖t * x‖ = ‖t‖ * ‖x‖)
    (φ : A' →+* B') (hφ : ∀ x, ‖φ x‖ ≤ ‖x‖) {x : A'}
    (hx : TopologicalRing.IsPowerBounded x) :
    TopologicalRing.IsPowerBounded (φ x) := by
  obtain ⟨M, hM0, hM⟩ := exists_norm_le_of_isBounded t ht1 ht0 hscale hx
  refine (isBounded_of_norm_le hM0 (fun y hy => ?_) : TopologicalRing.IsBounded
    (Set.range (φ x ^ · : ℕ → B')))
  obtain ⟨m, rfl⟩ := hy
  calc ‖φ x ^ m‖ = ‖φ (x ^ m)‖ := by rw [map_pow]
    _ ≤ ‖x ^ m‖ := hφ _
    _ ≤ M := hM _ ⟨m, rfl⟩

end Transport

include ϖ in
/-- The plus-transport `(StrictLoc.PA K n)⁺ ≤ ((StrictLoc.PB K n)⁺).comap (StrictLoc.extJB K n)`. -/
theorem plusLe_extJB :
    ((StrictLoc.PA K n)⁺ : Subring (StrictLoc.PA K n)) ≤ ((StrictLoc.PB K n)⁺ : Subring (StrictLoc.PB K n)).comap (StrictLoc.extJB K n) :=
  fun _ hx => powerBounded_le_comap (polyToP (MvPolynomial.C (piA ϖ)))
    (by rw [norm_tP _ (norm_piA_mul ϖ)]; exact norm_piA_lt_one ϖ)
    (by rw [norm_tP _ (norm_piA_mul ϖ)]; exact norm_piA_pos ϖ)
    (fun x => by rw [norm_tP _ (norm_piA_mul ϖ)]
                 exact norm_tP_mul _ (norm_piA_mul ϖ) x)
    (StrictLoc.extJB K n) ((extPinch K n ϖ).norm_φB_le) hx

include ϖ in
/-- The plus-transport `(StrictLoc.PA K n)⁺ ≤ ((StrictLoc.PC K n)⁺).comap (StrictLoc.extIotaC K n)`. -/
theorem plusLe_extIotaC :
    ((StrictLoc.PA K n)⁺ : Subring (StrictLoc.PA K n)) ≤
      ((StrictLoc.PC K n)⁺ : Subring (StrictLoc.PC K n)).comap (StrictLoc.extIotaC K n) :=
  fun _ hx => powerBounded_le_comap (polyToP (MvPolynomial.C (piA ϖ)))
    (by rw [norm_tP _ (norm_piA_mul ϖ)]; exact norm_piA_lt_one ϖ)
    (by rw [norm_tP _ (norm_piA_mul ϖ)]; exact norm_piA_pos ϖ)
    (fun x => by rw [norm_tP _ (norm_piA_mul ϖ)]
                 exact norm_tP_mul _ (norm_piA_mul ϖ) x)
    (StrictLoc.extIotaC K n) (fun p => le_of_eq ((extPinch K n ϖ).norm_φC p)) hx

include ϖ in
/-- The plus-transport along the composite leg to `StrictLoc.PD K n`. -/
theorem plusLe_extD :
    ((StrictLoc.PA K n)⁺ : Subring (StrictLoc.PA K n)) ≤
      ((StrictLoc.PD K n)⁺ : Subring (StrictLoc.PD K n)).comap ((StrictLoc.extRhoC K n).comp (StrictLoc.extIotaC K n)) :=
  fun _ hx => powerBounded_le_comap (polyToP (MvPolynomial.C (piA ϖ)))
    (by rw [norm_tP _ (norm_piA_mul ϖ)]; exact norm_piA_lt_one ϖ)
    (by rw [norm_tP _ (norm_piA_mul ϖ)]; exact norm_piA_pos ϖ)
    (fun x => by rw [norm_tP _ (norm_piA_mul ϖ)]
                 exact norm_tP_mul _ (norm_piA_mul ϖ) x)
    ((StrictLoc.extRhoC K n).comp (StrictLoc.extIotaC K n))
    (fun p => le_trans ((extPinch K n ϖ).norm_ψC_le _)
      (le_of_eq ((extPinch K n ϖ).norm_φC p))) hx

/-! ### The pushes (rationality-gated, T620 pattern) -/

open Classical in
/-- The total `B`-push of the extended square. -/
noncomputable def extPushB : RationalLocData (StrictLoc.PA K n) → RationalLocData (StrictLoc.PB K n) :=
  fun D => if h : D.IsRational then pushDatumOfHom (StrictLoc.extJB K n) (podPB K ϖ n) D h
    else trivialPlusDatum (StrictLoc.PB K n) (podPB K ϖ n) 1

open Classical in
/-- The total `C`-push. -/
noncomputable def extPushC : RationalLocData (StrictLoc.PA K n) → RationalLocData (StrictLoc.PC K n) :=
  fun D => if h : D.IsRational then pushDatumOfHom (StrictLoc.extIotaC K n) (podPC K ϖ n) D h
    else trivialPlusDatum (StrictLoc.PC K n) (podPC K ϖ n) 1

open Classical in
/-- The total `D`-push. -/
noncomputable def extPushD : RationalLocData (StrictLoc.PA K n) → RationalLocData (StrictLoc.PD K n) :=
  fun D => if h : D.IsRational then
    pushDatumOfHom ((StrictLoc.extRhoC K n).comp (StrictLoc.extIotaC K n)) (podPD K ϖ n) D h
    else trivialPlusDatum (StrictLoc.PD K n) (podPD K ϖ n) 1

theorem extPushB_eq {D : RationalLocData (StrictLoc.PA K n)} (hD : D.IsRational) :
    extPushB K ϖ n D = pushDatumOfHom (StrictLoc.extJB K n) (podPB K ϖ n) D hD := by
  simp [extPushB, dif_pos hD]

theorem extPushC_eq {D : RationalLocData (StrictLoc.PA K n)} (hD : D.IsRational) :
    extPushC K ϖ n D = pushDatumOfHom (StrictLoc.extIotaC K n) (podPC K ϖ n) D hD := by
  simp [extPushC, dif_pos hD]

theorem extPushD_eq {D : RationalLocData (StrictLoc.PA K n)} (hD : D.IsRational) :
    extPushD K ϖ n D =
      pushDatumOfHom ((StrictLoc.extRhoC K n).comp (StrictLoc.extIotaC K n)) (podPD K ϖ n) D hD := by
  simp [extPushD, dif_pos hD]

/-! ### Subst-helpers for the row and compat fields -/

include ϖ hK₀ in
private theorem extRowInjectiveAux (U : RationalLocData (StrictLoc.PA K n)) (hU : U.IsRational)
    {DB : RationalLocData (StrictLoc.PB K n)} {DC : RationalLocData (StrictLoc.PC K n)}
    (hDB : DB = pushDatumOfHom (StrictLoc.extJB K n) (podPB K ϖ n) U hU)
    (hDC : DC = pushDatumOfHom (StrictLoc.extIotaC K n) (podPC K ϖ n) U hU)
    (hsB : DB.s = StrictLoc.extJB K n U.s) (hTB : ∀ t ∈ U.T, StrictLoc.extJB K n t ∈ DB.T)
    (hsC : DC.s = StrictLoc.extIotaC K n U.s) (hTC : ∀ t ∈ U.T, StrictLoc.extIotaC K n t ∈ DC.T)
    (hφB : Continuous (StrictLoc.extJB K n)) (hφC : Continuous (StrictLoc.extIotaC K n))
    (x y : presheafValue U)
    (hB : presheafValueMapOfHom (StrictLoc.extJB K n) hφB U DB hsB hTB x =
      presheafValueMapOfHom (StrictLoc.extJB K n) hφB U DB hsB hTB y)
    (hC : presheafValueMapOfHom (StrictLoc.extIotaC K n) hφC U DC hsC hTC x =
      presheafValueMapOfHom (StrictLoc.extIotaC K n) hφC U DC hsC hTC y) :
    x = y := by
  subst hDB; subst hDC
  exact (extPinch K n ϖ).valueRow_injective (podPB K ϖ n) (podPC K ϖ n) U (cornerEnum U) hU
    (extNoethPack K n ϖ hK₀ (cornerEnum U).m)
    ((extPinch K n ϖ).isClosed_IA (cornerEnum U).m U.s (cornerEnum U).f
      (extNoethPack K n ϖ hK₀ (cornerEnum U).m) ((cornerEnum U).span_eq_top U hU))
    ((extPinch K n ϖ).isClosed_pushB U (cornerEnum U)
      (extNoethPack K n ϖ hK₀ (cornerEnum U).m).hPB
      (extNoethPack K n ϖ hK₀ (cornerEnum U).m).hPBball)
    ((extPinch K n ϖ).isClosed_pushC U (cornerEnum U)
      (extNoethPack K n ϖ hK₀ (cornerEnum U).m).hPC
      (extNoethPack K n ϖ hK₀ (cornerEnum U).m).hPCball)
    hφB hφC hsB hTB hsC hTC x y hB hC

include ϖ hK₀ in
private theorem extRowGlueAux (U : RationalLocData (StrictLoc.PA K n)) (hU : U.IsRational)
    {DB : RationalLocData (StrictLoc.PB K n)} {DC : RationalLocData (StrictLoc.PC K n)}
    {DD : RationalLocData (StrictLoc.PD K n)}
    (hDB : DB = pushDatumOfHom (StrictLoc.extJB K n) (podPB K ϖ n) U hU)
    (hDC : DC = pushDatumOfHom (StrictLoc.extIotaC K n) (podPC K ϖ n) U hU)
    (hDD : DD = pushDatumOfHom ((StrictLoc.extRhoC K n).comp (StrictLoc.extIotaC K n)) (podPD K ϖ n) U hU)
    (hsB : DB.s = StrictLoc.extJB K n U.s) (hTB : ∀ t ∈ U.T, StrictLoc.extJB K n t ∈ DB.T)
    (hsC : DC.s = StrictLoc.extIotaC K n U.s) (hTC : ∀ t ∈ U.T, StrictLoc.extIotaC K n t ∈ DC.T)
    (hsBD : DD.s = StrictLoc.extRhoB K n DB.s) (hTBD : ∀ t ∈ DB.T, StrictLoc.extRhoB K n t ∈ DD.T)
    (hsCD : DD.s = StrictLoc.extRhoC K n DC.s) (hTCD : ∀ t ∈ DC.T, StrictLoc.extRhoC K n t ∈ DD.T)
    (hφB : Continuous (StrictLoc.extJB K n)) (hφC : Continuous (StrictLoc.extIotaC K n))
    (hψB : Continuous (StrictLoc.extRhoB K n)) (hψC : Continuous (StrictLoc.extRhoC K n))
    (b : presheafValue DB) (c : presheafValue DC)
    (h : presheafValueMapOfHom (StrictLoc.extRhoB K n) hψB DB DD hsBD hTBD b =
      presheafValueMapOfHom (StrictLoc.extRhoC K n) hψC DC DD hsCD hTCD c) :
    ∃ x : presheafValue U,
      presheafValueMapOfHom (StrictLoc.extJB K n) hφB U DB hsB hTB x = b ∧
      presheafValueMapOfHom (StrictLoc.extIotaC K n) hφC U DC hsC hTC x = c := by
  subst hDB; subst hDC; subst hDD
  exact (extPinch K n ϖ).valueRow_glue (podPB K ϖ n) (podPC K ϖ n) (podPD K ϖ n) U
    (cornerEnum U) hU (extNoethPack K n ϖ hK₀ (cornerEnum U).m)
    ((extPinch K n ϖ).isClosed_IA (cornerEnum U).m U.s (cornerEnum U).f
      (extNoethPack K n ϖ hK₀ (cornerEnum U).m) ((cornerEnum U).span_eq_top U hU))
    ((extPinch K n ϖ).isClosed_pushB U (cornerEnum U)
      (extNoethPack K n ϖ hK₀ (cornerEnum U).m).hPB
      (extNoethPack K n ϖ hK₀ (cornerEnum U).m).hPBball)
    ((extPinch K n ϖ).isClosed_pushC U (cornerEnum U)
      (extNoethPack K n ϖ hK₀ (cornerEnum U).m).hPC
      (extNoethPack K n ϖ hK₀ (cornerEnum U).m).hPCball)
    ((extPinch K n ϖ).isClosed_pushD U (cornerEnum U)
      (extNoethPack K n ϖ hK₀ (cornerEnum U).m).hPD
      (extNoethPack K n ϖ hK₀ (cornerEnum U).m).hPDball)
    hφB hφC hψB hψC hsB hTB hsC hTC hsBD hTBD hsCD hTCD b c h

include ϖ hK₀ in
private theorem extRowEmbeddingAux (U : RationalLocData (StrictLoc.PA K n)) (hU : U.IsRational)
    {DB : RationalLocData (StrictLoc.PB K n)} {DC : RationalLocData (StrictLoc.PC K n)}
    (hDB : DB = pushDatumOfHom (StrictLoc.extJB K n) (podPB K ϖ n) U hU)
    (hDC : DC = pushDatumOfHom (StrictLoc.extIotaC K n) (podPC K ϖ n) U hU)
    (hsB : DB.s = StrictLoc.extJB K n U.s) (hTB : ∀ t ∈ U.T, StrictLoc.extJB K n t ∈ DB.T)
    (hsC : DC.s = StrictLoc.extIotaC K n U.s) (hTC : ∀ t ∈ U.T, StrictLoc.extIotaC K n t ∈ DC.T)
    (hφB : Continuous (StrictLoc.extJB K n)) (hφC : Continuous (StrictLoc.extIotaC K n)) :
    Topology.IsEmbedding (fun x : presheafValue U =>
      (presheafValueMapOfHom (StrictLoc.extJB K n) hφB U DB hsB hTB x,
       presheafValueMapOfHom (StrictLoc.extIotaC K n) hφC U DC hsC hTC x)) := by
  subst hDB; subst hDC
  exact (extPinch K n ϖ).valueRow_embedding (podPB K ϖ n) (podPC K ϖ n) U (cornerEnum U) hU
    (extNoethPack K n ϖ hK₀ (cornerEnum U).m)
    ((extPinch K n ϖ).isClosed_IA (cornerEnum U).m U.s (cornerEnum U).f
      (extNoethPack K n ϖ hK₀ (cornerEnum U).m) ((cornerEnum U).span_eq_top U hU))
    ((extPinch K n ϖ).isClosed_pushB U (cornerEnum U)
      (extNoethPack K n ϖ hK₀ (cornerEnum U).m).hPB
      (extNoethPack K n ϖ hK₀ (cornerEnum U).m).hPBball)
    ((extPinch K n ϖ).isClosed_pushC U (cornerEnum U)
      (extNoethPack K n ϖ hK₀ (cornerEnum U).m).hPC
      (extNoethPack K n ϖ hK₀ (cornerEnum U).m).hPCball)
    hφB hφC hsB hTB hsC hTC

include ϖ in
private theorem extPushedCompatBAux (U₁ U₂ : RationalLocData (StrictLoc.PA K n))
    (hU₁ : U₁.IsRational) (hU₂ : U₂.IsRational)
    {DB₁ DB₂ : RationalLocData (StrictLoc.PB K n)}
    (hDB₁ : DB₁ = pushDatumOfHom (StrictLoc.extJB K n) (podPB K ϖ n) U₁ hU₁)
    (hDB₂ : DB₂ = pushDatumOfHom (StrictLoc.extJB K n) (podPB K ϖ n) U₂ hU₂)
    (hφ : Continuous (StrictLoc.extJB K n))
    (hs₁ : DB₁.s = StrictLoc.extJB K n U₁.s) (hT₁ : ∀ t ∈ U₁.T, StrictLoc.extJB K n t ∈ DB₁.T)
    (hs₂ : DB₂.s = StrictLoc.extJB K n U₂.s) (hT₂ : ∀ t ∈ U₂.T, StrictLoc.extJB K n t ∈ DB₂.T)
    (x₁ : presheafValue U₁) (x₂ : presheafValue U₂)
    (hmatch : ∀ (D₃ : RationalLocData (StrictLoc.PA K n))
      (h₃₁ : rationalOpen D₃.T D₃.s ⊆ rationalOpen U₁.T U₁.s)
      (h₃₂ : rationalOpen D₃.T D₃.s ⊆ rationalOpen U₂.T U₂.s),
      restrictionMap U₁ D₃ h₃₁ x₁ = restrictionMap U₂ D₃ h₃₂ x₂)
    (E₃ : RationalLocData (StrictLoc.PB K n))
    (hE₁ : rationalOpen E₃.T E₃.s ⊆ rationalOpen DB₁.T DB₁.s)
    (hE₂ : rationalOpen E₃.T E₃.s ⊆ rationalOpen DB₂.T DB₂.s) :
    restrictionMap DB₁ E₃ hE₁
        (presheafValueMapOfHom (StrictLoc.extJB K n) hφ U₁ DB₁ hs₁ hT₁ x₁) =
      restrictionMap DB₂ E₃ hE₂
        (presheafValueMapOfHom (StrictLoc.extJB K n) hφ U₂ DB₂ hs₂ hT₂ x₂) := by
  subst hDB₁; subst hDB₂
  have hsub₁ : rationalOpen (interDatumOfRational U₁ U₂ hU₁ hU₂).T (interDatumOfRational U₁ U₂ hU₁ hU₂).s ⊆ rationalOpen U₁.T U₁.s := by
    rw [rationalOpen_interDatumOfRational]
    exact Set.inter_subset_left
  have hsub₂ : rationalOpen (interDatumOfRational U₁ U₂ hU₁ hU₂).T (interDatumOfRational U₁ U₂ hU₁ hU₂).s ⊆ rationalOpen U₂.T U₂.s := by
    rw [rationalOpen_interDatumOfRational]
    exact Set.inter_subset_right
  have hpush₁ : rationalOpen (pushDatumOfHom (StrictLoc.extJB K n) (podPB K ϖ n) (interDatumOfRational U₁ U₂ hU₁ hU₂) (interDatumOfRational_isRational hU₁ hU₂)).T
      (pushDatumOfHom (StrictLoc.extJB K n) (podPB K ϖ n) (interDatumOfRational U₁ U₂ hU₁ hU₂) (interDatumOfRational_isRational hU₁ hU₂)).s ⊆
      rationalOpen (pushDatumOfHom (StrictLoc.extJB K n) (podPB K ϖ n) U₁ hU₁).T
        (pushDatumOfHom (StrictLoc.extJB K n) (podPB K ϖ n) U₁ hU₁).s := by
    rw [pushDatumOfHom_interOpen hφ
      (plusLe_extJB K ϖ n) (podPB K ϖ n) U₁ U₂ hU₁ hU₂]
    exact Set.inter_subset_left
  have hpush₂ : rationalOpen (pushDatumOfHom (StrictLoc.extJB K n) (podPB K ϖ n) (interDatumOfRational U₁ U₂ hU₁ hU₂) (interDatumOfRational_isRational hU₁ hU₂)).T
      (pushDatumOfHom (StrictLoc.extJB K n) (podPB K ϖ n) (interDatumOfRational U₁ U₂ hU₁ hU₂) (interDatumOfRational_isRational hU₁ hU₂)).s ⊆
      rationalOpen (pushDatumOfHom (StrictLoc.extJB K n) (podPB K ϖ n) U₂ hU₂).T
        (pushDatumOfHom (StrictLoc.extJB K n) (podPB K ϖ n) U₂ hU₂).s := by
    rw [pushDatumOfHom_interOpen hφ
      (plusLe_extJB K ϖ n) (podPB K ϖ n) U₁ U₂ hU₁ hU₂]
    exact Set.inter_subset_right
  have h₃I : rationalOpen E₃.T E₃.s ⊆
      rationalOpen (pushDatumOfHom (StrictLoc.extJB K n) (podPB K ϖ n) (interDatumOfRational U₁ U₂ hU₁ hU₂) (interDatumOfRational_isRational hU₁ hU₂)).T
        (pushDatumOfHom (StrictLoc.extJB K n) (podPB K ϖ n) (interDatumOfRational U₁ U₂ hU₁ hU₂) (interDatumOfRational_isRational hU₁ hU₂)).s := by
    rw [pushDatumOfHom_interOpen hφ
      (plusLe_extJB K ϖ n) (podPB K ϖ n) U₁ U₂ hU₁ hU₂]
    exact Set.subset_inter hE₁ hE₂
  have hpushed := congrArg
    (presheafValueMapOfHom (StrictLoc.extJB K n) hφ (interDatumOfRational U₁ U₂ hU₁ hU₂)
      (pushDatumOfHom (StrictLoc.extJB K n) (podPB K ϖ n) (interDatumOfRational U₁ U₂ hU₁ hU₂) (interDatumOfRational_isRational hU₁ hU₂)) rfl
      (fun t ht => Finset.mem_image_of_mem _ ht))
    (hmatch (interDatumOfRational U₁ U₂ hU₁ hU₂) hsub₁ hsub₂)
  rw [presheafValueMapOfHom_restriction (StrictLoc.extJB K n) hφ U₁ (interDatumOfRational U₁ U₂ hU₁ hU₂)
      (pushDatumOfHom (StrictLoc.extJB K n) (podPB K ϖ n) U₁ hU₁)
      (pushDatumOfHom (StrictLoc.extJB K n) (podPB K ϖ n) (interDatumOfRational U₁ U₂ hU₁ hU₂) (interDatumOfRational_isRational hU₁ hU₂)) hs₁ hT₁ rfl
      (fun t ht => Finset.mem_image_of_mem _ ht) hsub₁ hpush₁ x₁,
    presheafValueMapOfHom_restriction (StrictLoc.extJB K n) hφ U₂ (interDatumOfRational U₁ U₂ hU₁ hU₂)
      (pushDatumOfHom (StrictLoc.extJB K n) (podPB K ϖ n) U₂ hU₂)
      (pushDatumOfHom (StrictLoc.extJB K n) (podPB K ϖ n) (interDatumOfRational U₁ U₂ hU₁ hU₂) (interDatumOfRational_isRational hU₁ hU₂)) hs₂ hT₂ rfl
      (fun t ht => Finset.mem_image_of_mem _ ht) hsub₂ hpush₂ x₂] at hpushed
  have hfac₁ := congrFun (restrictionMap_comp
    (pushDatumOfHom (StrictLoc.extJB K n) (podPB K ϖ n) U₁ hU₁)
    (pushDatumOfHom (StrictLoc.extJB K n) (podPB K ϖ n) (interDatumOfRational U₁ U₂ hU₁ hU₂) (interDatumOfRational_isRational hU₁ hU₂)) E₃ hpush₁ h₃I)
    (presheafValueMapOfHom (StrictLoc.extJB K n) hφ U₁
      (pushDatumOfHom (StrictLoc.extJB K n) (podPB K ϖ n) U₁ hU₁) hs₁ hT₁ x₁)
  have hfac₂ := congrFun (restrictionMap_comp
    (pushDatumOfHom (StrictLoc.extJB K n) (podPB K ϖ n) U₂ hU₂)
    (pushDatumOfHom (StrictLoc.extJB K n) (podPB K ϖ n) (interDatumOfRational U₁ U₂ hU₁ hU₂) (interDatumOfRational_isRational hU₁ hU₂)) E₃ hpush₂ h₃I)
    (presheafValueMapOfHom (StrictLoc.extJB K n) hφ U₂
      (pushDatumOfHom (StrictLoc.extJB K n) (podPB K ϖ n) U₂ hU₂) hs₂ hT₂ x₂)
  simp only [Function.comp_apply] at hfac₁ hfac₂
  rw [← hfac₁, ← hfac₂, hpushed]

include ϖ in
private theorem extPushedCompatCAux (U₁ U₂ : RationalLocData (StrictLoc.PA K n))
    (hU₁ : U₁.IsRational) (hU₂ : U₂.IsRational)
    {DC₁ DC₂ : RationalLocData (StrictLoc.PC K n)}
    (hDC₁ : DC₁ = pushDatumOfHom (StrictLoc.extIotaC K n) (podPC K ϖ n) U₁ hU₁)
    (hDC₂ : DC₂ = pushDatumOfHom (StrictLoc.extIotaC K n) (podPC K ϖ n) U₂ hU₂)
    (hφ : Continuous (StrictLoc.extIotaC K n))
    (hs₁ : DC₁.s = StrictLoc.extIotaC K n U₁.s) (hT₁ : ∀ t ∈ U₁.T, StrictLoc.extIotaC K n t ∈ DC₁.T)
    (hs₂ : DC₂.s = StrictLoc.extIotaC K n U₂.s) (hT₂ : ∀ t ∈ U₂.T, StrictLoc.extIotaC K n t ∈ DC₂.T)
    (x₁ : presheafValue U₁) (x₂ : presheafValue U₂)
    (hmatch : ∀ (D₃ : RationalLocData (StrictLoc.PA K n))
      (h₃₁ : rationalOpen D₃.T D₃.s ⊆ rationalOpen U₁.T U₁.s)
      (h₃₂ : rationalOpen D₃.T D₃.s ⊆ rationalOpen U₂.T U₂.s),
      restrictionMap U₁ D₃ h₃₁ x₁ = restrictionMap U₂ D₃ h₃₂ x₂)
    (E₃ : RationalLocData (StrictLoc.PC K n))
    (hE₁ : rationalOpen E₃.T E₃.s ⊆ rationalOpen DC₁.T DC₁.s)
    (hE₂ : rationalOpen E₃.T E₃.s ⊆ rationalOpen DC₂.T DC₂.s) :
    restrictionMap DC₁ E₃ hE₁
        (presheafValueMapOfHom (StrictLoc.extIotaC K n) hφ U₁ DC₁ hs₁ hT₁ x₁) =
      restrictionMap DC₂ E₃ hE₂
        (presheafValueMapOfHom (StrictLoc.extIotaC K n) hφ U₂ DC₂ hs₂ hT₂ x₂) := by
  subst hDC₁; subst hDC₂
  have hsub₁ : rationalOpen (interDatumOfRational U₁ U₂ hU₁ hU₂).T (interDatumOfRational U₁ U₂ hU₁ hU₂).s ⊆ rationalOpen U₁.T U₁.s := by
    rw [rationalOpen_interDatumOfRational]
    exact Set.inter_subset_left
  have hsub₂ : rationalOpen (interDatumOfRational U₁ U₂ hU₁ hU₂).T (interDatumOfRational U₁ U₂ hU₁ hU₂).s ⊆ rationalOpen U₂.T U₂.s := by
    rw [rationalOpen_interDatumOfRational]
    exact Set.inter_subset_right
  have hpush₁ : rationalOpen (pushDatumOfHom (StrictLoc.extIotaC K n) (podPC K ϖ n) (interDatumOfRational U₁ U₂ hU₁ hU₂) (interDatumOfRational_isRational hU₁ hU₂)).T
      (pushDatumOfHom (StrictLoc.extIotaC K n) (podPC K ϖ n) (interDatumOfRational U₁ U₂ hU₁ hU₂) (interDatumOfRational_isRational hU₁ hU₂)).s ⊆
      rationalOpen (pushDatumOfHom (StrictLoc.extIotaC K n) (podPC K ϖ n) U₁ hU₁).T
        (pushDatumOfHom (StrictLoc.extIotaC K n) (podPC K ϖ n) U₁ hU₁).s := by
    rw [pushDatumOfHom_interOpen hφ
      (plusLe_extIotaC K ϖ n) (podPC K ϖ n) U₁ U₂ hU₁ hU₂]
    exact Set.inter_subset_left
  have hpush₂ : rationalOpen (pushDatumOfHom (StrictLoc.extIotaC K n) (podPC K ϖ n) (interDatumOfRational U₁ U₂ hU₁ hU₂) (interDatumOfRational_isRational hU₁ hU₂)).T
      (pushDatumOfHom (StrictLoc.extIotaC K n) (podPC K ϖ n) (interDatumOfRational U₁ U₂ hU₁ hU₂) (interDatumOfRational_isRational hU₁ hU₂)).s ⊆
      rationalOpen (pushDatumOfHom (StrictLoc.extIotaC K n) (podPC K ϖ n) U₂ hU₂).T
        (pushDatumOfHom (StrictLoc.extIotaC K n) (podPC K ϖ n) U₂ hU₂).s := by
    rw [pushDatumOfHom_interOpen hφ
      (plusLe_extIotaC K ϖ n) (podPC K ϖ n) U₁ U₂ hU₁ hU₂]
    exact Set.inter_subset_right
  have h₃I : rationalOpen E₃.T E₃.s ⊆
      rationalOpen (pushDatumOfHom (StrictLoc.extIotaC K n) (podPC K ϖ n) (interDatumOfRational U₁ U₂ hU₁ hU₂) (interDatumOfRational_isRational hU₁ hU₂)).T
        (pushDatumOfHom (StrictLoc.extIotaC K n) (podPC K ϖ n) (interDatumOfRational U₁ U₂ hU₁ hU₂) (interDatumOfRational_isRational hU₁ hU₂)).s := by
    rw [pushDatumOfHom_interOpen hφ
      (plusLe_extIotaC K ϖ n) (podPC K ϖ n) U₁ U₂ hU₁ hU₂]
    exact Set.subset_inter hE₁ hE₂
  have hpushed := congrArg
    (presheafValueMapOfHom (StrictLoc.extIotaC K n) hφ (interDatumOfRational U₁ U₂ hU₁ hU₂)
      (pushDatumOfHom (StrictLoc.extIotaC K n) (podPC K ϖ n) (interDatumOfRational U₁ U₂ hU₁ hU₂) (interDatumOfRational_isRational hU₁ hU₂)) rfl
      (fun t ht => Finset.mem_image_of_mem _ ht))
    (hmatch (interDatumOfRational U₁ U₂ hU₁ hU₂) hsub₁ hsub₂)
  rw [presheafValueMapOfHom_restriction (StrictLoc.extIotaC K n) hφ U₁ (interDatumOfRational U₁ U₂ hU₁ hU₂)
      (pushDatumOfHom (StrictLoc.extIotaC K n) (podPC K ϖ n) U₁ hU₁)
      (pushDatumOfHom (StrictLoc.extIotaC K n) (podPC K ϖ n) (interDatumOfRational U₁ U₂ hU₁ hU₂) (interDatumOfRational_isRational hU₁ hU₂)) hs₁ hT₁ rfl
      (fun t ht => Finset.mem_image_of_mem _ ht) hsub₁ hpush₁ x₁,
    presheafValueMapOfHom_restriction (StrictLoc.extIotaC K n) hφ U₂ (interDatumOfRational U₁ U₂ hU₁ hU₂)
      (pushDatumOfHom (StrictLoc.extIotaC K n) (podPC K ϖ n) U₂ hU₂)
      (pushDatumOfHom (StrictLoc.extIotaC K n) (podPC K ϖ n) (interDatumOfRational U₁ U₂ hU₁ hU₂) (interDatumOfRational_isRational hU₁ hU₂)) hs₂ hT₂ rfl
      (fun t ht => Finset.mem_image_of_mem _ ht) hsub₂ hpush₂ x₂] at hpushed
  have hfac₁ := congrFun (restrictionMap_comp
    (pushDatumOfHom (StrictLoc.extIotaC K n) (podPC K ϖ n) U₁ hU₁)
    (pushDatumOfHom (StrictLoc.extIotaC K n) (podPC K ϖ n) (interDatumOfRational U₁ U₂ hU₁ hU₂) (interDatumOfRational_isRational hU₁ hU₂)) E₃ hpush₁ h₃I)
    (presheafValueMapOfHom (StrictLoc.extIotaC K n) hφ U₁
      (pushDatumOfHom (StrictLoc.extIotaC K n) (podPC K ϖ n) U₁ hU₁) hs₁ hT₁ x₁)
  have hfac₂ := congrFun (restrictionMap_comp
    (pushDatumOfHom (StrictLoc.extIotaC K n) (podPC K ϖ n) U₂ hU₂)
    (pushDatumOfHom (StrictLoc.extIotaC K n) (podPC K ϖ n) (interDatumOfRational U₁ U₂ hU₁ hU₂) (interDatumOfRational_isRational hU₁ hU₂)) E₃ hpush₂ h₃I)
    (presheafValueMapOfHom (StrictLoc.extIotaC K n) hφ U₂
      (pushDatumOfHom (StrictLoc.extIotaC K n) (podPC K ϖ n) U₂ hU₂) hs₂ hT₂ x₂)
  simp only [Function.comp_apply] at hfac₁ hfac₂
  rw [← hfac₁, ← hfac₂, hpushed]

/-! ### The extended square as a `MilnorSquareData` -/

include hK₀ in
/-- **The `⟨V⟩`-extended finite-jet square as a strict Milnor square-with-rows**
(T627): the T620 template at the extended corners, with the generic datum layer
and the abstract pinch's value-level row. -/
noncomputable def extJetSquare :
    MilnorSquareData (StrictLoc.extJB K n) (StrictLoc.extIotaC K n) ((StrictLoc.extRhoC K n).comp (StrictLoc.extIotaC K n))
      ((extPinch K n ϖ).φB_continuous) ((extPinch K n ϖ).φC_continuous)
      (by exact ((extPinch K n ϖ).ψC_continuous).comp ((extPinch K n ϖ).φC_continuous)) where
  pushB := extPushB K ϖ n
  pushC := extPushC K ϖ n
  pushD := extPushD K ϖ n
  pushB_s := by
    intro U hU
    rw [extPushB_eq K ϖ n hU]
    rfl
  pushC_s := by
    intro U hU
    rw [extPushC_eq K ϖ n hU]
    rfl
  pushD_s := by
    intro U hU
    rw [extPushD_eq K ϖ n hU]
    rfl
  pushB_T := by
    classical
    intro U hU t ht
    rw [extPushB_eq K ϖ n hU]
    exact Finset.mem_image_of_mem _ ht
  pushC_T := by
    classical
    intro U hU t ht
    rw [extPushC_eq K ϖ n hU]
    exact Finset.mem_image_of_mem _ ht
  pushD_T := by
    classical
    intro U hU t ht
    rw [extPushD_eq K ϖ n hU]
    exact Finset.mem_image_of_mem _ ht
  pushB_isRational := by
    intro U hU
    rw [extPushB_eq K ϖ n hU]
    exact pushDatumOfHom_isRational _ _ hU
  pushC_isRational := by
    intro U hU
    rw [extPushC_eq K ϖ n hU]
    exact pushDatumOfHom_isRational _ _ hU
  pushD_isRational := by
    intro U hU
    rw [extPushD_eq K ϖ n hU]
    exact pushDatumOfHom_isRational _ _ hU
  legB := StrictLoc.extRhoB K n
  legC := StrictLoc.extRhoC K n
  hlegB := (extPinch K n ϖ).ψB_continuous
  hlegC := (extPinch K n ϖ).ψC_continuous
  legB_s := by
    intro U hU
    rw [extPushB_eq K ϖ n hU, extPushD_eq K ϖ n hU]
    exact (StrictLoc.ext_square_commutes K n U.s).symm
  legC_s := by
    intro U hU
    rw [extPushC_eq K ϖ n hU, extPushD_eq K ϖ n hU]
    rfl
  legB_T := by
    classical
    intro U hU t ht
    rw [extPushB_eq K ϖ n hU] at ht
    rw [extPushD_eq K ϖ n hU]
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp ht
    rw [StrictLoc.ext_square_commutes K n u]
    exact Finset.mem_image_of_mem _ hu
  legC_T := by
    classical
    intro U hU t ht
    rw [extPushC_eq K ϖ n hU] at ht
    rw [extPushD_eq K ϖ n hU]
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp ht
    exact Finset.mem_image_of_mem _ hu
  row_injective := by
    intro U hU x y hB hC
    exact extRowInjectiveAux K ϖ hK₀ n U hU (extPushB_eq K ϖ n hU) (extPushC_eq K ϖ n hU)
      _ _ _ _ _ _ x y hB hC
  row_glue := by
    intro U hU b c h
    exact extRowGlueAux K ϖ hK₀ n U hU (extPushB_eq K ϖ n hU) (extPushC_eq K ϖ n hU)
      (extPushD_eq K ϖ n hU) _ _ _ _ _ _ _ _ _ _ _ _ b c h
  row_embedding := by
    intro U hU
    exact extRowEmbeddingAux K ϖ hK₀ n U hU (extPushB_eq K ϖ n hU) (extPushC_eq K ϖ n hU)
      _ _ _ _ _ _
  pushB_mono := by
    intro U U' hU hU' hsub v hv
    rw [extPushB_eq K ϖ n hU'] at hv
    rw [extPushB_eq K ϖ n hU]
    have hvspa := rationalOpen_subset_spa hv
    exact (mem_rationalOpen_pushDatumOfHom_iff ((extPinch K n ϖ).φB_continuous)
      (plusLe_extJB K ϖ n) (podPB K ϖ n) U hU v hvspa).mpr
      (hsub ((mem_rationalOpen_pushDatumOfHom_iff ((extPinch K n ϖ).φB_continuous)
        (plusLe_extJB K ϖ n) (podPB K ϖ n) U' hU' v hvspa).mp hv))
  pushC_mono := by
    intro U U' hU hU' hsub v hv
    rw [extPushC_eq K ϖ n hU'] at hv
    rw [extPushC_eq K ϖ n hU]
    have hvspa := rationalOpen_subset_spa hv
    exact (mem_rationalOpen_pushDatumOfHom_iff ((extPinch K n ϖ).φC_continuous)
      (plusLe_extIotaC K ϖ n) (podPC K ϖ n) U hU v hvspa).mpr
      (hsub ((mem_rationalOpen_pushDatumOfHom_iff ((extPinch K n ϖ).φC_continuous)
        (plusLe_extIotaC K ϖ n) (podPC K ϖ n) U' hU' v hvspa).mp hv))
  push_natural_B := by
    intro U U' hU hU' h x
    exact presheafValueMapOfHom_restriction (StrictLoc.extJB K n) ((extPinch K n ϖ).φB_continuous)
      U U' (extPushB K ϖ n U) (extPushB K ϖ n U') _ _ _ _ h _ x
  push_natural_C := by
    intro U U' hU hU' h x
    exact presheafValueMapOfHom_restriction (StrictLoc.extIotaC K n) ((extPinch K n ϖ).φC_continuous)
      U U' (extPushC K ϖ n U) (extPushC K ϖ n U') _ _ _ _ h _ x
  pushB_cover := by
    intro U S hU hS hcov w hw
    rw [extPushB_eq K ϖ n hU] at hw
    have hwspa := rationalOpen_subset_spa hw
    obtain ⟨W, hWS, hWmem⟩ := hcov (ValuationSpectrum.comap (StrictLoc.extJB K n) w)
      ((mem_rationalOpen_pushDatumOfHom_iff ((extPinch K n ϖ).φB_continuous)
        (plusLe_extJB K ϖ n) (podPB K ϖ n) U hU w hwspa).mp hw)
    refine ⟨W, hWS, ?_⟩
    rw [extPushB_eq K ϖ n (hS W hWS)]
    exact (mem_rationalOpen_pushDatumOfHom_iff ((extPinch K n ϖ).φB_continuous)
      (plusLe_extJB K ϖ n) (podPB K ϖ n) W (hS W hWS) w hwspa).mpr hWmem
  pushC_cover := by
    intro U S hU hS hcov w hw
    rw [extPushC_eq K ϖ n hU] at hw
    have hwspa := rationalOpen_subset_spa hw
    obtain ⟨W, hWS, hWmem⟩ := hcov (ValuationSpectrum.comap (StrictLoc.extIotaC K n) w)
      ((mem_rationalOpen_pushDatumOfHom_iff ((extPinch K n ϖ).φC_continuous)
        (plusLe_extIotaC K ϖ n) (podPC K ϖ n) U hU w hwspa).mp hw)
    refine ⟨W, hWS, ?_⟩
    rw [extPushC_eq K ϖ n (hS W hWS)]
    exact (mem_rationalOpen_pushDatumOfHom_iff ((extPinch K n ϖ).φC_continuous)
      (plusLe_extIotaC K ϖ n) (podPC K ϖ n) W (hS W hWS) w hwspa).mpr hWmem
  pushD_cover := by
    intro U S hU hS hcov w hw
    rw [extPushD_eq K ϖ n hU] at hw
    have hwspa := rationalOpen_subset_spa hw
    obtain ⟨W, hWS, hWmem⟩ := hcov
      (ValuationSpectrum.comap ((StrictLoc.extRhoC K n).comp (StrictLoc.extIotaC K n)) w)
      ((mem_rationalOpen_pushDatumOfHom_iff
        (by exact ((extPinch K n ϖ).ψC_continuous).comp ((extPinch K n ϖ).φC_continuous))
        (plusLe_extD K ϖ n) (podPD K ϖ n) U hU w hwspa).mp hw)
    refine ⟨W, hWS, ?_⟩
    rw [extPushD_eq K ϖ n (hS W hWS)]
    exact (mem_rationalOpen_pushDatumOfHom_iff
      (by exact ((extPinch K n ϖ).ψC_continuous).comp ((extPinch K n ϖ).φC_continuous))
      (plusLe_extD K ϖ n) (podPD K ϖ n) W (hS W hWS) w hwspa).mpr hWmem
  pushD_mono := by
    intro U U' hU hU' hsub v hv
    rw [extPushD_eq K ϖ n hU'] at hv
    rw [extPushD_eq K ϖ n hU]
    have hvspa := rationalOpen_subset_spa hv
    exact (mem_rationalOpen_pushDatumOfHom_iff
      (by exact ((extPinch K n ϖ).ψC_continuous).comp ((extPinch K n ϖ).φC_continuous))
      (plusLe_extD K ϖ n) (podPD K ϖ n) U hU v hvspa).mpr
      (hsub ((mem_rationalOpen_pushDatumOfHom_iff
        (by exact ((extPinch K n ϖ).ψC_continuous).comp ((extPinch K n ϖ).φC_continuous))
        (plusLe_extD K ϖ n) (podPD K ϖ n) U' hU' v hvspa).mp hv))
  leg_natural_B := by
    intro U U' hU hU' h b
    exact presheafValueMapOfHom_restriction (StrictLoc.extRhoB K n) ((extPinch K n ϖ).ψB_continuous)
      (extPushB K ϖ n U) (extPushB K ϖ n U') (extPushD K ϖ n U) (extPushD K ϖ n U')
      _ _ _ _ _ _ b
  leg_natural_C := by
    intro U U' hU hU' h c
    exact presheafValueMapOfHom_restriction (StrictLoc.extRhoC K n) ((extPinch K n ϖ).ψC_continuous)
      (extPushC K ϖ n U) (extPushC K ϖ n U') (extPushD K ϖ n U) (extPushD K ϖ n U')
      _ _ _ _ _ _ c
  row_comm := by
    intro U hU x
    have hsχ : (extPushD K ϖ n U).s = ((StrictLoc.extRhoC K n).comp (StrictLoc.extIotaC K n)) U.s := by
      rw [extPushD_eq K ϖ n hU]; rfl
    have hTχ : ∀ t ∈ U.T,
        ((StrictLoc.extRhoC K n).comp (StrictLoc.extIotaC K n)) t ∈ (extPushD K ϖ n U).T := by
      classical
      intro t ht
      rw [extPushD_eq K ϖ n hU]
      exact Finset.mem_image_of_mem _ ht
    refine (presheafValueMapOfHom_comp (StrictLoc.extJB K n) ((extPinch K n ϖ).φB_continuous)
      (StrictLoc.extRhoB K n) ((extPinch K n ϖ).ψB_continuous)
      ((StrictLoc.extRhoC K n).comp (StrictLoc.extIotaC K n))
      (by exact ((extPinch K n ϖ).ψC_continuous).comp ((extPinch K n ϖ).φC_continuous))
      (RingHom.ext fun a => StrictLoc.ext_square_commutes K n a)
      U (extPushB K ϖ n U) (extPushD K ϖ n U) _ _ _ _ hsχ hTχ x).trans
      (presheafValueMapOfHom_comp (StrictLoc.extIotaC K n) ((extPinch K n ϖ).φC_continuous)
        (StrictLoc.extRhoC K n) ((extPinch K n ϖ).ψC_continuous)
        ((StrictLoc.extRhoC K n).comp (StrictLoc.extIotaC K n))
        (by exact ((extPinch K n ϖ).ψC_continuous).comp ((extPinch K n ϖ).φC_continuous))
        rfl U (extPushC K ϖ n U) (extPushD K ϖ n U) _ _ _ _ hsχ hTχ x).symm
  pushedCompat_B := by
    intro U₁ U₂ hU₁ hU₂ x₁ x₂ hmatch E₃ hE₁ hE₂
    exact extPushedCompatBAux K ϖ n U₁ U₂ hU₁ hU₂ (extPushB_eq K ϖ n hU₁)
      (extPushB_eq K ϖ n hU₂) _ _ _ _ _ x₁ x₂ hmatch E₃ hE₁ hE₂
  pushedCompat_C := by
    intro U₁ U₂ hU₁ hU₂ x₁ x₂ hmatch E₃ hE₁ hE₂
    exact extPushedCompatCAux K ϖ n U₁ U₂ hU₁ hU₂ (extPushC_eq K ϖ n hU₁)
      (extPushC_eq K ϖ n hU₂) _ _ _ _ _ x₁ x₂ hmatch E₃ hE₁ hE₂

/-! ### Vertex sheafiness and the headline -/

include ϖ hK₀ in
/-- Strong noetherianity of the extended `B`-corner (Fubini + the base facts). -/
theorem isStronglyNoetherian_PB : IsStronglyNoetherian (StrictLoc.PB K n) := by
  refine ⟨fun k => ?_⟩
  obtain ⟨e, -⟩ := exists_flattenPP (JetB K) n k
  have h1 : IsNoetherianRing (P (StrictLoc.PB K n) k) := by
    have := StrictLoc.isNoetherianRing_PB K (n + k) ϖ hK₀
    exact isNoetherianRing_of_surjective (StrictLoc.PB K (n + k)) _
      e.symm.toRingHom e.symm.surjective
  exact isNoetherianRing_of_surjective (P (StrictLoc.PB K n) k) _
    (UnitDiscExample.restrictedGaussEquiv (StrictLoc.PB K n) k).toRingHom
    (RingEquiv.surjective _)

include ϖ hK₀ in
theorem isStronglyNoetherian_PC : IsStronglyNoetherian (StrictLoc.PC K n) := by
  refine ⟨fun k => ?_⟩
  obtain ⟨e, -⟩ := exists_flattenPP (JetC K) n k
  have h1 : IsNoetherianRing (P (StrictLoc.PC K n) k) := by
    have := StrictLoc.isNoetherianRing_PC K (n + k) ϖ hK₀
    exact isNoetherianRing_of_surjective (StrictLoc.PC K (n + k)) _
      e.symm.toRingHom e.symm.surjective
  exact isNoetherianRing_of_surjective (P (StrictLoc.PC K n) k) _
    (UnitDiscExample.restrictedGaussEquiv (StrictLoc.PC K n) k).toRingHom
    (RingEquiv.surjective _)

include ϖ hK₀ in
theorem isStronglyNoetherian_PD : IsStronglyNoetherian (StrictLoc.PD K n) := by
  refine ⟨fun k => ?_⟩
  obtain ⟨e, -⟩ := exists_flattenPP (JetD K) n k
  have h1 : IsNoetherianRing (P (StrictLoc.PD K n) k) := by
    have := StrictLoc.isNoetherianRing_PD K (n + k) ϖ hK₀
    exact isNoetherianRing_of_surjective (StrictLoc.PD K (n + k)) _
      e.symm.toRingHom e.symm.surjective
  exact isNoetherianRing_of_surjective (P (StrictLoc.PD K n) k) _
    (UnitDiscExample.restrictedGaussEquiv (StrictLoc.PD K n) k).toRingHom
    (RingEquiv.surjective _)

include ϖ hK₀ in
/-- Sheafiness of the extended `B`-corner (Wedhorn 8.28(b), clean form). -/
theorem isSheafy_PB : IsSheafy (StrictLoc.PB K n) := by
  have := isStronglyNoetherian_PB K ϖ hK₀ n
  exact ValuationSpectrum.isSheafy_of_stronglyNoetherian_828b

include ϖ hK₀ in
theorem isSheafy_PC : IsSheafy (StrictLoc.PC K n) := by
  have := isStronglyNoetherian_PC K ϖ hK₀ n
  exact ValuationSpectrum.isSheafy_of_stronglyNoetherian_828b

include ϖ hK₀ in
theorem isSheafy_PD : IsSheafy (StrictLoc.PD K n) := by
  have := isStronglyNoetherian_PD K ϖ hK₀ n
  exact ValuationSpectrum.isSheafy_of_stronglyNoetherian_828b

include ϖ hK₀ in
/-- **Sheafiness of the `⟨V⟩`-extended pinching algebra** ([Reviewer] §5.1, the
normed half of the B-headline): the Gauss-normed Tate extension `StrictLoc.PA K n` is
sheafy, by abstract strict Milnor descent at the extended square. -/
theorem isSheafy_extJetA : IsSheafy (StrictLoc.PA K n) := by
  classical
  let _iB : DecidableEq (RationalLocData (StrictLoc.PB K n)) := Classical.decEq _
  let _iC : DecidableEq (RationalLocData (StrictLoc.PC K n)) := Classical.decEq _
  let _iD : DecidableEq (RationalLocData (StrictLoc.PD K n)) := Classical.decEq _
  exact isSheafy_of_milnorSquare (StrictLoc.extJB K n) (StrictLoc.extIotaC K n)
    ((StrictLoc.extRhoC K n).comp (StrictLoc.extIotaC K n))
    ((extPinch K n ϖ).φB_continuous) ((extPinch K n ϖ).φC_continuous)
    (by rw [RingHom.coe_comp]
        exact ((extPinch K n ϖ).ψC_continuous).comp ((extPinch K n ϖ).φC_continuous))
    (extJetSquare K ϖ hK₀ n) (isSheafy_PB K ϖ hK₀ n) (isSheafy_PC K ϖ hK₀ n) (isSheafy_PD K ϖ hK₀ n)

end FiniteJetOver
