/-
Copyright (c) 2026 Qian Tang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qian Tang
-/
module
public import LeanPool.Zeta32.FstarPointsRho.Basic

/-! The fifteen lower bounds `Rlow k ≤ ρ_{a₋}(x_{k+1})`, one declaration per point.
The upstream comments attribute the data (`sl ≤ s ≤ sh`, `P`, `m`) to
`tools/b2_numerics.py`, which is not distributed upstream. The exact inputs and a replacement
rational reproduction procedure are documented in `CertificateReproduction.lean`. Each
side goal is a small `norm_num` on rationals. `U₁ ≤ 211761/100000`, `U₅ ≥ 266853/50000`. -/

public section

open Real
namespace Zeta32.Fstar.B2
noncomputable section

/-- `ρ_{a₋}(x_1) ≥ 223/500`. -/
theorem rho_pt1 : (223 / 500 : ℝ) ≤ rhoA aMinus (xk 1) :=
  rho_ge_of (sl := (186297 / 100000 : ℝ)) (sh := (93149 / 50000 : ℝ)) (U1 := (211761 / 100000 :
    ℝ)) (U5 := (266853 / 50000 : ℝ))
    (P := (29440000 : ℝ)) (by norm_num [xk, aMinus]) (by norm_num [xk, aMinus]) (by norm_num)
      (by norm_num [xk, aMinus])
    (by norm_num) (by norm_num [xk, aMinus]) (by norm_num) (by norm_num [aMinus]) (by norm_num)
      (by norm_num [aMinus])
    (by norm_num) (by norm_num) (by norm_num [aMinus]) (by norm_num)
    (le_trans (by norm_num [lser]) (log_ge _ 24 (by norm_num)))

/-- `ρ_{a₋}(x_2) ≥ 203/500`. -/
theorem rho_pt2 : (203 / 500 : ℝ) ≤ rhoA aMinus (xk 2) :=
  rho_ge_of (sl := (185197 / 100000 : ℝ)) (sh := (92599 / 50000 : ℝ)) (U1 := (211761 / 100000 :
    ℝ)) (U5 := (266853 / 50000 : ℝ))
    (P := (6136000 : ℝ)) (by norm_num [xk, aMinus]) (by norm_num [xk, aMinus]) (by norm_num) (by
      norm_num [xk, aMinus])
    (by norm_num) (by norm_num [xk, aMinus]) (by norm_num) (by norm_num [aMinus]) (by norm_num)
      (by norm_num [aMinus])
    (by norm_num) (by norm_num) (by norm_num [aMinus]) (by norm_num)
    (le_trans (by norm_num [lser]) (log_ge _ 22 (by norm_num)))

/-- `ρ_{a₋}(x_3) ≥ 377/1000`. -/
theorem rho_pt3 : (377 / 1000 : ℝ) ≤ rhoA aMinus (xk 3) :=
  rho_ge_of (sl := (183351 / 100000 : ℝ)) (sh := (22919 / 12500 : ℝ)) (U1 := (211761 / 100000 :
    ℝ)) (U5 := (266853 / 50000 : ℝ))
    (P := (2042700 : ℝ)) (by norm_num [xk, aMinus]) (by norm_num [xk, aMinus]) (by norm_num) (by
      norm_num [xk, aMinus])
    (by norm_num) (by norm_num [xk, aMinus]) (by norm_num) (by norm_num [aMinus]) (by norm_num)
      (by norm_num [aMinus])
    (by norm_num) (by norm_num) (by norm_num [aMinus]) (by norm_num)
    (le_trans (by norm_num [lser]) (log_ge _ 20 (by norm_num)))

/-- `ρ_{a₋}(x_4) ≥ 44/125`. -/
theorem rho_pt4 : (44 / 125 : ℝ) ≤ rhoA aMinus (xk 4) :=
  rho_ge_of (sl := (90367 / 50000 : ℝ)) (sh := (36147 / 20000 : ℝ)) (U1 := (211761 / 100000 :
    ℝ)) (U5 := (266853 / 50000 : ℝ))
    (P := (784100 : ℝ)) (by norm_num [xk, aMinus]) (by norm_num [xk, aMinus]) (by norm_num) (by
      norm_num [xk, aMinus])
    (by norm_num) (by norm_num [xk, aMinus]) (by norm_num) (by norm_num [aMinus]) (by norm_num)
      (by norm_num [aMinus])
    (by norm_num) (by norm_num) (by norm_num [aMinus]) (by norm_num)
    (le_trans (by norm_num [lser]) (log_ge _ 19 (by norm_num)))

/-- `ρ_{a₋}(x_5) ≥ 329/1000`. -/
theorem rho_pt5 : (329 / 1000 : ℝ) ≤ rhoA aMinus (xk 5) :=
  rho_ge_of (sl := (177313 / 100000 : ℝ)) (sh := (88657 / 50000 : ℝ)) (U1 := (211761 / 100000 :
    ℝ)) (U5 := (266853 / 50000 : ℝ))
    (P := (317550 : ℝ)) (by norm_num [xk, aMinus]) (by norm_num [xk, aMinus]) (by norm_num) (by
      norm_num [xk, aMinus])
    (by norm_num) (by norm_num [xk, aMinus]) (by norm_num) (by norm_num [aMinus]) (by norm_num)
      (by norm_num [aMinus])
    (by norm_num) (by norm_num) (by norm_num [aMinus]) (by norm_num)
    (le_trans (by norm_num [lser]) (log_ge _ 18 (by norm_num)))

/-- `ρ_{a₋}(x_6) ≥ 153/500`. -/
theorem rho_pt6 : (153 / 500 : ℝ) ≤ rhoA aMinus (xk 6) :=
  rho_ge_of (sl := (2163 / 1250 : ℝ)) (sh := (173041 / 100000 : ℝ)) (U1 := (211761 / 100000 :
    ℝ)) (U5 := (266853 / 50000 : ℝ))
    (P := (131430 : ℝ)) (by norm_num [xk, aMinus]) (by norm_num [xk, aMinus]) (by norm_num) (by
      norm_num [xk, aMinus])
    (by norm_num) (by norm_num [xk, aMinus]) (by norm_num) (by norm_num [aMinus]) (by norm_num)
      (by norm_num [aMinus])
    (by norm_num) (by norm_num) (by norm_num [aMinus]) (by norm_num)
    (le_trans (by norm_num [lser]) (log_ge _ 17 (by norm_num)))

/-- `ρ_{a₋}(x_7) ≥ 283/1000`. -/
theorem rho_pt7 : (283 / 1000 : ℝ) ≤ rhoA aMinus (xk 7) :=
  rho_ge_of (sl := (167849 / 100000 : ℝ)) (sh := (3357 / 2000 : ℝ)) (U1 := (211761 / 100000 :
    ℝ)) (U5 := (266853 / 50000 : ℝ))
    (P := (54882 : ℝ)) (by norm_num [xk, aMinus]) (by norm_num [xk, aMinus]) (by norm_num) (by
      norm_num [xk, aMinus])
    (by norm_num) (by norm_num [xk, aMinus]) (by norm_num) (by norm_num [aMinus]) (by norm_num)
      (by norm_num [aMinus])
    (by norm_num) (by norm_num) (by norm_num [aMinus]) (by norm_num)
    (le_trans (by norm_num [lser]) (log_ge _ 15 (by norm_num)))

/-- `ρ_{a₋}(x_8) ≥ 13/50`. -/
theorem rho_pt8 : (13 / 50 : ℝ) ≤ rhoA aMinus (xk 8) :=
  rho_ge_of (sl := (80827 / 50000 : ℝ)) (sh := (32331 / 20000 : ℝ)) (U1 := (211761 / 100000 :
    ℝ)) (U5 := (266853 / 50000 : ℝ))
    (P := (22985 : ℝ)) (by norm_num [xk, aMinus]) (by norm_num [xk, aMinus]) (by norm_num) (by
      norm_num [xk, aMinus])
    (by norm_num) (by norm_num [xk, aMinus]) (by norm_num) (by norm_num [aMinus]) (by norm_num)
      (by norm_num [aMinus])
    (by norm_num) (by norm_num) (by norm_num [aMinus]) (by norm_num)
    (le_trans (by norm_num [lser]) (log_ge _ 14 (by norm_num)))

/-- `ρ_{a₋}(x_9) ≥ 119/500`. -/
theorem rho_pt9 : (119 / 500 : ℝ) ≤ rhoA aMinus (xk 9) :=
  rho_ge_of (sl := (154331 / 100000 : ℝ)) (sh := (38583 / 25000 : ℝ)) (U1 := (211761 / 100000 :
    ℝ)) (U5 := (266853 / 50000 : ℝ))
    (P := (19205 / 2 : ℝ)) (by norm_num [xk, aMinus]) (by norm_num [xk, aMinus]) (by norm_num)
      (by norm_num [xk, aMinus])
    (by norm_num) (by norm_num [xk, aMinus]) (by norm_num) (by norm_num [aMinus]) (by norm_num)
      (by norm_num [aMinus])
    (by norm_num) (by norm_num) (by norm_num [aMinus]) (by norm_num)
    (le_trans (by norm_num [lser]) (log_ge _ 13 (by norm_num)))

/-- `ρ_{a₋}(x_10) ≥ 43/200`. -/
theorem rho_pt10 : (43 / 200 : ℝ) ≤ rhoA aMinus (xk 10) :=
  rho_ge_of (sl := (9107 / 6250 : ℝ)) (sh := (145713 / 100000 : ℝ)) (U1 := (211761 / 100000 :
    ℝ)) (U5 := (266853 / 50000 : ℝ))
    (P := (39771 / 10 : ℝ)) (by norm_num [xk, aMinus]) (by norm_num [xk, aMinus]) (by norm_num)
      (by norm_num [xk, aMinus])
    (by norm_num) (by norm_num [xk, aMinus]) (by norm_num) (by norm_num [aMinus]) (by norm_num)
      (by norm_num [aMinus])
    (by norm_num) (by norm_num) (by norm_num [aMinus]) (by norm_num)
    (le_trans (by norm_num [lser]) (log_ge _ 11 (by norm_num)))

/-- `ρ_{a₋}(x_11) ≥ 191/1000`. -/
theorem rho_pt11 : (191 / 1000 : ℝ) ≤ rhoA aMinus (xk 11) :=
  rho_ge_of (sl := (135551 / 100000 : ℝ)) (sh := (4236 / 3125 : ℝ)) (U1 := (211761 / 100000 :
    ℝ)) (U5 := (266853 / 50000 : ℝ))
    (P := (16177 / 10 : ℝ)) (by norm_num [xk, aMinus]) (by norm_num [xk, aMinus]) (by norm_num)
      (by norm_num [xk, aMinus])
    (by norm_num) (by norm_num [xk, aMinus]) (by norm_num) (by norm_num [aMinus]) (by norm_num)
      (by norm_num [aMinus])
    (by norm_num) (by norm_num) (by norm_num [aMinus]) (by norm_num)
    (le_trans (by norm_num [lser]) (log_ge _ 10 (by norm_num)))

/-- `ρ_{a₋}(x_12) ≥ 167/1000`. -/
theorem rho_pt12 : (167 / 1000 : ℝ) ≤ rhoA aMinus (xk 12) :=
  rho_ge_of (sl := (24693 / 20000 : ℝ)) (sh := (61733 / 50000 : ℝ)) (U1 := (211761 / 100000 :
    ℝ)) (U5 := (266853 / 50000 : ℝ))
    (P := (15912 / 25 : ℝ)) (by norm_num [xk, aMinus]) (by norm_num [xk, aMinus]) (by norm_num)
      (by norm_num [xk, aMinus])
    (by norm_num) (by norm_num [xk, aMinus]) (by norm_num) (by norm_num [aMinus]) (by norm_num)
      (by norm_num [aMinus])
    (by norm_num) (by norm_num) (by norm_num [aMinus]) (by norm_num)
    (le_trans (by norm_num [lser]) (log_ge _ 9 (by norm_num)))

/-- `ρ_{a₋}(x_13) ≥ 71/500`. -/
theorem rho_pt13 : (71 / 500 : ℝ) ≤ rhoA aMinus (xk 13) :=
  rho_ge_of (sl := (6801 / 6250 : ℝ)) (sh := (108817 / 100000 : ℝ)) (U1 := (211761 / 100000 :
    ℝ)) (U5 := (266853 / 50000 : ℝ))
    (P := (23603 / 100 : ℝ)) (by norm_num [xk, aMinus]) (by norm_num [xk, aMinus]) (by norm_num)
      (by norm_num [xk, aMinus])
    (by norm_num) (by norm_num [xk, aMinus]) (by norm_num) (by norm_num [aMinus]) (by norm_num)
      (by norm_num [aMinus])
    (by norm_num) (by norm_num) (by norm_num [aMinus]) (by norm_num)
    (le_trans (by norm_num [lser]) (log_ge _ 7 (by norm_num)))

/-- `ρ_{a₋}(x_14) ≥ 113/1000`. -/
theorem rho_pt14 : (113 / 1000 : ℝ) ≤ rhoA aMinus (xk 14) :=
  rho_ge_of (sl := (90367 / 100000 : ℝ)) (sh := (2824 / 3125 : ℝ)) (U1 := (211761 / 100000 : ℝ))
    (U5 := (266853 / 50000 : ℝ))
    (P := (39207 / 500 : ℝ)) (by norm_num [xk, aMinus]) (by norm_num [xk, aMinus]) (by norm_num)
      (by norm_num [xk, aMinus])
    (by norm_num) (by norm_num [xk, aMinus]) (by norm_num) (by norm_num [aMinus]) (by norm_num)
      (by norm_num [aMinus])
    (by norm_num) (by norm_num) (by norm_num [aMinus]) (by norm_num)
    (le_trans (by norm_num [lser]) (log_ge _ 6 (by norm_num)))

/-- `ρ_{a₋}(x_15) ≥ 39/500`. -/
theorem rho_pt15 : (39 / 500 : ℝ) ≤ rhoA aMinus (xk 15) :=
  rho_ge_of (sl := (12991 / 20000 : ℝ)) (sh := (16239 / 25000 : ℝ)) (U1 := (211761 / 100000 :
    ℝ)) (U5 := (266853 / 50000 : ℝ))
    (P := (20433 / 1000 : ℝ)) (by norm_num [xk, aMinus]) (by norm_num [xk, aMinus]) (by
      norm_num) (by norm_num [xk, aMinus])
    (by norm_num) (by norm_num [xk, aMinus]) (by norm_num) (by norm_num [aMinus]) (by norm_num)
      (by norm_num [aMinus])
    (by norm_num) (by norm_num) (by norm_num [aMinus]) (by norm_num)
    (le_trans (by norm_num [lser]) (log_ge _ 4 (by norm_num)))

theorem rho_all : ∀ k : Fin 15, ((Rlow k : ℚ) : ℝ) ≤ rhoA aMinus (xk (k.val + 1)) := by
  intro k
  fin_cases k
  · simpa [Rlow] using rho_pt1
  · simpa [Rlow] using rho_pt2
  · simpa [Rlow] using rho_pt3
  · simpa [Rlow] using rho_pt4
  · simpa [Rlow] using rho_pt5
  · simpa [Rlow] using rho_pt6
  · simpa [Rlow] using rho_pt7
  · simpa [Rlow] using rho_pt8
  · simpa [Rlow] using rho_pt9
  · simpa [Rlow] using rho_pt10
  · simpa [Rlow] using rho_pt11
  · simpa [Rlow] using rho_pt12
  · simpa [Rlow] using rho_pt13
  · simpa [Rlow] using rho_pt14
  · simpa [Rlow] using rho_pt15

end
end Zeta32.Fstar.B2
