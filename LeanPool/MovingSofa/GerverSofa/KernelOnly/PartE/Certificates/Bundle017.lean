/-
Copyright (c) 2026 Dawid Trela. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dawid Trela
-/
module

public import LeanPool.MovingSofa.GerverSofa.KernelOnly.Core.Bundle005
/-!
# Gerver sofa: related certificate and semantic modules

* `GerverSofa.KernelOnly.PartE.Certificates.Batch030`.
-/

public section

noncomputable section

namespace GerverSofa.PartE.CertificateCellsbc9ee1179f

/-- Subcell `0000` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000 : AngleCell :=
  childLL (childLL (childLL (childLL e24ThetaAboveRoot)))

/-- Subcell `00002201` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00002201 : AngleCell :=
  childLH (childLL (childHL (childHL thetaAboveCell0000)))

/-- Subcell `000022012100` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022012100 : AngleCell :=
  childLL (childLL (childLH (childHL thetaAboveCell00002201)))

/-- Subcell `000022012101` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022012101 : AngleCell :=
  childLH (childLL (childLH (childHL thetaAboveCell00002201)))

/-- Subcell `000022012102` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022012102 : AngleCell :=
  childHL (childLL (childLH (childHL thetaAboveCell00002201)))

/-- Subcell `000022012103` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022012103 : AngleCell :=
  childHH (childLL (childLH (childHL thetaAboveCell00002201)))

/-- Subcell `000022012110` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022012110 : AngleCell :=
  childLL (childLH (childLH (childHL thetaAboveCell00002201)))

/-- Subcell `000022012111` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022012111 : AngleCell :=
  childLH (childLH (childLH (childHL thetaAboveCell00002201)))

/-- Subcell `000022012112` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022012112 : AngleCell :=
  childHL (childLH (childLH (childHL thetaAboveCell00002201)))

/-- Subcell `000022012113` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022012113 : AngleCell :=
  childHH (childLH (childLH (childHL thetaAboveCell00002201)))

/-- Subcell `000022012120` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022012120 : AngleCell :=
  childLL (childHL (childLH (childHL thetaAboveCell00002201)))

/-- Subcell `000022012121` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022012121 : AngleCell :=
  childLH (childHL (childLH (childHL thetaAboveCell00002201)))

/-- Subcell `000022012122` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022012122 : AngleCell :=
  childHL (childHL (childLH (childHL thetaAboveCell00002201)))

/-- Subcell `000022012123` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022012123 : AngleCell :=
  childHH (childHL (childLH (childHL thetaAboveCell00002201)))

/-- Subcell `000022012130` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022012130 : AngleCell :=
  childLL (childHH (childLH (childHL thetaAboveCell00002201)))

/-- Subcell `000022012131` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022012131 : AngleCell :=
  childLH (childHH (childLH (childHL thetaAboveCell00002201)))

/-- Subcell `000022012132` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022012132 : AngleCell :=
  childHL (childHH (childLH (childHL thetaAboveCell00002201)))

/-- Subcell `000022012133` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022012133 : AngleCell :=
  childHH (childHH (childLH (childHL thetaAboveCell00002201)))

/-- Subcell `000022013000` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022013000 : AngleCell :=
  childLL (childLL (childLL (childHH thetaAboveCell00002201)))

/-- Subcell `000022013001` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022013001 : AngleCell :=
  childLH (childLL (childLL (childHH thetaAboveCell00002201)))

/-- Subcell `000022013002` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022013002 : AngleCell :=
  childHL (childLL (childLL (childHH thetaAboveCell00002201)))

/-- Subcell `000022013003` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022013003 : AngleCell :=
  childHH (childLL (childLL (childHH thetaAboveCell00002201)))

/-- Subcell `000022013010` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022013010 : AngleCell :=
  childLL (childLH (childLL (childHH thetaAboveCell00002201)))

/-- Subcell `000022013011` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022013011 : AngleCell :=
  childLH (childLH (childLL (childHH thetaAboveCell00002201)))

/-- Subcell `000022013012` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022013012 : AngleCell :=
  childHL (childLH (childLL (childHH thetaAboveCell00002201)))

/-- Subcell `000022013013` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022013013 : AngleCell :=
  childHH (childLH (childLL (childHH thetaAboveCell00002201)))

/-- Subcell `000022013020` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022013020 : AngleCell :=
  childLL (childHL (childLL (childHH thetaAboveCell00002201)))

/-- Subcell `000022013021` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022013021 : AngleCell :=
  childLH (childHL (childLL (childHH thetaAboveCell00002201)))

/-- Subcell `000022013022` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022013022 : AngleCell :=
  childHL (childHL (childLL (childHH thetaAboveCell00002201)))

/-- Subcell `000022013023` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022013023 : AngleCell :=
  childHH (childHL (childLL (childHH thetaAboveCell00002201)))

/-- Subcell `000022013030` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022013030 : AngleCell :=
  childLL (childHH (childLL (childHH thetaAboveCell00002201)))

/-- Subcell `000022013031` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022013031 : AngleCell :=
  childLH (childHH (childLL (childHH thetaAboveCell00002201)))

/-- Subcell `000022013032` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022013032 : AngleCell :=
  childHL (childHH (childLL (childHH thetaAboveCell00002201)))

/-- Subcell `000022013033` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022013033 : AngleCell :=
  childHH (childHH (childLL (childHH thetaAboveCell00002201)))

/-- Subcell `0000220121002020` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220121002020 : AngleCell :=
  childLL (childHL (childLL (childHL thetaAboveCell000022012100)))

/-- Subcell `0000220121002021` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220121002021 : AngleCell :=
  childLH (childHL (childLL (childHL thetaAboveCell000022012100)))

/-- Subcell `0000220121002022` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220121002022 : AngleCell :=
  childHL (childHL (childLL (childHL thetaAboveCell000022012100)))

/-- Subcell `0000220121002023` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220121002023 : AngleCell :=
  childHH (childHL (childLL (childHL thetaAboveCell000022012100)))

/-- Subcell `0000220121002030` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220121002030 : AngleCell :=
  childLL (childHH (childLL (childHL thetaAboveCell000022012100)))

/-- Subcell `0000220121002031` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220121002031 : AngleCell :=
  childLH (childHH (childLL (childHL thetaAboveCell000022012100)))

/-- Subcell `0000220121002032` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220121002032 : AngleCell :=
  childHL (childHH (childLL (childHL thetaAboveCell000022012100)))

/-- Subcell `0000220121002033` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220121002033 : AngleCell :=
  childHH (childHH (childLL (childHL thetaAboveCell000022012100)))

/-- Subcell `0000220121002120` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220121002120 : AngleCell :=
  childLL (childHL (childLH (childHL thetaAboveCell000022012100)))

/-- Subcell `0000220121002121` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220121002121 : AngleCell :=
  childLH (childHL (childLH (childHL thetaAboveCell000022012100)))

/-- Subcell `0000220121002122` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220121002122 : AngleCell :=
  childHL (childHL (childLH (childHL thetaAboveCell000022012100)))

/-- Subcell `0000220121002123` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220121002123 : AngleCell :=
  childHH (childHL (childLH (childHL thetaAboveCell000022012100)))

/-- Subcell `0000220121002130` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220121002130 : AngleCell :=
  childLL (childHH (childLH (childHL thetaAboveCell000022012100)))

/-- Subcell `0000220121002131` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220121002131 : AngleCell :=
  childLH (childHH (childLH (childHL thetaAboveCell000022012100)))

/-- Subcell `0000220121002132` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220121002132 : AngleCell :=
  childHL (childHH (childLH (childHL thetaAboveCell000022012100)))

/-- Subcell `0000220121002133` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220121002133 : AngleCell :=
  childHH (childHH (childLH (childHL thetaAboveCell000022012100)))

/-- Subcell `0000220121002200` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220121002200 : AngleCell :=
  childLL (childLL (childHL (childHL thetaAboveCell000022012100)))

/-- Subcell `0000220121002201` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220121002201 : AngleCell :=
  childLH (childLL (childHL (childHL thetaAboveCell000022012100)))

/-- Subcell `0000220121002202` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220121002202 : AngleCell :=
  childHL (childLL (childHL (childHL thetaAboveCell000022012100)))

/-- Subcell `0000220121002203` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220121002203 : AngleCell :=
  childHH (childLL (childHL (childHL thetaAboveCell000022012100)))

/-- Subcell `0000220121002210` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220121002210 : AngleCell :=
  childLL (childLH (childHL (childHL thetaAboveCell000022012100)))

/-- Subcell `0000220121002211` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220121002211 : AngleCell :=
  childLH (childLH (childHL (childHL thetaAboveCell000022012100)))

/-- Subcell `0000220121002212` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220121002212 : AngleCell :=
  childHL (childLH (childHL (childHL thetaAboveCell000022012100)))

/-- Subcell `0000220121002213` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220121002213 : AngleCell :=
  childHH (childLH (childHL (childHL thetaAboveCell000022012100)))

/-- Subcell `0000220121002220` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220121002220 : AngleCell :=
  childLL (childHL (childHL (childHL thetaAboveCell000022012100)))

/-- Subcell `0000220121002221` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220121002221 : AngleCell :=
  childLH (childHL (childHL (childHL thetaAboveCell000022012100)))

/-- Subcell `0000220121002222` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220121002222 : AngleCell :=
  childHL (childHL (childHL (childHL thetaAboveCell000022012100)))

/-- Subcell `0000220121002223` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220121002223 : AngleCell :=
  childHH (childHL (childHL (childHL thetaAboveCell000022012100)))

/-- Subcell `0000220121002230` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220121002230 : AngleCell :=
  childLL (childHH (childHL (childHL thetaAboveCell000022012100)))

/-- Subcell `0000220121002231` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220121002231 : AngleCell :=
  childLH (childHH (childHL (childHL thetaAboveCell000022012100)))

/-- Subcell `0000220121002232` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220121002232 : AngleCell :=
  childHL (childHH (childHL (childHL thetaAboveCell000022012100)))

/-- Subcell `0000220121002233` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220121002233 : AngleCell :=
  childHH (childHH (childHL (childHL thetaAboveCell000022012100)))

/-- Subcell `0000220121002300` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220121002300 : AngleCell :=
  childLL (childLL (childHH (childHL thetaAboveCell000022012100)))

/-- Subcell `0000220121002301` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220121002301 : AngleCell :=
  childLH (childLL (childHH (childHL thetaAboveCell000022012100)))

/-- Subcell `0000220121002302` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220121002302 : AngleCell :=
  childHL (childLL (childHH (childHL thetaAboveCell000022012100)))

/-- Subcell `0000220121002303` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220121002303 : AngleCell :=
  childHH (childLL (childHH (childHL thetaAboveCell000022012100)))

/-- Subcell `0000220121002310` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220121002310 : AngleCell :=
  childLL (childLH (childHH (childHL thetaAboveCell000022012100)))

/-- Subcell `0000220121002311` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220121002311 : AngleCell :=
  childLH (childLH (childHH (childHL thetaAboveCell000022012100)))

/-- Subcell `0000220121002312` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220121002312 : AngleCell :=
  childHL (childLH (childHH (childHL thetaAboveCell000022012100)))

/-- Subcell `0000220121002313` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220121002313 : AngleCell :=
  childHH (childLH (childHH (childHL thetaAboveCell000022012100)))

/-- Subcell `0000220121002320` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220121002320 : AngleCell :=
  childLL (childHL (childHH (childHL thetaAboveCell000022012100)))

/-- Subcell `0000220121002321` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220121002321 : AngleCell :=
  childLH (childHL (childHH (childHL thetaAboveCell000022012100)))

/-- Subcell `0000220121002322` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220121002322 : AngleCell :=
  childHL (childHL (childHH (childHL thetaAboveCell000022012100)))

/-- Subcell `0000220121002323` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220121002323 : AngleCell :=
  childHH (childHL (childHH (childHL thetaAboveCell000022012100)))

/-- Subcell `0000220121002330` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220121002330 : AngleCell :=
  childLL (childHH (childHH (childHL thetaAboveCell000022012100)))

/-- Subcell `0000220121002331` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220121002331 : AngleCell :=
  childLH (childHH (childHH (childHL thetaAboveCell000022012100)))

/-- Subcell `0000220121002332` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220121002332 : AngleCell :=
  childHL (childHH (childHH (childHL thetaAboveCell000022012100)))

/-- Subcell `0000220121002333` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220121002333 : AngleCell :=
  childHH (childHH (childHH (childHL thetaAboveCell000022012100)))

/-- Subcell `0000220121003020` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220121003020 : AngleCell :=
  childLL (childHL (childLL (childHH thetaAboveCell000022012100)))

/-- Subcell `0000220121003021` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220121003021 : AngleCell :=
  childLH (childHL (childLL (childHH thetaAboveCell000022012100)))

/-- Subcell `0000220121003022` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220121003022 : AngleCell :=
  childHL (childHL (childLL (childHH thetaAboveCell000022012100)))

/-- Subcell `0000220121003023` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220121003023 : AngleCell :=
  childHH (childHL (childLL (childHH thetaAboveCell000022012100)))

/-- Subcell `0000220121003030` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220121003030 : AngleCell :=
  childLL (childHH (childLL (childHH thetaAboveCell000022012100)))

/-- Subcell `0000220121003031` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220121003031 : AngleCell :=
  childLH (childHH (childLL (childHH thetaAboveCell000022012100)))

/-- Subcell `0000220121003032` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220121003032 : AngleCell :=
  childHL (childHH (childLL (childHH thetaAboveCell000022012100)))

/-- Subcell `0000220121003033` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220121003033 : AngleCell :=
  childHH (childHH (childLL (childHH thetaAboveCell000022012100)))

/-- Subcell `0000220121003120` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220121003120 : AngleCell :=
  childLL (childHL (childLH (childHH thetaAboveCell000022012100)))

/-- Subcell `0000220121003121` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220121003121 : AngleCell :=
  childLH (childHL (childLH (childHH thetaAboveCell000022012100)))

/-- Subcell `0000220121003122` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220121003122 : AngleCell :=
  childHL (childHL (childLH (childHH thetaAboveCell000022012100)))

/-- Subcell `0000220121003123` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220121003123 : AngleCell :=
  childHH (childHL (childLH (childHH thetaAboveCell000022012100)))

/-- Subcell `0000220121003130` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220121003130 : AngleCell :=
  childLL (childHH (childLH (childHH thetaAboveCell000022012100)))

/-- Subcell `0000220121003131` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220121003131 : AngleCell :=
  childLH (childHH (childLH (childHH thetaAboveCell000022012100)))

/-- Subcell `0000220121003132` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220121003132 : AngleCell :=
  childHL (childHH (childLH (childHH thetaAboveCell000022012100)))

/-- Subcell `0000220121003133` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220121003133 : AngleCell :=
  childHH (childHH (childLH (childHH thetaAboveCell000022012100)))

/-- Subcell `0000220121003200` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220121003200 : AngleCell :=
  childLL (childLL (childHL (childHH thetaAboveCell000022012100)))

/-- Subcell `0000220121003201` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220121003201 : AngleCell :=
  childLH (childLL (childHL (childHH thetaAboveCell000022012100)))

/-- Subcell `0000220121003202` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220121003202 : AngleCell :=
  childHL (childLL (childHL (childHH thetaAboveCell000022012100)))

/-- Subcell `0000220121003203` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220121003203 : AngleCell :=
  childHH (childLL (childHL (childHH thetaAboveCell000022012100)))

/-- Subcell `0000220121003210` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220121003210 : AngleCell :=
  childLL (childLH (childHL (childHH thetaAboveCell000022012100)))

/-- Subcell `0000220121003211` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220121003211 : AngleCell :=
  childLH (childLH (childHL (childHH thetaAboveCell000022012100)))

/-- Subcell `0000220121003212` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220121003212 : AngleCell :=
  childHL (childLH (childHL (childHH thetaAboveCell000022012100)))

/-- Subcell `0000220121003213` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220121003213 : AngleCell :=
  childHH (childLH (childHL (childHH thetaAboveCell000022012100)))

/-- Subcell `0000220121003220` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220121003220 : AngleCell :=
  childLL (childHL (childHL (childHH thetaAboveCell000022012100)))

/-- Subcell `0000220121003221` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220121003221 : AngleCell :=
  childLH (childHL (childHL (childHH thetaAboveCell000022012100)))

/-- Subcell `0000220121003222` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220121003222 : AngleCell :=
  childHL (childHL (childHL (childHH thetaAboveCell000022012100)))

/-- Subcell `0000220121003223` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220121003223 : AngleCell :=
  childHH (childHL (childHL (childHH thetaAboveCell000022012100)))

/-- Subcell `0000220121003230` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220121003230 : AngleCell :=
  childLL (childHH (childHL (childHH thetaAboveCell000022012100)))

/-- Subcell `0000220121003231` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220121003231 : AngleCell :=
  childLH (childHH (childHL (childHH thetaAboveCell000022012100)))

/-- Subcell `0000220121003232` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220121003232 : AngleCell :=
  childHL (childHH (childHL (childHH thetaAboveCell000022012100)))

/-- Subcell `0000220121003233` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220121003233 : AngleCell :=
  childHH (childHH (childHL (childHH thetaAboveCell000022012100)))

/-- Subcell `0000220121003300` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220121003300 : AngleCell :=
  childLL (childLL (childHH (childHH thetaAboveCell000022012100)))

/-- Subcell `0000220121003301` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220121003301 : AngleCell :=
  childLH (childLL (childHH (childHH thetaAboveCell000022012100)))

/-- Subcell `0000220121003302` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220121003302 : AngleCell :=
  childHL (childLL (childHH (childHH thetaAboveCell000022012100)))

/-- Subcell `0000220121003303` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220121003303 : AngleCell :=
  childHH (childLL (childHH (childHH thetaAboveCell000022012100)))

/-- Subcell `0000220121003310` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220121003310 : AngleCell :=
  childLL (childLH (childHH (childHH thetaAboveCell000022012100)))

/-- Subcell `0000220121003311` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220121003311 : AngleCell :=
  childLH (childLH (childHH (childHH thetaAboveCell000022012100)))

/-- Subcell `0000220121003312` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220121003312 : AngleCell :=
  childHL (childLH (childHH (childHH thetaAboveCell000022012100)))

/-- Subcell `0000220121003313` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220121003313 : AngleCell :=
  childHH (childLH (childHH (childHH thetaAboveCell000022012100)))

/-- Subcell `0000220121003320` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220121003320 : AngleCell :=
  childLL (childHL (childHH (childHH thetaAboveCell000022012100)))

/-- Subcell `0000220121003321` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220121003321 : AngleCell :=
  childLH (childHL (childHH (childHH thetaAboveCell000022012100)))

/-- Subcell `0000220121003322` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220121003322 : AngleCell :=
  childHL (childHL (childHH (childHH thetaAboveCell000022012100)))

/-- Subcell `0000220121003323` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220121003323 : AngleCell :=
  childHH (childHL (childHH (childHH thetaAboveCell000022012100)))

/-- Subcell `0000220121003330` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220121003330 : AngleCell :=
  childLL (childHH (childHH (childHH thetaAboveCell000022012100)))

/-- Subcell `0000220121003331` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220121003331 : AngleCell :=
  childLH (childHH (childHH (childHH thetaAboveCell000022012100)))

/-- Subcell `0000220121003332` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220121003332 : AngleCell :=
  childHL (childHH (childHH (childHH thetaAboveCell000022012100)))

/-- Subcell `0000220121003333` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220121003333 : AngleCell :=
  childHH (childHH (childHH (childHH thetaAboveCell000022012100)))

/-- Subcell `0000220121012020` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220121012020 : AngleCell :=
  childLL (childHL (childLL (childHL thetaAboveCell000022012101)))

/-- Subcell `0000220121012021` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220121012021 : AngleCell :=
  childLH (childHL (childLL (childHL thetaAboveCell000022012101)))

/-- Subcell `0000220121012022` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220121012022 : AngleCell :=
  childHL (childHL (childLL (childHL thetaAboveCell000022012101)))

/-- Subcell `0000220121012023` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220121012023 : AngleCell :=
  childHH (childHL (childLL (childHL thetaAboveCell000022012101)))

/-- Subcell `0000220121012030` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220121012030 : AngleCell :=
  childLL (childHH (childLL (childHL thetaAboveCell000022012101)))

/-- Subcell `0000220121012031` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220121012031 : AngleCell :=
  childLH (childHH (childLL (childHL thetaAboveCell000022012101)))

/-- Subcell `0000220121012032` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220121012032 : AngleCell :=
  childHL (childHH (childLL (childHL thetaAboveCell000022012101)))

/-- Subcell `0000220121012033` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220121012033 : AngleCell :=
  childHH (childHH (childLL (childHL thetaAboveCell000022012101)))

/-- Subcell `0000220121012120` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220121012120 : AngleCell :=
  childLL (childHL (childLH (childHL thetaAboveCell000022012101)))

/-- Subcell `0000220121012121` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220121012121 : AngleCell :=
  childLH (childHL (childLH (childHL thetaAboveCell000022012101)))

/-- Subcell `0000220121012122` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220121012122 : AngleCell :=
  childHL (childHL (childLH (childHL thetaAboveCell000022012101)))

/-- Subcell `0000220121012123` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220121012123 : AngleCell :=
  childHH (childHL (childLH (childHL thetaAboveCell000022012101)))

/-- Subcell `0000220121012130` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220121012130 : AngleCell :=
  childLL (childHH (childLH (childHL thetaAboveCell000022012101)))

/-- Subcell `0000220121012131` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220121012131 : AngleCell :=
  childLH (childHH (childLH (childHL thetaAboveCell000022012101)))

/-- Subcell `0000220121012132` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220121012132 : AngleCell :=
  childHL (childHH (childLH (childHL thetaAboveCell000022012101)))

/-- Subcell `0000220121012133` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220121012133 : AngleCell :=
  childHH (childHH (childLH (childHL thetaAboveCell000022012101)))

/-- Subcell `0000220121012200` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220121012200 : AngleCell :=
  childLL (childLL (childHL (childHL thetaAboveCell000022012101)))

/-- Subcell `0000220121012201` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220121012201 : AngleCell :=
  childLH (childLL (childHL (childHL thetaAboveCell000022012101)))

/-- Subcell `0000220121012202` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220121012202 : AngleCell :=
  childHL (childLL (childHL (childHL thetaAboveCell000022012101)))

/-- Subcell `0000220121012203` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220121012203 : AngleCell :=
  childHH (childLL (childHL (childHL thetaAboveCell000022012101)))

/-- Subcell `0000220121012210` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220121012210 : AngleCell :=
  childLL (childLH (childHL (childHL thetaAboveCell000022012101)))

/-- Subcell `0000220121012211` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220121012211 : AngleCell :=
  childLH (childLH (childHL (childHL thetaAboveCell000022012101)))

/-- Subcell `0000220121012212` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220121012212 : AngleCell :=
  childHL (childLH (childHL (childHL thetaAboveCell000022012101)))

/-- Subcell `0000220121012213` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220121012213 : AngleCell :=
  childHH (childLH (childHL (childHL thetaAboveCell000022012101)))

/-- Subcell `0000220121012220` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220121012220 : AngleCell :=
  childLL (childHL (childHL (childHL thetaAboveCell000022012101)))

/-- Subcell `0000220121012221` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220121012221 : AngleCell :=
  childLH (childHL (childHL (childHL thetaAboveCell000022012101)))

/-- Subcell `0000220121012222` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220121012222 : AngleCell :=
  childHL (childHL (childHL (childHL thetaAboveCell000022012101)))

/-- Subcell `0000220121012223` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220121012223 : AngleCell :=
  childHH (childHL (childHL (childHL thetaAboveCell000022012101)))

/-- Subcell `0000220121012230` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220121012230 : AngleCell :=
  childLL (childHH (childHL (childHL thetaAboveCell000022012101)))

/-- Subcell `0000220121012231` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220121012231 : AngleCell :=
  childLH (childHH (childHL (childHL thetaAboveCell000022012101)))

/-- Subcell `0000220121012232` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220121012232 : AngleCell :=
  childHL (childHH (childHL (childHL thetaAboveCell000022012101)))

/-- Subcell `0000220121012233` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220121012233 : AngleCell :=
  childHH (childHH (childHL (childHL thetaAboveCell000022012101)))

/-- Subcell `0000220121012300` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220121012300 : AngleCell :=
  childLL (childLL (childHH (childHL thetaAboveCell000022012101)))

/-- Subcell `0000220121012301` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220121012301 : AngleCell :=
  childLH (childLL (childHH (childHL thetaAboveCell000022012101)))

/-- Subcell `0000220121012302` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220121012302 : AngleCell :=
  childHL (childLL (childHH (childHL thetaAboveCell000022012101)))

/-- Subcell `0000220121012303` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220121012303 : AngleCell :=
  childHH (childLL (childHH (childHL thetaAboveCell000022012101)))

/-- Subcell `0000220121012310` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220121012310 : AngleCell :=
  childLL (childLH (childHH (childHL thetaAboveCell000022012101)))

/-- Subcell `0000220121012311` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220121012311 : AngleCell :=
  childLH (childLH (childHH (childHL thetaAboveCell000022012101)))

/-- Subcell `0000220121012312` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220121012312 : AngleCell :=
  childHL (childLH (childHH (childHL thetaAboveCell000022012101)))

/-- Subcell `0000220121012313` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220121012313 : AngleCell :=
  childHH (childLH (childHH (childHL thetaAboveCell000022012101)))

/-- Subcell `0000220121012320` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220121012320 : AngleCell :=
  childLL (childHL (childHH (childHL thetaAboveCell000022012101)))

/-- Subcell `0000220121012321` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220121012321 : AngleCell :=
  childLH (childHL (childHH (childHL thetaAboveCell000022012101)))

/-- Subcell `0000220121012322` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220121012322 : AngleCell :=
  childHL (childHL (childHH (childHL thetaAboveCell000022012101)))

/-- Subcell `0000220121012323` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220121012323 : AngleCell :=
  childHH (childHL (childHH (childHL thetaAboveCell000022012101)))

/-- Subcell `0000220121012330` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220121012330 : AngleCell :=
  childLL (childHH (childHH (childHL thetaAboveCell000022012101)))

/-- Subcell `0000220121012331` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220121012331 : AngleCell :=
  childLH (childHH (childHH (childHL thetaAboveCell000022012101)))

/-- Subcell `0000220121012332` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220121012332 : AngleCell :=
  childHL (childHH (childHH (childHL thetaAboveCell000022012101)))

/-- Subcell `0000220121012333` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220121012333 : AngleCell :=
  childHH (childHH (childHH (childHL thetaAboveCell000022012101)))

/-- Subcell `0000220121013020` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220121013020 : AngleCell :=
  childLL (childHL (childLL (childHH thetaAboveCell000022012101)))

/-- Subcell `0000220121013021` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220121013021 : AngleCell :=
  childLH (childHL (childLL (childHH thetaAboveCell000022012101)))

/-- Subcell `0000220121013022` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220121013022 : AngleCell :=
  childHL (childHL (childLL (childHH thetaAboveCell000022012101)))

/-- Subcell `0000220121013023` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220121013023 : AngleCell :=
  childHH (childHL (childLL (childHH thetaAboveCell000022012101)))

/-- Subcell `0000220121013030` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220121013030 : AngleCell :=
  childLL (childHH (childLL (childHH thetaAboveCell000022012101)))

/-- Subcell `0000220121013031` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220121013031 : AngleCell :=
  childLH (childHH (childLL (childHH thetaAboveCell000022012101)))

/-- Subcell `0000220121013032` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220121013032 : AngleCell :=
  childHL (childHH (childLL (childHH thetaAboveCell000022012101)))

/-- Subcell `0000220121013033` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220121013033 : AngleCell :=
  childHH (childHH (childLL (childHH thetaAboveCell000022012101)))

/-- Subcell `0000220121013120` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220121013120 : AngleCell :=
  childLL (childHL (childLH (childHH thetaAboveCell000022012101)))

/-- Subcell `0000220121013121` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220121013121 : AngleCell :=
  childLH (childHL (childLH (childHH thetaAboveCell000022012101)))

/-- Subcell `0000220121013122` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220121013122 : AngleCell :=
  childHL (childHL (childLH (childHH thetaAboveCell000022012101)))

/-- Subcell `0000220121013123` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220121013123 : AngleCell :=
  childHH (childHL (childLH (childHH thetaAboveCell000022012101)))

/-- Subcell `0000220121013130` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220121013130 : AngleCell :=
  childLL (childHH (childLH (childHH thetaAboveCell000022012101)))

/-- Subcell `0000220121013131` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220121013131 : AngleCell :=
  childLH (childHH (childLH (childHH thetaAboveCell000022012101)))

/-- Subcell `0000220121013132` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220121013132 : AngleCell :=
  childHL (childHH (childLH (childHH thetaAboveCell000022012101)))

/-- Subcell `0000220121013133` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220121013133 : AngleCell :=
  childHH (childHH (childLH (childHH thetaAboveCell000022012101)))

/-- Subcell `0000220121013200` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220121013200 : AngleCell :=
  childLL (childLL (childHL (childHH thetaAboveCell000022012101)))

/-- Subcell `0000220121013201` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220121013201 : AngleCell :=
  childLH (childLL (childHL (childHH thetaAboveCell000022012101)))

/-- Subcell `0000220121013202` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220121013202 : AngleCell :=
  childHL (childLL (childHL (childHH thetaAboveCell000022012101)))

/-- Subcell `0000220121013203` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220121013203 : AngleCell :=
  childHH (childLL (childHL (childHH thetaAboveCell000022012101)))

/-- Subcell `0000220121013210` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220121013210 : AngleCell :=
  childLL (childLH (childHL (childHH thetaAboveCell000022012101)))

/-- Subcell `0000220121013211` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220121013211 : AngleCell :=
  childLH (childLH (childHL (childHH thetaAboveCell000022012101)))

/-- Subcell `0000220121013212` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220121013212 : AngleCell :=
  childHL (childLH (childHL (childHH thetaAboveCell000022012101)))

/-- Subcell `0000220121013213` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220121013213 : AngleCell :=
  childHH (childLH (childHL (childHH thetaAboveCell000022012101)))

/-- Subcell `0000220121013220` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220121013220 : AngleCell :=
  childLL (childHL (childHL (childHH thetaAboveCell000022012101)))

/-- Subcell `0000220121013221` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220121013221 : AngleCell :=
  childLH (childHL (childHL (childHH thetaAboveCell000022012101)))

/-- Subcell `0000220121013222` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220121013222 : AngleCell :=
  childHL (childHL (childHL (childHH thetaAboveCell000022012101)))

/-- Subcell `0000220121013223` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220121013223 : AngleCell :=
  childHH (childHL (childHL (childHH thetaAboveCell000022012101)))

/-- Subcell `0000220121013230` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220121013230 : AngleCell :=
  childLL (childHH (childHL (childHH thetaAboveCell000022012101)))

/-- Subcell `0000220121013231` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220121013231 : AngleCell :=
  childLH (childHH (childHL (childHH thetaAboveCell000022012101)))

/-- Subcell `0000220121013232` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220121013232 : AngleCell :=
  childHL (childHH (childHL (childHH thetaAboveCell000022012101)))

/-- Subcell `0000220121013233` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220121013233 : AngleCell :=
  childHH (childHH (childHL (childHH thetaAboveCell000022012101)))

/-- Subcell `0000220121013300` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220121013300 : AngleCell :=
  childLL (childLL (childHH (childHH thetaAboveCell000022012101)))

/-- Subcell `0000220121013301` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220121013301 : AngleCell :=
  childLH (childLL (childHH (childHH thetaAboveCell000022012101)))

/-- Subcell `0000220121013302` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220121013302 : AngleCell :=
  childHL (childLL (childHH (childHH thetaAboveCell000022012101)))

/-- Subcell `0000220121013303` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220121013303 : AngleCell :=
  childHH (childLL (childHH (childHH thetaAboveCell000022012101)))

/-- Subcell `0000220121013310` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220121013310 : AngleCell :=
  childLL (childLH (childHH (childHH thetaAboveCell000022012101)))

/-- Subcell `0000220121013311` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220121013311 : AngleCell :=
  childLH (childLH (childHH (childHH thetaAboveCell000022012101)))

/-- Subcell `0000220121013312` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220121013312 : AngleCell :=
  childHL (childLH (childHH (childHH thetaAboveCell000022012101)))

/-- Subcell `0000220121013313` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220121013313 : AngleCell :=
  childHH (childLH (childHH (childHH thetaAboveCell000022012101)))

/-- Subcell `0000220121013320` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220121013320 : AngleCell :=
  childLL (childHL (childHH (childHH thetaAboveCell000022012101)))

/-- Subcell `0000220121013321` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220121013321 : AngleCell :=
  childLH (childHL (childHH (childHH thetaAboveCell000022012101)))

/-- Subcell `0000220121013322` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220121013322 : AngleCell :=
  childHL (childHL (childHH (childHH thetaAboveCell000022012101)))

/-- Subcell `0000220121013323` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220121013323 : AngleCell :=
  childHH (childHL (childHH (childHH thetaAboveCell000022012101)))

/-- Subcell `0000220121013330` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220121013330 : AngleCell :=
  childLL (childHH (childHH (childHH thetaAboveCell000022012101)))

/-- Subcell `0000220121013331` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220121013331 : AngleCell :=
  childLH (childHH (childHH (childHH thetaAboveCell000022012101)))

/-- Subcell `0000220121013332` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220121013332 : AngleCell :=
  childHL (childHH (childHH (childHH thetaAboveCell000022012101)))

/-- Subcell `0000220121013333` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220121013333 : AngleCell :=
  childHH (childHH (childHH (childHH thetaAboveCell000022012101)))

/-- Subcell `0000220121102020` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220121102020 : AngleCell :=
  childLL (childHL (childLL (childHL thetaAboveCell000022012110)))

/-- Subcell `0000220121102021` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220121102021 : AngleCell :=
  childLH (childHL (childLL (childHL thetaAboveCell000022012110)))

/-- Subcell `0000220121102022` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220121102022 : AngleCell :=
  childHL (childHL (childLL (childHL thetaAboveCell000022012110)))

/-- Subcell `0000220121102023` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220121102023 : AngleCell :=
  childHH (childHL (childLL (childHL thetaAboveCell000022012110)))

/-- Subcell `0000220121102030` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220121102030 : AngleCell :=
  childLL (childHH (childLL (childHL thetaAboveCell000022012110)))

/-- Subcell `0000220121102031` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220121102031 : AngleCell :=
  childLH (childHH (childLL (childHL thetaAboveCell000022012110)))

/-- Subcell `0000220121102032` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220121102032 : AngleCell :=
  childHL (childHH (childLL (childHL thetaAboveCell000022012110)))

/-- Subcell `0000220121102033` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220121102033 : AngleCell :=
  childHH (childHH (childLL (childHL thetaAboveCell000022012110)))

/-- Subcell `0000220121102120` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220121102120 : AngleCell :=
  childLL (childHL (childLH (childHL thetaAboveCell000022012110)))

/-- Subcell `0000220121102121` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220121102121 : AngleCell :=
  childLH (childHL (childLH (childHL thetaAboveCell000022012110)))

/-- Subcell `0000220121102122` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220121102122 : AngleCell :=
  childHL (childHL (childLH (childHL thetaAboveCell000022012110)))

/-- Subcell `0000220121102123` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220121102123 : AngleCell :=
  childHH (childHL (childLH (childHL thetaAboveCell000022012110)))

/-- Subcell `0000220121102130` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220121102130 : AngleCell :=
  childLL (childHH (childLH (childHL thetaAboveCell000022012110)))

/-- Subcell `0000220121102131` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220121102131 : AngleCell :=
  childLH (childHH (childLH (childHL thetaAboveCell000022012110)))

/-- Subcell `0000220121102132` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220121102132 : AngleCell :=
  childHL (childHH (childLH (childHL thetaAboveCell000022012110)))

/-- Subcell `0000220121102133` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220121102133 : AngleCell :=
  childHH (childHH (childLH (childHL thetaAboveCell000022012110)))

/-- Subcell `0000220121102200` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220121102200 : AngleCell :=
  childLL (childLL (childHL (childHL thetaAboveCell000022012110)))

/-- Subcell `0000220121102201` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220121102201 : AngleCell :=
  childLH (childLL (childHL (childHL thetaAboveCell000022012110)))

/-- Subcell `0000220121102202` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220121102202 : AngleCell :=
  childHL (childLL (childHL (childHL thetaAboveCell000022012110)))

/-- Subcell `0000220121102203` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220121102203 : AngleCell :=
  childHH (childLL (childHL (childHL thetaAboveCell000022012110)))

/-- Subcell `0000220121102210` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220121102210 : AngleCell :=
  childLL (childLH (childHL (childHL thetaAboveCell000022012110)))

/-- Subcell `0000220121102211` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220121102211 : AngleCell :=
  childLH (childLH (childHL (childHL thetaAboveCell000022012110)))

/-- Subcell `0000220121102212` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220121102212 : AngleCell :=
  childHL (childLH (childHL (childHL thetaAboveCell000022012110)))

/-- Subcell `0000220121102213` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220121102213 : AngleCell :=
  childHH (childLH (childHL (childHL thetaAboveCell000022012110)))

/-- Subcell `0000220121102220` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220121102220 : AngleCell :=
  childLL (childHL (childHL (childHL thetaAboveCell000022012110)))

/-- Subcell `0000220121102221` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220121102221 : AngleCell :=
  childLH (childHL (childHL (childHL thetaAboveCell000022012110)))

/-- Subcell `0000220121102222` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220121102222 : AngleCell :=
  childHL (childHL (childHL (childHL thetaAboveCell000022012110)))

/-- Subcell `0000220121102223` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220121102223 : AngleCell :=
  childHH (childHL (childHL (childHL thetaAboveCell000022012110)))

/-- Subcell `0000220121102230` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220121102230 : AngleCell :=
  childLL (childHH (childHL (childHL thetaAboveCell000022012110)))

/-- Subcell `0000220121102231` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220121102231 : AngleCell :=
  childLH (childHH (childHL (childHL thetaAboveCell000022012110)))

/-- Subcell `0000220121102232` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220121102232 : AngleCell :=
  childHL (childHH (childHL (childHL thetaAboveCell000022012110)))

/-- Subcell `0000220121102233` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220121102233 : AngleCell :=
  childHH (childHH (childHL (childHL thetaAboveCell000022012110)))

/-- Subcell `0000220121102300` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220121102300 : AngleCell :=
  childLL (childLL (childHH (childHL thetaAboveCell000022012110)))

/-- Subcell `0000220121102301` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220121102301 : AngleCell :=
  childLH (childLL (childHH (childHL thetaAboveCell000022012110)))

/-- Subcell `0000220121102302` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220121102302 : AngleCell :=
  childHL (childLL (childHH (childHL thetaAboveCell000022012110)))

/-- Subcell `0000220121102303` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220121102303 : AngleCell :=
  childHH (childLL (childHH (childHL thetaAboveCell000022012110)))

/-- Subcell `0000220121102310` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220121102310 : AngleCell :=
  childLL (childLH (childHH (childHL thetaAboveCell000022012110)))

/-- Subcell `0000220121102311` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220121102311 : AngleCell :=
  childLH (childLH (childHH (childHL thetaAboveCell000022012110)))

/-- Subcell `0000220121102312` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220121102312 : AngleCell :=
  childHL (childLH (childHH (childHL thetaAboveCell000022012110)))

/-- Subcell `0000220121102313` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220121102313 : AngleCell :=
  childHH (childLH (childHH (childHL thetaAboveCell000022012110)))

/-- Subcell `0000220121102320` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220121102320 : AngleCell :=
  childLL (childHL (childHH (childHL thetaAboveCell000022012110)))

/-- Subcell `0000220121102321` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220121102321 : AngleCell :=
  childLH (childHL (childHH (childHL thetaAboveCell000022012110)))

/-- Subcell `0000220121102322` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220121102322 : AngleCell :=
  childHL (childHL (childHH (childHL thetaAboveCell000022012110)))

/-- Subcell `0000220121102323` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220121102323 : AngleCell :=
  childHH (childHL (childHH (childHL thetaAboveCell000022012110)))

/-- Subcell `0000220121102330` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220121102330 : AngleCell :=
  childLL (childHH (childHH (childHL thetaAboveCell000022012110)))

/-- Subcell `0000220121102331` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220121102331 : AngleCell :=
  childLH (childHH (childHH (childHL thetaAboveCell000022012110)))

/-- Subcell `0000220121102332` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220121102332 : AngleCell :=
  childHL (childHH (childHH (childHL thetaAboveCell000022012110)))

/-- Subcell `0000220121102333` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220121102333 : AngleCell :=
  childHH (childHH (childHH (childHL thetaAboveCell000022012110)))

/-- Subcell `0000220121103020` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220121103020 : AngleCell :=
  childLL (childHL (childLL (childHH thetaAboveCell000022012110)))

/-- Subcell `0000220121103021` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220121103021 : AngleCell :=
  childLH (childHL (childLL (childHH thetaAboveCell000022012110)))

/-- Subcell `0000220121103022` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220121103022 : AngleCell :=
  childHL (childHL (childLL (childHH thetaAboveCell000022012110)))

/-- Subcell `0000220121103023` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220121103023 : AngleCell :=
  childHH (childHL (childLL (childHH thetaAboveCell000022012110)))

/-- Subcell `0000220121103030` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220121103030 : AngleCell :=
  childLL (childHH (childLL (childHH thetaAboveCell000022012110)))

/-- Subcell `0000220121103031` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220121103031 : AngleCell :=
  childLH (childHH (childLL (childHH thetaAboveCell000022012110)))

/-- Subcell `0000220121103032` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220121103032 : AngleCell :=
  childHL (childHH (childLL (childHH thetaAboveCell000022012110)))

/-- Subcell `0000220121103033` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220121103033 : AngleCell :=
  childHH (childHH (childLL (childHH thetaAboveCell000022012110)))

/-- Subcell `0000220121103120` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220121103120 : AngleCell :=
  childLL (childHL (childLH (childHH thetaAboveCell000022012110)))

/-- Subcell `0000220121103121` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220121103121 : AngleCell :=
  childLH (childHL (childLH (childHH thetaAboveCell000022012110)))

/-- Subcell `0000220121103122` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220121103122 : AngleCell :=
  childHL (childHL (childLH (childHH thetaAboveCell000022012110)))

/-- Subcell `0000220121103123` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220121103123 : AngleCell :=
  childHH (childHL (childLH (childHH thetaAboveCell000022012110)))

/-- Subcell `0000220121103130` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220121103130 : AngleCell :=
  childLL (childHH (childLH (childHH thetaAboveCell000022012110)))

/-- Subcell `0000220121103131` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220121103131 : AngleCell :=
  childLH (childHH (childLH (childHH thetaAboveCell000022012110)))

/-- Subcell `0000220121103132` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220121103132 : AngleCell :=
  childHL (childHH (childLH (childHH thetaAboveCell000022012110)))

/-- Subcell `0000220121103133` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220121103133 : AngleCell :=
  childHH (childHH (childLH (childHH thetaAboveCell000022012110)))

/-- Subcell `0000220121103200` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220121103200 : AngleCell :=
  childLL (childLL (childHL (childHH thetaAboveCell000022012110)))

/-- Subcell `0000220121103201` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220121103201 : AngleCell :=
  childLH (childLL (childHL (childHH thetaAboveCell000022012110)))

/-- Subcell `0000220121103202` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220121103202 : AngleCell :=
  childHL (childLL (childHL (childHH thetaAboveCell000022012110)))

/-- Subcell `0000220121103203` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220121103203 : AngleCell :=
  childHH (childLL (childHL (childHH thetaAboveCell000022012110)))

/-- Subcell `0000220121103210` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220121103210 : AngleCell :=
  childLL (childLH (childHL (childHH thetaAboveCell000022012110)))

/-- Subcell `0000220121103211` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220121103211 : AngleCell :=
  childLH (childLH (childHL (childHH thetaAboveCell000022012110)))

/-- Subcell `0000220121103212` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220121103212 : AngleCell :=
  childHL (childLH (childHL (childHH thetaAboveCell000022012110)))

/-- Subcell `0000220121103213` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220121103213 : AngleCell :=
  childHH (childLH (childHL (childHH thetaAboveCell000022012110)))

/-- Subcell `0000220121103220` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220121103220 : AngleCell :=
  childLL (childHL (childHL (childHH thetaAboveCell000022012110)))

/-- Subcell `0000220121103221` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220121103221 : AngleCell :=
  childLH (childHL (childHL (childHH thetaAboveCell000022012110)))

/-- Subcell `0000220121103222` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220121103222 : AngleCell :=
  childHL (childHL (childHL (childHH thetaAboveCell000022012110)))

/-- Subcell `0000220121103223` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220121103223 : AngleCell :=
  childHH (childHL (childHL (childHH thetaAboveCell000022012110)))

/-- Subcell `0000220121103230` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220121103230 : AngleCell :=
  childLL (childHH (childHL (childHH thetaAboveCell000022012110)))

/-- Subcell `0000220121103231` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220121103231 : AngleCell :=
  childLH (childHH (childHL (childHH thetaAboveCell000022012110)))

/-- Subcell `0000220121103232` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220121103232 : AngleCell :=
  childHL (childHH (childHL (childHH thetaAboveCell000022012110)))

/-- Subcell `0000220121103233` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220121103233 : AngleCell :=
  childHH (childHH (childHL (childHH thetaAboveCell000022012110)))

/-- Subcell `0000220121103300` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220121103300 : AngleCell :=
  childLL (childLL (childHH (childHH thetaAboveCell000022012110)))

/-- Subcell `0000220121103301` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220121103301 : AngleCell :=
  childLH (childLL (childHH (childHH thetaAboveCell000022012110)))

/-- Subcell `0000220121103302` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220121103302 : AngleCell :=
  childHL (childLL (childHH (childHH thetaAboveCell000022012110)))

/-- Subcell `0000220121103303` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220121103303 : AngleCell :=
  childHH (childLL (childHH (childHH thetaAboveCell000022012110)))

/-- Subcell `0000220121103310` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220121103310 : AngleCell :=
  childLL (childLH (childHH (childHH thetaAboveCell000022012110)))

/-- Subcell `0000220121103311` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220121103311 : AngleCell :=
  childLH (childLH (childHH (childHH thetaAboveCell000022012110)))

/-- Subcell `0000220121103312` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220121103312 : AngleCell :=
  childHL (childLH (childHH (childHH thetaAboveCell000022012110)))

/-- Subcell `0000220121103313` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220121103313 : AngleCell :=
  childHH (childLH (childHH (childHH thetaAboveCell000022012110)))

/-- Subcell `0000220121103320` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220121103320 : AngleCell :=
  childLL (childHL (childHH (childHH thetaAboveCell000022012110)))

/-- Subcell `0000220121103321` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220121103321 : AngleCell :=
  childLH (childHL (childHH (childHH thetaAboveCell000022012110)))

/-- Subcell `0000220121103322` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220121103322 : AngleCell :=
  childHL (childHL (childHH (childHH thetaAboveCell000022012110)))

/-- Subcell `0000220121103323` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220121103323 : AngleCell :=
  childHH (childHL (childHH (childHH thetaAboveCell000022012110)))

/-- Subcell `0000220121103330` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220121103330 : AngleCell :=
  childLL (childHH (childHH (childHH thetaAboveCell000022012110)))

/-- Subcell `0000220121103331` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220121103331 : AngleCell :=
  childLH (childHH (childHH (childHH thetaAboveCell000022012110)))

/-- Subcell `0000220121103332` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220121103332 : AngleCell :=
  childHL (childHH (childHH (childHH thetaAboveCell000022012110)))

/-- Subcell `0000220121103333` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220121103333 : AngleCell :=
  childHH (childHH (childHH (childHH thetaAboveCell000022012110)))

/-- Subcell `0000220121112020` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220121112020 : AngleCell :=
  childLL (childHL (childLL (childHL thetaAboveCell000022012111)))

/-- Subcell `0000220121112021` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220121112021 : AngleCell :=
  childLH (childHL (childLL (childHL thetaAboveCell000022012111)))

/-- Subcell `0000220121112022` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220121112022 : AngleCell :=
  childHL (childHL (childLL (childHL thetaAboveCell000022012111)))

/-- Subcell `0000220121112023` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220121112023 : AngleCell :=
  childHH (childHL (childLL (childHL thetaAboveCell000022012111)))

/-- Subcell `0000220121112030` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220121112030 : AngleCell :=
  childLL (childHH (childLL (childHL thetaAboveCell000022012111)))

/-- Subcell `0000220121112031` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220121112031 : AngleCell :=
  childLH (childHH (childLL (childHL thetaAboveCell000022012111)))

/-- Subcell `0000220121112032` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220121112032 : AngleCell :=
  childHL (childHH (childLL (childHL thetaAboveCell000022012111)))

/-- Subcell `0000220121112033` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220121112033 : AngleCell :=
  childHH (childHH (childLL (childHL thetaAboveCell000022012111)))

/-- Subcell `0000220121112120` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220121112120 : AngleCell :=
  childLL (childHL (childLH (childHL thetaAboveCell000022012111)))

/-- Subcell `0000220121112121` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220121112121 : AngleCell :=
  childLH (childHL (childLH (childHL thetaAboveCell000022012111)))

/-- Subcell `0000220121112122` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220121112122 : AngleCell :=
  childHL (childHL (childLH (childHL thetaAboveCell000022012111)))

/-- Subcell `0000220121112123` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220121112123 : AngleCell :=
  childHH (childHL (childLH (childHL thetaAboveCell000022012111)))

/-- Subcell `0000220121112130` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220121112130 : AngleCell :=
  childLL (childHH (childLH (childHL thetaAboveCell000022012111)))

/-- Subcell `0000220121112131` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220121112131 : AngleCell :=
  childLH (childHH (childLH (childHL thetaAboveCell000022012111)))

/-- Subcell `0000220121112132` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220121112132 : AngleCell :=
  childHL (childHH (childLH (childHL thetaAboveCell000022012111)))

/-- Subcell `0000220121112133` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220121112133 : AngleCell :=
  childHH (childHH (childLH (childHL thetaAboveCell000022012111)))

/-- Subcell `0000220121112200` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220121112200 : AngleCell :=
  childLL (childLL (childHL (childHL thetaAboveCell000022012111)))

/-- Subcell `0000220121112201` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220121112201 : AngleCell :=
  childLH (childLL (childHL (childHL thetaAboveCell000022012111)))

/-- Subcell `0000220121112202` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220121112202 : AngleCell :=
  childHL (childLL (childHL (childHL thetaAboveCell000022012111)))

/-- Subcell `0000220121112203` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220121112203 : AngleCell :=
  childHH (childLL (childHL (childHL thetaAboveCell000022012111)))

/-- Subcell `0000220121112210` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220121112210 : AngleCell :=
  childLL (childLH (childHL (childHL thetaAboveCell000022012111)))

/-- Subcell `0000220121112211` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220121112211 : AngleCell :=
  childLH (childLH (childHL (childHL thetaAboveCell000022012111)))

/-- Subcell `0000220121112212` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220121112212 : AngleCell :=
  childHL (childLH (childHL (childHL thetaAboveCell000022012111)))

/-- Subcell `0000220121112213` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220121112213 : AngleCell :=
  childHH (childLH (childHL (childHL thetaAboveCell000022012111)))

/-- Subcell `0000220121112220` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220121112220 : AngleCell :=
  childLL (childHL (childHL (childHL thetaAboveCell000022012111)))

/-- Subcell `0000220121112221` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220121112221 : AngleCell :=
  childLH (childHL (childHL (childHL thetaAboveCell000022012111)))

/-- Subcell `0000220121112222` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220121112222 : AngleCell :=
  childHL (childHL (childHL (childHL thetaAboveCell000022012111)))

/-- Subcell `0000220121112223` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220121112223 : AngleCell :=
  childHH (childHL (childHL (childHL thetaAboveCell000022012111)))

/-- Subcell `0000220121112230` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220121112230 : AngleCell :=
  childLL (childHH (childHL (childHL thetaAboveCell000022012111)))

/-- Subcell `0000220121112231` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220121112231 : AngleCell :=
  childLH (childHH (childHL (childHL thetaAboveCell000022012111)))

/-- Subcell `0000220121112232` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220121112232 : AngleCell :=
  childHL (childHH (childHL (childHL thetaAboveCell000022012111)))

/-- Subcell `0000220121112233` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220121112233 : AngleCell :=
  childHH (childHH (childHL (childHL thetaAboveCell000022012111)))

/-- Subcell `0000220121112300` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220121112300 : AngleCell :=
  childLL (childLL (childHH (childHL thetaAboveCell000022012111)))

/-- Subcell `0000220121112301` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220121112301 : AngleCell :=
  childLH (childLL (childHH (childHL thetaAboveCell000022012111)))

/-- Subcell `0000220121112302` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220121112302 : AngleCell :=
  childHL (childLL (childHH (childHL thetaAboveCell000022012111)))

/-- Subcell `0000220121112303` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220121112303 : AngleCell :=
  childHH (childLL (childHH (childHL thetaAboveCell000022012111)))

/-- Subcell `0000220121112310` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220121112310 : AngleCell :=
  childLL (childLH (childHH (childHL thetaAboveCell000022012111)))

/-- Subcell `0000220121112311` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220121112311 : AngleCell :=
  childLH (childLH (childHH (childHL thetaAboveCell000022012111)))

/-- Subcell `0000220121112312` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220121112312 : AngleCell :=
  childHL (childLH (childHH (childHL thetaAboveCell000022012111)))

/-- Subcell `0000220121112313` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220121112313 : AngleCell :=
  childHH (childLH (childHH (childHL thetaAboveCell000022012111)))

/-- Subcell `0000220121112320` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220121112320 : AngleCell :=
  childLL (childHL (childHH (childHL thetaAboveCell000022012111)))

/-- Subcell `0000220121112321` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220121112321 : AngleCell :=
  childLH (childHL (childHH (childHL thetaAboveCell000022012111)))

/-- Subcell `0000220121112322` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220121112322 : AngleCell :=
  childHL (childHL (childHH (childHL thetaAboveCell000022012111)))

/-- Subcell `0000220121112323` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220121112323 : AngleCell :=
  childHH (childHL (childHH (childHL thetaAboveCell000022012111)))

/-- Subcell `0000220121112330` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220121112330 : AngleCell :=
  childLL (childHH (childHH (childHL thetaAboveCell000022012111)))

/-- Subcell `0000220121112331` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220121112331 : AngleCell :=
  childLH (childHH (childHH (childHL thetaAboveCell000022012111)))

/-- Subcell `0000220121112332` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220121112332 : AngleCell :=
  childHL (childHH (childHH (childHL thetaAboveCell000022012111)))

/-- Subcell `0000220121112333` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220121112333 : AngleCell :=
  childHH (childHH (childHH (childHL thetaAboveCell000022012111)))

/-- Subcell `0000220121113020` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220121113020 : AngleCell :=
  childLL (childHL (childLL (childHH thetaAboveCell000022012111)))

/-- Subcell `0000220121113021` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220121113021 : AngleCell :=
  childLH (childHL (childLL (childHH thetaAboveCell000022012111)))

/-- Subcell `0000220121113022` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220121113022 : AngleCell :=
  childHL (childHL (childLL (childHH thetaAboveCell000022012111)))

/-- Subcell `0000220121113023` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220121113023 : AngleCell :=
  childHH (childHL (childLL (childHH thetaAboveCell000022012111)))

/-- Subcell `0000220121113030` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220121113030 : AngleCell :=
  childLL (childHH (childLL (childHH thetaAboveCell000022012111)))

/-- Subcell `0000220121113031` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220121113031 : AngleCell :=
  childLH (childHH (childLL (childHH thetaAboveCell000022012111)))

/-- Subcell `0000220121113032` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220121113032 : AngleCell :=
  childHL (childHH (childLL (childHH thetaAboveCell000022012111)))

/-- Subcell `0000220121113033` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220121113033 : AngleCell :=
  childHH (childHH (childLL (childHH thetaAboveCell000022012111)))

/-- Subcell `0000220121113120` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220121113120 : AngleCell :=
  childLL (childHL (childLH (childHH thetaAboveCell000022012111)))

/-- Subcell `0000220121113121` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220121113121 : AngleCell :=
  childLH (childHL (childLH (childHH thetaAboveCell000022012111)))

/-- Subcell `0000220121113122` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220121113122 : AngleCell :=
  childHL (childHL (childLH (childHH thetaAboveCell000022012111)))

/-- Subcell `0000220121113123` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220121113123 : AngleCell :=
  childHH (childHL (childLH (childHH thetaAboveCell000022012111)))

/-- Subcell `0000220121113130` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220121113130 : AngleCell :=
  childLL (childHH (childLH (childHH thetaAboveCell000022012111)))

/-- Subcell `0000220121113131` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220121113131 : AngleCell :=
  childLH (childHH (childLH (childHH thetaAboveCell000022012111)))

/-- Subcell `0000220121113132` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220121113132 : AngleCell :=
  childHL (childHH (childLH (childHH thetaAboveCell000022012111)))

/-- Subcell `0000220121113133` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220121113133 : AngleCell :=
  childHH (childHH (childLH (childHH thetaAboveCell000022012111)))

/-- Subcell `0000220121113200` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220121113200 : AngleCell :=
  childLL (childLL (childHL (childHH thetaAboveCell000022012111)))

/-- Subcell `0000220121113201` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220121113201 : AngleCell :=
  childLH (childLL (childHL (childHH thetaAboveCell000022012111)))

/-- Subcell `0000220121113202` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220121113202 : AngleCell :=
  childHL (childLL (childHL (childHH thetaAboveCell000022012111)))

/-- Subcell `0000220121113203` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220121113203 : AngleCell :=
  childHH (childLL (childHL (childHH thetaAboveCell000022012111)))

/-- Subcell `0000220121113210` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220121113210 : AngleCell :=
  childLL (childLH (childHL (childHH thetaAboveCell000022012111)))

/-- Subcell `0000220121113211` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220121113211 : AngleCell :=
  childLH (childLH (childHL (childHH thetaAboveCell000022012111)))

/-- Subcell `0000220121113212` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220121113212 : AngleCell :=
  childHL (childLH (childHL (childHH thetaAboveCell000022012111)))

/-- Subcell `0000220121113213` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220121113213 : AngleCell :=
  childHH (childLH (childHL (childHH thetaAboveCell000022012111)))

/-- Subcell `0000220121113220` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220121113220 : AngleCell :=
  childLL (childHL (childHL (childHH thetaAboveCell000022012111)))

/-- Subcell `0000220121113221` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220121113221 : AngleCell :=
  childLH (childHL (childHL (childHH thetaAboveCell000022012111)))

/-- Subcell `0000220121113222` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220121113222 : AngleCell :=
  childHL (childHL (childHL (childHH thetaAboveCell000022012111)))

/-- Subcell `0000220121113223` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220121113223 : AngleCell :=
  childHH (childHL (childHL (childHH thetaAboveCell000022012111)))

/-- Subcell `0000220121113230` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220121113230 : AngleCell :=
  childLL (childHH (childHL (childHH thetaAboveCell000022012111)))

/-- Subcell `0000220121113231` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220121113231 : AngleCell :=
  childLH (childHH (childHL (childHH thetaAboveCell000022012111)))

/-- Subcell `0000220121113232` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220121113232 : AngleCell :=
  childHL (childHH (childHL (childHH thetaAboveCell000022012111)))

/-- Subcell `0000220121113233` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220121113233 : AngleCell :=
  childHH (childHH (childHL (childHH thetaAboveCell000022012111)))

/-- Subcell `0000220121113300` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220121113300 : AngleCell :=
  childLL (childLL (childHH (childHH thetaAboveCell000022012111)))

/-- Subcell `0000220121113301` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220121113301 : AngleCell :=
  childLH (childLL (childHH (childHH thetaAboveCell000022012111)))

/-- Subcell `0000220121113302` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220121113302 : AngleCell :=
  childHL (childLL (childHH (childHH thetaAboveCell000022012111)))

/-- Subcell `0000220121113303` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220121113303 : AngleCell :=
  childHH (childLL (childHH (childHH thetaAboveCell000022012111)))

/-- Subcell `0000220121113310` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220121113310 : AngleCell :=
  childLL (childLH (childHH (childHH thetaAboveCell000022012111)))

/-- Subcell `0000220121113311` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220121113311 : AngleCell :=
  childLH (childLH (childHH (childHH thetaAboveCell000022012111)))

/-- Subcell `0000220121113312` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220121113312 : AngleCell :=
  childHL (childLH (childHH (childHH thetaAboveCell000022012111)))

/-- Subcell `0000220121113313` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220121113313 : AngleCell :=
  childHH (childLH (childHH (childHH thetaAboveCell000022012111)))

/-- Subcell `0000220121113320` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220121113320 : AngleCell :=
  childLL (childHL (childHH (childHH thetaAboveCell000022012111)))

/-- Subcell `0000220121113321` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220121113321 : AngleCell :=
  childLH (childHL (childHH (childHH thetaAboveCell000022012111)))

/-- Subcell `0000220121113322` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220121113322 : AngleCell :=
  childHL (childHL (childHH (childHH thetaAboveCell000022012111)))

/-- Subcell `0000220121113323` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220121113323 : AngleCell :=
  childHH (childHL (childHH (childHH thetaAboveCell000022012111)))

/-- Subcell `0000220121113330` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220121113330 : AngleCell :=
  childLL (childHH (childHH (childHH thetaAboveCell000022012111)))

/-- Subcell `0000220121113331` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220121113331 : AngleCell :=
  childLH (childHH (childHH (childHH thetaAboveCell000022012111)))

/-- Subcell `0000220121113332` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220121113332 : AngleCell :=
  childHL (childHH (childHH (childHH thetaAboveCell000022012111)))

/-- Subcell `0000220121113333` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220121113333 : AngleCell :=
  childHH (childHH (childHH (childHH thetaAboveCell000022012111)))

/-- Subcell `0000220130002020` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220130002020 : AngleCell :=
  childLL (childHL (childLL (childHL thetaAboveCell000022013000)))

/-- Subcell `0000220130002021` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220130002021 : AngleCell :=
  childLH (childHL (childLL (childHL thetaAboveCell000022013000)))

/-- Subcell `0000220130002022` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220130002022 : AngleCell :=
  childHL (childHL (childLL (childHL thetaAboveCell000022013000)))

/-- Subcell `0000220130002023` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220130002023 : AngleCell :=
  childHH (childHL (childLL (childHL thetaAboveCell000022013000)))

/-- Subcell `0000220130002030` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220130002030 : AngleCell :=
  childLL (childHH (childLL (childHL thetaAboveCell000022013000)))

/-- Subcell `0000220130002031` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220130002031 : AngleCell :=
  childLH (childHH (childLL (childHL thetaAboveCell000022013000)))

/-- Subcell `0000220130002032` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220130002032 : AngleCell :=
  childHL (childHH (childLL (childHL thetaAboveCell000022013000)))

/-- Subcell `0000220130002033` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220130002033 : AngleCell :=
  childHH (childHH (childLL (childHL thetaAboveCell000022013000)))

/-- Subcell `0000220130002120` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220130002120 : AngleCell :=
  childLL (childHL (childLH (childHL thetaAboveCell000022013000)))

/-- Subcell `0000220130002121` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220130002121 : AngleCell :=
  childLH (childHL (childLH (childHL thetaAboveCell000022013000)))

/-- Subcell `0000220130002122` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220130002122 : AngleCell :=
  childHL (childHL (childLH (childHL thetaAboveCell000022013000)))

/-- Subcell `0000220130002123` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220130002123 : AngleCell :=
  childHH (childHL (childLH (childHL thetaAboveCell000022013000)))

/-- Subcell `0000220130002130` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220130002130 : AngleCell :=
  childLL (childHH (childLH (childHL thetaAboveCell000022013000)))

/-- Subcell `0000220130002131` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220130002131 : AngleCell :=
  childLH (childHH (childLH (childHL thetaAboveCell000022013000)))

/-- Subcell `0000220130002132` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220130002132 : AngleCell :=
  childHL (childHH (childLH (childHL thetaAboveCell000022013000)))

/-- Subcell `0000220130002133` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220130002133 : AngleCell :=
  childHH (childHH (childLH (childHL thetaAboveCell000022013000)))

/-- Subcell `0000220130002200` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220130002200 : AngleCell :=
  childLL (childLL (childHL (childHL thetaAboveCell000022013000)))

/-- Subcell `0000220130002201` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220130002201 : AngleCell :=
  childLH (childLL (childHL (childHL thetaAboveCell000022013000)))

/-- Subcell `0000220130002202` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220130002202 : AngleCell :=
  childHL (childLL (childHL (childHL thetaAboveCell000022013000)))

/-- Subcell `0000220130002203` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220130002203 : AngleCell :=
  childHH (childLL (childHL (childHL thetaAboveCell000022013000)))

/-- Subcell `0000220130002210` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220130002210 : AngleCell :=
  childLL (childLH (childHL (childHL thetaAboveCell000022013000)))

/-- Subcell `0000220130002211` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220130002211 : AngleCell :=
  childLH (childLH (childHL (childHL thetaAboveCell000022013000)))

/-- Subcell `0000220130002212` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220130002212 : AngleCell :=
  childHL (childLH (childHL (childHL thetaAboveCell000022013000)))

/-- Subcell `0000220130002213` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220130002213 : AngleCell :=
  childHH (childLH (childHL (childHL thetaAboveCell000022013000)))

/-- Subcell `0000220130002220` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220130002220 : AngleCell :=
  childLL (childHL (childHL (childHL thetaAboveCell000022013000)))

/-- Subcell `0000220130002221` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220130002221 : AngleCell :=
  childLH (childHL (childHL (childHL thetaAboveCell000022013000)))

/-- Subcell `0000220130002222` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220130002222 : AngleCell :=
  childHL (childHL (childHL (childHL thetaAboveCell000022013000)))

/-- Subcell `0000220130002223` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220130002223 : AngleCell :=
  childHH (childHL (childHL (childHL thetaAboveCell000022013000)))

/-- Subcell `0000220130002230` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220130002230 : AngleCell :=
  childLL (childHH (childHL (childHL thetaAboveCell000022013000)))

/-- Subcell `0000220130002231` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220130002231 : AngleCell :=
  childLH (childHH (childHL (childHL thetaAboveCell000022013000)))

/-- Subcell `0000220130002232` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220130002232 : AngleCell :=
  childHL (childHH (childHL (childHL thetaAboveCell000022013000)))

/-- Subcell `0000220130002233` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220130002233 : AngleCell :=
  childHH (childHH (childHL (childHL thetaAboveCell000022013000)))

/-- Subcell `0000220130002300` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220130002300 : AngleCell :=
  childLL (childLL (childHH (childHL thetaAboveCell000022013000)))

/-- Subcell `0000220130002301` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220130002301 : AngleCell :=
  childLH (childLL (childHH (childHL thetaAboveCell000022013000)))

/-- Subcell `0000220130002302` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220130002302 : AngleCell :=
  childHL (childLL (childHH (childHL thetaAboveCell000022013000)))

/-- Subcell `0000220130002303` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220130002303 : AngleCell :=
  childHH (childLL (childHH (childHL thetaAboveCell000022013000)))

/-- Subcell `0000220130002310` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220130002310 : AngleCell :=
  childLL (childLH (childHH (childHL thetaAboveCell000022013000)))

/-- Subcell `0000220130002311` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220130002311 : AngleCell :=
  childLH (childLH (childHH (childHL thetaAboveCell000022013000)))

/-- Subcell `0000220130002312` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220130002312 : AngleCell :=
  childHL (childLH (childHH (childHL thetaAboveCell000022013000)))

/-- Subcell `0000220130002313` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220130002313 : AngleCell :=
  childHH (childLH (childHH (childHL thetaAboveCell000022013000)))

/-- Subcell `0000220130002320` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220130002320 : AngleCell :=
  childLL (childHL (childHH (childHL thetaAboveCell000022013000)))

/-- Subcell `0000220130002321` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220130002321 : AngleCell :=
  childLH (childHL (childHH (childHL thetaAboveCell000022013000)))

/-- Subcell `0000220130002322` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220130002322 : AngleCell :=
  childHL (childHL (childHH (childHL thetaAboveCell000022013000)))

/-- Subcell `0000220130002323` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220130002323 : AngleCell :=
  childHH (childHL (childHH (childHL thetaAboveCell000022013000)))

/-- Subcell `0000220130002330` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220130002330 : AngleCell :=
  childLL (childHH (childHH (childHL thetaAboveCell000022013000)))

/-- Subcell `0000220130002331` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220130002331 : AngleCell :=
  childLH (childHH (childHH (childHL thetaAboveCell000022013000)))

/-- Subcell `0000220130002332` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220130002332 : AngleCell :=
  childHL (childHH (childHH (childHL thetaAboveCell000022013000)))

/-- Subcell `0000220130002333` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220130002333 : AngleCell :=
  childHH (childHH (childHH (childHL thetaAboveCell000022013000)))

/-- Subcell `0000220130003020` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220130003020 : AngleCell :=
  childLL (childHL (childLL (childHH thetaAboveCell000022013000)))

/-- Subcell `0000220130003021` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220130003021 : AngleCell :=
  childLH (childHL (childLL (childHH thetaAboveCell000022013000)))

/-- Subcell `0000220130003022` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220130003022 : AngleCell :=
  childHL (childHL (childLL (childHH thetaAboveCell000022013000)))

/-- Subcell `0000220130003023` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220130003023 : AngleCell :=
  childHH (childHL (childLL (childHH thetaAboveCell000022013000)))

/-- Subcell `0000220130003030` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220130003030 : AngleCell :=
  childLL (childHH (childLL (childHH thetaAboveCell000022013000)))

/-- Subcell `0000220130003031` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220130003031 : AngleCell :=
  childLH (childHH (childLL (childHH thetaAboveCell000022013000)))

/-- Subcell `0000220130003032` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220130003032 : AngleCell :=
  childHL (childHH (childLL (childHH thetaAboveCell000022013000)))

/-- Subcell `0000220130003033` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220130003033 : AngleCell :=
  childHH (childHH (childLL (childHH thetaAboveCell000022013000)))

/-- Subcell `0000220130003120` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220130003120 : AngleCell :=
  childLL (childHL (childLH (childHH thetaAboveCell000022013000)))

/-- Subcell `0000220130003121` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220130003121 : AngleCell :=
  childLH (childHL (childLH (childHH thetaAboveCell000022013000)))

/-- Subcell `0000220130003122` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220130003122 : AngleCell :=
  childHL (childHL (childLH (childHH thetaAboveCell000022013000)))

/-- Subcell `0000220130003123` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220130003123 : AngleCell :=
  childHH (childHL (childLH (childHH thetaAboveCell000022013000)))

/-- Subcell `0000220130003130` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220130003130 : AngleCell :=
  childLL (childHH (childLH (childHH thetaAboveCell000022013000)))

/-- Subcell `0000220130003131` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220130003131 : AngleCell :=
  childLH (childHH (childLH (childHH thetaAboveCell000022013000)))

/-- Subcell `0000220130003132` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220130003132 : AngleCell :=
  childHL (childHH (childLH (childHH thetaAboveCell000022013000)))

/-- Subcell `0000220130003133` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220130003133 : AngleCell :=
  childHH (childHH (childLH (childHH thetaAboveCell000022013000)))

/-- Subcell `0000220130003200` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220130003200 : AngleCell :=
  childLL (childLL (childHL (childHH thetaAboveCell000022013000)))

/-- Subcell `0000220130003201` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220130003201 : AngleCell :=
  childLH (childLL (childHL (childHH thetaAboveCell000022013000)))

/-- Subcell `0000220130003202` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220130003202 : AngleCell :=
  childHL (childLL (childHL (childHH thetaAboveCell000022013000)))

/-- Subcell `0000220130003203` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220130003203 : AngleCell :=
  childHH (childLL (childHL (childHH thetaAboveCell000022013000)))

/-- Subcell `0000220130003210` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220130003210 : AngleCell :=
  childLL (childLH (childHL (childHH thetaAboveCell000022013000)))

/-- Subcell `0000220130003211` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220130003211 : AngleCell :=
  childLH (childLH (childHL (childHH thetaAboveCell000022013000)))

/-- Subcell `0000220130003212` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220130003212 : AngleCell :=
  childHL (childLH (childHL (childHH thetaAboveCell000022013000)))

/-- Subcell `0000220130003213` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220130003213 : AngleCell :=
  childHH (childLH (childHL (childHH thetaAboveCell000022013000)))

/-- Subcell `0000220130003220` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220130003220 : AngleCell :=
  childLL (childHL (childHL (childHH thetaAboveCell000022013000)))

/-- Subcell `0000220130003221` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220130003221 : AngleCell :=
  childLH (childHL (childHL (childHH thetaAboveCell000022013000)))

/-- Subcell `0000220130003222` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220130003222 : AngleCell :=
  childHL (childHL (childHL (childHH thetaAboveCell000022013000)))

/-- Subcell `0000220130003223` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220130003223 : AngleCell :=
  childHH (childHL (childHL (childHH thetaAboveCell000022013000)))

/-- Subcell `0000220130003230` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220130003230 : AngleCell :=
  childLL (childHH (childHL (childHH thetaAboveCell000022013000)))

/-- Subcell `0000220130003231` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220130003231 : AngleCell :=
  childLH (childHH (childHL (childHH thetaAboveCell000022013000)))

/-- Subcell `0000220130003232` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220130003232 : AngleCell :=
  childHL (childHH (childHL (childHH thetaAboveCell000022013000)))

/-- Subcell `0000220130003233` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220130003233 : AngleCell :=
  childHH (childHH (childHL (childHH thetaAboveCell000022013000)))

/-- Subcell `0000220130003300` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220130003300 : AngleCell :=
  childLL (childLL (childHH (childHH thetaAboveCell000022013000)))

/-- Subcell `0000220130003301` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220130003301 : AngleCell :=
  childLH (childLL (childHH (childHH thetaAboveCell000022013000)))

/-- Subcell `0000220130003302` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220130003302 : AngleCell :=
  childHL (childLL (childHH (childHH thetaAboveCell000022013000)))

/-- Subcell `0000220130003303` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220130003303 : AngleCell :=
  childHH (childLL (childHH (childHH thetaAboveCell000022013000)))

/-- Subcell `0000220130003310` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220130003310 : AngleCell :=
  childLL (childLH (childHH (childHH thetaAboveCell000022013000)))

/-- Subcell `0000220130003311` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220130003311 : AngleCell :=
  childLH (childLH (childHH (childHH thetaAboveCell000022013000)))

/-- Subcell `0000220130003312` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220130003312 : AngleCell :=
  childHL (childLH (childHH (childHH thetaAboveCell000022013000)))

/-- Subcell `0000220130003313` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220130003313 : AngleCell :=
  childHH (childLH (childHH (childHH thetaAboveCell000022013000)))

/-- Subcell `0000220130003320` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220130003320 : AngleCell :=
  childLL (childHL (childHH (childHH thetaAboveCell000022013000)))

/-- Subcell `0000220130003321` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220130003321 : AngleCell :=
  childLH (childHL (childHH (childHH thetaAboveCell000022013000)))

/-- Subcell `0000220130003322` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220130003322 : AngleCell :=
  childHL (childHL (childHH (childHH thetaAboveCell000022013000)))

/-- Subcell `0000220130003323` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220130003323 : AngleCell :=
  childHH (childHL (childHH (childHH thetaAboveCell000022013000)))

/-- Subcell `0000220130003330` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220130003330 : AngleCell :=
  childLL (childHH (childHH (childHH thetaAboveCell000022013000)))

/-- Subcell `0000220130003331` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220130003331 : AngleCell :=
  childLH (childHH (childHH (childHH thetaAboveCell000022013000)))

/-- Subcell `0000220130003332` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220130003332 : AngleCell :=
  childHL (childHH (childHH (childHH thetaAboveCell000022013000)))

/-- Subcell `0000220130003333` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220130003333 : AngleCell :=
  childHH (childHH (childHH (childHH thetaAboveCell000022013000)))

/-- Subcell `0000220130012020` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220130012020 : AngleCell :=
  childLL (childHL (childLL (childHL thetaAboveCell000022013001)))

/-- Subcell `0000220130012021` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220130012021 : AngleCell :=
  childLH (childHL (childLL (childHL thetaAboveCell000022013001)))

/-- Subcell `0000220130012022` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220130012022 : AngleCell :=
  childHL (childHL (childLL (childHL thetaAboveCell000022013001)))

/-- Subcell `0000220130012023` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220130012023 : AngleCell :=
  childHH (childHL (childLL (childHL thetaAboveCell000022013001)))

/-- Subcell `0000220130012030` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220130012030 : AngleCell :=
  childLL (childHH (childLL (childHL thetaAboveCell000022013001)))

/-- Subcell `0000220130012031` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220130012031 : AngleCell :=
  childLH (childHH (childLL (childHL thetaAboveCell000022013001)))

/-- Subcell `0000220130012032` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220130012032 : AngleCell :=
  childHL (childHH (childLL (childHL thetaAboveCell000022013001)))

/-- Subcell `0000220130012033` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220130012033 : AngleCell :=
  childHH (childHH (childLL (childHL thetaAboveCell000022013001)))

/-- Subcell `0000220130012120` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220130012120 : AngleCell :=
  childLL (childHL (childLH (childHL thetaAboveCell000022013001)))

/-- Subcell `0000220130012121` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220130012121 : AngleCell :=
  childLH (childHL (childLH (childHL thetaAboveCell000022013001)))

/-- Subcell `0000220130012122` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220130012122 : AngleCell :=
  childHL (childHL (childLH (childHL thetaAboveCell000022013001)))

/-- Subcell `0000220130012123` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220130012123 : AngleCell :=
  childHH (childHL (childLH (childHL thetaAboveCell000022013001)))

/-- Subcell `0000220130012130` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220130012130 : AngleCell :=
  childLL (childHH (childLH (childHL thetaAboveCell000022013001)))

/-- Subcell `0000220130012131` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220130012131 : AngleCell :=
  childLH (childHH (childLH (childHL thetaAboveCell000022013001)))

/-- Subcell `0000220130012132` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220130012132 : AngleCell :=
  childHL (childHH (childLH (childHL thetaAboveCell000022013001)))

/-- Subcell `0000220130012133` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220130012133 : AngleCell :=
  childHH (childHH (childLH (childHL thetaAboveCell000022013001)))

/-- Subcell `0000220130012200` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220130012200 : AngleCell :=
  childLL (childLL (childHL (childHL thetaAboveCell000022013001)))

/-- Subcell `0000220130012201` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220130012201 : AngleCell :=
  childLH (childLL (childHL (childHL thetaAboveCell000022013001)))

/-- Subcell `0000220130012202` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220130012202 : AngleCell :=
  childHL (childLL (childHL (childHL thetaAboveCell000022013001)))

/-- Subcell `0000220130012203` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220130012203 : AngleCell :=
  childHH (childLL (childHL (childHL thetaAboveCell000022013001)))

/-- Subcell `0000220130012210` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220130012210 : AngleCell :=
  childLL (childLH (childHL (childHL thetaAboveCell000022013001)))

/-- Subcell `0000220130012211` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220130012211 : AngleCell :=
  childLH (childLH (childHL (childHL thetaAboveCell000022013001)))

/-- Subcell `0000220130012212` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220130012212 : AngleCell :=
  childHL (childLH (childHL (childHL thetaAboveCell000022013001)))

/-- Subcell `0000220130012213` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220130012213 : AngleCell :=
  childHH (childLH (childHL (childHL thetaAboveCell000022013001)))

/-- Subcell `0000220130012220` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220130012220 : AngleCell :=
  childLL (childHL (childHL (childHL thetaAboveCell000022013001)))

/-- Subcell `0000220130012221` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220130012221 : AngleCell :=
  childLH (childHL (childHL (childHL thetaAboveCell000022013001)))

/-- Subcell `0000220130012222` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220130012222 : AngleCell :=
  childHL (childHL (childHL (childHL thetaAboveCell000022013001)))

/-- Subcell `0000220130012223` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220130012223 : AngleCell :=
  childHH (childHL (childHL (childHL thetaAboveCell000022013001)))

/-- Subcell `0000220130012230` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220130012230 : AngleCell :=
  childLL (childHH (childHL (childHL thetaAboveCell000022013001)))

/-- Subcell `0000220130012231` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220130012231 : AngleCell :=
  childLH (childHH (childHL (childHL thetaAboveCell000022013001)))

/-- Subcell `0000220130012232` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220130012232 : AngleCell :=
  childHL (childHH (childHL (childHL thetaAboveCell000022013001)))

/-- Subcell `0000220130012233` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220130012233 : AngleCell :=
  childHH (childHH (childHL (childHL thetaAboveCell000022013001)))

/-- Subcell `0000220130012300` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220130012300 : AngleCell :=
  childLL (childLL (childHH (childHL thetaAboveCell000022013001)))

/-- Subcell `0000220130012301` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220130012301 : AngleCell :=
  childLH (childLL (childHH (childHL thetaAboveCell000022013001)))

/-- Subcell `0000220130012302` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220130012302 : AngleCell :=
  childHL (childLL (childHH (childHL thetaAboveCell000022013001)))

/-- Subcell `0000220130012303` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220130012303 : AngleCell :=
  childHH (childLL (childHH (childHL thetaAboveCell000022013001)))

/-- Subcell `0000220130012310` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220130012310 : AngleCell :=
  childLL (childLH (childHH (childHL thetaAboveCell000022013001)))

/-- Subcell `0000220130012311` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220130012311 : AngleCell :=
  childLH (childLH (childHH (childHL thetaAboveCell000022013001)))

/-- Subcell `0000220130012312` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220130012312 : AngleCell :=
  childHL (childLH (childHH (childHL thetaAboveCell000022013001)))

/-- Subcell `0000220130012313` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220130012313 : AngleCell :=
  childHH (childLH (childHH (childHL thetaAboveCell000022013001)))

/-- Subcell `0000220130012320` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220130012320 : AngleCell :=
  childLL (childHL (childHH (childHL thetaAboveCell000022013001)))

/-- Subcell `0000220130012321` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220130012321 : AngleCell :=
  childLH (childHL (childHH (childHL thetaAboveCell000022013001)))

/-- Subcell `0000220130012322` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220130012322 : AngleCell :=
  childHL (childHL (childHH (childHL thetaAboveCell000022013001)))

/-- Subcell `0000220130012323` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220130012323 : AngleCell :=
  childHH (childHL (childHH (childHL thetaAboveCell000022013001)))

/-- Subcell `0000220130012330` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220130012330 : AngleCell :=
  childLL (childHH (childHH (childHL thetaAboveCell000022013001)))

/-- Subcell `0000220130012331` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220130012331 : AngleCell :=
  childLH (childHH (childHH (childHL thetaAboveCell000022013001)))

/-- Subcell `0000220130012332` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220130012332 : AngleCell :=
  childHL (childHH (childHH (childHL thetaAboveCell000022013001)))

/-- Subcell `0000220130012333` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220130012333 : AngleCell :=
  childHH (childHH (childHH (childHL thetaAboveCell000022013001)))

/-- Subcell `0000220130013020` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220130013020 : AngleCell :=
  childLL (childHL (childLL (childHH thetaAboveCell000022013001)))

/-- Subcell `0000220130013021` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220130013021 : AngleCell :=
  childLH (childHL (childLL (childHH thetaAboveCell000022013001)))

/-- Subcell `0000220130013022` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220130013022 : AngleCell :=
  childHL (childHL (childLL (childHH thetaAboveCell000022013001)))

/-- Subcell `0000220130013023` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220130013023 : AngleCell :=
  childHH (childHL (childLL (childHH thetaAboveCell000022013001)))

/-- Subcell `0000220130013030` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220130013030 : AngleCell :=
  childLL (childHH (childLL (childHH thetaAboveCell000022013001)))

/-- Subcell `0000220130013031` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220130013031 : AngleCell :=
  childLH (childHH (childLL (childHH thetaAboveCell000022013001)))

/-- Subcell `0000220130013032` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220130013032 : AngleCell :=
  childHL (childHH (childLL (childHH thetaAboveCell000022013001)))

/-- Subcell `0000220130013033` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220130013033 : AngleCell :=
  childHH (childHH (childLL (childHH thetaAboveCell000022013001)))

/-- Subcell `0000220130013120` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220130013120 : AngleCell :=
  childLL (childHL (childLH (childHH thetaAboveCell000022013001)))

/-- Subcell `0000220130013121` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220130013121 : AngleCell :=
  childLH (childHL (childLH (childHH thetaAboveCell000022013001)))

/-- Subcell `0000220130013122` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220130013122 : AngleCell :=
  childHL (childHL (childLH (childHH thetaAboveCell000022013001)))

/-- Subcell `0000220130013123` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220130013123 : AngleCell :=
  childHH (childHL (childLH (childHH thetaAboveCell000022013001)))

/-- Subcell `0000220130013130` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220130013130 : AngleCell :=
  childLL (childHH (childLH (childHH thetaAboveCell000022013001)))

/-- Subcell `0000220130013131` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220130013131 : AngleCell :=
  childLH (childHH (childLH (childHH thetaAboveCell000022013001)))

/-- Subcell `0000220130013132` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220130013132 : AngleCell :=
  childHL (childHH (childLH (childHH thetaAboveCell000022013001)))

/-- Subcell `0000220130013133` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220130013133 : AngleCell :=
  childHH (childHH (childLH (childHH thetaAboveCell000022013001)))

/-- Subcell `0000220130013200` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220130013200 : AngleCell :=
  childLL (childLL (childHL (childHH thetaAboveCell000022013001)))

/-- Subcell `0000220130013201` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220130013201 : AngleCell :=
  childLH (childLL (childHL (childHH thetaAboveCell000022013001)))

/-- Subcell `0000220130013202` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220130013202 : AngleCell :=
  childHL (childLL (childHL (childHH thetaAboveCell000022013001)))

/-- Subcell `0000220130013203` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220130013203 : AngleCell :=
  childHH (childLL (childHL (childHH thetaAboveCell000022013001)))

/-- Subcell `0000220130013210` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220130013210 : AngleCell :=
  childLL (childLH (childHL (childHH thetaAboveCell000022013001)))

/-- Subcell `0000220130013211` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220130013211 : AngleCell :=
  childLH (childLH (childHL (childHH thetaAboveCell000022013001)))

/-- Subcell `0000220130013212` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220130013212 : AngleCell :=
  childHL (childLH (childHL (childHH thetaAboveCell000022013001)))

/-- Subcell `0000220130013213` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220130013213 : AngleCell :=
  childHH (childLH (childHL (childHH thetaAboveCell000022013001)))

/-- Subcell `0000220130013220` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220130013220 : AngleCell :=
  childLL (childHL (childHL (childHH thetaAboveCell000022013001)))

/-- Subcell `0000220130013221` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220130013221 : AngleCell :=
  childLH (childHL (childHL (childHH thetaAboveCell000022013001)))

/-- Subcell `0000220130013222` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220130013222 : AngleCell :=
  childHL (childHL (childHL (childHH thetaAboveCell000022013001)))

/-- Subcell `0000220130013223` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220130013223 : AngleCell :=
  childHH (childHL (childHL (childHH thetaAboveCell000022013001)))

/-- Subcell `0000220130013230` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220130013230 : AngleCell :=
  childLL (childHH (childHL (childHH thetaAboveCell000022013001)))

/-- Subcell `0000220130013231` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220130013231 : AngleCell :=
  childLH (childHH (childHL (childHH thetaAboveCell000022013001)))

/-- Subcell `0000220130013232` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220130013232 : AngleCell :=
  childHL (childHH (childHL (childHH thetaAboveCell000022013001)))

/-- Subcell `0000220130013233` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220130013233 : AngleCell :=
  childHH (childHH (childHL (childHH thetaAboveCell000022013001)))

/-- Subcell `0000220130013300` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220130013300 : AngleCell :=
  childLL (childLL (childHH (childHH thetaAboveCell000022013001)))

/-- Subcell `0000220130013301` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220130013301 : AngleCell :=
  childLH (childLL (childHH (childHH thetaAboveCell000022013001)))

/-- Subcell `0000220130013302` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220130013302 : AngleCell :=
  childHL (childLL (childHH (childHH thetaAboveCell000022013001)))

/-- Subcell `0000220130013303` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220130013303 : AngleCell :=
  childHH (childLL (childHH (childHH thetaAboveCell000022013001)))

/-- Subcell `0000220130013310` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220130013310 : AngleCell :=
  childLL (childLH (childHH (childHH thetaAboveCell000022013001)))

/-- Subcell `0000220130013311` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220130013311 : AngleCell :=
  childLH (childLH (childHH (childHH thetaAboveCell000022013001)))

/-- Subcell `0000220130013312` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220130013312 : AngleCell :=
  childHL (childLH (childHH (childHH thetaAboveCell000022013001)))

/-- Subcell `0000220130013313` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220130013313 : AngleCell :=
  childHH (childLH (childHH (childHH thetaAboveCell000022013001)))

/-- Subcell `0000220130013320` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220130013320 : AngleCell :=
  childLL (childHL (childHH (childHH thetaAboveCell000022013001)))

/-- Subcell `0000220130013321` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220130013321 : AngleCell :=
  childLH (childHL (childHH (childHH thetaAboveCell000022013001)))

/-- Subcell `0000220130013322` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220130013322 : AngleCell :=
  childHL (childHL (childHH (childHH thetaAboveCell000022013001)))

/-- Subcell `0000220130013323` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220130013323 : AngleCell :=
  childHH (childHL (childHH (childHH thetaAboveCell000022013001)))

/-- Subcell `0000220130013330` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220130013330 : AngleCell :=
  childLL (childHH (childHH (childHH thetaAboveCell000022013001)))

/-- Subcell `0000220130013331` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220130013331 : AngleCell :=
  childLH (childHH (childHH (childHH thetaAboveCell000022013001)))

/-- Subcell `0000220130013332` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220130013332 : AngleCell :=
  childHL (childHH (childHH (childHH thetaAboveCell000022013001)))

/-- Subcell `0000220130013333` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220130013333 : AngleCell :=
  childHH (childHH (childHH (childHH thetaAboveCell000022013001)))

/-- Subcell `0000220130102020` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220130102020 : AngleCell :=
  childLL (childHL (childLL (childHL thetaAboveCell000022013010)))

/-- Subcell `0000220130102021` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220130102021 : AngleCell :=
  childLH (childHL (childLL (childHL thetaAboveCell000022013010)))

/-- Subcell `0000220130102022` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220130102022 : AngleCell :=
  childHL (childHL (childLL (childHL thetaAboveCell000022013010)))

/-- Subcell `0000220130102023` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220130102023 : AngleCell :=
  childHH (childHL (childLL (childHL thetaAboveCell000022013010)))

/-- Subcell `0000220130102030` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220130102030 : AngleCell :=
  childLL (childHH (childLL (childHL thetaAboveCell000022013010)))

/-- Subcell `0000220130102031` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220130102031 : AngleCell :=
  childLH (childHH (childLL (childHL thetaAboveCell000022013010)))

/-- Subcell `0000220130102032` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220130102032 : AngleCell :=
  childHL (childHH (childLL (childHL thetaAboveCell000022013010)))

/-- Subcell `0000220130102033` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220130102033 : AngleCell :=
  childHH (childHH (childLL (childHL thetaAboveCell000022013010)))

/-- Subcell `0000220130102120` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220130102120 : AngleCell :=
  childLL (childHL (childLH (childHL thetaAboveCell000022013010)))

/-- Subcell `0000220130102121` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220130102121 : AngleCell :=
  childLH (childHL (childLH (childHL thetaAboveCell000022013010)))

/-- Subcell `0000220130102122` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220130102122 : AngleCell :=
  childHL (childHL (childLH (childHL thetaAboveCell000022013010)))

/-- Subcell `0000220130102123` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220130102123 : AngleCell :=
  childHH (childHL (childLH (childHL thetaAboveCell000022013010)))

/-- Subcell `0000220130102130` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220130102130 : AngleCell :=
  childLL (childHH (childLH (childHL thetaAboveCell000022013010)))

/-- Subcell `0000220130102131` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220130102131 : AngleCell :=
  childLH (childHH (childLH (childHL thetaAboveCell000022013010)))

/-- Subcell `0000220130102132` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220130102132 : AngleCell :=
  childHL (childHH (childLH (childHL thetaAboveCell000022013010)))

/-- Subcell `0000220130102133` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220130102133 : AngleCell :=
  childHH (childHH (childLH (childHL thetaAboveCell000022013010)))

/-- Subcell `0000220130102200` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220130102200 : AngleCell :=
  childLL (childLL (childHL (childHL thetaAboveCell000022013010)))

/-- Subcell `0000220130102201` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220130102201 : AngleCell :=
  childLH (childLL (childHL (childHL thetaAboveCell000022013010)))

/-- Subcell `0000220130102202` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220130102202 : AngleCell :=
  childHL (childLL (childHL (childHL thetaAboveCell000022013010)))

/-- Subcell `0000220130102203` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220130102203 : AngleCell :=
  childHH (childLL (childHL (childHL thetaAboveCell000022013010)))

/-- Subcell `0000220130102210` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220130102210 : AngleCell :=
  childLL (childLH (childHL (childHL thetaAboveCell000022013010)))

/-- Subcell `0000220130102211` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220130102211 : AngleCell :=
  childLH (childLH (childHL (childHL thetaAboveCell000022013010)))

/-- Subcell `0000220130102212` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220130102212 : AngleCell :=
  childHL (childLH (childHL (childHL thetaAboveCell000022013010)))

/-- Subcell `0000220130102213` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220130102213 : AngleCell :=
  childHH (childLH (childHL (childHL thetaAboveCell000022013010)))

/-- Subcell `0000220130102220` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220130102220 : AngleCell :=
  childLL (childHL (childHL (childHL thetaAboveCell000022013010)))

/-- Subcell `0000220130102221` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220130102221 : AngleCell :=
  childLH (childHL (childHL (childHL thetaAboveCell000022013010)))

/-- Subcell `0000220130102222` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220130102222 : AngleCell :=
  childHL (childHL (childHL (childHL thetaAboveCell000022013010)))

/-- Subcell `0000220130102223` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220130102223 : AngleCell :=
  childHH (childHL (childHL (childHL thetaAboveCell000022013010)))

/-- Subcell `0000220130102230` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220130102230 : AngleCell :=
  childLL (childHH (childHL (childHL thetaAboveCell000022013010)))

/-- Subcell `0000220130102231` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220130102231 : AngleCell :=
  childLH (childHH (childHL (childHL thetaAboveCell000022013010)))

/-- Subcell `0000220130102232` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220130102232 : AngleCell :=
  childHL (childHH (childHL (childHL thetaAboveCell000022013010)))

/-- Subcell `0000220130102233` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220130102233 : AngleCell :=
  childHH (childHH (childHL (childHL thetaAboveCell000022013010)))

/-- Subcell `0000220130102300` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220130102300 : AngleCell :=
  childLL (childLL (childHH (childHL thetaAboveCell000022013010)))

/-- Subcell `0000220130102301` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220130102301 : AngleCell :=
  childLH (childLL (childHH (childHL thetaAboveCell000022013010)))

/-- Subcell `0000220130102302` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220130102302 : AngleCell :=
  childHL (childLL (childHH (childHL thetaAboveCell000022013010)))

/-- Subcell `0000220130102303` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220130102303 : AngleCell :=
  childHH (childLL (childHH (childHL thetaAboveCell000022013010)))

/-- Subcell `0000220130102310` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220130102310 : AngleCell :=
  childLL (childLH (childHH (childHL thetaAboveCell000022013010)))

/-- Subcell `0000220130102311` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220130102311 : AngleCell :=
  childLH (childLH (childHH (childHL thetaAboveCell000022013010)))

/-- Subcell `0000220130102312` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220130102312 : AngleCell :=
  childHL (childLH (childHH (childHL thetaAboveCell000022013010)))

/-- Subcell `0000220130102313` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220130102313 : AngleCell :=
  childHH (childLH (childHH (childHL thetaAboveCell000022013010)))

/-- Subcell `0000220130102320` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220130102320 : AngleCell :=
  childLL (childHL (childHH (childHL thetaAboveCell000022013010)))

/-- Subcell `0000220130102321` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220130102321 : AngleCell :=
  childLH (childHL (childHH (childHL thetaAboveCell000022013010)))

/-- Subcell `0000220130102322` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220130102322 : AngleCell :=
  childHL (childHL (childHH (childHL thetaAboveCell000022013010)))

/-- Subcell `0000220130102323` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220130102323 : AngleCell :=
  childHH (childHL (childHH (childHL thetaAboveCell000022013010)))

/-- Subcell `0000220130102330` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220130102330 : AngleCell :=
  childLL (childHH (childHH (childHL thetaAboveCell000022013010)))

/-- Subcell `0000220130102331` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220130102331 : AngleCell :=
  childLH (childHH (childHH (childHL thetaAboveCell000022013010)))

/-- Subcell `0000220130102332` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220130102332 : AngleCell :=
  childHL (childHH (childHH (childHL thetaAboveCell000022013010)))

/-- Subcell `0000220130102333` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220130102333 : AngleCell :=
  childHH (childHH (childHH (childHL thetaAboveCell000022013010)))

/-- Subcell `0000220130103020` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220130103020 : AngleCell :=
  childLL (childHL (childLL (childHH thetaAboveCell000022013010)))

/-- Subcell `0000220130103021` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220130103021 : AngleCell :=
  childLH (childHL (childLL (childHH thetaAboveCell000022013010)))

/-- Subcell `0000220130103022` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220130103022 : AngleCell :=
  childHL (childHL (childLL (childHH thetaAboveCell000022013010)))

/-- Subcell `0000220130103023` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220130103023 : AngleCell :=
  childHH (childHL (childLL (childHH thetaAboveCell000022013010)))

/-- Subcell `0000220130103030` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220130103030 : AngleCell :=
  childLL (childHH (childLL (childHH thetaAboveCell000022013010)))

/-- Subcell `0000220130103031` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220130103031 : AngleCell :=
  childLH (childHH (childLL (childHH thetaAboveCell000022013010)))

/-- Subcell `0000220130103032` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220130103032 : AngleCell :=
  childHL (childHH (childLL (childHH thetaAboveCell000022013010)))

/-- Subcell `0000220130103033` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220130103033 : AngleCell :=
  childHH (childHH (childLL (childHH thetaAboveCell000022013010)))

/-- Subcell `0000220130103120` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220130103120 : AngleCell :=
  childLL (childHL (childLH (childHH thetaAboveCell000022013010)))

/-- Subcell `0000220130103121` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220130103121 : AngleCell :=
  childLH (childHL (childLH (childHH thetaAboveCell000022013010)))

/-- Subcell `0000220130103122` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220130103122 : AngleCell :=
  childHL (childHL (childLH (childHH thetaAboveCell000022013010)))

/-- Subcell `0000220130103123` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220130103123 : AngleCell :=
  childHH (childHL (childLH (childHH thetaAboveCell000022013010)))

/-- Subcell `0000220130103130` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220130103130 : AngleCell :=
  childLL (childHH (childLH (childHH thetaAboveCell000022013010)))

/-- Subcell `0000220130103131` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220130103131 : AngleCell :=
  childLH (childHH (childLH (childHH thetaAboveCell000022013010)))

/-- Subcell `0000220130103132` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220130103132 : AngleCell :=
  childHL (childHH (childLH (childHH thetaAboveCell000022013010)))

/-- Subcell `0000220130103133` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220130103133 : AngleCell :=
  childHH (childHH (childLH (childHH thetaAboveCell000022013010)))

/-- Subcell `0000220130103200` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220130103200 : AngleCell :=
  childLL (childLL (childHL (childHH thetaAboveCell000022013010)))

/-- Subcell `0000220130103201` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220130103201 : AngleCell :=
  childLH (childLL (childHL (childHH thetaAboveCell000022013010)))

/-- Subcell `0000220130103202` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220130103202 : AngleCell :=
  childHL (childLL (childHL (childHH thetaAboveCell000022013010)))

/-- Subcell `0000220130103203` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220130103203 : AngleCell :=
  childHH (childLL (childHL (childHH thetaAboveCell000022013010)))

/-- Subcell `0000220130103210` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220130103210 : AngleCell :=
  childLL (childLH (childHL (childHH thetaAboveCell000022013010)))

/-- Subcell `0000220130103211` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220130103211 : AngleCell :=
  childLH (childLH (childHL (childHH thetaAboveCell000022013010)))

/-- Subcell `0000220130103212` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220130103212 : AngleCell :=
  childHL (childLH (childHL (childHH thetaAboveCell000022013010)))

/-- Subcell `0000220130103213` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220130103213 : AngleCell :=
  childHH (childLH (childHL (childHH thetaAboveCell000022013010)))

/-- Subcell `0000220130103220` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220130103220 : AngleCell :=
  childLL (childHL (childHL (childHH thetaAboveCell000022013010)))

/-- Subcell `0000220130103221` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220130103221 : AngleCell :=
  childLH (childHL (childHL (childHH thetaAboveCell000022013010)))

/-- Subcell `0000220130103222` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220130103222 : AngleCell :=
  childHL (childHL (childHL (childHH thetaAboveCell000022013010)))

/-- Subcell `0000220130103223` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220130103223 : AngleCell :=
  childHH (childHL (childHL (childHH thetaAboveCell000022013010)))

/-- Subcell `0000220130103230` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220130103230 : AngleCell :=
  childLL (childHH (childHL (childHH thetaAboveCell000022013010)))

/-- Subcell `0000220130103231` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220130103231 : AngleCell :=
  childLH (childHH (childHL (childHH thetaAboveCell000022013010)))

/-- Subcell `0000220130103232` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220130103232 : AngleCell :=
  childHL (childHH (childHL (childHH thetaAboveCell000022013010)))

/-- Subcell `0000220130103233` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220130103233 : AngleCell :=
  childHH (childHH (childHL (childHH thetaAboveCell000022013010)))

/-- Subcell `0000220130103300` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220130103300 : AngleCell :=
  childLL (childLL (childHH (childHH thetaAboveCell000022013010)))

/-- Subcell `0000220130103301` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220130103301 : AngleCell :=
  childLH (childLL (childHH (childHH thetaAboveCell000022013010)))

/-- Subcell `0000220130103302` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220130103302 : AngleCell :=
  childHL (childLL (childHH (childHH thetaAboveCell000022013010)))

/-- Subcell `0000220130103303` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220130103303 : AngleCell :=
  childHH (childLL (childHH (childHH thetaAboveCell000022013010)))

/-- Subcell `0000220130103310` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220130103310 : AngleCell :=
  childLL (childLH (childHH (childHH thetaAboveCell000022013010)))

/-- Subcell `0000220130103311` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220130103311 : AngleCell :=
  childLH (childLH (childHH (childHH thetaAboveCell000022013010)))

/-- Subcell `0000220130103312` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220130103312 : AngleCell :=
  childHL (childLH (childHH (childHH thetaAboveCell000022013010)))

/-- Subcell `0000220130103313` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220130103313 : AngleCell :=
  childHH (childLH (childHH (childHH thetaAboveCell000022013010)))

/-- Subcell `0000220130103320` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220130103320 : AngleCell :=
  childLL (childHL (childHH (childHH thetaAboveCell000022013010)))

/-- Subcell `0000220130103321` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220130103321 : AngleCell :=
  childLH (childHL (childHH (childHH thetaAboveCell000022013010)))

/-- Subcell `0000220130103322` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220130103322 : AngleCell :=
  childHL (childHL (childHH (childHH thetaAboveCell000022013010)))

/-- Subcell `0000220130103323` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220130103323 : AngleCell :=
  childHH (childHL (childHH (childHH thetaAboveCell000022013010)))

/-- Subcell `0000220130103330` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220130103330 : AngleCell :=
  childLL (childHH (childHH (childHH thetaAboveCell000022013010)))

/-- Subcell `0000220130103331` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220130103331 : AngleCell :=
  childLH (childHH (childHH (childHH thetaAboveCell000022013010)))

/-- Subcell `0000220130103332` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220130103332 : AngleCell :=
  childHL (childHH (childHH (childHH thetaAboveCell000022013010)))

/-- Subcell `0000220130103333` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220130103333 : AngleCell :=
  childHH (childHH (childHH (childHH thetaAboveCell000022013010)))

/-- Subcell `0000220130112020` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220130112020 : AngleCell :=
  childLL (childHL (childLL (childHL thetaAboveCell000022013011)))

/-- Subcell `0000220130112021` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220130112021 : AngleCell :=
  childLH (childHL (childLL (childHL thetaAboveCell000022013011)))

/-- Subcell `0000220130112022` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220130112022 : AngleCell :=
  childHL (childHL (childLL (childHL thetaAboveCell000022013011)))

/-- Subcell `0000220130112023` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220130112023 : AngleCell :=
  childHH (childHL (childLL (childHL thetaAboveCell000022013011)))

/-- Subcell `0000220130112030` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220130112030 : AngleCell :=
  childLL (childHH (childLL (childHL thetaAboveCell000022013011)))

/-- Subcell `0000220130112031` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220130112031 : AngleCell :=
  childLH (childHH (childLL (childHL thetaAboveCell000022013011)))

/-- Subcell `0000220130112032` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220130112032 : AngleCell :=
  childHL (childHH (childLL (childHL thetaAboveCell000022013011)))

/-- Subcell `0000220130112033` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220130112033 : AngleCell :=
  childHH (childHH (childLL (childHL thetaAboveCell000022013011)))

/-- Subcell `0000220130112120` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220130112120 : AngleCell :=
  childLL (childHL (childLH (childHL thetaAboveCell000022013011)))

/-- Subcell `0000220130112121` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220130112121 : AngleCell :=
  childLH (childHL (childLH (childHL thetaAboveCell000022013011)))

/-- Subcell `0000220130112122` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220130112122 : AngleCell :=
  childHL (childHL (childLH (childHL thetaAboveCell000022013011)))

/-- Subcell `0000220130112123` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220130112123 : AngleCell :=
  childHH (childHL (childLH (childHL thetaAboveCell000022013011)))

/-- Subcell `0000220130112130` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220130112130 : AngleCell :=
  childLL (childHH (childLH (childHL thetaAboveCell000022013011)))

/-- Subcell `0000220130112131` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220130112131 : AngleCell :=
  childLH (childHH (childLH (childHL thetaAboveCell000022013011)))

/-- Subcell `0000220130112132` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220130112132 : AngleCell :=
  childHL (childHH (childLH (childHL thetaAboveCell000022013011)))

/-- Subcell `0000220130112133` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220130112133 : AngleCell :=
  childHH (childHH (childLH (childHL thetaAboveCell000022013011)))

/-- Subcell `0000220130112200` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220130112200 : AngleCell :=
  childLL (childLL (childHL (childHL thetaAboveCell000022013011)))

/-- Subcell `0000220130112201` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220130112201 : AngleCell :=
  childLH (childLL (childHL (childHL thetaAboveCell000022013011)))

/-- Subcell `0000220130112202` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220130112202 : AngleCell :=
  childHL (childLL (childHL (childHL thetaAboveCell000022013011)))

/-- Subcell `0000220130112203` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220130112203 : AngleCell :=
  childHH (childLL (childHL (childHL thetaAboveCell000022013011)))

/-- Subcell `0000220130112210` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220130112210 : AngleCell :=
  childLL (childLH (childHL (childHL thetaAboveCell000022013011)))

/-- Subcell `0000220130112211` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220130112211 : AngleCell :=
  childLH (childLH (childHL (childHL thetaAboveCell000022013011)))

/-- Subcell `0000220130112212` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220130112212 : AngleCell :=
  childHL (childLH (childHL (childHL thetaAboveCell000022013011)))

/-- Subcell `0000220130112213` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220130112213 : AngleCell :=
  childHH (childLH (childHL (childHL thetaAboveCell000022013011)))

/-- Subcell `0000220130112220` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220130112220 : AngleCell :=
  childLL (childHL (childHL (childHL thetaAboveCell000022013011)))

/-- Subcell `0000220130112221` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220130112221 : AngleCell :=
  childLH (childHL (childHL (childHL thetaAboveCell000022013011)))

/-- Subcell `0000220130112222` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220130112222 : AngleCell :=
  childHL (childHL (childHL (childHL thetaAboveCell000022013011)))

/-- Subcell `0000220130112223` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220130112223 : AngleCell :=
  childHH (childHL (childHL (childHL thetaAboveCell000022013011)))

/-- Subcell `0000220130112230` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220130112230 : AngleCell :=
  childLL (childHH (childHL (childHL thetaAboveCell000022013011)))

/-- Subcell `0000220130112231` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220130112231 : AngleCell :=
  childLH (childHH (childHL (childHL thetaAboveCell000022013011)))

/-- Subcell `0000220130112232` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220130112232 : AngleCell :=
  childHL (childHH (childHL (childHL thetaAboveCell000022013011)))

/-- Subcell `0000220130112233` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220130112233 : AngleCell :=
  childHH (childHH (childHL (childHL thetaAboveCell000022013011)))

/-- Subcell `0000220130112300` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220130112300 : AngleCell :=
  childLL (childLL (childHH (childHL thetaAboveCell000022013011)))

/-- Subcell `0000220130112301` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220130112301 : AngleCell :=
  childLH (childLL (childHH (childHL thetaAboveCell000022013011)))

/-- Subcell `0000220130112302` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220130112302 : AngleCell :=
  childHL (childLL (childHH (childHL thetaAboveCell000022013011)))

/-- Subcell `0000220130112303` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220130112303 : AngleCell :=
  childHH (childLL (childHH (childHL thetaAboveCell000022013011)))

/-- Subcell `0000220130112310` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220130112310 : AngleCell :=
  childLL (childLH (childHH (childHL thetaAboveCell000022013011)))

/-- Subcell `0000220130112311` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220130112311 : AngleCell :=
  childLH (childLH (childHH (childHL thetaAboveCell000022013011)))

/-- Subcell `0000220130112312` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220130112312 : AngleCell :=
  childHL (childLH (childHH (childHL thetaAboveCell000022013011)))

/-- Subcell `0000220130112313` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220130112313 : AngleCell :=
  childHH (childLH (childHH (childHL thetaAboveCell000022013011)))

/-- Subcell `0000220130112320` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220130112320 : AngleCell :=
  childLL (childHL (childHH (childHL thetaAboveCell000022013011)))

/-- Subcell `0000220130112321` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220130112321 : AngleCell :=
  childLH (childHL (childHH (childHL thetaAboveCell000022013011)))

/-- Subcell `0000220130112322` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220130112322 : AngleCell :=
  childHL (childHL (childHH (childHL thetaAboveCell000022013011)))

/-- Subcell `0000220130112323` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220130112323 : AngleCell :=
  childHH (childHL (childHH (childHL thetaAboveCell000022013011)))

/-- Subcell `0000220130112330` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220130112330 : AngleCell :=
  childLL (childHH (childHH (childHL thetaAboveCell000022013011)))

/-- Subcell `0000220130112331` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220130112331 : AngleCell :=
  childLH (childHH (childHH (childHL thetaAboveCell000022013011)))

/-- Subcell `0000220130112332` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220130112332 : AngleCell :=
  childHL (childHH (childHH (childHL thetaAboveCell000022013011)))

/-- Subcell `0000220130112333` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220130112333 : AngleCell :=
  childHH (childHH (childHH (childHL thetaAboveCell000022013011)))

/-- Subcell `0000220130113020` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220130113020 : AngleCell :=
  childLL (childHL (childLL (childHH thetaAboveCell000022013011)))

/-- Subcell `0000220130113021` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220130113021 : AngleCell :=
  childLH (childHL (childLL (childHH thetaAboveCell000022013011)))

/-- Subcell `0000220130113022` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220130113022 : AngleCell :=
  childHL (childHL (childLL (childHH thetaAboveCell000022013011)))

/-- Subcell `0000220130113023` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220130113023 : AngleCell :=
  childHH (childHL (childLL (childHH thetaAboveCell000022013011)))

/-- Subcell `0000220130113030` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220130113030 : AngleCell :=
  childLL (childHH (childLL (childHH thetaAboveCell000022013011)))

/-- Subcell `0000220130113031` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220130113031 : AngleCell :=
  childLH (childHH (childLL (childHH thetaAboveCell000022013011)))

/-- Subcell `0000220130113032` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220130113032 : AngleCell :=
  childHL (childHH (childLL (childHH thetaAboveCell000022013011)))

/-- Subcell `0000220130113033` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220130113033 : AngleCell :=
  childHH (childHH (childLL (childHH thetaAboveCell000022013011)))

/-- Subcell `0000220130113120` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220130113120 : AngleCell :=
  childLL (childHL (childLH (childHH thetaAboveCell000022013011)))

/-- Subcell `0000220130113121` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220130113121 : AngleCell :=
  childLH (childHL (childLH (childHH thetaAboveCell000022013011)))

/-- Subcell `0000220130113122` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220130113122 : AngleCell :=
  childHL (childHL (childLH (childHH thetaAboveCell000022013011)))

/-- Subcell `0000220130113123` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220130113123 : AngleCell :=
  childHH (childHL (childLH (childHH thetaAboveCell000022013011)))

/-- Subcell `0000220130113130` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220130113130 : AngleCell :=
  childLL (childHH (childLH (childHH thetaAboveCell000022013011)))

/-- Subcell `0000220130113131` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220130113131 : AngleCell :=
  childLH (childHH (childLH (childHH thetaAboveCell000022013011)))

/-- Subcell `0000220130113132` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220130113132 : AngleCell :=
  childHL (childHH (childLH (childHH thetaAboveCell000022013011)))

/-- Subcell `0000220130113133` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220130113133 : AngleCell :=
  childHH (childHH (childLH (childHH thetaAboveCell000022013011)))

/-- Subcell `0000220130113200` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220130113200 : AngleCell :=
  childLL (childLL (childHL (childHH thetaAboveCell000022013011)))

/-- Subcell `0000220130113201` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220130113201 : AngleCell :=
  childLH (childLL (childHL (childHH thetaAboveCell000022013011)))

/-- Subcell `0000220130113202` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220130113202 : AngleCell :=
  childHL (childLL (childHL (childHH thetaAboveCell000022013011)))

/-- Subcell `0000220130113203` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220130113203 : AngleCell :=
  childHH (childLL (childHL (childHH thetaAboveCell000022013011)))

/-- Subcell `0000220130113210` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220130113210 : AngleCell :=
  childLL (childLH (childHL (childHH thetaAboveCell000022013011)))

/-- Subcell `0000220130113211` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220130113211 : AngleCell :=
  childLH (childLH (childHL (childHH thetaAboveCell000022013011)))

/-- Subcell `0000220130113212` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220130113212 : AngleCell :=
  childHL (childLH (childHL (childHH thetaAboveCell000022013011)))

/-- Subcell `0000220130113213` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220130113213 : AngleCell :=
  childHH (childLH (childHL (childHH thetaAboveCell000022013011)))

/-- Subcell `0000220130113220` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220130113220 : AngleCell :=
  childLL (childHL (childHL (childHH thetaAboveCell000022013011)))

/-- Subcell `0000220130113221` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220130113221 : AngleCell :=
  childLH (childHL (childHL (childHH thetaAboveCell000022013011)))

/-- Subcell `0000220130113222` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220130113222 : AngleCell :=
  childHL (childHL (childHL (childHH thetaAboveCell000022013011)))

/-- Subcell `0000220130113223` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220130113223 : AngleCell :=
  childHH (childHL (childHL (childHH thetaAboveCell000022013011)))

/-- Subcell `0000220130113230` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220130113230 : AngleCell :=
  childLL (childHH (childHL (childHH thetaAboveCell000022013011)))

/-- Subcell `0000220130113231` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220130113231 : AngleCell :=
  childLH (childHH (childHL (childHH thetaAboveCell000022013011)))

/-- Subcell `0000220130113232` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220130113232 : AngleCell :=
  childHL (childHH (childHL (childHH thetaAboveCell000022013011)))

/-- Subcell `0000220130113233` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220130113233 : AngleCell :=
  childHH (childHH (childHL (childHH thetaAboveCell000022013011)))

/-- Subcell `0000220130113300` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220130113300 : AngleCell :=
  childLL (childLL (childHH (childHH thetaAboveCell000022013011)))

/-- Subcell `0000220130113301` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220130113301 : AngleCell :=
  childLH (childLL (childHH (childHH thetaAboveCell000022013011)))

/-- Subcell `0000220130113302` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220130113302 : AngleCell :=
  childHL (childLL (childHH (childHH thetaAboveCell000022013011)))

/-- Subcell `0000220130113303` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220130113303 : AngleCell :=
  childHH (childLL (childHH (childHH thetaAboveCell000022013011)))

/-- Subcell `0000220130113310` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220130113310 : AngleCell :=
  childLL (childLH (childHH (childHH thetaAboveCell000022013011)))

/-- Subcell `0000220130113311` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220130113311 : AngleCell :=
  childLH (childLH (childHH (childHH thetaAboveCell000022013011)))

/-- Subcell `0000220130113312` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220130113312 : AngleCell :=
  childHL (childLH (childHH (childHH thetaAboveCell000022013011)))

/-- Subcell `0000220130113313` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220130113313 : AngleCell :=
  childHH (childLH (childHH (childHH thetaAboveCell000022013011)))

/-- Subcell `0000220130113320` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220130113320 : AngleCell :=
  childLL (childHL (childHH (childHH thetaAboveCell000022013011)))

/-- Subcell `0000220130113321` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220130113321 : AngleCell :=
  childLH (childHL (childHH (childHH thetaAboveCell000022013011)))

/-- Subcell `0000220130113322` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220130113322 : AngleCell :=
  childHL (childHL (childHH (childHH thetaAboveCell000022013011)))

/-- Subcell `0000220130113323` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220130113323 : AngleCell :=
  childHH (childHL (childHH (childHH thetaAboveCell000022013011)))

end GerverSofa.PartE.CertificateCellsbc9ee1179f

section

/-
Copyright (c) 2026 Dawid Trela. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dawid Trela
-/
/-!
# Gerver sofa dependency batch

* `KernelOnly.PartE.E24KC6ProofBatchE7cbedc8143c8e9f`.
-/

public section

noncomputable section

section

/-! E24KC6 explicit proof-producing certificate batch. -/

public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCellsbc9ee1179f

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.

end CertificateCellsbc9ee1179f

open CertificateCellsbc9ee1179f
theorem cover_subtree_c4eb81eb7e49 :
    adaptiveCoverCheck 5 (childLL (childHL thetaAboveCell000022012100)) = true := by
  exact adaptiveCoverCheck_succ_of_children 4 (childLL (childHL thetaAboveCell000022012100))
    (by
      have h : ((childLL (childLL (childHL thetaAboveCell000022012100)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childLL (childHL
        thetaAboveCell000022012100))) h)
    (by
      have h : ((childLH (childLL (childHL thetaAboveCell000022012100)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childLL (childHL
        thetaAboveCell000022012100))) h)
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childHL (childLL (childHL
        thetaAboveCell000022012100)))
        (by
          have h : (thetaAboveCell0000220121002020).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220121002020 h)
        (by
          have h : (thetaAboveCell0000220121002021).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220121002021 h)
        (by
          have h : (thetaAboveCell0000220121002022).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220121002022 h)
        (by
          have h : (thetaAboveCell0000220121002023).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220121002023 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childHH (childLL (childHL
        thetaAboveCell000022012100)))
        (by
          have h : (thetaAboveCell0000220121002030).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220121002030 h)
        (by
          have h : (thetaAboveCell0000220121002031).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220121002031 h)
        (by
          have h : (thetaAboveCell0000220121002032).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220121002032 h)
        (by
          have h : (thetaAboveCell0000220121002033).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220121002033 h))

theorem cover_subtree_20c58a0c1f65 :
    adaptiveCoverCheck 5 (childLH (childHL thetaAboveCell000022012100)) = true := by
  exact adaptiveCoverCheck_succ_of_children 4 (childLH (childHL thetaAboveCell000022012100))
    (by
      have h : ((childLL (childLH (childHL thetaAboveCell000022012100)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childLH (childHL
        thetaAboveCell000022012100))) h)
    (by
      have h : ((childLH (childLH (childHL thetaAboveCell000022012100)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childLH (childHL
        thetaAboveCell000022012100))) h)
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childHL (childLH (childHL
        thetaAboveCell000022012100)))
        (by
          have h : (thetaAboveCell0000220121002120).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220121002120 h)
        (by
          have h : (thetaAboveCell0000220121002121).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220121002121 h)
        (by
          have h : (thetaAboveCell0000220121002122).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220121002122 h)
        (by
          have h : (thetaAboveCell0000220121002123).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220121002123 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childHH (childLH (childHL
        thetaAboveCell000022012100)))
        (by
          have h : (thetaAboveCell0000220121002130).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220121002130 h)
        (by
          have h : (thetaAboveCell0000220121002131).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220121002131 h)
        (by
          have h : (thetaAboveCell0000220121002132).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220121002132 h)
        (by
          have h : (thetaAboveCell0000220121002133).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220121002133 h))

theorem cover_subtree_a8a40a37bd16 :
    adaptiveCoverCheck 5 (childHL (childHL thetaAboveCell000022012100)) = true := by
  exact adaptiveCoverCheck_succ_of_children 4 (childHL (childHL thetaAboveCell000022012100))
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childLL (childHL (childHL
        thetaAboveCell000022012100)))
        (by
          have h : (thetaAboveCell0000220121002200).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220121002200 h)
        (by
          have h : (thetaAboveCell0000220121002201).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220121002201 h)
        (by
          have h : (thetaAboveCell0000220121002202).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220121002202 h)
        (by
          have h : (thetaAboveCell0000220121002203).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220121002203 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childLH (childHL (childHL
        thetaAboveCell000022012100)))
        (by
          have h : (thetaAboveCell0000220121002210).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220121002210 h)
        (by
          have h : (thetaAboveCell0000220121002211).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220121002211 h)
        (by
          have h : (thetaAboveCell0000220121002212).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220121002212 h)
        (by
          have h : (thetaAboveCell0000220121002213).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220121002213 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childHL (childHL (childHL
        thetaAboveCell000022012100)))
        (by
          have h : (thetaAboveCell0000220121002220).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220121002220 h)
        (by
          have h : (thetaAboveCell0000220121002221).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220121002221 h)
        (by
          have h : (thetaAboveCell0000220121002222).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220121002222 h)
        (by
          have h : (thetaAboveCell0000220121002223).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220121002223 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childHH (childHL (childHL
        thetaAboveCell000022012100)))
        (by
          have h : (thetaAboveCell0000220121002230).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220121002230 h)
        (by
          have h : (thetaAboveCell0000220121002231).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220121002231 h)
        (by
          have h : (thetaAboveCell0000220121002232).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220121002232 h)
        (by
          have h : (thetaAboveCell0000220121002233).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220121002233 h))

theorem cover_subtree_71af7f863f59 :
    adaptiveCoverCheck 5 (childHH (childHL thetaAboveCell000022012100)) = true := by
  exact adaptiveCoverCheck_succ_of_children 4 (childHH (childHL thetaAboveCell000022012100))
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childLL (childHH (childHL
        thetaAboveCell000022012100)))
        (by
          have h : (thetaAboveCell0000220121002300).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220121002300 h)
        (by
          have h : (thetaAboveCell0000220121002301).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220121002301 h)
        (by
          have h : (thetaAboveCell0000220121002302).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220121002302 h)
        (by
          have h : (thetaAboveCell0000220121002303).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220121002303 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childLH (childHH (childHL
        thetaAboveCell000022012100)))
        (by
          have h : (thetaAboveCell0000220121002310).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220121002310 h)
        (by
          have h : (thetaAboveCell0000220121002311).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220121002311 h)
        (by
          have h : (thetaAboveCell0000220121002312).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220121002312 h)
        (by
          have h : (thetaAboveCell0000220121002313).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220121002313 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childHL (childHH (childHL
        thetaAboveCell000022012100)))
        (by
          have h : (thetaAboveCell0000220121002320).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220121002320 h)
        (by
          have h : (thetaAboveCell0000220121002321).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220121002321 h)
        (by
          have h : (thetaAboveCell0000220121002322).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220121002322 h)
        (by
          have h : (thetaAboveCell0000220121002323).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220121002323 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childHH (childHH (childHL
        thetaAboveCell000022012100)))
        (by
          have h : (thetaAboveCell0000220121002330).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220121002330 h)
        (by
          have h : (thetaAboveCell0000220121002331).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220121002331 h)
        (by
          have h : (thetaAboveCell0000220121002332).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220121002332 h)
        (by
          have h : (thetaAboveCell0000220121002333).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220121002333 h))

theorem cover_subtree_e8b421b5f980 :
    adaptiveCoverCheck 6 (childHL thetaAboveCell000022012100) = true := by
  exact adaptiveCoverCheck_succ_of_children 5 (childHL thetaAboveCell000022012100)
    cover_subtree_c4eb81eb7e49
    cover_subtree_20c58a0c1f65
    cover_subtree_a8a40a37bd16
    cover_subtree_71af7f863f59

theorem cover_subtree_807256c88993 :
    adaptiveCoverCheck 5 (childLL (childHH thetaAboveCell000022012100)) = true := by
  exact adaptiveCoverCheck_succ_of_children 4 (childLL (childHH thetaAboveCell000022012100))
    (by
      have h : ((childLL (childLL (childHH thetaAboveCell000022012100)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childLL (childHH
        thetaAboveCell000022012100))) h)
    (by
      have h : ((childLH (childLL (childHH thetaAboveCell000022012100)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childLL (childHH
        thetaAboveCell000022012100))) h)
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childHL (childLL (childHH
        thetaAboveCell000022012100)))
        (by
          have h : (thetaAboveCell0000220121003020).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220121003020 h)
        (by
          have h : (thetaAboveCell0000220121003021).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220121003021 h)
        (by
          have h : (thetaAboveCell0000220121003022).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220121003022 h)
        (by
          have h : (thetaAboveCell0000220121003023).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220121003023 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childHH (childLL (childHH
        thetaAboveCell000022012100)))
        (by
          have h : (thetaAboveCell0000220121003030).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220121003030 h)
        (by
          have h : (thetaAboveCell0000220121003031).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220121003031 h)
        (by
          have h : (thetaAboveCell0000220121003032).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220121003032 h)
        (by
          have h : (thetaAboveCell0000220121003033).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220121003033 h))

theorem cover_subtree_8f2cea51bbf4 :
    adaptiveCoverCheck 5 (childLH (childHH thetaAboveCell000022012100)) = true := by
  exact adaptiveCoverCheck_succ_of_children 4 (childLH (childHH thetaAboveCell000022012100))
    (by
      have h : ((childLL (childLH (childHH thetaAboveCell000022012100)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childLH (childHH
        thetaAboveCell000022012100))) h)
    (by
      have h : ((childLH (childLH (childHH thetaAboveCell000022012100)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childLH (childHH
        thetaAboveCell000022012100))) h)
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childHL (childLH (childHH
        thetaAboveCell000022012100)))
        (by
          have h : (thetaAboveCell0000220121003120).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220121003120 h)
        (by
          have h : (thetaAboveCell0000220121003121).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220121003121 h)
        (by
          have h : (thetaAboveCell0000220121003122).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220121003122 h)
        (by
          have h : (thetaAboveCell0000220121003123).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220121003123 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childHH (childLH (childHH
        thetaAboveCell000022012100)))
        (by
          have h : (thetaAboveCell0000220121003130).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220121003130 h)
        (by
          have h : (thetaAboveCell0000220121003131).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220121003131 h)
        (by
          have h : (thetaAboveCell0000220121003132).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220121003132 h)
        (by
          have h : (thetaAboveCell0000220121003133).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220121003133 h))

theorem cover_subtree_c244889fccb8 :
    adaptiveCoverCheck 5 (childHL (childHH thetaAboveCell000022012100)) = true := by
  exact adaptiveCoverCheck_succ_of_children 4 (childHL (childHH thetaAboveCell000022012100))
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childLL (childHL (childHH
        thetaAboveCell000022012100)))
        (by
          have h : (thetaAboveCell0000220121003200).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220121003200 h)
        (by
          have h : (thetaAboveCell0000220121003201).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220121003201 h)
        (by
          have h : (thetaAboveCell0000220121003202).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220121003202 h)
        (by
          have h : (thetaAboveCell0000220121003203).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220121003203 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childLH (childHL (childHH
        thetaAboveCell000022012100)))
        (by
          have h : (thetaAboveCell0000220121003210).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220121003210 h)
        (by
          have h : (thetaAboveCell0000220121003211).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220121003211 h)
        (by
          have h : (thetaAboveCell0000220121003212).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220121003212 h)
        (by
          have h : (thetaAboveCell0000220121003213).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220121003213 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childHL (childHL (childHH
        thetaAboveCell000022012100)))
        (by
          have h : (thetaAboveCell0000220121003220).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220121003220 h)
        (by
          have h : (thetaAboveCell0000220121003221).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220121003221 h)
        (by
          have h : (thetaAboveCell0000220121003222).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220121003222 h)
        (by
          have h : (thetaAboveCell0000220121003223).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220121003223 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childHH (childHL (childHH
        thetaAboveCell000022012100)))
        (by
          have h : (thetaAboveCell0000220121003230).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220121003230 h)
        (by
          have h : (thetaAboveCell0000220121003231).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220121003231 h)
        (by
          have h : (thetaAboveCell0000220121003232).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220121003232 h)
        (by
          have h : (thetaAboveCell0000220121003233).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220121003233 h))

theorem cover_subtree_2684f740078d :
    adaptiveCoverCheck 5 (childHH (childHH thetaAboveCell000022012100)) = true := by
  exact adaptiveCoverCheck_succ_of_children 4 (childHH (childHH thetaAboveCell000022012100))
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childLL (childHH (childHH
        thetaAboveCell000022012100)))
        (by
          have h : (thetaAboveCell0000220121003300).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220121003300 h)
        (by
          have h : (thetaAboveCell0000220121003301).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220121003301 h)
        (by
          have h : (thetaAboveCell0000220121003302).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220121003302 h)
        (by
          have h : (thetaAboveCell0000220121003303).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220121003303 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childLH (childHH (childHH
        thetaAboveCell000022012100)))
        (by
          have h : (thetaAboveCell0000220121003310).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220121003310 h)
        (by
          have h : (thetaAboveCell0000220121003311).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220121003311 h)
        (by
          have h : (thetaAboveCell0000220121003312).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220121003312 h)
        (by
          have h : (thetaAboveCell0000220121003313).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220121003313 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childHL (childHH (childHH
        thetaAboveCell000022012100)))
        (by
          have h : (thetaAboveCell0000220121003320).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220121003320 h)
        (by
          have h : (thetaAboveCell0000220121003321).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220121003321 h)
        (by
          have h : (thetaAboveCell0000220121003322).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220121003322 h)
        (by
          have h : (thetaAboveCell0000220121003323).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220121003323 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childHH (childHH (childHH
        thetaAboveCell000022012100)))
        (by
          have h : (thetaAboveCell0000220121003330).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220121003330 h)
        (by
          have h : (thetaAboveCell0000220121003331).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220121003331 h)
        (by
          have h : (thetaAboveCell0000220121003332).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220121003332 h)
        (by
          have h : (thetaAboveCell0000220121003333).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220121003333 h))

theorem cover_subtree_38440f81d562 :
    adaptiveCoverCheck 6 (childHH thetaAboveCell000022012100) = true := by
  exact adaptiveCoverCheck_succ_of_children 5 (childHH thetaAboveCell000022012100)
    cover_subtree_807256c88993
    cover_subtree_8f2cea51bbf4
    cover_subtree_c244889fccb8
    cover_subtree_2684f740078d

theorem cover_subtree_c0614247fef2 :
    adaptiveCoverCheck 7 thetaAboveCell000022012100 = true := by
  exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000022012100
    (by
      exact adaptiveCoverCheck_succ_of_children 5 (childLL thetaAboveCell000022012100)
        (by
          have h : ((childLL (childLL thetaAboveCell000022012100))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childLL
            thetaAboveCell000022012100)) h)
        (by
          have h : ((childLH (childLL thetaAboveCell000022012100))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childLL
            thetaAboveCell000022012100)) h)
        (by
          have h : ((childHL (childLL thetaAboveCell000022012100))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childLL
            thetaAboveCell000022012100)) h)
        (by
          have h : ((childHH (childLL thetaAboveCell000022012100))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childLL
            thetaAboveCell000022012100)) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 5 (childLH thetaAboveCell000022012100)
        (by
          have h : ((childLL (childLH thetaAboveCell000022012100))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childLH
            thetaAboveCell000022012100)) h)
        (by
          have h : ((childLH (childLH thetaAboveCell000022012100))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childLH
            thetaAboveCell000022012100)) h)
        (by
          have h : ((childHL (childLH thetaAboveCell000022012100))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childLH
            thetaAboveCell000022012100)) h)
        (by
          have h : ((childHH (childLH thetaAboveCell000022012100))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childLH
            thetaAboveCell000022012100)) h))
    cover_subtree_e8b421b5f980
    cover_subtree_38440f81d562

theorem cover_subtree_31258573aaec :
    adaptiveCoverCheck 5 (childLL (childHL thetaAboveCell000022012101)) = true := by
  exact adaptiveCoverCheck_succ_of_children 4 (childLL (childHL thetaAboveCell000022012101))
    (by
      have h : ((childLL (childLL (childHL thetaAboveCell000022012101)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childLL (childHL
        thetaAboveCell000022012101))) h)
    (by
      have h : ((childLH (childLL (childHL thetaAboveCell000022012101)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childLL (childHL
        thetaAboveCell000022012101))) h)
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childHL (childLL (childHL
        thetaAboveCell000022012101)))
        (by
          have h : (thetaAboveCell0000220121012020).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220121012020 h)
        (by
          have h : (thetaAboveCell0000220121012021).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220121012021 h)
        (by
          have h : (thetaAboveCell0000220121012022).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220121012022 h)
        (by
          have h : (thetaAboveCell0000220121012023).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220121012023 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childHH (childLL (childHL
        thetaAboveCell000022012101)))
        (by
          have h : (thetaAboveCell0000220121012030).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220121012030 h)
        (by
          have h : (thetaAboveCell0000220121012031).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220121012031 h)
        (by
          have h : (thetaAboveCell0000220121012032).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220121012032 h)
        (by
          have h : (thetaAboveCell0000220121012033).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220121012033 h))

theorem cover_subtree_72b7b156e7ee :
    adaptiveCoverCheck 5 (childLH (childHL thetaAboveCell000022012101)) = true := by
  exact adaptiveCoverCheck_succ_of_children 4 (childLH (childHL thetaAboveCell000022012101))
    (by
      have h : ((childLL (childLH (childHL thetaAboveCell000022012101)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childLH (childHL
        thetaAboveCell000022012101))) h)
    (by
      have h : ((childLH (childLH (childHL thetaAboveCell000022012101)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childLH (childHL
        thetaAboveCell000022012101))) h)
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childHL (childLH (childHL
        thetaAboveCell000022012101)))
        (by
          have h : (thetaAboveCell0000220121012120).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220121012120 h)
        (by
          have h : (thetaAboveCell0000220121012121).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220121012121 h)
        (by
          have h : (thetaAboveCell0000220121012122).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220121012122 h)
        (by
          have h : (thetaAboveCell0000220121012123).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220121012123 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childHH (childLH (childHL
        thetaAboveCell000022012101)))
        (by
          have h : (thetaAboveCell0000220121012130).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220121012130 h)
        (by
          have h : (thetaAboveCell0000220121012131).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220121012131 h)
        (by
          have h : (thetaAboveCell0000220121012132).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220121012132 h)
        (by
          have h : (thetaAboveCell0000220121012133).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220121012133 h))

theorem cover_subtree_49d59b40ac80 :
    adaptiveCoverCheck 5 (childHL (childHL thetaAboveCell000022012101)) = true := by
  exact adaptiveCoverCheck_succ_of_children 4 (childHL (childHL thetaAboveCell000022012101))
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childLL (childHL (childHL
        thetaAboveCell000022012101)))
        (by
          have h : (thetaAboveCell0000220121012200).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220121012200 h)
        (by
          have h : (thetaAboveCell0000220121012201).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220121012201 h)
        (by
          have h : (thetaAboveCell0000220121012202).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220121012202 h)
        (by
          have h : (thetaAboveCell0000220121012203).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220121012203 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childLH (childHL (childHL
        thetaAboveCell000022012101)))
        (by
          have h : (thetaAboveCell0000220121012210).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220121012210 h)
        (by
          have h : (thetaAboveCell0000220121012211).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220121012211 h)
        (by
          have h : (thetaAboveCell0000220121012212).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220121012212 h)
        (by
          have h : (thetaAboveCell0000220121012213).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220121012213 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childHL (childHL (childHL
        thetaAboveCell000022012101)))
        (by
          have h : (thetaAboveCell0000220121012220).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220121012220 h)
        (by
          have h : (thetaAboveCell0000220121012221).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220121012221 h)
        (by
          have h : (thetaAboveCell0000220121012222).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220121012222 h)
        (by
          have h : (thetaAboveCell0000220121012223).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220121012223 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childHH (childHL (childHL
        thetaAboveCell000022012101)))
        (by
          have h : (thetaAboveCell0000220121012230).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220121012230 h)
        (by
          have h : (thetaAboveCell0000220121012231).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220121012231 h)
        (by
          have h : (thetaAboveCell0000220121012232).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220121012232 h)
        (by
          have h : (thetaAboveCell0000220121012233).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220121012233 h))

theorem cover_subtree_de88d1b7e4d0 :
    adaptiveCoverCheck 5 (childHH (childHL thetaAboveCell000022012101)) = true := by
  exact adaptiveCoverCheck_succ_of_children 4 (childHH (childHL thetaAboveCell000022012101))
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childLL (childHH (childHL
        thetaAboveCell000022012101)))
        (by
          have h : (thetaAboveCell0000220121012300).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220121012300 h)
        (by
          have h : (thetaAboveCell0000220121012301).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220121012301 h)
        (by
          have h : (thetaAboveCell0000220121012302).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220121012302 h)
        (by
          have h : (thetaAboveCell0000220121012303).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220121012303 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childLH (childHH (childHL
        thetaAboveCell000022012101)))
        (by
          have h : (thetaAboveCell0000220121012310).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220121012310 h)
        (by
          have h : (thetaAboveCell0000220121012311).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220121012311 h)
        (by
          have h : (thetaAboveCell0000220121012312).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220121012312 h)
        (by
          have h : (thetaAboveCell0000220121012313).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220121012313 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childHL (childHH (childHL
        thetaAboveCell000022012101)))
        (by
          have h : (thetaAboveCell0000220121012320).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220121012320 h)
        (by
          have h : (thetaAboveCell0000220121012321).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220121012321 h)
        (by
          have h : (thetaAboveCell0000220121012322).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220121012322 h)
        (by
          have h : (thetaAboveCell0000220121012323).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220121012323 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childHH (childHH (childHL
        thetaAboveCell000022012101)))
        (by
          have h : (thetaAboveCell0000220121012330).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220121012330 h)
        (by
          have h : (thetaAboveCell0000220121012331).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220121012331 h)
        (by
          have h : (thetaAboveCell0000220121012332).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220121012332 h)
        (by
          have h : (thetaAboveCell0000220121012333).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220121012333 h))

theorem cover_subtree_8fb6927013d7 :
    adaptiveCoverCheck 6 (childHL thetaAboveCell000022012101) = true := by
  exact adaptiveCoverCheck_succ_of_children 5 (childHL thetaAboveCell000022012101)
    cover_subtree_31258573aaec
    cover_subtree_72b7b156e7ee
    cover_subtree_49d59b40ac80
    cover_subtree_de88d1b7e4d0

theorem cover_subtree_02e81ee0d1ef :
    adaptiveCoverCheck 5 (childLL (childHH thetaAboveCell000022012101)) = true := by
  exact adaptiveCoverCheck_succ_of_children 4 (childLL (childHH thetaAboveCell000022012101))
    (by
      have h : ((childLL (childLL (childHH thetaAboveCell000022012101)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childLL (childHH
        thetaAboveCell000022012101))) h)
    (by
      have h : ((childLH (childLL (childHH thetaAboveCell000022012101)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childLL (childHH
        thetaAboveCell000022012101))) h)
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childHL (childLL (childHH
        thetaAboveCell000022012101)))
        (by
          have h : (thetaAboveCell0000220121013020).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220121013020 h)
        (by
          have h : (thetaAboveCell0000220121013021).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220121013021 h)
        (by
          have h : (thetaAboveCell0000220121013022).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220121013022 h)
        (by
          have h : (thetaAboveCell0000220121013023).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220121013023 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childHH (childLL (childHH
        thetaAboveCell000022012101)))
        (by
          have h : (thetaAboveCell0000220121013030).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220121013030 h)
        (by
          have h : (thetaAboveCell0000220121013031).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220121013031 h)
        (by
          have h : (thetaAboveCell0000220121013032).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220121013032 h)
        (by
          have h : (thetaAboveCell0000220121013033).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220121013033 h))

theorem cover_subtree_cc00f203ac8d :
    adaptiveCoverCheck 5 (childLH (childHH thetaAboveCell000022012101)) = true := by
  exact adaptiveCoverCheck_succ_of_children 4 (childLH (childHH thetaAboveCell000022012101))
    (by
      have h : ((childLL (childLH (childHH thetaAboveCell000022012101)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childLH (childHH
        thetaAboveCell000022012101))) h)
    (by
      have h : ((childLH (childLH (childHH thetaAboveCell000022012101)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childLH (childHH
        thetaAboveCell000022012101))) h)
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childHL (childLH (childHH
        thetaAboveCell000022012101)))
        (by
          have h : (thetaAboveCell0000220121013120).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220121013120 h)
        (by
          have h : (thetaAboveCell0000220121013121).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220121013121 h)
        (by
          have h : (thetaAboveCell0000220121013122).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220121013122 h)
        (by
          have h : (thetaAboveCell0000220121013123).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220121013123 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childHH (childLH (childHH
        thetaAboveCell000022012101)))
        (by
          have h : (thetaAboveCell0000220121013130).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220121013130 h)
        (by
          have h : (thetaAboveCell0000220121013131).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220121013131 h)
        (by
          have h : (thetaAboveCell0000220121013132).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220121013132 h)
        (by
          have h : (thetaAboveCell0000220121013133).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220121013133 h))

theorem cover_subtree_d22ca7c15af3 :
    adaptiveCoverCheck 5 (childHL (childHH thetaAboveCell000022012101)) = true := by
  exact adaptiveCoverCheck_succ_of_children 4 (childHL (childHH thetaAboveCell000022012101))
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childLL (childHL (childHH
        thetaAboveCell000022012101)))
        (by
          have h : (thetaAboveCell0000220121013200).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220121013200 h)
        (by
          have h : (thetaAboveCell0000220121013201).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220121013201 h)
        (by
          have h : (thetaAboveCell0000220121013202).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220121013202 h)
        (by
          have h : (thetaAboveCell0000220121013203).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220121013203 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childLH (childHL (childHH
        thetaAboveCell000022012101)))
        (by
          have h : (thetaAboveCell0000220121013210).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220121013210 h)
        (by
          have h : (thetaAboveCell0000220121013211).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220121013211 h)
        (by
          have h : (thetaAboveCell0000220121013212).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220121013212 h)
        (by
          have h : (thetaAboveCell0000220121013213).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220121013213 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childHL (childHL (childHH
        thetaAboveCell000022012101)))
        (by
          have h : (thetaAboveCell0000220121013220).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220121013220 h)
        (by
          have h : (thetaAboveCell0000220121013221).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220121013221 h)
        (by
          have h : (thetaAboveCell0000220121013222).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220121013222 h)
        (by
          have h : (thetaAboveCell0000220121013223).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220121013223 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childHH (childHL (childHH
        thetaAboveCell000022012101)))
        (by
          have h : (thetaAboveCell0000220121013230).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220121013230 h)
        (by
          have h : (thetaAboveCell0000220121013231).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220121013231 h)
        (by
          have h : (thetaAboveCell0000220121013232).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220121013232 h)
        (by
          have h : (thetaAboveCell0000220121013233).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220121013233 h))

theorem cover_subtree_f04c91fe2c64 :
    adaptiveCoverCheck 5 (childHH (childHH thetaAboveCell000022012101)) = true := by
  exact adaptiveCoverCheck_succ_of_children 4 (childHH (childHH thetaAboveCell000022012101))
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childLL (childHH (childHH
        thetaAboveCell000022012101)))
        (by
          have h : (thetaAboveCell0000220121013300).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220121013300 h)
        (by
          have h : (thetaAboveCell0000220121013301).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220121013301 h)
        (by
          have h : (thetaAboveCell0000220121013302).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220121013302 h)
        (by
          have h : (thetaAboveCell0000220121013303).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220121013303 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childLH (childHH (childHH
        thetaAboveCell000022012101)))
        (by
          have h : (thetaAboveCell0000220121013310).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220121013310 h)
        (by
          have h : (thetaAboveCell0000220121013311).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220121013311 h)
        (by
          have h : (thetaAboveCell0000220121013312).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220121013312 h)
        (by
          have h : (thetaAboveCell0000220121013313).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220121013313 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childHL (childHH (childHH
        thetaAboveCell000022012101)))
        (by
          have h : (thetaAboveCell0000220121013320).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220121013320 h)
        (by
          have h : (thetaAboveCell0000220121013321).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220121013321 h)
        (by
          have h : (thetaAboveCell0000220121013322).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220121013322 h)
        (by
          have h : (thetaAboveCell0000220121013323).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220121013323 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childHH (childHH (childHH
        thetaAboveCell000022012101)))
        (by
          have h : (thetaAboveCell0000220121013330).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220121013330 h)
        (by
          have h : (thetaAboveCell0000220121013331).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220121013331 h)
        (by
          have h : (thetaAboveCell0000220121013332).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220121013332 h)
        (by
          have h : (thetaAboveCell0000220121013333).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220121013333 h))

theorem cover_subtree_893a2b14ea46 :
    adaptiveCoverCheck 6 (childHH thetaAboveCell000022012101) = true := by
  exact adaptiveCoverCheck_succ_of_children 5 (childHH thetaAboveCell000022012101)
    cover_subtree_02e81ee0d1ef
    cover_subtree_cc00f203ac8d
    cover_subtree_d22ca7c15af3
    cover_subtree_f04c91fe2c64

theorem cover_subtree_8bce29d5bf8e :
    adaptiveCoverCheck 7 thetaAboveCell000022012101 = true := by
  exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000022012101
    (by
      exact adaptiveCoverCheck_succ_of_children 5 (childLL thetaAboveCell000022012101)
        (by
          have h : ((childLL (childLL thetaAboveCell000022012101))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childLL
            thetaAboveCell000022012101)) h)
        (by
          have h : ((childLH (childLL thetaAboveCell000022012101))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childLL
            thetaAboveCell000022012101)) h)
        (by
          have h : ((childHL (childLL thetaAboveCell000022012101))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childLL
            thetaAboveCell000022012101)) h)
        (by
          have h : ((childHH (childLL thetaAboveCell000022012101))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childLL
            thetaAboveCell000022012101)) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 5 (childLH thetaAboveCell000022012101)
        (by
          have h : ((childLL (childLH thetaAboveCell000022012101))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childLH
            thetaAboveCell000022012101)) h)
        (by
          have h : ((childLH (childLH thetaAboveCell000022012101))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childLH
            thetaAboveCell000022012101)) h)
        (by
          have h : ((childHL (childLH thetaAboveCell000022012101))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childLH
            thetaAboveCell000022012101)) h)
        (by
          have h : ((childHH (childLH thetaAboveCell000022012101))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childLH
            thetaAboveCell000022012101)) h))
    cover_subtree_8fb6927013d7
    cover_subtree_893a2b14ea46

theorem cover_subtree_042414b8b05d :
    adaptiveCoverCheck 7 thetaAboveCell000022012102 = true := by
  exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000022012102
    (by
      exact adaptiveCoverCheck_succ_of_children 5 (childLL thetaAboveCell000022012102)
        (by
          have h : ((childLL (childLL thetaAboveCell000022012102))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childLL
            thetaAboveCell000022012102)) h)
        (by
          have h : ((childLH (childLL thetaAboveCell000022012102))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childLL
            thetaAboveCell000022012102)) h)
        (by
          have h : ((childHL (childLL thetaAboveCell000022012102))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childLL
            thetaAboveCell000022012102)) h)
        (by
          have h : ((childHH (childLL thetaAboveCell000022012102))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childLL
            thetaAboveCell000022012102)) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 5 (childLH thetaAboveCell000022012102)
        (by
          have h : ((childLL (childLH thetaAboveCell000022012102))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childLH
            thetaAboveCell000022012102)) h)
        (by
          have h : ((childLH (childLH thetaAboveCell000022012102))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childLH
            thetaAboveCell000022012102)) h)
        (by
          have h : ((childHL (childLH thetaAboveCell000022012102))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childLH
            thetaAboveCell000022012102)) h)
        (by
          have h : ((childHH (childLH thetaAboveCell000022012102))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childLH
            thetaAboveCell000022012102)) h))
    (by
      have h : ((childHL thetaAboveCell000022012102)).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000022012102) h)
    (by
      have h : ((childHH thetaAboveCell000022012102)).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000022012102) h)

theorem cover_subtree_7648aff1a886 :
    adaptiveCoverCheck 7 thetaAboveCell000022012103 = true := by
  exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000022012103
    (by
      exact adaptiveCoverCheck_succ_of_children 5 (childLL thetaAboveCell000022012103)
        (by
          have h : ((childLL (childLL thetaAboveCell000022012103))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childLL
            thetaAboveCell000022012103)) h)
        (by
          have h : ((childLH (childLL thetaAboveCell000022012103))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childLL
            thetaAboveCell000022012103)) h)
        (by
          have h : ((childHL (childLL thetaAboveCell000022012103))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childLL
            thetaAboveCell000022012103)) h)
        (by
          have h : ((childHH (childLL thetaAboveCell000022012103))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childLL
            thetaAboveCell000022012103)) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 5 (childLH thetaAboveCell000022012103)
        (by
          have h : ((childLL (childLH thetaAboveCell000022012103))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childLH
            thetaAboveCell000022012103)) h)
        (by
          exact adaptiveCoverCheck_succ_of_children 4 (childLH (childLH thetaAboveCell000022012103))
            (by
              have h : ((childLL (childLH (childLH thetaAboveCell000022012103)))).rejected = true
                := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childLH (childLH
                thetaAboveCell000022012103))) h)
            (by
              have h : ((childLH (childLH (childLH thetaAboveCell000022012103)))).rejected = true
                := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childLH (childLH
                thetaAboveCell000022012103))) h)
            (by
              have h : ((childHL (childLH (childLH thetaAboveCell000022012103)))).rejected = true
                := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childLH (childLH
                thetaAboveCell000022012103))) h)
            (by
              have h : ((childHH (childLH (childLH thetaAboveCell000022012103)))).rejected = true
                := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childLH (childLH
                thetaAboveCell000022012103))) h))
        (by
          have h : ((childHL (childLH thetaAboveCell000022012103))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childLH
            thetaAboveCell000022012103)) h)
        (by
          have h : ((childHH (childLH thetaAboveCell000022012103))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childLH
            thetaAboveCell000022012103)) h))
    (by
      have h : ((childHL thetaAboveCell000022012103)).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000022012103) h)
    (by
      have h : ((childHH thetaAboveCell000022012103)).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000022012103) h)

theorem cover_subtree_c6c6b7e63010 :
    adaptiveCoverCheck 8 (childLL (childLH (childHL thetaAboveCell00002201))) = true := by
  exact adaptiveCoverCheck_succ_of_children 7 (childLL (childLH (childHL thetaAboveCell00002201)))
    cover_subtree_c0614247fef2
    cover_subtree_8bce29d5bf8e
    cover_subtree_042414b8b05d
    cover_subtree_7648aff1a886

theorem cover_subtree_7be42b58a89a :
    adaptiveCoverCheck 5 (childLL (childHL thetaAboveCell000022012110)) = true := by
  exact adaptiveCoverCheck_succ_of_children 4 (childLL (childHL thetaAboveCell000022012110))
    (by
      have h : ((childLL (childLL (childHL thetaAboveCell000022012110)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childLL (childHL
        thetaAboveCell000022012110))) h)
    (by
      have h : ((childLH (childLL (childHL thetaAboveCell000022012110)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childLL (childHL
        thetaAboveCell000022012110))) h)
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childHL (childLL (childHL
        thetaAboveCell000022012110)))
        (by
          have h : (thetaAboveCell0000220121102020).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220121102020 h)
        (by
          have h : (thetaAboveCell0000220121102021).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220121102021 h)
        (by
          have h : (thetaAboveCell0000220121102022).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220121102022 h)
        (by
          have h : (thetaAboveCell0000220121102023).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220121102023 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childHH (childLL (childHL
        thetaAboveCell000022012110)))
        (by
          have h : (thetaAboveCell0000220121102030).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220121102030 h)
        (by
          have h : (thetaAboveCell0000220121102031).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220121102031 h)
        (by
          have h : (thetaAboveCell0000220121102032).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220121102032 h)
        (by
          have h : (thetaAboveCell0000220121102033).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220121102033 h))

theorem cover_subtree_b2dbe383f962 :
    adaptiveCoverCheck 5 (childLH (childHL thetaAboveCell000022012110)) = true := by
  exact adaptiveCoverCheck_succ_of_children 4 (childLH (childHL thetaAboveCell000022012110))
    (by
      have h : ((childLL (childLH (childHL thetaAboveCell000022012110)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childLH (childHL
        thetaAboveCell000022012110))) h)
    (by
      have h : ((childLH (childLH (childHL thetaAboveCell000022012110)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childLH (childHL
        thetaAboveCell000022012110))) h)
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childHL (childLH (childHL
        thetaAboveCell000022012110)))
        (by
          have h : (thetaAboveCell0000220121102120).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220121102120 h)
        (by
          have h : (thetaAboveCell0000220121102121).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220121102121 h)
        (by
          have h : (thetaAboveCell0000220121102122).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220121102122 h)
        (by
          have h : (thetaAboveCell0000220121102123).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220121102123 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childHH (childLH (childHL
        thetaAboveCell000022012110)))
        (by
          have h : (thetaAboveCell0000220121102130).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220121102130 h)
        (by
          have h : (thetaAboveCell0000220121102131).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220121102131 h)
        (by
          have h : (thetaAboveCell0000220121102132).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220121102132 h)
        (by
          have h : (thetaAboveCell0000220121102133).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220121102133 h))

theorem cover_subtree_62ab94416880 :
    adaptiveCoverCheck 5 (childHL (childHL thetaAboveCell000022012110)) = true := by
  exact adaptiveCoverCheck_succ_of_children 4 (childHL (childHL thetaAboveCell000022012110))
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childLL (childHL (childHL
        thetaAboveCell000022012110)))
        (by
          have h : (thetaAboveCell0000220121102200).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220121102200 h)
        (by
          have h : (thetaAboveCell0000220121102201).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220121102201 h)
        (by
          have h : (thetaAboveCell0000220121102202).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220121102202 h)
        (by
          have h : (thetaAboveCell0000220121102203).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220121102203 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childLH (childHL (childHL
        thetaAboveCell000022012110)))
        (by
          have h : (thetaAboveCell0000220121102210).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220121102210 h)
        (by
          have h : (thetaAboveCell0000220121102211).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220121102211 h)
        (by
          have h : (thetaAboveCell0000220121102212).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220121102212 h)
        (by
          have h : (thetaAboveCell0000220121102213).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220121102213 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childHL (childHL (childHL
        thetaAboveCell000022012110)))
        (by
          have h : (thetaAboveCell0000220121102220).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220121102220 h)
        (by
          have h : (thetaAboveCell0000220121102221).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220121102221 h)
        (by
          have h : (thetaAboveCell0000220121102222).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220121102222 h)
        (by
          have h : (thetaAboveCell0000220121102223).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220121102223 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childHH (childHL (childHL
        thetaAboveCell000022012110)))
        (by
          have h : (thetaAboveCell0000220121102230).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220121102230 h)
        (by
          have h : (thetaAboveCell0000220121102231).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220121102231 h)
        (by
          have h : (thetaAboveCell0000220121102232).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220121102232 h)
        (by
          have h : (thetaAboveCell0000220121102233).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220121102233 h))

theorem cover_subtree_55ef04fe757d :
    adaptiveCoverCheck 5 (childHH (childHL thetaAboveCell000022012110)) = true := by
  exact adaptiveCoverCheck_succ_of_children 4 (childHH (childHL thetaAboveCell000022012110))
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childLL (childHH (childHL
        thetaAboveCell000022012110)))
        (by
          have h : (thetaAboveCell0000220121102300).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220121102300 h)
        (by
          have h : (thetaAboveCell0000220121102301).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220121102301 h)
        (by
          have h : (thetaAboveCell0000220121102302).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220121102302 h)
        (by
          have h : (thetaAboveCell0000220121102303).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220121102303 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childLH (childHH (childHL
        thetaAboveCell000022012110)))
        (by
          have h : (thetaAboveCell0000220121102310).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220121102310 h)
        (by
          have h : (thetaAboveCell0000220121102311).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220121102311 h)
        (by
          have h : (thetaAboveCell0000220121102312).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220121102312 h)
        (by
          have h : (thetaAboveCell0000220121102313).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220121102313 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childHL (childHH (childHL
        thetaAboveCell000022012110)))
        (by
          have h : (thetaAboveCell0000220121102320).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220121102320 h)
        (by
          have h : (thetaAboveCell0000220121102321).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220121102321 h)
        (by
          have h : (thetaAboveCell0000220121102322).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220121102322 h)
        (by
          have h : (thetaAboveCell0000220121102323).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220121102323 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childHH (childHH (childHL
        thetaAboveCell000022012110)))
        (by
          have h : (thetaAboveCell0000220121102330).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220121102330 h)
        (by
          have h : (thetaAboveCell0000220121102331).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220121102331 h)
        (by
          have h : (thetaAboveCell0000220121102332).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220121102332 h)
        (by
          have h : (thetaAboveCell0000220121102333).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220121102333 h))

theorem cover_subtree_3e8ada6913b4 :
    adaptiveCoverCheck 6 (childHL thetaAboveCell000022012110) = true := by
  exact adaptiveCoverCheck_succ_of_children 5 (childHL thetaAboveCell000022012110)
    cover_subtree_7be42b58a89a
    cover_subtree_b2dbe383f962
    cover_subtree_62ab94416880
    cover_subtree_55ef04fe757d

theorem cover_subtree_9b287e7b4186 :
    adaptiveCoverCheck 5 (childLL (childHH thetaAboveCell000022012110)) = true := by
  exact adaptiveCoverCheck_succ_of_children 4 (childLL (childHH thetaAboveCell000022012110))
    (by
      have h : ((childLL (childLL (childHH thetaAboveCell000022012110)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childLL (childHH
        thetaAboveCell000022012110))) h)
    (by
      have h : ((childLH (childLL (childHH thetaAboveCell000022012110)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childLL (childHH
        thetaAboveCell000022012110))) h)
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childHL (childLL (childHH
        thetaAboveCell000022012110)))
        (by
          have h : (thetaAboveCell0000220121103020).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220121103020 h)
        (by
          have h : (thetaAboveCell0000220121103021).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220121103021 h)
        (by
          have h : (thetaAboveCell0000220121103022).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220121103022 h)
        (by
          have h : (thetaAboveCell0000220121103023).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220121103023 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childHH (childLL (childHH
        thetaAboveCell000022012110)))
        (by
          have h : (thetaAboveCell0000220121103030).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220121103030 h)
        (by
          have h : (thetaAboveCell0000220121103031).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220121103031 h)
        (by
          have h : (thetaAboveCell0000220121103032).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220121103032 h)
        (by
          have h : (thetaAboveCell0000220121103033).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220121103033 h))

theorem cover_subtree_6f0c3876c853 :
    adaptiveCoverCheck 5 (childLH (childHH thetaAboveCell000022012110)) = true := by
  exact adaptiveCoverCheck_succ_of_children 4 (childLH (childHH thetaAboveCell000022012110))
    (by
      have h : ((childLL (childLH (childHH thetaAboveCell000022012110)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childLH (childHH
        thetaAboveCell000022012110))) h)
    (by
      have h : ((childLH (childLH (childHH thetaAboveCell000022012110)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childLH (childHH
        thetaAboveCell000022012110))) h)
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childHL (childLH (childHH
        thetaAboveCell000022012110)))
        (by
          have h : (thetaAboveCell0000220121103120).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220121103120 h)
        (by
          have h : (thetaAboveCell0000220121103121).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220121103121 h)
        (by
          have h : (thetaAboveCell0000220121103122).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220121103122 h)
        (by
          have h : (thetaAboveCell0000220121103123).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220121103123 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childHH (childLH (childHH
        thetaAboveCell000022012110)))
        (by
          have h : (thetaAboveCell0000220121103130).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220121103130 h)
        (by
          have h : (thetaAboveCell0000220121103131).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220121103131 h)
        (by
          have h : (thetaAboveCell0000220121103132).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220121103132 h)
        (by
          have h : (thetaAboveCell0000220121103133).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220121103133 h))

theorem cover_subtree_b459e9c4ef11 :
    adaptiveCoverCheck 5 (childHL (childHH thetaAboveCell000022012110)) = true := by
  exact adaptiveCoverCheck_succ_of_children 4 (childHL (childHH thetaAboveCell000022012110))
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childLL (childHL (childHH
        thetaAboveCell000022012110)))
        (by
          have h : (thetaAboveCell0000220121103200).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220121103200 h)
        (by
          have h : (thetaAboveCell0000220121103201).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220121103201 h)
        (by
          have h : (thetaAboveCell0000220121103202).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220121103202 h)
        (by
          have h : (thetaAboveCell0000220121103203).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220121103203 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childLH (childHL (childHH
        thetaAboveCell000022012110)))
        (by
          have h : (thetaAboveCell0000220121103210).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220121103210 h)
        (by
          have h : (thetaAboveCell0000220121103211).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220121103211 h)
        (by
          have h : (thetaAboveCell0000220121103212).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220121103212 h)
        (by
          have h : (thetaAboveCell0000220121103213).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220121103213 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childHL (childHL (childHH
        thetaAboveCell000022012110)))
        (by
          have h : (thetaAboveCell0000220121103220).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220121103220 h)
        (by
          have h : (thetaAboveCell0000220121103221).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220121103221 h)
        (by
          have h : (thetaAboveCell0000220121103222).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220121103222 h)
        (by
          have h : (thetaAboveCell0000220121103223).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220121103223 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childHH (childHL (childHH
        thetaAboveCell000022012110)))
        (by
          have h : (thetaAboveCell0000220121103230).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220121103230 h)
        (by
          have h : (thetaAboveCell0000220121103231).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220121103231 h)
        (by
          have h : (thetaAboveCell0000220121103232).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220121103232 h)
        (by
          have h : (thetaAboveCell0000220121103233).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220121103233 h))

theorem cover_subtree_59308c01291f :
    adaptiveCoverCheck 5 (childHH (childHH thetaAboveCell000022012110)) = true := by
  exact adaptiveCoverCheck_succ_of_children 4 (childHH (childHH thetaAboveCell000022012110))
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childLL (childHH (childHH
        thetaAboveCell000022012110)))
        (by
          have h : (thetaAboveCell0000220121103300).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220121103300 h)
        (by
          have h : (thetaAboveCell0000220121103301).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220121103301 h)
        (by
          have h : (thetaAboveCell0000220121103302).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220121103302 h)
        (by
          have h : (thetaAboveCell0000220121103303).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220121103303 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childLH (childHH (childHH
        thetaAboveCell000022012110)))
        (by
          have h : (thetaAboveCell0000220121103310).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220121103310 h)
        (by
          have h : (thetaAboveCell0000220121103311).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220121103311 h)
        (by
          have h : (thetaAboveCell0000220121103312).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220121103312 h)
        (by
          have h : (thetaAboveCell0000220121103313).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220121103313 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childHL (childHH (childHH
        thetaAboveCell000022012110)))
        (by
          have h : (thetaAboveCell0000220121103320).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220121103320 h)
        (by
          have h : (thetaAboveCell0000220121103321).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220121103321 h)
        (by
          have h : (thetaAboveCell0000220121103322).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220121103322 h)
        (by
          have h : (thetaAboveCell0000220121103323).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220121103323 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childHH (childHH (childHH
        thetaAboveCell000022012110)))
        (by
          have h : (thetaAboveCell0000220121103330).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220121103330 h)
        (by
          have h : (thetaAboveCell0000220121103331).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220121103331 h)
        (by
          have h : (thetaAboveCell0000220121103332).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220121103332 h)
        (by
          have h : (thetaAboveCell0000220121103333).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220121103333 h))

theorem cover_subtree_cc7dfcac2ef6 :
    adaptiveCoverCheck 6 (childHH thetaAboveCell000022012110) = true := by
  exact adaptiveCoverCheck_succ_of_children 5 (childHH thetaAboveCell000022012110)
    cover_subtree_9b287e7b4186
    cover_subtree_6f0c3876c853
    cover_subtree_b459e9c4ef11
    cover_subtree_59308c01291f

theorem cover_subtree_4255f05ab59f :
    adaptiveCoverCheck 7 thetaAboveCell000022012110 = true := by
  exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000022012110
    (by
      exact adaptiveCoverCheck_succ_of_children 5 (childLL thetaAboveCell000022012110)
        (by
          have h : ((childLL (childLL thetaAboveCell000022012110))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childLL
            thetaAboveCell000022012110)) h)
        (by
          have h : ((childLH (childLL thetaAboveCell000022012110))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childLL
            thetaAboveCell000022012110)) h)
        (by
          have h : ((childHL (childLL thetaAboveCell000022012110))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childLL
            thetaAboveCell000022012110)) h)
        (by
          have h : ((childHH (childLL thetaAboveCell000022012110))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childLL
            thetaAboveCell000022012110)) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 5 (childLH thetaAboveCell000022012110)
        (by
          have h : ((childLL (childLH thetaAboveCell000022012110))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childLH
            thetaAboveCell000022012110)) h)
        (by
          have h : ((childLH (childLH thetaAboveCell000022012110))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childLH
            thetaAboveCell000022012110)) h)
        (by
          have h : ((childHL (childLH thetaAboveCell000022012110))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childLH
            thetaAboveCell000022012110)) h)
        (by
          have h : ((childHH (childLH thetaAboveCell000022012110))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childLH
            thetaAboveCell000022012110)) h))
    cover_subtree_3e8ada6913b4
    cover_subtree_cc7dfcac2ef6

theorem cover_subtree_2c166d84fe59 :
    adaptiveCoverCheck 5 (childLL (childHL thetaAboveCell000022012111)) = true := by
  exact adaptiveCoverCheck_succ_of_children 4 (childLL (childHL thetaAboveCell000022012111))
    (by
      have h : ((childLL (childLL (childHL thetaAboveCell000022012111)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childLL (childHL
        thetaAboveCell000022012111))) h)
    (by
      have h : ((childLH (childLL (childHL thetaAboveCell000022012111)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childLL (childHL
        thetaAboveCell000022012111))) h)
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childHL (childLL (childHL
        thetaAboveCell000022012111)))
        (by
          have h : (thetaAboveCell0000220121112020).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220121112020 h)
        (by
          have h : (thetaAboveCell0000220121112021).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220121112021 h)
        (by
          have h : (thetaAboveCell0000220121112022).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220121112022 h)
        (by
          have h : (thetaAboveCell0000220121112023).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220121112023 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childHH (childLL (childHL
        thetaAboveCell000022012111)))
        (by
          have h : (thetaAboveCell0000220121112030).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220121112030 h)
        (by
          have h : (thetaAboveCell0000220121112031).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220121112031 h)
        (by
          have h : (thetaAboveCell0000220121112032).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220121112032 h)
        (by
          have h : (thetaAboveCell0000220121112033).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220121112033 h))

theorem cover_subtree_d41cf2e18f87 :
    adaptiveCoverCheck 5 (childLH (childHL thetaAboveCell000022012111)) = true := by
  exact adaptiveCoverCheck_succ_of_children 4 (childLH (childHL thetaAboveCell000022012111))
    (by
      have h : ((childLL (childLH (childHL thetaAboveCell000022012111)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childLH (childHL
        thetaAboveCell000022012111))) h)
    (by
      have h : ((childLH (childLH (childHL thetaAboveCell000022012111)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childLH (childHL
        thetaAboveCell000022012111))) h)
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childHL (childLH (childHL
        thetaAboveCell000022012111)))
        (by
          have h : (thetaAboveCell0000220121112120).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220121112120 h)
        (by
          have h : (thetaAboveCell0000220121112121).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220121112121 h)
        (by
          have h : (thetaAboveCell0000220121112122).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220121112122 h)
        (by
          have h : (thetaAboveCell0000220121112123).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220121112123 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childHH (childLH (childHL
        thetaAboveCell000022012111)))
        (by
          have h : (thetaAboveCell0000220121112130).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220121112130 h)
        (by
          have h : (thetaAboveCell0000220121112131).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220121112131 h)
        (by
          have h : (thetaAboveCell0000220121112132).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220121112132 h)
        (by
          have h : (thetaAboveCell0000220121112133).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220121112133 h))

theorem cover_subtree_1fd2ad12dba0 :
    adaptiveCoverCheck 5 (childHL (childHL thetaAboveCell000022012111)) = true := by
  exact adaptiveCoverCheck_succ_of_children 4 (childHL (childHL thetaAboveCell000022012111))
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childLL (childHL (childHL
        thetaAboveCell000022012111)))
        (by
          have h : (thetaAboveCell0000220121112200).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220121112200 h)
        (by
          have h : (thetaAboveCell0000220121112201).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220121112201 h)
        (by
          have h : (thetaAboveCell0000220121112202).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220121112202 h)
        (by
          have h : (thetaAboveCell0000220121112203).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220121112203 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childLH (childHL (childHL
        thetaAboveCell000022012111)))
        (by
          have h : (thetaAboveCell0000220121112210).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220121112210 h)
        (by
          have h : (thetaAboveCell0000220121112211).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220121112211 h)
        (by
          have h : (thetaAboveCell0000220121112212).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220121112212 h)
        (by
          have h : (thetaAboveCell0000220121112213).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220121112213 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childHL (childHL (childHL
        thetaAboveCell000022012111)))
        (by
          have h : (thetaAboveCell0000220121112220).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220121112220 h)
        (by
          have h : (thetaAboveCell0000220121112221).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220121112221 h)
        (by
          have h : (thetaAboveCell0000220121112222).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220121112222 h)
        (by
          have h : (thetaAboveCell0000220121112223).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220121112223 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childHH (childHL (childHL
        thetaAboveCell000022012111)))
        (by
          have h : (thetaAboveCell0000220121112230).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220121112230 h)
        (by
          have h : (thetaAboveCell0000220121112231).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220121112231 h)
        (by
          have h : (thetaAboveCell0000220121112232).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220121112232 h)
        (by
          have h : (thetaAboveCell0000220121112233).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220121112233 h))

theorem cover_subtree_88e81007f06f :
    adaptiveCoverCheck 5 (childHH (childHL thetaAboveCell000022012111)) = true := by
  exact adaptiveCoverCheck_succ_of_children 4 (childHH (childHL thetaAboveCell000022012111))
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childLL (childHH (childHL
        thetaAboveCell000022012111)))
        (by
          have h : (thetaAboveCell0000220121112300).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220121112300 h)
        (by
          have h : (thetaAboveCell0000220121112301).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220121112301 h)
        (by
          have h : (thetaAboveCell0000220121112302).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220121112302 h)
        (by
          have h : (thetaAboveCell0000220121112303).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220121112303 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childLH (childHH (childHL
        thetaAboveCell000022012111)))
        (by
          have h : (thetaAboveCell0000220121112310).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220121112310 h)
        (by
          have h : (thetaAboveCell0000220121112311).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220121112311 h)
        (by
          have h : (thetaAboveCell0000220121112312).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220121112312 h)
        (by
          have h : (thetaAboveCell0000220121112313).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220121112313 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childHL (childHH (childHL
        thetaAboveCell000022012111)))
        (by
          have h : (thetaAboveCell0000220121112320).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220121112320 h)
        (by
          have h : (thetaAboveCell0000220121112321).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220121112321 h)
        (by
          have h : (thetaAboveCell0000220121112322).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220121112322 h)
        (by
          have h : (thetaAboveCell0000220121112323).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220121112323 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childHH (childHH (childHL
        thetaAboveCell000022012111)))
        (by
          have h : (thetaAboveCell0000220121112330).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220121112330 h)
        (by
          have h : (thetaAboveCell0000220121112331).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220121112331 h)
        (by
          have h : (thetaAboveCell0000220121112332).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220121112332 h)
        (by
          have h : (thetaAboveCell0000220121112333).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220121112333 h))

theorem cover_subtree_c6507edf1fb6 :
    adaptiveCoverCheck 6 (childHL thetaAboveCell000022012111) = true := by
  exact adaptiveCoverCheck_succ_of_children 5 (childHL thetaAboveCell000022012111)
    cover_subtree_2c166d84fe59
    cover_subtree_d41cf2e18f87
    cover_subtree_1fd2ad12dba0
    cover_subtree_88e81007f06f

theorem cover_subtree_fa22cb64c6e6 :
    adaptiveCoverCheck 5 (childLL (childHH thetaAboveCell000022012111)) = true := by
  exact adaptiveCoverCheck_succ_of_children 4 (childLL (childHH thetaAboveCell000022012111))
    (by
      have h : ((childLL (childLL (childHH thetaAboveCell000022012111)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childLL (childHH
        thetaAboveCell000022012111))) h)
    (by
      have h : ((childLH (childLL (childHH thetaAboveCell000022012111)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childLL (childHH
        thetaAboveCell000022012111))) h)
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childHL (childLL (childHH
        thetaAboveCell000022012111)))
        (by
          have h : (thetaAboveCell0000220121113020).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220121113020 h)
        (by
          have h : (thetaAboveCell0000220121113021).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220121113021 h)
        (by
          have h : (thetaAboveCell0000220121113022).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220121113022 h)
        (by
          have h : (thetaAboveCell0000220121113023).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220121113023 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childHH (childLL (childHH
        thetaAboveCell000022012111)))
        (by
          have h : (thetaAboveCell0000220121113030).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220121113030 h)
        (by
          have h : (thetaAboveCell0000220121113031).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220121113031 h)
        (by
          have h : (thetaAboveCell0000220121113032).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220121113032 h)
        (by
          have h : (thetaAboveCell0000220121113033).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220121113033 h))

theorem cover_subtree_8b0952b6da88 :
    adaptiveCoverCheck 5 (childLH (childHH thetaAboveCell000022012111)) = true := by
  exact adaptiveCoverCheck_succ_of_children 4 (childLH (childHH thetaAboveCell000022012111))
    (by
      have h : ((childLL (childLH (childHH thetaAboveCell000022012111)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childLH (childHH
        thetaAboveCell000022012111))) h)
    (by
      have h : ((childLH (childLH (childHH thetaAboveCell000022012111)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childLH (childHH
        thetaAboveCell000022012111))) h)
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childHL (childLH (childHH
        thetaAboveCell000022012111)))
        (by
          have h : (thetaAboveCell0000220121113120).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220121113120 h)
        (by
          have h : (thetaAboveCell0000220121113121).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220121113121 h)
        (by
          have h : (thetaAboveCell0000220121113122).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220121113122 h)
        (by
          have h : (thetaAboveCell0000220121113123).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220121113123 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childHH (childLH (childHH
        thetaAboveCell000022012111)))
        (by
          have h : (thetaAboveCell0000220121113130).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220121113130 h)
        (by
          have h : (thetaAboveCell0000220121113131).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220121113131 h)
        (by
          have h : (thetaAboveCell0000220121113132).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220121113132 h)
        (by
          have h : (thetaAboveCell0000220121113133).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220121113133 h))

theorem cover_subtree_549042ebc77b :
    adaptiveCoverCheck 5 (childHL (childHH thetaAboveCell000022012111)) = true := by
  exact adaptiveCoverCheck_succ_of_children 4 (childHL (childHH thetaAboveCell000022012111))
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childLL (childHL (childHH
        thetaAboveCell000022012111)))
        (by
          have h : (thetaAboveCell0000220121113200).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220121113200 h)
        (by
          have h : (thetaAboveCell0000220121113201).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220121113201 h)
        (by
          have h : (thetaAboveCell0000220121113202).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220121113202 h)
        (by
          have h : (thetaAboveCell0000220121113203).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220121113203 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childLH (childHL (childHH
        thetaAboveCell000022012111)))
        (by
          have h : (thetaAboveCell0000220121113210).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220121113210 h)
        (by
          have h : (thetaAboveCell0000220121113211).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220121113211 h)
        (by
          have h : (thetaAboveCell0000220121113212).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220121113212 h)
        (by
          have h : (thetaAboveCell0000220121113213).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220121113213 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childHL (childHL (childHH
        thetaAboveCell000022012111)))
        (by
          have h : (thetaAboveCell0000220121113220).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220121113220 h)
        (by
          have h : (thetaAboveCell0000220121113221).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220121113221 h)
        (by
          have h : (thetaAboveCell0000220121113222).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220121113222 h)
        (by
          have h : (thetaAboveCell0000220121113223).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220121113223 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childHH (childHL (childHH
        thetaAboveCell000022012111)))
        (by
          have h : (thetaAboveCell0000220121113230).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220121113230 h)
        (by
          have h : (thetaAboveCell0000220121113231).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220121113231 h)
        (by
          have h : (thetaAboveCell0000220121113232).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220121113232 h)
        (by
          have h : (thetaAboveCell0000220121113233).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220121113233 h))

theorem cover_subtree_de6e3b296ec1 :
    adaptiveCoverCheck 5 (childHH (childHH thetaAboveCell000022012111)) = true := by
  exact adaptiveCoverCheck_succ_of_children 4 (childHH (childHH thetaAboveCell000022012111))
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childLL (childHH (childHH
        thetaAboveCell000022012111)))
        (by
          have h : (thetaAboveCell0000220121113300).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220121113300 h)
        (by
          have h : (thetaAboveCell0000220121113301).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220121113301 h)
        (by
          have h : (thetaAboveCell0000220121113302).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220121113302 h)
        (by
          have h : (thetaAboveCell0000220121113303).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220121113303 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childLH (childHH (childHH
        thetaAboveCell000022012111)))
        (by
          have h : (thetaAboveCell0000220121113310).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220121113310 h)
        (by
          have h : (thetaAboveCell0000220121113311).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220121113311 h)
        (by
          have h : (thetaAboveCell0000220121113312).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220121113312 h)
        (by
          have h : (thetaAboveCell0000220121113313).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220121113313 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childHL (childHH (childHH
        thetaAboveCell000022012111)))
        (by
          have h : (thetaAboveCell0000220121113320).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220121113320 h)
        (by
          have h : (thetaAboveCell0000220121113321).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220121113321 h)
        (by
          have h : (thetaAboveCell0000220121113322).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220121113322 h)
        (by
          have h : (thetaAboveCell0000220121113323).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220121113323 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childHH (childHH (childHH
        thetaAboveCell000022012111)))
        (by
          have h : (thetaAboveCell0000220121113330).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220121113330 h)
        (by
          have h : (thetaAboveCell0000220121113331).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220121113331 h)
        (by
          have h : (thetaAboveCell0000220121113332).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220121113332 h)
        (by
          have h : (thetaAboveCell0000220121113333).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220121113333 h))

theorem cover_subtree_0f2e720f6017 :
    adaptiveCoverCheck 6 (childHH thetaAboveCell000022012111) = true := by
  exact adaptiveCoverCheck_succ_of_children 5 (childHH thetaAboveCell000022012111)
    cover_subtree_fa22cb64c6e6
    cover_subtree_8b0952b6da88
    cover_subtree_549042ebc77b
    cover_subtree_de6e3b296ec1

theorem cover_subtree_35e94d0e7310 :
    adaptiveCoverCheck 7 thetaAboveCell000022012111 = true := by
  exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000022012111
    (by
      exact adaptiveCoverCheck_succ_of_children 5 (childLL thetaAboveCell000022012111)
        (by
          have h : ((childLL (childLL thetaAboveCell000022012111))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childLL
            thetaAboveCell000022012111)) h)
        (by
          have h : ((childLH (childLL thetaAboveCell000022012111))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childLL
            thetaAboveCell000022012111)) h)
        (by
          have h : ((childHL (childLL thetaAboveCell000022012111))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childLL
            thetaAboveCell000022012111)) h)
        (by
          have h : ((childHH (childLL thetaAboveCell000022012111))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childLL
            thetaAboveCell000022012111)) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 5 (childLH thetaAboveCell000022012111)
        (by
          have h : ((childLL (childLH thetaAboveCell000022012111))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childLH
            thetaAboveCell000022012111)) h)
        (by
          have h : ((childLH (childLH thetaAboveCell000022012111))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childLH
            thetaAboveCell000022012111)) h)
        (by
          have h : ((childHL (childLH thetaAboveCell000022012111))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childLH
            thetaAboveCell000022012111)) h)
        (by
          have h : ((childHH (childLH thetaAboveCell000022012111))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childLH
            thetaAboveCell000022012111)) h))
    cover_subtree_c6507edf1fb6
    cover_subtree_0f2e720f6017

theorem cover_subtree_65f4b19fe529 :
    adaptiveCoverCheck 6 (childLL thetaAboveCell000022012112) = true := by
  exact adaptiveCoverCheck_succ_of_children 5 (childLL thetaAboveCell000022012112)
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childLL (childLL thetaAboveCell000022012112))
        (by
          have h : ((childLL (childLL (childLL thetaAboveCell000022012112)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childLL (childLL
            thetaAboveCell000022012112))) h)
        (by
          have h : ((childLH (childLL (childLL thetaAboveCell000022012112)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childLL (childLL
            thetaAboveCell000022012112))) h)
        (by
          have h : ((childHL (childLL (childLL thetaAboveCell000022012112)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childLL (childLL
            thetaAboveCell000022012112))) h)
        (by
          have h : ((childHH (childLL (childLL thetaAboveCell000022012112)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childLL (childLL
            thetaAboveCell000022012112))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childLH (childLL thetaAboveCell000022012112))
        (by
          have h : ((childLL (childLH (childLL thetaAboveCell000022012112)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childLH (childLL
            thetaAboveCell000022012112))) h)
        (by
          have h : ((childLH (childLH (childLL thetaAboveCell000022012112)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childLH (childLL
            thetaAboveCell000022012112))) h)
        (by
          have h : ((childHL (childLH (childLL thetaAboveCell000022012112)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childLH (childLL
            thetaAboveCell000022012112))) h)
        (by
          have h : ((childHH (childLH (childLL thetaAboveCell000022012112)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childLH (childLL
            thetaAboveCell000022012112))) h))
    (by
      have h : ((childHL (childLL thetaAboveCell000022012112))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childLL thetaAboveCell000022012112)) h)
    (by
      have h : ((childHH (childLL thetaAboveCell000022012112))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childLL thetaAboveCell000022012112)) h)

theorem cover_subtree_334b61157880 :
    adaptiveCoverCheck 6 (childLH thetaAboveCell000022012112) = true := by
  exact adaptiveCoverCheck_succ_of_children 5 (childLH thetaAboveCell000022012112)
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childLL (childLH thetaAboveCell000022012112))
        (by
          have h : ((childLL (childLL (childLH thetaAboveCell000022012112)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childLL (childLH
            thetaAboveCell000022012112))) h)
        (by
          have h : ((childLH (childLL (childLH thetaAboveCell000022012112)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childLL (childLH
            thetaAboveCell000022012112))) h)
        (by
          have h : ((childHL (childLL (childLH thetaAboveCell000022012112)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childLL (childLH
            thetaAboveCell000022012112))) h)
        (by
          have h : ((childHH (childLL (childLH thetaAboveCell000022012112)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childLL (childLH
            thetaAboveCell000022012112))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childLH (childLH thetaAboveCell000022012112))
        (by
          have h : ((childLL (childLH (childLH thetaAboveCell000022012112)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childLH (childLH
            thetaAboveCell000022012112))) h)
        (by
          have h : ((childLH (childLH (childLH thetaAboveCell000022012112)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childLH (childLH
            thetaAboveCell000022012112))) h)
        (by
          have h : ((childHL (childLH (childLH thetaAboveCell000022012112)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childLH (childLH
            thetaAboveCell000022012112))) h)
        (by
          have h : ((childHH (childLH (childLH thetaAboveCell000022012112)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childLH (childLH
            thetaAboveCell000022012112))) h))
    (by
      have h : ((childHL (childLH thetaAboveCell000022012112))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childLH thetaAboveCell000022012112)) h)
    (by
      have h : ((childHH (childLH thetaAboveCell000022012112))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childLH thetaAboveCell000022012112)) h)

theorem cover_subtree_681fbeb68abf :
    adaptiveCoverCheck 7 thetaAboveCell000022012112 = true := by
  exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000022012112
    cover_subtree_65f4b19fe529
    cover_subtree_334b61157880
    (by
      have h : ((childHL thetaAboveCell000022012112)).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000022012112) h)
    (by
      have h : ((childHH thetaAboveCell000022012112)).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000022012112) h)

theorem cover_subtree_2f0ab83958c9 :
    adaptiveCoverCheck 6 (childLL thetaAboveCell000022012113) = true := by
  exact adaptiveCoverCheck_succ_of_children 5 (childLL thetaAboveCell000022012113)
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childLL (childLL thetaAboveCell000022012113))
        (by
          have h : ((childLL (childLL (childLL thetaAboveCell000022012113)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childLL (childLL
            thetaAboveCell000022012113))) h)
        (by
          have h : ((childLH (childLL (childLL thetaAboveCell000022012113)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childLL (childLL
            thetaAboveCell000022012113))) h)
        (by
          have h : ((childHL (childLL (childLL thetaAboveCell000022012113)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childLL (childLL
            thetaAboveCell000022012113))) h)
        (by
          have h : ((childHH (childLL (childLL thetaAboveCell000022012113)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childLL (childLL
            thetaAboveCell000022012113))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childLH (childLL thetaAboveCell000022012113))
        (by
          have h : ((childLL (childLH (childLL thetaAboveCell000022012113)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childLH (childLL
            thetaAboveCell000022012113))) h)
        (by
          have h : ((childLH (childLH (childLL thetaAboveCell000022012113)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childLH (childLL
            thetaAboveCell000022012113))) h)
        (by
          have h : ((childHL (childLH (childLL thetaAboveCell000022012113)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childLH (childLL
            thetaAboveCell000022012113))) h)
        (by
          have h : ((childHH (childLH (childLL thetaAboveCell000022012113)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childLH (childLL
            thetaAboveCell000022012113))) h))
    (by
      have h : ((childHL (childLL thetaAboveCell000022012113))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childLL thetaAboveCell000022012113)) h)
    (by
      have h : ((childHH (childLL thetaAboveCell000022012113))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childLL thetaAboveCell000022012113)) h)

theorem cover_subtree_4675766b5fc3 :
    adaptiveCoverCheck 6 (childLH thetaAboveCell000022012113) = true := by
  exact adaptiveCoverCheck_succ_of_children 5 (childLH thetaAboveCell000022012113)
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childLL (childLH thetaAboveCell000022012113))
        (by
          have h : ((childLL (childLL (childLH thetaAboveCell000022012113)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childLL (childLH
            thetaAboveCell000022012113))) h)
        (by
          have h : ((childLH (childLL (childLH thetaAboveCell000022012113)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childLL (childLH
            thetaAboveCell000022012113))) h)
        (by
          have h : ((childHL (childLL (childLH thetaAboveCell000022012113)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childLL (childLH
            thetaAboveCell000022012113))) h)
        (by
          have h : ((childHH (childLL (childLH thetaAboveCell000022012113)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childLL (childLH
            thetaAboveCell000022012113))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childLH (childLH thetaAboveCell000022012113))
        (by
          have h : ((childLL (childLH (childLH thetaAboveCell000022012113)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childLH (childLH
            thetaAboveCell000022012113))) h)
        (by
          have h : ((childLH (childLH (childLH thetaAboveCell000022012113)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childLH (childLH
            thetaAboveCell000022012113))) h)
        (by
          have h : ((childHL (childLH (childLH thetaAboveCell000022012113)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childLH (childLH
            thetaAboveCell000022012113))) h)
        (by
          have h : ((childHH (childLH (childLH thetaAboveCell000022012113)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childLH (childLH
            thetaAboveCell000022012113))) h))
    (by
      have h : ((childHL (childLH thetaAboveCell000022012113))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childLH thetaAboveCell000022012113)) h)
    (by
      have h : ((childHH (childLH thetaAboveCell000022012113))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childLH thetaAboveCell000022012113)) h)

theorem cover_subtree_9e9d455fd0db :
    adaptiveCoverCheck 7 thetaAboveCell000022012113 = true := by
  exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000022012113
    cover_subtree_2f0ab83958c9
    cover_subtree_4675766b5fc3
    (by
      have h : ((childHL thetaAboveCell000022012113)).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000022012113) h)
    (by
      have h : ((childHH thetaAboveCell000022012113)).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000022012113) h)

theorem cover_subtree_ba2ddc618064 :
    adaptiveCoverCheck 8 (childLH (childLH (childHL thetaAboveCell00002201))) = true := by
  exact adaptiveCoverCheck_succ_of_children 7 (childLH (childLH (childHL thetaAboveCell00002201)))
    cover_subtree_4255f05ab59f
    cover_subtree_35e94d0e7310
    cover_subtree_681fbeb68abf
    cover_subtree_9e9d455fd0db

theorem e24KC2ThetaAboveLeaf0000220121 :
    adaptiveCoverCheck 9 (childLH (childHL thetaAboveCell00002201)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLH (childHL thetaAboveCell00002201))
    cover_subtree_c6c6b7e63010
    cover_subtree_ba2ddc618064
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHL (childLH (childHL
        thetaAboveCell00002201)))
        (by
          have h : (thetaAboveCell000022012120).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000022012120 h)
        (by
          have h : (thetaAboveCell000022012121).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000022012121 h)
        (by
          have h : (thetaAboveCell000022012122).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000022012122 h)
        (by
          have h : (thetaAboveCell000022012123).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000022012123 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHH (childLH (childHL
        thetaAboveCell00002201)))
        (by
          have h : (thetaAboveCell000022012130).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000022012130 h)
        (by
          have h : (thetaAboveCell000022012131).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000022012131 h)
        (by
          have h : (thetaAboveCell000022012132).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000022012132 h)
        (by
          have h : (thetaAboveCell000022012133).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000022012133 h))
theorem e24KC2ThetaAboveLeaf0000220122 :
    adaptiveCoverCheck 9 (childHL (childHL thetaAboveCell00002201)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHL (childHL thetaAboveCell00002201))
    (by
      have h : ((childLL (childHL (childHL thetaAboveCell00002201)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHL (childHL
        thetaAboveCell00002201))) h)
    (by
      have h : ((childLH (childHL (childHL thetaAboveCell00002201)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHL (childHL
        thetaAboveCell00002201))) h)
    (by
      have h : ((childHL (childHL (childHL thetaAboveCell00002201)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHL (childHL
        thetaAboveCell00002201))) h)
    (by
      have h : ((childHH (childHL (childHL thetaAboveCell00002201)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHL (childHL
        thetaAboveCell00002201))) h)
theorem e24KC2ThetaAboveLeaf0000220123 :
    adaptiveCoverCheck 9 (childHH (childHL thetaAboveCell00002201)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHH (childHL thetaAboveCell00002201))
    (by
      have h : ((childLL (childHH (childHL thetaAboveCell00002201)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHH (childHL
        thetaAboveCell00002201))) h)
    (by
      have h : ((childLH (childHH (childHL thetaAboveCell00002201)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHH (childHL
        thetaAboveCell00002201))) h)
    (by
      have h : ((childHL (childHH (childHL thetaAboveCell00002201)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHH (childHL
        thetaAboveCell00002201))) h)
    (by
      have h : ((childHH (childHH (childHL thetaAboveCell00002201)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHH (childHL
        thetaAboveCell00002201))) h)
theorem cover_subtree_cb54dc4a2aa0 :
    adaptiveCoverCheck 5 (childLL (childHL thetaAboveCell000022013000)) = true := by
  exact adaptiveCoverCheck_succ_of_children 4 (childLL (childHL thetaAboveCell000022013000))
    (by
      have h : ((childLL (childLL (childHL thetaAboveCell000022013000)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childLL (childHL
        thetaAboveCell000022013000))) h)
    (by
      have h : ((childLH (childLL (childHL thetaAboveCell000022013000)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childLL (childHL
        thetaAboveCell000022013000))) h)
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childHL (childLL (childHL
        thetaAboveCell000022013000)))
        (by
          have h : (thetaAboveCell0000220130002020).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220130002020 h)
        (by
          have h : (thetaAboveCell0000220130002021).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220130002021 h)
        (by
          have h : (thetaAboveCell0000220130002022).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220130002022 h)
        (by
          have h : (thetaAboveCell0000220130002023).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220130002023 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childHH (childLL (childHL
        thetaAboveCell000022013000)))
        (by
          have h : (thetaAboveCell0000220130002030).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220130002030 h)
        (by
          have h : (thetaAboveCell0000220130002031).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220130002031 h)
        (by
          have h : (thetaAboveCell0000220130002032).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220130002032 h)
        (by
          have h : (thetaAboveCell0000220130002033).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220130002033 h))

theorem cover_subtree_348d77482bf3 :
    adaptiveCoverCheck 5 (childLH (childHL thetaAboveCell000022013000)) = true := by
  exact adaptiveCoverCheck_succ_of_children 4 (childLH (childHL thetaAboveCell000022013000))
    (by
      have h : ((childLL (childLH (childHL thetaAboveCell000022013000)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childLH (childHL
        thetaAboveCell000022013000))) h)
    (by
      have h : ((childLH (childLH (childHL thetaAboveCell000022013000)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childLH (childHL
        thetaAboveCell000022013000))) h)
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childHL (childLH (childHL
        thetaAboveCell000022013000)))
        (by
          have h : (thetaAboveCell0000220130002120).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220130002120 h)
        (by
          have h : (thetaAboveCell0000220130002121).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220130002121 h)
        (by
          have h : (thetaAboveCell0000220130002122).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220130002122 h)
        (by
          have h : (thetaAboveCell0000220130002123).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220130002123 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childHH (childLH (childHL
        thetaAboveCell000022013000)))
        (by
          have h : (thetaAboveCell0000220130002130).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220130002130 h)
        (by
          have h : (thetaAboveCell0000220130002131).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220130002131 h)
        (by
          have h : (thetaAboveCell0000220130002132).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220130002132 h)
        (by
          have h : (thetaAboveCell0000220130002133).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220130002133 h))

theorem cover_subtree_cc712ad349df :
    adaptiveCoverCheck 5 (childHL (childHL thetaAboveCell000022013000)) = true := by
  exact adaptiveCoverCheck_succ_of_children 4 (childHL (childHL thetaAboveCell000022013000))
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childLL (childHL (childHL
        thetaAboveCell000022013000)))
        (by
          have h : (thetaAboveCell0000220130002200).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220130002200 h)
        (by
          have h : (thetaAboveCell0000220130002201).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220130002201 h)
        (by
          have h : (thetaAboveCell0000220130002202).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220130002202 h)
        (by
          have h : (thetaAboveCell0000220130002203).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220130002203 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childLH (childHL (childHL
        thetaAboveCell000022013000)))
        (by
          have h : (thetaAboveCell0000220130002210).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220130002210 h)
        (by
          have h : (thetaAboveCell0000220130002211).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220130002211 h)
        (by
          have h : (thetaAboveCell0000220130002212).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220130002212 h)
        (by
          have h : (thetaAboveCell0000220130002213).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220130002213 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childHL (childHL (childHL
        thetaAboveCell000022013000)))
        (by
          have h : (thetaAboveCell0000220130002220).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220130002220 h)
        (by
          have h : (thetaAboveCell0000220130002221).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220130002221 h)
        (by
          have h : (thetaAboveCell0000220130002222).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220130002222 h)
        (by
          have h : (thetaAboveCell0000220130002223).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220130002223 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childHH (childHL (childHL
        thetaAboveCell000022013000)))
        (by
          have h : (thetaAboveCell0000220130002230).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220130002230 h)
        (by
          have h : (thetaAboveCell0000220130002231).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220130002231 h)
        (by
          have h : (thetaAboveCell0000220130002232).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220130002232 h)
        (by
          have h : (thetaAboveCell0000220130002233).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220130002233 h))

theorem cover_subtree_791e2ddd0c41 :
    adaptiveCoverCheck 5 (childHH (childHL thetaAboveCell000022013000)) = true := by
  exact adaptiveCoverCheck_succ_of_children 4 (childHH (childHL thetaAboveCell000022013000))
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childLL (childHH (childHL
        thetaAboveCell000022013000)))
        (by
          have h : (thetaAboveCell0000220130002300).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220130002300 h)
        (by
          have h : (thetaAboveCell0000220130002301).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220130002301 h)
        (by
          have h : (thetaAboveCell0000220130002302).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220130002302 h)
        (by
          have h : (thetaAboveCell0000220130002303).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220130002303 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childLH (childHH (childHL
        thetaAboveCell000022013000)))
        (by
          have h : (thetaAboveCell0000220130002310).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220130002310 h)
        (by
          have h : (thetaAboveCell0000220130002311).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220130002311 h)
        (by
          have h : (thetaAboveCell0000220130002312).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220130002312 h)
        (by
          have h : (thetaAboveCell0000220130002313).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220130002313 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childHL (childHH (childHL
        thetaAboveCell000022013000)))
        (by
          have h : (thetaAboveCell0000220130002320).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220130002320 h)
        (by
          have h : (thetaAboveCell0000220130002321).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220130002321 h)
        (by
          have h : (thetaAboveCell0000220130002322).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220130002322 h)
        (by
          have h : (thetaAboveCell0000220130002323).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220130002323 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childHH (childHH (childHL
        thetaAboveCell000022013000)))
        (by
          have h : (thetaAboveCell0000220130002330).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220130002330 h)
        (by
          have h : (thetaAboveCell0000220130002331).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220130002331 h)
        (by
          have h : (thetaAboveCell0000220130002332).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220130002332 h)
        (by
          have h : (thetaAboveCell0000220130002333).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220130002333 h))

theorem cover_subtree_3a2f1fd548a5 :
    adaptiveCoverCheck 6 (childHL thetaAboveCell000022013000) = true := by
  exact adaptiveCoverCheck_succ_of_children 5 (childHL thetaAboveCell000022013000)
    cover_subtree_cb54dc4a2aa0
    cover_subtree_348d77482bf3
    cover_subtree_cc712ad349df
    cover_subtree_791e2ddd0c41

theorem cover_subtree_bd2306545933 :
    adaptiveCoverCheck 5 (childLL (childHH thetaAboveCell000022013000)) = true := by
  exact adaptiveCoverCheck_succ_of_children 4 (childLL (childHH thetaAboveCell000022013000))
    (by
      have h : ((childLL (childLL (childHH thetaAboveCell000022013000)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childLL (childHH
        thetaAboveCell000022013000))) h)
    (by
      have h : ((childLH (childLL (childHH thetaAboveCell000022013000)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childLL (childHH
        thetaAboveCell000022013000))) h)
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childHL (childLL (childHH
        thetaAboveCell000022013000)))
        (by
          have h : (thetaAboveCell0000220130003020).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220130003020 h)
        (by
          have h : (thetaAboveCell0000220130003021).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220130003021 h)
        (by
          have h : (thetaAboveCell0000220130003022).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220130003022 h)
        (by
          have h : (thetaAboveCell0000220130003023).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220130003023 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childHH (childLL (childHH
        thetaAboveCell000022013000)))
        (by
          have h : (thetaAboveCell0000220130003030).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220130003030 h)
        (by
          have h : (thetaAboveCell0000220130003031).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220130003031 h)
        (by
          have h : (thetaAboveCell0000220130003032).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220130003032 h)
        (by
          have h : (thetaAboveCell0000220130003033).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220130003033 h))

theorem cover_subtree_65fba8c7a135 :
    adaptiveCoverCheck 5 (childLH (childHH thetaAboveCell000022013000)) = true := by
  exact adaptiveCoverCheck_succ_of_children 4 (childLH (childHH thetaAboveCell000022013000))
    (by
      have h : ((childLL (childLH (childHH thetaAboveCell000022013000)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childLH (childHH
        thetaAboveCell000022013000))) h)
    (by
      have h : ((childLH (childLH (childHH thetaAboveCell000022013000)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childLH (childHH
        thetaAboveCell000022013000))) h)
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childHL (childLH (childHH
        thetaAboveCell000022013000)))
        (by
          have h : (thetaAboveCell0000220130003120).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220130003120 h)
        (by
          have h : (thetaAboveCell0000220130003121).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220130003121 h)
        (by
          have h : (thetaAboveCell0000220130003122).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220130003122 h)
        (by
          have h : (thetaAboveCell0000220130003123).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220130003123 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childHH (childLH (childHH
        thetaAboveCell000022013000)))
        (by
          have h : (thetaAboveCell0000220130003130).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220130003130 h)
        (by
          have h : (thetaAboveCell0000220130003131).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220130003131 h)
        (by
          have h : (thetaAboveCell0000220130003132).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220130003132 h)
        (by
          have h : (thetaAboveCell0000220130003133).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220130003133 h))

theorem cover_subtree_f63aaf9046af :
    adaptiveCoverCheck 5 (childHL (childHH thetaAboveCell000022013000)) = true := by
  exact adaptiveCoverCheck_succ_of_children 4 (childHL (childHH thetaAboveCell000022013000))
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childLL (childHL (childHH
        thetaAboveCell000022013000)))
        (by
          have h : (thetaAboveCell0000220130003200).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220130003200 h)
        (by
          have h : (thetaAboveCell0000220130003201).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220130003201 h)
        (by
          have h : (thetaAboveCell0000220130003202).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220130003202 h)
        (by
          have h : (thetaAboveCell0000220130003203).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220130003203 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childLH (childHL (childHH
        thetaAboveCell000022013000)))
        (by
          have h : (thetaAboveCell0000220130003210).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220130003210 h)
        (by
          have h : (thetaAboveCell0000220130003211).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220130003211 h)
        (by
          have h : (thetaAboveCell0000220130003212).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220130003212 h)
        (by
          have h : (thetaAboveCell0000220130003213).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220130003213 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childHL (childHL (childHH
        thetaAboveCell000022013000)))
        (by
          have h : (thetaAboveCell0000220130003220).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220130003220 h)
        (by
          have h : (thetaAboveCell0000220130003221).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220130003221 h)
        (by
          have h : (thetaAboveCell0000220130003222).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220130003222 h)
        (by
          have h : (thetaAboveCell0000220130003223).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220130003223 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childHH (childHL (childHH
        thetaAboveCell000022013000)))
        (by
          have h : (thetaAboveCell0000220130003230).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220130003230 h)
        (by
          have h : (thetaAboveCell0000220130003231).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220130003231 h)
        (by
          have h : (thetaAboveCell0000220130003232).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220130003232 h)
        (by
          have h : (thetaAboveCell0000220130003233).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220130003233 h))

theorem cover_subtree_dff62e50df3b :
    adaptiveCoverCheck 5 (childHH (childHH thetaAboveCell000022013000)) = true := by
  exact adaptiveCoverCheck_succ_of_children 4 (childHH (childHH thetaAboveCell000022013000))
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childLL (childHH (childHH
        thetaAboveCell000022013000)))
        (by
          have h : (thetaAboveCell0000220130003300).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220130003300 h)
        (by
          have h : (thetaAboveCell0000220130003301).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220130003301 h)
        (by
          have h : (thetaAboveCell0000220130003302).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220130003302 h)
        (by
          have h : (thetaAboveCell0000220130003303).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220130003303 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childLH (childHH (childHH
        thetaAboveCell000022013000)))
        (by
          have h : (thetaAboveCell0000220130003310).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220130003310 h)
        (by
          have h : (thetaAboveCell0000220130003311).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220130003311 h)
        (by
          have h : (thetaAboveCell0000220130003312).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220130003312 h)
        (by
          have h : (thetaAboveCell0000220130003313).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220130003313 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childHL (childHH (childHH
        thetaAboveCell000022013000)))
        (by
          have h : (thetaAboveCell0000220130003320).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220130003320 h)
        (by
          have h : (thetaAboveCell0000220130003321).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220130003321 h)
        (by
          have h : (thetaAboveCell0000220130003322).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220130003322 h)
        (by
          have h : (thetaAboveCell0000220130003323).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220130003323 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childHH (childHH (childHH
        thetaAboveCell000022013000)))
        (by
          have h : (thetaAboveCell0000220130003330).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220130003330 h)
        (by
          have h : (thetaAboveCell0000220130003331).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220130003331 h)
        (by
          have h : (thetaAboveCell0000220130003332).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220130003332 h)
        (by
          have h : (thetaAboveCell0000220130003333).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220130003333 h))

theorem cover_subtree_c954080a5fc2 :
    adaptiveCoverCheck 6 (childHH thetaAboveCell000022013000) = true := by
  exact adaptiveCoverCheck_succ_of_children 5 (childHH thetaAboveCell000022013000)
    cover_subtree_bd2306545933
    cover_subtree_65fba8c7a135
    cover_subtree_f63aaf9046af
    cover_subtree_dff62e50df3b

theorem cover_subtree_701e722ef144 :
    adaptiveCoverCheck 7 thetaAboveCell000022013000 = true := by
  exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000022013000
    (by
      exact adaptiveCoverCheck_succ_of_children 5 (childLL thetaAboveCell000022013000)
        (by
          have h : ((childLL (childLL thetaAboveCell000022013000))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childLL
            thetaAboveCell000022013000)) h)
        (by
          have h : ((childLH (childLL thetaAboveCell000022013000))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childLL
            thetaAboveCell000022013000)) h)
        (by
          have h : ((childHL (childLL thetaAboveCell000022013000))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childLL
            thetaAboveCell000022013000)) h)
        (by
          have h : ((childHH (childLL thetaAboveCell000022013000))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childLL
            thetaAboveCell000022013000)) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 5 (childLH thetaAboveCell000022013000)
        (by
          have h : ((childLL (childLH thetaAboveCell000022013000))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childLH
            thetaAboveCell000022013000)) h)
        (by
          have h : ((childLH (childLH thetaAboveCell000022013000))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childLH
            thetaAboveCell000022013000)) h)
        (by
          have h : ((childHL (childLH thetaAboveCell000022013000))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childLH
            thetaAboveCell000022013000)) h)
        (by
          have h : ((childHH (childLH thetaAboveCell000022013000))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childLH
            thetaAboveCell000022013000)) h))
    cover_subtree_3a2f1fd548a5
    cover_subtree_c954080a5fc2

theorem cover_subtree_1812a1843696 :
    adaptiveCoverCheck 5 (childLL (childHL thetaAboveCell000022013001)) = true := by
  exact adaptiveCoverCheck_succ_of_children 4 (childLL (childHL thetaAboveCell000022013001))
    (by
      have h : ((childLL (childLL (childHL thetaAboveCell000022013001)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childLL (childHL
        thetaAboveCell000022013001))) h)
    (by
      have h : ((childLH (childLL (childHL thetaAboveCell000022013001)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childLL (childHL
        thetaAboveCell000022013001))) h)
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childHL (childLL (childHL
        thetaAboveCell000022013001)))
        (by
          have h : (thetaAboveCell0000220130012020).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220130012020 h)
        (by
          have h : (thetaAboveCell0000220130012021).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220130012021 h)
        (by
          have h : (thetaAboveCell0000220130012022).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220130012022 h)
        (by
          have h : (thetaAboveCell0000220130012023).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220130012023 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childHH (childLL (childHL
        thetaAboveCell000022013001)))
        (by
          have h : (thetaAboveCell0000220130012030).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220130012030 h)
        (by
          have h : (thetaAboveCell0000220130012031).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220130012031 h)
        (by
          have h : (thetaAboveCell0000220130012032).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220130012032 h)
        (by
          have h : (thetaAboveCell0000220130012033).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220130012033 h))

theorem cover_subtree_422793f2f2c6 :
    adaptiveCoverCheck 5 (childLH (childHL thetaAboveCell000022013001)) = true := by
  exact adaptiveCoverCheck_succ_of_children 4 (childLH (childHL thetaAboveCell000022013001))
    (by
      have h : ((childLL (childLH (childHL thetaAboveCell000022013001)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childLH (childHL
        thetaAboveCell000022013001))) h)
    (by
      have h : ((childLH (childLH (childHL thetaAboveCell000022013001)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childLH (childHL
        thetaAboveCell000022013001))) h)
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childHL (childLH (childHL
        thetaAboveCell000022013001)))
        (by
          have h : (thetaAboveCell0000220130012120).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220130012120 h)
        (by
          have h : (thetaAboveCell0000220130012121).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220130012121 h)
        (by
          have h : (thetaAboveCell0000220130012122).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220130012122 h)
        (by
          have h : (thetaAboveCell0000220130012123).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220130012123 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childHH (childLH (childHL
        thetaAboveCell000022013001)))
        (by
          have h : (thetaAboveCell0000220130012130).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220130012130 h)
        (by
          have h : (thetaAboveCell0000220130012131).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220130012131 h)
        (by
          have h : (thetaAboveCell0000220130012132).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220130012132 h)
        (by
          have h : (thetaAboveCell0000220130012133).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220130012133 h))

theorem cover_subtree_386e2b83e45a :
    adaptiveCoverCheck 5 (childHL (childHL thetaAboveCell000022013001)) = true := by
  exact adaptiveCoverCheck_succ_of_children 4 (childHL (childHL thetaAboveCell000022013001))
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childLL (childHL (childHL
        thetaAboveCell000022013001)))
        (by
          have h : (thetaAboveCell0000220130012200).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220130012200 h)
        (by
          have h : (thetaAboveCell0000220130012201).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220130012201 h)
        (by
          have h : (thetaAboveCell0000220130012202).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220130012202 h)
        (by
          have h : (thetaAboveCell0000220130012203).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220130012203 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childLH (childHL (childHL
        thetaAboveCell000022013001)))
        (by
          have h : (thetaAboveCell0000220130012210).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220130012210 h)
        (by
          have h : (thetaAboveCell0000220130012211).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220130012211 h)
        (by
          have h : (thetaAboveCell0000220130012212).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220130012212 h)
        (by
          have h : (thetaAboveCell0000220130012213).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220130012213 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childHL (childHL (childHL
        thetaAboveCell000022013001)))
        (by
          have h : (thetaAboveCell0000220130012220).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220130012220 h)
        (by
          have h : (thetaAboveCell0000220130012221).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220130012221 h)
        (by
          have h : (thetaAboveCell0000220130012222).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220130012222 h)
        (by
          have h : (thetaAboveCell0000220130012223).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220130012223 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childHH (childHL (childHL
        thetaAboveCell000022013001)))
        (by
          have h : (thetaAboveCell0000220130012230).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220130012230 h)
        (by
          have h : (thetaAboveCell0000220130012231).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220130012231 h)
        (by
          have h : (thetaAboveCell0000220130012232).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220130012232 h)
        (by
          have h : (thetaAboveCell0000220130012233).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220130012233 h))

theorem cover_subtree_37513ddf0672 :
    adaptiveCoverCheck 5 (childHH (childHL thetaAboveCell000022013001)) = true := by
  exact adaptiveCoverCheck_succ_of_children 4 (childHH (childHL thetaAboveCell000022013001))
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childLL (childHH (childHL
        thetaAboveCell000022013001)))
        (by
          have h : (thetaAboveCell0000220130012300).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220130012300 h)
        (by
          have h : (thetaAboveCell0000220130012301).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220130012301 h)
        (by
          have h : (thetaAboveCell0000220130012302).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220130012302 h)
        (by
          have h : (thetaAboveCell0000220130012303).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220130012303 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childLH (childHH (childHL
        thetaAboveCell000022013001)))
        (by
          have h : (thetaAboveCell0000220130012310).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220130012310 h)
        (by
          have h : (thetaAboveCell0000220130012311).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220130012311 h)
        (by
          have h : (thetaAboveCell0000220130012312).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220130012312 h)
        (by
          have h : (thetaAboveCell0000220130012313).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220130012313 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childHL (childHH (childHL
        thetaAboveCell000022013001)))
        (by
          have h : (thetaAboveCell0000220130012320).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220130012320 h)
        (by
          have h : (thetaAboveCell0000220130012321).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220130012321 h)
        (by
          have h : (thetaAboveCell0000220130012322).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220130012322 h)
        (by
          have h : (thetaAboveCell0000220130012323).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220130012323 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childHH (childHH (childHL
        thetaAboveCell000022013001)))
        (by
          have h : (thetaAboveCell0000220130012330).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220130012330 h)
        (by
          have h : (thetaAboveCell0000220130012331).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220130012331 h)
        (by
          have h : (thetaAboveCell0000220130012332).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220130012332 h)
        (by
          have h : (thetaAboveCell0000220130012333).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220130012333 h))

theorem cover_subtree_6d7b5fde1ce9 :
    adaptiveCoverCheck 6 (childHL thetaAboveCell000022013001) = true := by
  exact adaptiveCoverCheck_succ_of_children 5 (childHL thetaAboveCell000022013001)
    cover_subtree_1812a1843696
    cover_subtree_422793f2f2c6
    cover_subtree_386e2b83e45a
    cover_subtree_37513ddf0672

theorem cover_subtree_dc89c8b48c1d :
    adaptiveCoverCheck 5 (childLL (childHH thetaAboveCell000022013001)) = true := by
  exact adaptiveCoverCheck_succ_of_children 4 (childLL (childHH thetaAboveCell000022013001))
    (by
      have h : ((childLL (childLL (childHH thetaAboveCell000022013001)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childLL (childHH
        thetaAboveCell000022013001))) h)
    (by
      have h : ((childLH (childLL (childHH thetaAboveCell000022013001)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childLL (childHH
        thetaAboveCell000022013001))) h)
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childHL (childLL (childHH
        thetaAboveCell000022013001)))
        (by
          have h : (thetaAboveCell0000220130013020).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220130013020 h)
        (by
          have h : (thetaAboveCell0000220130013021).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220130013021 h)
        (by
          have h : (thetaAboveCell0000220130013022).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220130013022 h)
        (by
          have h : (thetaAboveCell0000220130013023).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220130013023 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childHH (childLL (childHH
        thetaAboveCell000022013001)))
        (by
          have h : (thetaAboveCell0000220130013030).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220130013030 h)
        (by
          have h : (thetaAboveCell0000220130013031).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220130013031 h)
        (by
          have h : (thetaAboveCell0000220130013032).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220130013032 h)
        (by
          have h : (thetaAboveCell0000220130013033).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220130013033 h))

theorem cover_subtree_b7e0401eaa5c :
    adaptiveCoverCheck 5 (childLH (childHH thetaAboveCell000022013001)) = true := by
  exact adaptiveCoverCheck_succ_of_children 4 (childLH (childHH thetaAboveCell000022013001))
    (by
      have h : ((childLL (childLH (childHH thetaAboveCell000022013001)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childLH (childHH
        thetaAboveCell000022013001))) h)
    (by
      have h : ((childLH (childLH (childHH thetaAboveCell000022013001)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childLH (childHH
        thetaAboveCell000022013001))) h)
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childHL (childLH (childHH
        thetaAboveCell000022013001)))
        (by
          have h : (thetaAboveCell0000220130013120).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220130013120 h)
        (by
          have h : (thetaAboveCell0000220130013121).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220130013121 h)
        (by
          have h : (thetaAboveCell0000220130013122).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220130013122 h)
        (by
          have h : (thetaAboveCell0000220130013123).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220130013123 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childHH (childLH (childHH
        thetaAboveCell000022013001)))
        (by
          have h : (thetaAboveCell0000220130013130).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220130013130 h)
        (by
          have h : (thetaAboveCell0000220130013131).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220130013131 h)
        (by
          have h : (thetaAboveCell0000220130013132).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220130013132 h)
        (by
          have h : (thetaAboveCell0000220130013133).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220130013133 h))

theorem cover_subtree_3178ee01a645 :
    adaptiveCoverCheck 5 (childHL (childHH thetaAboveCell000022013001)) = true := by
  exact adaptiveCoverCheck_succ_of_children 4 (childHL (childHH thetaAboveCell000022013001))
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childLL (childHL (childHH
        thetaAboveCell000022013001)))
        (by
          have h : (thetaAboveCell0000220130013200).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220130013200 h)
        (by
          have h : (thetaAboveCell0000220130013201).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220130013201 h)
        (by
          have h : (thetaAboveCell0000220130013202).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220130013202 h)
        (by
          have h : (thetaAboveCell0000220130013203).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220130013203 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childLH (childHL (childHH
        thetaAboveCell000022013001)))
        (by
          have h : (thetaAboveCell0000220130013210).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220130013210 h)
        (by
          have h : (thetaAboveCell0000220130013211).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220130013211 h)
        (by
          have h : (thetaAboveCell0000220130013212).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220130013212 h)
        (by
          have h : (thetaAboveCell0000220130013213).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220130013213 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childHL (childHL (childHH
        thetaAboveCell000022013001)))
        (by
          have h : (thetaAboveCell0000220130013220).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220130013220 h)
        (by
          have h : (thetaAboveCell0000220130013221).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220130013221 h)
        (by
          have h : (thetaAboveCell0000220130013222).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220130013222 h)
        (by
          have h : (thetaAboveCell0000220130013223).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220130013223 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childHH (childHL (childHH
        thetaAboveCell000022013001)))
        (by
          have h : (thetaAboveCell0000220130013230).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220130013230 h)
        (by
          have h : (thetaAboveCell0000220130013231).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220130013231 h)
        (by
          have h : (thetaAboveCell0000220130013232).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220130013232 h)
        (by
          have h : (thetaAboveCell0000220130013233).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220130013233 h))

theorem cover_subtree_2842986097c5 :
    adaptiveCoverCheck 5 (childHH (childHH thetaAboveCell000022013001)) = true := by
  exact adaptiveCoverCheck_succ_of_children 4 (childHH (childHH thetaAboveCell000022013001))
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childLL (childHH (childHH
        thetaAboveCell000022013001)))
        (by
          have h : (thetaAboveCell0000220130013300).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220130013300 h)
        (by
          have h : (thetaAboveCell0000220130013301).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220130013301 h)
        (by
          have h : (thetaAboveCell0000220130013302).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220130013302 h)
        (by
          have h : (thetaAboveCell0000220130013303).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220130013303 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childLH (childHH (childHH
        thetaAboveCell000022013001)))
        (by
          have h : (thetaAboveCell0000220130013310).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220130013310 h)
        (by
          have h : (thetaAboveCell0000220130013311).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220130013311 h)
        (by
          have h : (thetaAboveCell0000220130013312).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220130013312 h)
        (by
          have h : (thetaAboveCell0000220130013313).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220130013313 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childHL (childHH (childHH
        thetaAboveCell000022013001)))
        (by
          have h : (thetaAboveCell0000220130013320).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220130013320 h)
        (by
          have h : (thetaAboveCell0000220130013321).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220130013321 h)
        (by
          have h : (thetaAboveCell0000220130013322).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220130013322 h)
        (by
          have h : (thetaAboveCell0000220130013323).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220130013323 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childHH (childHH (childHH
        thetaAboveCell000022013001)))
        (by
          have h : (thetaAboveCell0000220130013330).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220130013330 h)
        (by
          have h : (thetaAboveCell0000220130013331).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220130013331 h)
        (by
          have h : (thetaAboveCell0000220130013332).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220130013332 h)
        (by
          have h : (thetaAboveCell0000220130013333).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220130013333 h))

theorem cover_subtree_0385d11aabba :
    adaptiveCoverCheck 6 (childHH thetaAboveCell000022013001) = true := by
  exact adaptiveCoverCheck_succ_of_children 5 (childHH thetaAboveCell000022013001)
    cover_subtree_dc89c8b48c1d
    cover_subtree_b7e0401eaa5c
    cover_subtree_3178ee01a645
    cover_subtree_2842986097c5

theorem cover_subtree_f1411005533f :
    adaptiveCoverCheck 7 thetaAboveCell000022013001 = true := by
  exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000022013001
    (by
      exact adaptiveCoverCheck_succ_of_children 5 (childLL thetaAboveCell000022013001)
        (by
          have h : ((childLL (childLL thetaAboveCell000022013001))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childLL
            thetaAboveCell000022013001)) h)
        (by
          have h : ((childLH (childLL thetaAboveCell000022013001))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childLL
            thetaAboveCell000022013001)) h)
        (by
          have h : ((childHL (childLL thetaAboveCell000022013001))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childLL
            thetaAboveCell000022013001)) h)
        (by
          have h : ((childHH (childLL thetaAboveCell000022013001))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childLL
            thetaAboveCell000022013001)) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 5 (childLH thetaAboveCell000022013001)
        (by
          have h : ((childLL (childLH thetaAboveCell000022013001))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childLH
            thetaAboveCell000022013001)) h)
        (by
          have h : ((childLH (childLH thetaAboveCell000022013001))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childLH
            thetaAboveCell000022013001)) h)
        (by
          have h : ((childHL (childLH thetaAboveCell000022013001))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childLH
            thetaAboveCell000022013001)) h)
        (by
          have h : ((childHH (childLH thetaAboveCell000022013001))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childLH
            thetaAboveCell000022013001)) h))
    cover_subtree_6d7b5fde1ce9
    cover_subtree_0385d11aabba

theorem cover_subtree_1032efc16567 :
    adaptiveCoverCheck 6 (childLL thetaAboveCell000022013002) = true := by
  exact adaptiveCoverCheck_succ_of_children 5 (childLL thetaAboveCell000022013002)
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childLL (childLL thetaAboveCell000022013002))
        (by
          have h : ((childLL (childLL (childLL thetaAboveCell000022013002)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childLL (childLL
            thetaAboveCell000022013002))) h)
        (by
          have h : ((childLH (childLL (childLL thetaAboveCell000022013002)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childLL (childLL
            thetaAboveCell000022013002))) h)
        (by
          have h : ((childHL (childLL (childLL thetaAboveCell000022013002)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childLL (childLL
            thetaAboveCell000022013002))) h)
        (by
          have h : ((childHH (childLL (childLL thetaAboveCell000022013002)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childLL (childLL
            thetaAboveCell000022013002))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childLH (childLL thetaAboveCell000022013002))
        (by
          have h : ((childLL (childLH (childLL thetaAboveCell000022013002)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childLH (childLL
            thetaAboveCell000022013002))) h)
        (by
          have h : ((childLH (childLH (childLL thetaAboveCell000022013002)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childLH (childLL
            thetaAboveCell000022013002))) h)
        (by
          have h : ((childHL (childLH (childLL thetaAboveCell000022013002)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childLH (childLL
            thetaAboveCell000022013002))) h)
        (by
          have h : ((childHH (childLH (childLL thetaAboveCell000022013002)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childLH (childLL
            thetaAboveCell000022013002))) h))
    (by
      have h : ((childHL (childLL thetaAboveCell000022013002))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childLL thetaAboveCell000022013002)) h)
    (by
      have h : ((childHH (childLL thetaAboveCell000022013002))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childLL thetaAboveCell000022013002)) h)

theorem cover_subtree_9fa6122a45d4 :
    adaptiveCoverCheck 6 (childLH thetaAboveCell000022013002) = true := by
  exact adaptiveCoverCheck_succ_of_children 5 (childLH thetaAboveCell000022013002)
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childLL (childLH thetaAboveCell000022013002))
        (by
          have h : ((childLL (childLL (childLH thetaAboveCell000022013002)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childLL (childLH
            thetaAboveCell000022013002))) h)
        (by
          have h : ((childLH (childLL (childLH thetaAboveCell000022013002)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childLL (childLH
            thetaAboveCell000022013002))) h)
        (by
          have h : ((childHL (childLL (childLH thetaAboveCell000022013002)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childLL (childLH
            thetaAboveCell000022013002))) h)
        (by
          have h : ((childHH (childLL (childLH thetaAboveCell000022013002)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childLL (childLH
            thetaAboveCell000022013002))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childLH (childLH thetaAboveCell000022013002))
        (by
          have h : ((childLL (childLH (childLH thetaAboveCell000022013002)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childLH (childLH
            thetaAboveCell000022013002))) h)
        (by
          have h : ((childLH (childLH (childLH thetaAboveCell000022013002)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childLH (childLH
            thetaAboveCell000022013002))) h)
        (by
          have h : ((childHL (childLH (childLH thetaAboveCell000022013002)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childLH (childLH
            thetaAboveCell000022013002))) h)
        (by
          have h : ((childHH (childLH (childLH thetaAboveCell000022013002)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childLH (childLH
            thetaAboveCell000022013002))) h))
    (by
      have h : ((childHL (childLH thetaAboveCell000022013002))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childLH thetaAboveCell000022013002)) h)
    (by
      have h : ((childHH (childLH thetaAboveCell000022013002))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childLH thetaAboveCell000022013002)) h)

theorem cover_subtree_144d92380fd4 :
    adaptiveCoverCheck 7 thetaAboveCell000022013002 = true := by
  exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000022013002
    cover_subtree_1032efc16567
    cover_subtree_9fa6122a45d4
    (by
      have h : ((childHL thetaAboveCell000022013002)).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000022013002) h)
    (by
      have h : ((childHH thetaAboveCell000022013002)).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000022013002) h)

theorem cover_subtree_fd47657a07ff :
    adaptiveCoverCheck 6 (childLL thetaAboveCell000022013003) = true := by
  exact adaptiveCoverCheck_succ_of_children 5 (childLL thetaAboveCell000022013003)
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childLL (childLL thetaAboveCell000022013003))
        (by
          have h : ((childLL (childLL (childLL thetaAboveCell000022013003)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childLL (childLL
            thetaAboveCell000022013003))) h)
        (by
          have h : ((childLH (childLL (childLL thetaAboveCell000022013003)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childLL (childLL
            thetaAboveCell000022013003))) h)
        (by
          have h : ((childHL (childLL (childLL thetaAboveCell000022013003)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childLL (childLL
            thetaAboveCell000022013003))) h)
        (by
          have h : ((childHH (childLL (childLL thetaAboveCell000022013003)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childLL (childLL
            thetaAboveCell000022013003))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childLH (childLL thetaAboveCell000022013003))
        (by
          have h : ((childLL (childLH (childLL thetaAboveCell000022013003)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childLH (childLL
            thetaAboveCell000022013003))) h)
        (by
          have h : ((childLH (childLH (childLL thetaAboveCell000022013003)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childLH (childLL
            thetaAboveCell000022013003))) h)
        (by
          have h : ((childHL (childLH (childLL thetaAboveCell000022013003)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childLH (childLL
            thetaAboveCell000022013003))) h)
        (by
          have h : ((childHH (childLH (childLL thetaAboveCell000022013003)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childLH (childLL
            thetaAboveCell000022013003))) h))
    (by
      have h : ((childHL (childLL thetaAboveCell000022013003))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childLL thetaAboveCell000022013003)) h)
    (by
      have h : ((childHH (childLL thetaAboveCell000022013003))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childLL thetaAboveCell000022013003)) h)

theorem cover_subtree_e586a2e528dc :
    adaptiveCoverCheck 6 (childLH thetaAboveCell000022013003) = true := by
  exact adaptiveCoverCheck_succ_of_children 5 (childLH thetaAboveCell000022013003)
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childLL (childLH thetaAboveCell000022013003))
        (by
          have h : ((childLL (childLL (childLH thetaAboveCell000022013003)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childLL (childLH
            thetaAboveCell000022013003))) h)
        (by
          have h : ((childLH (childLL (childLH thetaAboveCell000022013003)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childLL (childLH
            thetaAboveCell000022013003))) h)
        (by
          have h : ((childHL (childLL (childLH thetaAboveCell000022013003)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childLL (childLH
            thetaAboveCell000022013003))) h)
        (by
          have h : ((childHH (childLL (childLH thetaAboveCell000022013003)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childLL (childLH
            thetaAboveCell000022013003))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childLH (childLH thetaAboveCell000022013003))
        (by
          have h : ((childLL (childLH (childLH thetaAboveCell000022013003)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childLH (childLH
            thetaAboveCell000022013003))) h)
        (by
          have h : ((childLH (childLH (childLH thetaAboveCell000022013003)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childLH (childLH
            thetaAboveCell000022013003))) h)
        (by
          have h : ((childHL (childLH (childLH thetaAboveCell000022013003)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childLH (childLH
            thetaAboveCell000022013003))) h)
        (by
          have h : ((childHH (childLH (childLH thetaAboveCell000022013003)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childLH (childLH
            thetaAboveCell000022013003))) h))
    (by
      have h : ((childHL (childLH thetaAboveCell000022013003))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childLH thetaAboveCell000022013003)) h)
    (by
      have h : ((childHH (childLH thetaAboveCell000022013003))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childLH thetaAboveCell000022013003)) h)

theorem cover_subtree_b0c1a95db5a1 :
    adaptiveCoverCheck 7 thetaAboveCell000022013003 = true := by
  exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000022013003
    cover_subtree_fd47657a07ff
    cover_subtree_e586a2e528dc
    (by
      have h : ((childHL thetaAboveCell000022013003)).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000022013003) h)
    (by
      have h : ((childHH thetaAboveCell000022013003)).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000022013003) h)

theorem cover_subtree_deb83366e758 :
    adaptiveCoverCheck 8 (childLL (childLL (childHH thetaAboveCell00002201))) = true := by
  exact adaptiveCoverCheck_succ_of_children 7 (childLL (childLL (childHH thetaAboveCell00002201)))
    cover_subtree_701e722ef144
    cover_subtree_f1411005533f
    cover_subtree_144d92380fd4
    cover_subtree_b0c1a95db5a1

theorem cover_subtree_39d8fa6eaebd :
    adaptiveCoverCheck 5 (childLL (childHL thetaAboveCell000022013010)) = true := by
  exact adaptiveCoverCheck_succ_of_children 4 (childLL (childHL thetaAboveCell000022013010))
    (by
      have h : ((childLL (childLL (childHL thetaAboveCell000022013010)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childLL (childHL
        thetaAboveCell000022013010))) h)
    (by
      have h : ((childLH (childLL (childHL thetaAboveCell000022013010)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childLL (childHL
        thetaAboveCell000022013010))) h)
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childHL (childLL (childHL
        thetaAboveCell000022013010)))
        (by
          have h : (thetaAboveCell0000220130102020).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220130102020 h)
        (by
          have h : (thetaAboveCell0000220130102021).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220130102021 h)
        (by
          have h : (thetaAboveCell0000220130102022).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220130102022 h)
        (by
          have h : (thetaAboveCell0000220130102023).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220130102023 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childHH (childLL (childHL
        thetaAboveCell000022013010)))
        (by
          have h : (thetaAboveCell0000220130102030).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220130102030 h)
        (by
          have h : (thetaAboveCell0000220130102031).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220130102031 h)
        (by
          have h : (thetaAboveCell0000220130102032).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220130102032 h)
        (by
          have h : (thetaAboveCell0000220130102033).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220130102033 h))

theorem cover_subtree_c9870a8382fd :
    adaptiveCoverCheck 5 (childLH (childHL thetaAboveCell000022013010)) = true := by
  exact adaptiveCoverCheck_succ_of_children 4 (childLH (childHL thetaAboveCell000022013010))
    (by
      have h : ((childLL (childLH (childHL thetaAboveCell000022013010)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childLH (childHL
        thetaAboveCell000022013010))) h)
    (by
      have h : ((childLH (childLH (childHL thetaAboveCell000022013010)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childLH (childHL
        thetaAboveCell000022013010))) h)
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childHL (childLH (childHL
        thetaAboveCell000022013010)))
        (by
          have h : (thetaAboveCell0000220130102120).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220130102120 h)
        (by
          have h : (thetaAboveCell0000220130102121).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220130102121 h)
        (by
          have h : (thetaAboveCell0000220130102122).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220130102122 h)
        (by
          have h : (thetaAboveCell0000220130102123).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220130102123 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childHH (childLH (childHL
        thetaAboveCell000022013010)))
        (by
          have h : (thetaAboveCell0000220130102130).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220130102130 h)
        (by
          have h : (thetaAboveCell0000220130102131).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220130102131 h)
        (by
          have h : (thetaAboveCell0000220130102132).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220130102132 h)
        (by
          have h : (thetaAboveCell0000220130102133).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220130102133 h))

theorem cover_subtree_9ebf3cbb8048 :
    adaptiveCoverCheck 5 (childHL (childHL thetaAboveCell000022013010)) = true := by
  exact adaptiveCoverCheck_succ_of_children 4 (childHL (childHL thetaAboveCell000022013010))
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childLL (childHL (childHL
        thetaAboveCell000022013010)))
        (by
          have h : (thetaAboveCell0000220130102200).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220130102200 h)
        (by
          have h : (thetaAboveCell0000220130102201).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220130102201 h)
        (by
          have h : (thetaAboveCell0000220130102202).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220130102202 h)
        (by
          have h : (thetaAboveCell0000220130102203).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220130102203 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childLH (childHL (childHL
        thetaAboveCell000022013010)))
        (by
          have h : (thetaAboveCell0000220130102210).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220130102210 h)
        (by
          have h : (thetaAboveCell0000220130102211).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220130102211 h)
        (by
          have h : (thetaAboveCell0000220130102212).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220130102212 h)
        (by
          have h : (thetaAboveCell0000220130102213).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220130102213 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childHL (childHL (childHL
        thetaAboveCell000022013010)))
        (by
          have h : (thetaAboveCell0000220130102220).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220130102220 h)
        (by
          have h : (thetaAboveCell0000220130102221).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220130102221 h)
        (by
          have h : (thetaAboveCell0000220130102222).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220130102222 h)
        (by
          have h : (thetaAboveCell0000220130102223).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220130102223 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childHH (childHL (childHL
        thetaAboveCell000022013010)))
        (by
          have h : (thetaAboveCell0000220130102230).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220130102230 h)
        (by
          have h : (thetaAboveCell0000220130102231).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220130102231 h)
        (by
          have h : (thetaAboveCell0000220130102232).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220130102232 h)
        (by
          have h : (thetaAboveCell0000220130102233).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220130102233 h))

theorem cover_subtree_5943bf03a25d :
    adaptiveCoverCheck 5 (childHH (childHL thetaAboveCell000022013010)) = true := by
  exact adaptiveCoverCheck_succ_of_children 4 (childHH (childHL thetaAboveCell000022013010))
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childLL (childHH (childHL
        thetaAboveCell000022013010)))
        (by
          have h : (thetaAboveCell0000220130102300).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220130102300 h)
        (by
          have h : (thetaAboveCell0000220130102301).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220130102301 h)
        (by
          have h : (thetaAboveCell0000220130102302).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220130102302 h)
        (by
          have h : (thetaAboveCell0000220130102303).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220130102303 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childLH (childHH (childHL
        thetaAboveCell000022013010)))
        (by
          have h : (thetaAboveCell0000220130102310).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220130102310 h)
        (by
          have h : (thetaAboveCell0000220130102311).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220130102311 h)
        (by
          have h : (thetaAboveCell0000220130102312).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220130102312 h)
        (by
          have h : (thetaAboveCell0000220130102313).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220130102313 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childHL (childHH (childHL
        thetaAboveCell000022013010)))
        (by
          have h : (thetaAboveCell0000220130102320).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220130102320 h)
        (by
          have h : (thetaAboveCell0000220130102321).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220130102321 h)
        (by
          have h : (thetaAboveCell0000220130102322).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220130102322 h)
        (by
          have h : (thetaAboveCell0000220130102323).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220130102323 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childHH (childHH (childHL
        thetaAboveCell000022013010)))
        (by
          have h : (thetaAboveCell0000220130102330).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220130102330 h)
        (by
          have h : (thetaAboveCell0000220130102331).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220130102331 h)
        (by
          have h : (thetaAboveCell0000220130102332).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220130102332 h)
        (by
          have h : (thetaAboveCell0000220130102333).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220130102333 h))

theorem cover_subtree_6b97e89b4d72 :
    adaptiveCoverCheck 6 (childHL thetaAboveCell000022013010) = true := by
  exact adaptiveCoverCheck_succ_of_children 5 (childHL thetaAboveCell000022013010)
    cover_subtree_39d8fa6eaebd
    cover_subtree_c9870a8382fd
    cover_subtree_9ebf3cbb8048
    cover_subtree_5943bf03a25d

theorem cover_subtree_b9a006cc60d2 :
    adaptiveCoverCheck 5 (childLL (childHH thetaAboveCell000022013010)) = true := by
  exact adaptiveCoverCheck_succ_of_children 4 (childLL (childHH thetaAboveCell000022013010))
    (by
      have h : ((childLL (childLL (childHH thetaAboveCell000022013010)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childLL (childHH
        thetaAboveCell000022013010))) h)
    (by
      have h : ((childLH (childLL (childHH thetaAboveCell000022013010)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childLL (childHH
        thetaAboveCell000022013010))) h)
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childHL (childLL (childHH
        thetaAboveCell000022013010)))
        (by
          have h : (thetaAboveCell0000220130103020).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220130103020 h)
        (by
          have h : (thetaAboveCell0000220130103021).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220130103021 h)
        (by
          have h : (thetaAboveCell0000220130103022).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220130103022 h)
        (by
          have h : (thetaAboveCell0000220130103023).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220130103023 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childHH (childLL (childHH
        thetaAboveCell000022013010)))
        (by
          have h : (thetaAboveCell0000220130103030).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220130103030 h)
        (by
          have h : (thetaAboveCell0000220130103031).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220130103031 h)
        (by
          have h : (thetaAboveCell0000220130103032).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220130103032 h)
        (by
          have h : (thetaAboveCell0000220130103033).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220130103033 h))

theorem cover_subtree_a77e4838b8e6 :
    adaptiveCoverCheck 5 (childLH (childHH thetaAboveCell000022013010)) = true := by
  exact adaptiveCoverCheck_succ_of_children 4 (childLH (childHH thetaAboveCell000022013010))
    (by
      have h : ((childLL (childLH (childHH thetaAboveCell000022013010)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childLH (childHH
        thetaAboveCell000022013010))) h)
    (by
      have h : ((childLH (childLH (childHH thetaAboveCell000022013010)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childLH (childHH
        thetaAboveCell000022013010))) h)
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childHL (childLH (childHH
        thetaAboveCell000022013010)))
        (by
          have h : (thetaAboveCell0000220130103120).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220130103120 h)
        (by
          have h : (thetaAboveCell0000220130103121).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220130103121 h)
        (by
          have h : (thetaAboveCell0000220130103122).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220130103122 h)
        (by
          have h : (thetaAboveCell0000220130103123).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220130103123 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childHH (childLH (childHH
        thetaAboveCell000022013010)))
        (by
          have h : (thetaAboveCell0000220130103130).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220130103130 h)
        (by
          have h : (thetaAboveCell0000220130103131).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220130103131 h)
        (by
          have h : (thetaAboveCell0000220130103132).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220130103132 h)
        (by
          have h : (thetaAboveCell0000220130103133).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220130103133 h))

theorem cover_subtree_c5585ab205b2 :
    adaptiveCoverCheck 5 (childHL (childHH thetaAboveCell000022013010)) = true := by
  exact adaptiveCoverCheck_succ_of_children 4 (childHL (childHH thetaAboveCell000022013010))
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childLL (childHL (childHH
        thetaAboveCell000022013010)))
        (by
          have h : (thetaAboveCell0000220130103200).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220130103200 h)
        (by
          have h : (thetaAboveCell0000220130103201).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220130103201 h)
        (by
          have h : (thetaAboveCell0000220130103202).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220130103202 h)
        (by
          have h : (thetaAboveCell0000220130103203).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220130103203 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childLH (childHL (childHH
        thetaAboveCell000022013010)))
        (by
          have h : (thetaAboveCell0000220130103210).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220130103210 h)
        (by
          have h : (thetaAboveCell0000220130103211).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220130103211 h)
        (by
          have h : (thetaAboveCell0000220130103212).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220130103212 h)
        (by
          have h : (thetaAboveCell0000220130103213).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220130103213 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childHL (childHL (childHH
        thetaAboveCell000022013010)))
        (by
          have h : (thetaAboveCell0000220130103220).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220130103220 h)
        (by
          have h : (thetaAboveCell0000220130103221).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220130103221 h)
        (by
          have h : (thetaAboveCell0000220130103222).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220130103222 h)
        (by
          have h : (thetaAboveCell0000220130103223).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220130103223 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childHH (childHL (childHH
        thetaAboveCell000022013010)))
        (by
          have h : (thetaAboveCell0000220130103230).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220130103230 h)
        (by
          have h : (thetaAboveCell0000220130103231).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220130103231 h)
        (by
          have h : (thetaAboveCell0000220130103232).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220130103232 h)
        (by
          have h : (thetaAboveCell0000220130103233).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220130103233 h))

theorem cover_subtree_0a8fc7348d19 :
    adaptiveCoverCheck 5 (childHH (childHH thetaAboveCell000022013010)) = true := by
  exact adaptiveCoverCheck_succ_of_children 4 (childHH (childHH thetaAboveCell000022013010))
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childLL (childHH (childHH
        thetaAboveCell000022013010)))
        (by
          have h : (thetaAboveCell0000220130103300).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220130103300 h)
        (by
          have h : (thetaAboveCell0000220130103301).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220130103301 h)
        (by
          have h : (thetaAboveCell0000220130103302).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220130103302 h)
        (by
          have h : (thetaAboveCell0000220130103303).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220130103303 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childLH (childHH (childHH
        thetaAboveCell000022013010)))
        (by
          have h : (thetaAboveCell0000220130103310).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220130103310 h)
        (by
          have h : (thetaAboveCell0000220130103311).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220130103311 h)
        (by
          have h : (thetaAboveCell0000220130103312).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220130103312 h)
        (by
          have h : (thetaAboveCell0000220130103313).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220130103313 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childHL (childHH (childHH
        thetaAboveCell000022013010)))
        (by
          have h : (thetaAboveCell0000220130103320).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220130103320 h)
        (by
          have h : (thetaAboveCell0000220130103321).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220130103321 h)
        (by
          have h : (thetaAboveCell0000220130103322).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220130103322 h)
        (by
          have h : (thetaAboveCell0000220130103323).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220130103323 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childHH (childHH (childHH
        thetaAboveCell000022013010)))
        (by
          have h : (thetaAboveCell0000220130103330).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220130103330 h)
        (by
          have h : (thetaAboveCell0000220130103331).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220130103331 h)
        (by
          have h : (thetaAboveCell0000220130103332).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220130103332 h)
        (by
          have h : (thetaAboveCell0000220130103333).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220130103333 h))

theorem cover_subtree_dffa22b1c9a1 :
    adaptiveCoverCheck 6 (childHH thetaAboveCell000022013010) = true := by
  exact adaptiveCoverCheck_succ_of_children 5 (childHH thetaAboveCell000022013010)
    cover_subtree_b9a006cc60d2
    cover_subtree_a77e4838b8e6
    cover_subtree_c5585ab205b2
    cover_subtree_0a8fc7348d19

theorem cover_subtree_3a257d8444b0 :
    adaptiveCoverCheck 7 thetaAboveCell000022013010 = true := by
  exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000022013010
    (by
      exact adaptiveCoverCheck_succ_of_children 5 (childLL thetaAboveCell000022013010)
        (by
          have h : ((childLL (childLL thetaAboveCell000022013010))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childLL
            thetaAboveCell000022013010)) h)
        (by
          have h : ((childLH (childLL thetaAboveCell000022013010))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childLL
            thetaAboveCell000022013010)) h)
        (by
          have h : ((childHL (childLL thetaAboveCell000022013010))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childLL
            thetaAboveCell000022013010)) h)
        (by
          have h : ((childHH (childLL thetaAboveCell000022013010))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childLL
            thetaAboveCell000022013010)) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 5 (childLH thetaAboveCell000022013010)
        (by
          have h : ((childLL (childLH thetaAboveCell000022013010))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childLH
            thetaAboveCell000022013010)) h)
        (by
          have h : ((childLH (childLH thetaAboveCell000022013010))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childLH
            thetaAboveCell000022013010)) h)
        (by
          have h : ((childHL (childLH thetaAboveCell000022013010))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childLH
            thetaAboveCell000022013010)) h)
        (by
          have h : ((childHH (childLH thetaAboveCell000022013010))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childLH
            thetaAboveCell000022013010)) h))
    cover_subtree_6b97e89b4d72
    cover_subtree_dffa22b1c9a1

theorem cover_subtree_0ba56921169a :
    adaptiveCoverCheck 5 (childLL (childHL thetaAboveCell000022013011)) = true := by
  exact adaptiveCoverCheck_succ_of_children 4 (childLL (childHL thetaAboveCell000022013011))
    (by
      have h : ((childLL (childLL (childHL thetaAboveCell000022013011)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childLL (childHL
        thetaAboveCell000022013011))) h)
    (by
      have h : ((childLH (childLL (childHL thetaAboveCell000022013011)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childLL (childHL
        thetaAboveCell000022013011))) h)
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childHL (childLL (childHL
        thetaAboveCell000022013011)))
        (by
          have h : (thetaAboveCell0000220130112020).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220130112020 h)
        (by
          have h : (thetaAboveCell0000220130112021).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220130112021 h)
        (by
          have h : (thetaAboveCell0000220130112022).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220130112022 h)
        (by
          have h : (thetaAboveCell0000220130112023).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220130112023 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childHH (childLL (childHL
        thetaAboveCell000022013011)))
        (by
          have h : (thetaAboveCell0000220130112030).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220130112030 h)
        (by
          have h : (thetaAboveCell0000220130112031).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220130112031 h)
        (by
          have h : (thetaAboveCell0000220130112032).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220130112032 h)
        (by
          have h : (thetaAboveCell0000220130112033).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220130112033 h))

theorem cover_subtree_7969bce7dc99 :
    adaptiveCoverCheck 5 (childLH (childHL thetaAboveCell000022013011)) = true := by
  exact adaptiveCoverCheck_succ_of_children 4 (childLH (childHL thetaAboveCell000022013011))
    (by
      have h : ((childLL (childLH (childHL thetaAboveCell000022013011)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childLH (childHL
        thetaAboveCell000022013011))) h)
    (by
      have h : ((childLH (childLH (childHL thetaAboveCell000022013011)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childLH (childHL
        thetaAboveCell000022013011))) h)
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childHL (childLH (childHL
        thetaAboveCell000022013011)))
        (by
          have h : (thetaAboveCell0000220130112120).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220130112120 h)
        (by
          have h : (thetaAboveCell0000220130112121).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220130112121 h)
        (by
          have h : (thetaAboveCell0000220130112122).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220130112122 h)
        (by
          have h : (thetaAboveCell0000220130112123).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220130112123 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childHH (childLH (childHL
        thetaAboveCell000022013011)))
        (by
          have h : (thetaAboveCell0000220130112130).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220130112130 h)
        (by
          have h : (thetaAboveCell0000220130112131).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220130112131 h)
        (by
          have h : (thetaAboveCell0000220130112132).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220130112132 h)
        (by
          have h : (thetaAboveCell0000220130112133).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220130112133 h))

theorem cover_subtree_6a708e0151cf :
    adaptiveCoverCheck 5 (childHL (childHL thetaAboveCell000022013011)) = true := by
  exact adaptiveCoverCheck_succ_of_children 4 (childHL (childHL thetaAboveCell000022013011))
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childLL (childHL (childHL
        thetaAboveCell000022013011)))
        (by
          have h : (thetaAboveCell0000220130112200).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220130112200 h)
        (by
          have h : (thetaAboveCell0000220130112201).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220130112201 h)
        (by
          have h : (thetaAboveCell0000220130112202).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220130112202 h)
        (by
          have h : (thetaAboveCell0000220130112203).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220130112203 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childLH (childHL (childHL
        thetaAboveCell000022013011)))
        (by
          have h : (thetaAboveCell0000220130112210).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220130112210 h)
        (by
          have h : (thetaAboveCell0000220130112211).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220130112211 h)
        (by
          have h : (thetaAboveCell0000220130112212).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220130112212 h)
        (by
          have h : (thetaAboveCell0000220130112213).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220130112213 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childHL (childHL (childHL
        thetaAboveCell000022013011)))
        (by
          have h : (thetaAboveCell0000220130112220).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220130112220 h)
        (by
          have h : (thetaAboveCell0000220130112221).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220130112221 h)
        (by
          have h : (thetaAboveCell0000220130112222).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220130112222 h)
        (by
          have h : (thetaAboveCell0000220130112223).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220130112223 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childHH (childHL (childHL
        thetaAboveCell000022013011)))
        (by
          have h : (thetaAboveCell0000220130112230).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220130112230 h)
        (by
          have h : (thetaAboveCell0000220130112231).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220130112231 h)
        (by
          have h : (thetaAboveCell0000220130112232).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220130112232 h)
        (by
          have h : (thetaAboveCell0000220130112233).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220130112233 h))

theorem cover_subtree_8de093d065af :
    adaptiveCoverCheck 5 (childHH (childHL thetaAboveCell000022013011)) = true := by
  exact adaptiveCoverCheck_succ_of_children 4 (childHH (childHL thetaAboveCell000022013011))
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childLL (childHH (childHL
        thetaAboveCell000022013011)))
        (by
          have h : (thetaAboveCell0000220130112300).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220130112300 h)
        (by
          have h : (thetaAboveCell0000220130112301).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220130112301 h)
        (by
          have h : (thetaAboveCell0000220130112302).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220130112302 h)
        (by
          have h : (thetaAboveCell0000220130112303).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220130112303 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childLH (childHH (childHL
        thetaAboveCell000022013011)))
        (by
          have h : (thetaAboveCell0000220130112310).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220130112310 h)
        (by
          have h : (thetaAboveCell0000220130112311).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220130112311 h)
        (by
          have h : (thetaAboveCell0000220130112312).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220130112312 h)
        (by
          have h : (thetaAboveCell0000220130112313).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220130112313 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childHL (childHH (childHL
        thetaAboveCell000022013011)))
        (by
          have h : (thetaAboveCell0000220130112320).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220130112320 h)
        (by
          have h : (thetaAboveCell0000220130112321).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220130112321 h)
        (by
          have h : (thetaAboveCell0000220130112322).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220130112322 h)
        (by
          have h : (thetaAboveCell0000220130112323).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220130112323 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childHH (childHH (childHL
        thetaAboveCell000022013011)))
        (by
          have h : (thetaAboveCell0000220130112330).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220130112330 h)
        (by
          have h : (thetaAboveCell0000220130112331).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220130112331 h)
        (by
          have h : (thetaAboveCell0000220130112332).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220130112332 h)
        (by
          have h : (thetaAboveCell0000220130112333).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220130112333 h))

theorem cover_subtree_03f7c5873741 :
    adaptiveCoverCheck 6 (childHL thetaAboveCell000022013011) = true := by
  exact adaptiveCoverCheck_succ_of_children 5 (childHL thetaAboveCell000022013011)
    cover_subtree_0ba56921169a
    cover_subtree_7969bce7dc99
    cover_subtree_6a708e0151cf
    cover_subtree_8de093d065af

theorem cover_subtree_b3bbbe006bfc :
    adaptiveCoverCheck 5 (childLL (childHH thetaAboveCell000022013011)) = true := by
  exact adaptiveCoverCheck_succ_of_children 4 (childLL (childHH thetaAboveCell000022013011))
    (by
      have h : ((childLL (childLL (childHH thetaAboveCell000022013011)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childLL (childHH
        thetaAboveCell000022013011))) h)
    (by
      have h : ((childLH (childLL (childHH thetaAboveCell000022013011)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childLL (childHH
        thetaAboveCell000022013011))) h)
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childHL (childLL (childHH
        thetaAboveCell000022013011)))
        (by
          have h : (thetaAboveCell0000220130113020).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220130113020 h)
        (by
          have h : (thetaAboveCell0000220130113021).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220130113021 h)
        (by
          have h : (thetaAboveCell0000220130113022).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220130113022 h)
        (by
          have h : (thetaAboveCell0000220130113023).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220130113023 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childHH (childLL (childHH
        thetaAboveCell000022013011)))
        (by
          have h : (thetaAboveCell0000220130113030).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220130113030 h)
        (by
          have h : (thetaAboveCell0000220130113031).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220130113031 h)
        (by
          have h : (thetaAboveCell0000220130113032).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220130113032 h)
        (by
          have h : (thetaAboveCell0000220130113033).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220130113033 h))

theorem cover_subtree_10ce55f7ce75 :
    adaptiveCoverCheck 5 (childLH (childHH thetaAboveCell000022013011)) = true := by
  exact adaptiveCoverCheck_succ_of_children 4 (childLH (childHH thetaAboveCell000022013011))
    (by
      have h : ((childLL (childLH (childHH thetaAboveCell000022013011)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childLH (childHH
        thetaAboveCell000022013011))) h)
    (by
      have h : ((childLH (childLH (childHH thetaAboveCell000022013011)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childLH (childHH
        thetaAboveCell000022013011))) h)
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childHL (childLH (childHH
        thetaAboveCell000022013011)))
        (by
          have h : (thetaAboveCell0000220130113120).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220130113120 h)
        (by
          have h : (thetaAboveCell0000220130113121).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220130113121 h)
        (by
          have h : (thetaAboveCell0000220130113122).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220130113122 h)
        (by
          have h : (thetaAboveCell0000220130113123).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220130113123 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childHH (childLH (childHH
        thetaAboveCell000022013011)))
        (by
          have h : (thetaAboveCell0000220130113130).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220130113130 h)
        (by
          have h : (thetaAboveCell0000220130113131).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220130113131 h)
        (by
          have h : (thetaAboveCell0000220130113132).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220130113132 h)
        (by
          have h : (thetaAboveCell0000220130113133).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220130113133 h))

theorem cover_subtree_b98ded6b50f2 :
    adaptiveCoverCheck 5 (childHL (childHH thetaAboveCell000022013011)) = true := by
  exact adaptiveCoverCheck_succ_of_children 4 (childHL (childHH thetaAboveCell000022013011))
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childLL (childHL (childHH
        thetaAboveCell000022013011)))
        (by
          have h : (thetaAboveCell0000220130113200).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220130113200 h)
        (by
          have h : (thetaAboveCell0000220130113201).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220130113201 h)
        (by
          have h : (thetaAboveCell0000220130113202).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220130113202 h)
        (by
          have h : (thetaAboveCell0000220130113203).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220130113203 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childLH (childHL (childHH
        thetaAboveCell000022013011)))
        (by
          have h : (thetaAboveCell0000220130113210).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220130113210 h)
        (by
          have h : (thetaAboveCell0000220130113211).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220130113211 h)
        (by
          have h : (thetaAboveCell0000220130113212).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220130113212 h)
        (by
          have h : (thetaAboveCell0000220130113213).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220130113213 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childHL (childHL (childHH
        thetaAboveCell000022013011)))
        (by
          have h : (thetaAboveCell0000220130113220).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220130113220 h)
        (by
          have h : (thetaAboveCell0000220130113221).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220130113221 h)
        (by
          have h : (thetaAboveCell0000220130113222).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220130113222 h)
        (by
          have h : (thetaAboveCell0000220130113223).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220130113223 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childHH (childHL (childHH
        thetaAboveCell000022013011)))
        (by
          have h : (thetaAboveCell0000220130113230).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220130113230 h)
        (by
          have h : (thetaAboveCell0000220130113231).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220130113231 h)
        (by
          have h : (thetaAboveCell0000220130113232).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220130113232 h)
        (by
          have h : (thetaAboveCell0000220130113233).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220130113233 h))

theorem cover_subtree_6021efadc4fa :
    adaptiveCoverCheck 5 (childHH (childHH thetaAboveCell000022013011)) = true := by
  exact adaptiveCoverCheck_succ_of_children 4 (childHH (childHH thetaAboveCell000022013011))
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childLL (childHH (childHH
        thetaAboveCell000022013011)))
        (by
          have h : (thetaAboveCell0000220130113300).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220130113300 h)
        (by
          have h : (thetaAboveCell0000220130113301).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220130113301 h)
        (by
          have h : (thetaAboveCell0000220130113302).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220130113302 h)
        (by
          have h : (thetaAboveCell0000220130113303).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220130113303 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childLH (childHH (childHH
        thetaAboveCell000022013011)))
        (by
          have h : (thetaAboveCell0000220130113310).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220130113310 h)
        (by
          have h : (thetaAboveCell0000220130113311).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220130113311 h)
        (by
          have h : (thetaAboveCell0000220130113312).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220130113312 h)
        (by
          have h : (thetaAboveCell0000220130113313).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220130113313 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childHL (childHH (childHH
        thetaAboveCell000022013011)))
        (by
          have h : (thetaAboveCell0000220130113320).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220130113320 h)
        (by
          have h : (thetaAboveCell0000220130113321).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220130113321 h)
        (by
          have h : (thetaAboveCell0000220130113322).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220130113322 h)
        (by
          have h : (thetaAboveCell0000220130113323).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220130113323 h))
    (by
      have h : ((childHH (childHH (childHH thetaAboveCell000022013011)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childHH (childHH
        thetaAboveCell000022013011))) h)

theorem cover_subtree_3daa6e2b09d9 :
    adaptiveCoverCheck 6 (childHH thetaAboveCell000022013011) = true := by
  exact adaptiveCoverCheck_succ_of_children 5 (childHH thetaAboveCell000022013011)
    cover_subtree_b3bbbe006bfc
    cover_subtree_10ce55f7ce75
    cover_subtree_b98ded6b50f2
    cover_subtree_6021efadc4fa

theorem cover_subtree_adb5bf33bc5c :
    adaptiveCoverCheck 7 thetaAboveCell000022013011 = true := by
  exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000022013011
    (by
      exact adaptiveCoverCheck_succ_of_children 5 (childLL thetaAboveCell000022013011)
        (by
          have h : ((childLL (childLL thetaAboveCell000022013011))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childLL
            thetaAboveCell000022013011)) h)
        (by
          have h : ((childLH (childLL thetaAboveCell000022013011))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childLL
            thetaAboveCell000022013011)) h)
        (by
          have h : ((childHL (childLL thetaAboveCell000022013011))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childLL
            thetaAboveCell000022013011)) h)
        (by
          have h : ((childHH (childLL thetaAboveCell000022013011))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childLL
            thetaAboveCell000022013011)) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 5 (childLH thetaAboveCell000022013011)
        (by
          have h : ((childLL (childLH thetaAboveCell000022013011))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childLH
            thetaAboveCell000022013011)) h)
        (by
          have h : ((childLH (childLH thetaAboveCell000022013011))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childLH
            thetaAboveCell000022013011)) h)
        (by
          have h : ((childHL (childLH thetaAboveCell000022013011))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childLH
            thetaAboveCell000022013011)) h)
        (by
          have h : ((childHH (childLH thetaAboveCell000022013011))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childLH
            thetaAboveCell000022013011)) h))
    cover_subtree_03f7c5873741
    cover_subtree_3daa6e2b09d9

theorem cover_subtree_b3708d7f6b8c :
    adaptiveCoverCheck 6 (childLL thetaAboveCell000022013012) = true := by
  exact adaptiveCoverCheck_succ_of_children 5 (childLL thetaAboveCell000022013012)
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childLL (childLL thetaAboveCell000022013012))
        (by
          have h : ((childLL (childLL (childLL thetaAboveCell000022013012)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childLL (childLL
            thetaAboveCell000022013012))) h)
        (by
          have h : ((childLH (childLL (childLL thetaAboveCell000022013012)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childLL (childLL
            thetaAboveCell000022013012))) h)
        (by
          have h : ((childHL (childLL (childLL thetaAboveCell000022013012)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childLL (childLL
            thetaAboveCell000022013012))) h)
        (by
          have h : ((childHH (childLL (childLL thetaAboveCell000022013012)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childLL (childLL
            thetaAboveCell000022013012))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childLH (childLL thetaAboveCell000022013012))
        (by
          have h : ((childLL (childLH (childLL thetaAboveCell000022013012)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childLH (childLL
            thetaAboveCell000022013012))) h)
        (by
          have h : ((childLH (childLH (childLL thetaAboveCell000022013012)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childLH (childLL
            thetaAboveCell000022013012))) h)
        (by
          have h : ((childHL (childLH (childLL thetaAboveCell000022013012)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childLH (childLL
            thetaAboveCell000022013012))) h)
        (by
          have h : ((childHH (childLH (childLL thetaAboveCell000022013012)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childLH (childLL
            thetaAboveCell000022013012))) h))
    (by
      have h : ((childHL (childLL thetaAboveCell000022013012))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childLL thetaAboveCell000022013012)) h)
    (by
      have h : ((childHH (childLL thetaAboveCell000022013012))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childLL thetaAboveCell000022013012)) h)

theorem cover_subtree_74cca09731bd :
    adaptiveCoverCheck 6 (childLH thetaAboveCell000022013012) = true := by
  exact adaptiveCoverCheck_succ_of_children 5 (childLH thetaAboveCell000022013012)
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childLL (childLH thetaAboveCell000022013012))
        (by
          have h : ((childLL (childLL (childLH thetaAboveCell000022013012)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childLL (childLH
            thetaAboveCell000022013012))) h)
        (by
          have h : ((childLH (childLL (childLH thetaAboveCell000022013012)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childLL (childLH
            thetaAboveCell000022013012))) h)
        (by
          have h : ((childHL (childLL (childLH thetaAboveCell000022013012)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childLL (childLH
            thetaAboveCell000022013012))) h)
        (by
          have h : ((childHH (childLL (childLH thetaAboveCell000022013012)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childLL (childLH
            thetaAboveCell000022013012))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childLH (childLH thetaAboveCell000022013012))
        (by
          have h : ((childLL (childLH (childLH thetaAboveCell000022013012)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childLH (childLH
            thetaAboveCell000022013012))) h)
        (by
          have h : ((childLH (childLH (childLH thetaAboveCell000022013012)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childLH (childLH
            thetaAboveCell000022013012))) h)
        (by
          have h : ((childHL (childLH (childLH thetaAboveCell000022013012)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childLH (childLH
            thetaAboveCell000022013012))) h)
        (by
          have h : ((childHH (childLH (childLH thetaAboveCell000022013012)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childLH (childLH
            thetaAboveCell000022013012))) h))
    (by
      have h : ((childHL (childLH thetaAboveCell000022013012))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childLH thetaAboveCell000022013012)) h)
    (by
      have h : ((childHH (childLH thetaAboveCell000022013012))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childLH thetaAboveCell000022013012)) h)

theorem cover_subtree_04cd22005970 :
    adaptiveCoverCheck 7 thetaAboveCell000022013012 = true := by
  exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000022013012
    cover_subtree_b3708d7f6b8c
    cover_subtree_74cca09731bd
    (by
      have h : ((childHL thetaAboveCell000022013012)).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000022013012) h)
    (by
      have h : ((childHH thetaAboveCell000022013012)).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000022013012) h)

theorem cover_subtree_f57488cb8c35 :
    adaptiveCoverCheck 6 (childLL thetaAboveCell000022013013) = true := by
  exact adaptiveCoverCheck_succ_of_children 5 (childLL thetaAboveCell000022013013)
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childLL (childLL thetaAboveCell000022013013))
        (by
          have h : ((childLL (childLL (childLL thetaAboveCell000022013013)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childLL (childLL
            thetaAboveCell000022013013))) h)
        (by
          have h : ((childLH (childLL (childLL thetaAboveCell000022013013)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childLL (childLL
            thetaAboveCell000022013013))) h)
        (by
          have h : ((childHL (childLL (childLL thetaAboveCell000022013013)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childLL (childLL
            thetaAboveCell000022013013))) h)
        (by
          have h : ((childHH (childLL (childLL thetaAboveCell000022013013)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childLL (childLL
            thetaAboveCell000022013013))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childLH (childLL thetaAboveCell000022013013))
        (by
          have h : ((childLL (childLH (childLL thetaAboveCell000022013013)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childLH (childLL
            thetaAboveCell000022013013))) h)
        (by
          have h : ((childLH (childLH (childLL thetaAboveCell000022013013)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childLH (childLL
            thetaAboveCell000022013013))) h)
        (by
          have h : ((childHL (childLH (childLL thetaAboveCell000022013013)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childLH (childLL
            thetaAboveCell000022013013))) h)
        (by
          have h : ((childHH (childLH (childLL thetaAboveCell000022013013)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childLH (childLL
            thetaAboveCell000022013013))) h))
    (by
      have h : ((childHL (childLL thetaAboveCell000022013013))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childLL thetaAboveCell000022013013)) h)
    (by
      have h : ((childHH (childLL thetaAboveCell000022013013))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childLL thetaAboveCell000022013013)) h)

theorem cover_subtree_5e11cdd5ab21 :
    adaptiveCoverCheck 6 (childLH thetaAboveCell000022013013) = true := by
  exact adaptiveCoverCheck_succ_of_children 5 (childLH thetaAboveCell000022013013)
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childLL (childLH thetaAboveCell000022013013))
        (by
          have h : ((childLL (childLL (childLH thetaAboveCell000022013013)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childLL (childLH
            thetaAboveCell000022013013))) h)
        (by
          have h : ((childLH (childLL (childLH thetaAboveCell000022013013)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childLL (childLH
            thetaAboveCell000022013013))) h)
        (by
          have h : ((childHL (childLL (childLH thetaAboveCell000022013013)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childLL (childLH
            thetaAboveCell000022013013))) h)
        (by
          have h : ((childHH (childLL (childLH thetaAboveCell000022013013)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childLL (childLH
            thetaAboveCell000022013013))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childLH (childLH thetaAboveCell000022013013))
        (by
          have h : ((childLL (childLH (childLH thetaAboveCell000022013013)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childLH (childLH
            thetaAboveCell000022013013))) h)
        (by
          have h : ((childLH (childLH (childLH thetaAboveCell000022013013)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childLH (childLH
            thetaAboveCell000022013013))) h)
        (by
          have h : ((childHL (childLH (childLH thetaAboveCell000022013013)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childLH (childLH
            thetaAboveCell000022013013))) h)
        (by
          have h : ((childHH (childLH (childLH thetaAboveCell000022013013)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childLH (childLH
            thetaAboveCell000022013013))) h))
    (by
      have h : ((childHL (childLH thetaAboveCell000022013013))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childLH thetaAboveCell000022013013)) h)
    (by
      have h : ((childHH (childLH thetaAboveCell000022013013))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childLH thetaAboveCell000022013013)) h)

theorem cover_subtree_d6f5101b1ccd :
    adaptiveCoverCheck 7 thetaAboveCell000022013013 = true := by
  exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000022013013
    cover_subtree_f57488cb8c35
    cover_subtree_5e11cdd5ab21
    (by
      have h : ((childHL thetaAboveCell000022013013)).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000022013013) h)
    (by
      have h : ((childHH thetaAboveCell000022013013)).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000022013013) h)

theorem cover_subtree_2784ec883b01 :
    adaptiveCoverCheck 8 (childLH (childLL (childHH thetaAboveCell00002201))) = true := by
  exact adaptiveCoverCheck_succ_of_children 7 (childLH (childLL (childHH thetaAboveCell00002201)))
    cover_subtree_3a257d8444b0
    cover_subtree_adb5bf33bc5c
    cover_subtree_04cd22005970
    cover_subtree_d6f5101b1ccd

theorem e24KC2ThetaAboveLeaf0000220130 :
    adaptiveCoverCheck 9 (childLL (childHH thetaAboveCell00002201)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLL (childHH thetaAboveCell00002201))
    cover_subtree_deb83366e758
    cover_subtree_2784ec883b01
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHL (childLL (childHH
        thetaAboveCell00002201)))
        (by
          have h : (thetaAboveCell000022013020).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000022013020 h)
        (by
          have h : (thetaAboveCell000022013021).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000022013021 h)
        (by
          have h : (thetaAboveCell000022013022).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000022013022 h)
        (by
          have h : (thetaAboveCell000022013023).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000022013023 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHH (childLL (childHH
        thetaAboveCell00002201)))
        (by
          have h : (thetaAboveCell000022013030).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000022013030 h)
        (by
          have h : (thetaAboveCell000022013031).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000022013031 h)
        (by
          have h : (thetaAboveCell000022013032).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000022013032 h)
        (by
          have h : (thetaAboveCell000022013033).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000022013033 h))

end PartE
end GerverSofa

end

end

end

end

end

end
