/-
Copyright (c) 2026 Dawid Trela. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dawid Trela
-/
module

public import LeanPool.MovingSofa.GerverSofa.KernelOnly.PartE.Certificates.Bundle022
public import LeanPool.MovingSofa.GerverSofa.KernelOnly.PartE.Certificates.Bundle024
public import LeanPool.MovingSofa.GerverSofa.KernelOnly.PartE.Certificates.Bundle028
public import LeanPool.MovingSofa.GerverSofa.KernelOnly.PartE.Certificates.Bundle031
/-!
# Gerver sofa: related certificate and semantic modules

* `GerverSofa.KernelOnly.PartE.Certificates.Batch046`.
-/

public section

noncomputable section

section

/-
Copyright (c) 2026 Dawid Trela. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dawid Trela
-/
/-!
# Gerver sofa dependency batch

* `KernelOnly.PartE.ThetaAbove.ReconstructionMiddle`.
* `KernelOnly.PartE.E24KC6ThetaAboveReconstruct`.
* `KernelOnly.PartE.E24KC6KernelFinalClosure`.
-/

public section

noncomputable section

section

/-!
# Intermediate reconstruction of the upper theta cover
-/

public section

noncomputable section

namespace GerverSofa
namespace PartE

open CertificateCells1a75b359b5

theorem e24KC2ThetaAboveNode011123123 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell01112312) = true :=
  adaptiveCoverCheck_succ_of_children 9 (childHH thetaAboveCell01112312)
    e24KC2ThetaAboveLeaf0111231230 e24KC2ThetaAboveLeaf0111231231 e24KC2ThetaAboveLeaf0111231232
      e24KC2ThetaAboveLeaf0111231233

theorem e24KC2ThetaAboveNode011123130 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell01112313) = true :=
  adaptiveCoverCheck_succ_of_children 9 (childLL thetaAboveCell01112313)
    e24KC2ThetaAboveLeaf0111231300 e24KC2ThetaAboveLeaf0111231301 e24KC2ThetaAboveLeaf0111231302
      e24KC2ThetaAboveLeaf0111231303

theorem e24KC2ThetaAboveNode011123131 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell01112313) = true :=
  adaptiveCoverCheck_succ_of_children 9 (childLH thetaAboveCell01112313)
    e24KC2ThetaAboveLeaf0111231310 e24KC2ThetaAboveLeaf0111231311 e24KC2ThetaAboveLeaf0111231312
      e24KC2ThetaAboveLeaf0111231313

theorem e24KC2ThetaAboveNode011123132 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell01112313) = true :=
  adaptiveCoverCheck_succ_of_children 9 (childHL thetaAboveCell01112313)
    e24KC2ThetaAboveLeaf0111231320 e24KC2ThetaAboveLeaf0111231321 e24KC2ThetaAboveLeaf0111231322
      e24KC2ThetaAboveLeaf0111231323

theorem e24KC2ThetaAboveNode011123133 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell01112313) = true :=
  adaptiveCoverCheck_succ_of_children 9 (childHH thetaAboveCell01112313)
    e24KC2ThetaAboveLeaf0111231330 e24KC2ThetaAboveLeaf0111231331 e24KC2ThetaAboveLeaf0111231332
      e24KC2ThetaAboveLeaf0111231333

theorem e24KC2ThetaAboveNode011132002 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell01113200) = true :=
  adaptiveCoverCheck_succ_of_children 9 (childHL thetaAboveCell01113200)
    e24KC2ThetaAboveLeaf0111320020 e24KC2ThetaAboveLeaf0111320021 e24KC2ThetaAboveLeaf0111320022
      e24KC2ThetaAboveLeaf0111320023

theorem e24KC2ThetaAboveNode011132003 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell01113200) = true :=
  adaptiveCoverCheck_succ_of_children 9 (childHH thetaAboveCell01113200)
    e24KC2ThetaAboveLeaf0111320030 e24KC2ThetaAboveLeaf0111320031 e24KC2ThetaAboveLeaf0111320032
      e24KC2ThetaAboveLeaf0111320033

theorem e24KC2ThetaAboveNode011132012 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell01113201) = true :=
  adaptiveCoverCheck_succ_of_children 9 (childHL thetaAboveCell01113201)
    e24KC2ThetaAboveLeaf0111320120 e24KC2ThetaAboveLeaf0111320121 e24KC2ThetaAboveLeaf0111320122
      e24KC2ThetaAboveLeaf0111320123

theorem e24KC2ThetaAboveNode011132013 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell01113201) = true :=
  adaptiveCoverCheck_succ_of_children 9 (childHH thetaAboveCell01113201)
    e24KC2ThetaAboveLeaf0111320130 e24KC2ThetaAboveLeaf0111320131 e24KC2ThetaAboveLeaf0111320132
      e24KC2ThetaAboveLeaf0111320133

theorem e24KC2ThetaAboveNode011132020 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell01113202) = true :=
  adaptiveCoverCheck_succ_of_children 9 (childLL thetaAboveCell01113202)
    e24KC2ThetaAboveLeaf0111320200 e24KC2ThetaAboveLeaf0111320201 e24KC2ThetaAboveLeaf0111320202
      e24KC2ThetaAboveLeaf0111320203

theorem e24KC2ThetaAboveNode011132021 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell01113202) = true :=
  adaptiveCoverCheck_succ_of_children 9 (childLH thetaAboveCell01113202)
    e24KC2ThetaAboveLeaf0111320210 e24KC2ThetaAboveLeaf0111320211 e24KC2ThetaAboveLeaf0111320212
      e24KC2ThetaAboveLeaf0111320213

theorem e24KC2ThetaAboveNode011132022 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell01113202) = true :=
  adaptiveCoverCheck_succ_of_children 9 (childHL thetaAboveCell01113202)
    e24KC2ThetaAboveLeaf0111320220 e24KC2ThetaAboveLeaf0111320221 e24KC2ThetaAboveLeaf0111320222
      e24KC2ThetaAboveLeaf0111320223

theorem e24KC2ThetaAboveNode011132023 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell01113202) = true :=
  adaptiveCoverCheck_succ_of_children 9 (childHH thetaAboveCell01113202)
    e24KC2ThetaAboveLeaf0111320230 e24KC2ThetaAboveLeaf0111320231 e24KC2ThetaAboveLeaf0111320232
      e24KC2ThetaAboveLeaf0111320233

theorem e24KC2ThetaAboveNode011132030 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell01113203) = true :=
  adaptiveCoverCheck_succ_of_children 9 (childLL thetaAboveCell01113203)
    e24KC2ThetaAboveLeaf0111320300 e24KC2ThetaAboveLeaf0111320301 e24KC2ThetaAboveLeaf0111320302
      e24KC2ThetaAboveLeaf0111320303

theorem e24KC2ThetaAboveNode011132031 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell01113203) = true :=
  adaptiveCoverCheck_succ_of_children 9 (childLH thetaAboveCell01113203)
    e24KC2ThetaAboveLeaf0111320310 e24KC2ThetaAboveLeaf0111320311 e24KC2ThetaAboveLeaf0111320312
      e24KC2ThetaAboveLeaf0111320313

theorem e24KC2ThetaAboveNode011132032 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell01113203) = true :=
  adaptiveCoverCheck_succ_of_children 9 (childHL thetaAboveCell01113203)
    e24KC2ThetaAboveLeaf0111320320 e24KC2ThetaAboveLeaf0111320321 e24KC2ThetaAboveLeaf0111320322
      e24KC2ThetaAboveLeaf0111320323

theorem e24KC2ThetaAboveNode011132033 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell01113203) = true :=
  adaptiveCoverCheck_succ_of_children 9 (childHH thetaAboveCell01113203)
    e24KC2ThetaAboveLeaf0111320330 e24KC2ThetaAboveLeaf0111320331 e24KC2ThetaAboveLeaf0111320332
      e24KC2ThetaAboveLeaf0111320333

theorem e24KC2ThetaAboveNode011132120 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell01113212) = true :=
  adaptiveCoverCheck_succ_of_children 9 (childLL thetaAboveCell01113212)
    e24KC2ThetaAboveLeaf0111321200 e24KC2ThetaAboveLeaf0111321201 e24KC2ThetaAboveLeaf0111321202
      e24KC2ThetaAboveLeaf0111321203

theorem e24KC2ThetaAboveNode011132121 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell01113212) = true :=
  adaptiveCoverCheck_succ_of_children 9 (childLH thetaAboveCell01113212)
    e24KC2ThetaAboveLeaf0111321210 e24KC2ThetaAboveLeaf0111321211 e24KC2ThetaAboveLeaf0111321212
      e24KC2ThetaAboveLeaf0111321213

theorem e24KC2ThetaAboveNode011132122 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell01113212) = true :=
  adaptiveCoverCheck_succ_of_children 9 (childHL thetaAboveCell01113212)
    e24KC2ThetaAboveLeaf0111321220 e24KC2ThetaAboveLeaf0111321221 e24KC2ThetaAboveLeaf0111321222
      e24KC2ThetaAboveLeaf0111321223

theorem e24KC2ThetaAboveNode011132123 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell01113212) = true :=
  adaptiveCoverCheck_succ_of_children 9 (childHH thetaAboveCell01113212)
    e24KC2ThetaAboveLeaf0111321230 e24KC2ThetaAboveLeaf0111321231 e24KC2ThetaAboveLeaf0111321232
      e24KC2ThetaAboveLeaf0111321233

theorem e24KC2ThetaAboveNode011132130 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell01113213) = true :=
  adaptiveCoverCheck_succ_of_children 9 (childLL thetaAboveCell01113213)
    e24KC2ThetaAboveLeaf0111321300 e24KC2ThetaAboveLeaf0111321301 e24KC2ThetaAboveLeaf0111321302
      e24KC2ThetaAboveLeaf0111321303

theorem e24KC2ThetaAboveNode011132131 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell01113213) = true :=
  adaptiveCoverCheck_succ_of_children 9 (childLH thetaAboveCell01113213)
    e24KC2ThetaAboveLeaf0111321310 e24KC2ThetaAboveLeaf0111321311 e24KC2ThetaAboveLeaf0111321312
      e24KC2ThetaAboveLeaf0111321313

theorem e24KC2ThetaAboveNode011132132 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell01113213) = true :=
  adaptiveCoverCheck_succ_of_children 9 (childHL thetaAboveCell01113213)
    e24KC2ThetaAboveLeaf0111321320 e24KC2ThetaAboveLeaf0111321321 e24KC2ThetaAboveLeaf0111321322
      e24KC2ThetaAboveLeaf0111321323

theorem e24KC2ThetaAboveNode011132133 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell01113213) = true :=
  adaptiveCoverCheck_succ_of_children 9 (childHH thetaAboveCell01113213)
    e24KC2ThetaAboveLeaf0111321330 e24KC2ThetaAboveLeaf0111321331 e24KC2ThetaAboveLeaf0111321332
      e24KC2ThetaAboveLeaf0111321333

theorem e24KC2ThetaAboveNode011133020 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell01113302) = true :=
  adaptiveCoverCheck_succ_of_children 9 (childLL thetaAboveCell01113302)
    e24KC2ThetaAboveLeaf0111330200 e24KC2ThetaAboveLeaf0111330201 e24KC2ThetaAboveLeaf0111330202
      e24KC2ThetaAboveLeaf0111330203

theorem e24KC2ThetaAboveNode011133021 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell01113302) = true :=
  adaptiveCoverCheck_succ_of_children 9 (childLH thetaAboveCell01113302)
    e24KC2ThetaAboveLeaf0111330210 e24KC2ThetaAboveLeaf0111330211 e24KC2ThetaAboveLeaf0111330212
      e24KC2ThetaAboveLeaf0111330213

theorem e24KC2ThetaAboveNode011133022 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell01113302) = true :=
  adaptiveCoverCheck_succ_of_children 9 (childHL thetaAboveCell01113302)
    e24KC2ThetaAboveLeaf0111330220 e24KC2ThetaAboveLeaf0111330221 e24KC2ThetaAboveLeaf0111330222
      e24KC2ThetaAboveLeaf0111330223

theorem e24KC2ThetaAboveNode011133023 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell01113302) = true :=
  adaptiveCoverCheck_succ_of_children 9 (childHH thetaAboveCell01113302)
    e24KC2ThetaAboveLeaf0111330230 e24KC2ThetaAboveLeaf0111330231 e24KC2ThetaAboveLeaf0111330232
      e24KC2ThetaAboveLeaf0111330233

theorem e24KC2ThetaAboveNode011133030 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell01113303) = true :=
  adaptiveCoverCheck_succ_of_children 9 (childLL thetaAboveCell01113303)
    e24KC2ThetaAboveLeaf0111330300 e24KC2ThetaAboveLeaf0111330301 e24KC2ThetaAboveLeaf0111330302
      e24KC2ThetaAboveLeaf0111330303

theorem e24KC2ThetaAboveNode011133031 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell01113303) = true :=
  adaptiveCoverCheck_succ_of_children 9 (childLH thetaAboveCell01113303)
    e24KC2ThetaAboveLeaf0111330310 e24KC2ThetaAboveLeaf0111330311 e24KC2ThetaAboveLeaf0111330312
      e24KC2ThetaAboveLeaf0111330313

theorem e24KC2ThetaAboveNode011133032 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell01113303) = true :=
  adaptiveCoverCheck_succ_of_children 9 (childHL thetaAboveCell01113303)
    e24KC2ThetaAboveLeaf0111330320 e24KC2ThetaAboveLeaf0111330321 e24KC2ThetaAboveLeaf0111330322
      e24KC2ThetaAboveLeaf0111330323

theorem e24KC2ThetaAboveNode011133033 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell01113303) = true :=
  adaptiveCoverCheck_succ_of_children 9 (childHH thetaAboveCell01113303)
    e24KC2ThetaAboveLeaf0111330330 e24KC2ThetaAboveLeaf0111330331 e24KC2ThetaAboveLeaf0111330332
      e24KC2ThetaAboveLeaf0111330333

theorem e24KC2ThetaAboveNode011133120 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell01113312) = true :=
  adaptiveCoverCheck_succ_of_children 9 (childLL thetaAboveCell01113312)
    e24KC2ThetaAboveLeaf0111331200 e24KC2ThetaAboveLeaf0111331201 e24KC2ThetaAboveLeaf0111331202
      e24KC2ThetaAboveLeaf0111331203

theorem e24KC2ThetaAboveNode011133121 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell01113312) = true :=
  adaptiveCoverCheck_succ_of_children 9 (childLH thetaAboveCell01113312)
    e24KC2ThetaAboveLeaf0111331210 e24KC2ThetaAboveLeaf0111331211 e24KC2ThetaAboveLeaf0111331212
      e24KC2ThetaAboveLeaf0111331213

theorem e24KC2ThetaAboveNode011133122 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell01113312) = true :=
  adaptiveCoverCheck_succ_of_children 9 (childHL thetaAboveCell01113312)
    e24KC2ThetaAboveLeaf0111331220 e24KC2ThetaAboveLeaf0111331221 e24KC2ThetaAboveLeaf0111331222
      e24KC2ThetaAboveLeaf0111331223

theorem e24KC2ThetaAboveNode011133123 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell01113312) = true :=
  adaptiveCoverCheck_succ_of_children 9 (childHH thetaAboveCell01113312)
    e24KC2ThetaAboveLeaf0111331230 e24KC2ThetaAboveLeaf0111331231 e24KC2ThetaAboveLeaf0111331232
      e24KC2ThetaAboveLeaf0111331233

theorem e24KC2ThetaAboveNode011133130 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell01113313) = true :=
  adaptiveCoverCheck_succ_of_children 9 (childLL thetaAboveCell01113313)
    e24KC2ThetaAboveLeaf0111331300 e24KC2ThetaAboveLeaf0111331301 e24KC2ThetaAboveLeaf0111331302
      e24KC2ThetaAboveLeaf0111331303

theorem e24KC2ThetaAboveNode011133131 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell01113313) = true :=
  adaptiveCoverCheck_succ_of_children 9 (childLH thetaAboveCell01113313)
    e24KC2ThetaAboveLeaf0111331310 e24KC2ThetaAboveLeaf0111331311 e24KC2ThetaAboveLeaf0111331312
      e24KC2ThetaAboveLeaf0111331313

theorem e24KC2ThetaAboveNode011133132 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell01113313) = true :=
  adaptiveCoverCheck_succ_of_children 9 (childHL thetaAboveCell01113313)
    e24KC2ThetaAboveLeaf0111331320 e24KC2ThetaAboveLeaf0111331321 e24KC2ThetaAboveLeaf0111331322
      e24KC2ThetaAboveLeaf0111331323

theorem e24KC2ThetaAboveNode011133133 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell01113313) = true :=
  adaptiveCoverCheck_succ_of_children 9 (childHH thetaAboveCell01113313)
    e24KC2ThetaAboveLeaf0111331330 e24KC2ThetaAboveLeaf0111331331 e24KC2ThetaAboveLeaf0111331332
      e24KC2ThetaAboveLeaf0111331333

theorem e24KC2ThetaAboveNode100022020 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell10002202) = true :=
  adaptiveCoverCheck_succ_of_children 9 (childLL thetaAboveCell10002202)
    e24KC2ThetaAboveLeaf1000220200 e24KC2ThetaAboveLeaf1000220201 e24KC2ThetaAboveLeaf1000220202
      e24KC2ThetaAboveLeaf1000220203

theorem e24KC2ThetaAboveNode100022021 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell10002202) = true :=
  adaptiveCoverCheck_succ_of_children 9 (childLH thetaAboveCell10002202)
    e24KC2ThetaAboveLeaf1000220210 e24KC2ThetaAboveLeaf1000220211 e24KC2ThetaAboveLeaf1000220212
      e24KC2ThetaAboveLeaf1000220213

theorem e24KC2ThetaAboveNode100022022 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell10002202) = true :=
  adaptiveCoverCheck_succ_of_children 9 (childHL thetaAboveCell10002202)
    e24KC2ThetaAboveLeaf1000220220 e24KC2ThetaAboveLeaf1000220221 e24KC2ThetaAboveLeaf1000220222
      e24KC2ThetaAboveLeaf1000220223

theorem e24KC2ThetaAboveNode100022023 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell10002202) = true :=
  adaptiveCoverCheck_succ_of_children 9 (childHH thetaAboveCell10002202)
    e24KC2ThetaAboveLeaf1000220230 e24KC2ThetaAboveLeaf1000220231 e24KC2ThetaAboveLeaf1000220232
      e24KC2ThetaAboveLeaf1000220233

theorem e24KC2ThetaAboveNode100022030 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell10002203) = true :=
  adaptiveCoverCheck_succ_of_children 9 (childLL thetaAboveCell10002203)
    e24KC2ThetaAboveLeaf1000220300 e24KC2ThetaAboveLeaf1000220301 e24KC2ThetaAboveLeaf1000220302
      e24KC2ThetaAboveLeaf1000220303

theorem e24KC2ThetaAboveNode100022031 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell10002203) = true :=
  adaptiveCoverCheck_succ_of_children 9 (childLH thetaAboveCell10002203)
    e24KC2ThetaAboveLeaf1000220310 e24KC2ThetaAboveLeaf1000220311 e24KC2ThetaAboveLeaf1000220312
      e24KC2ThetaAboveLeaf1000220313

theorem e24KC2ThetaAboveNode100022032 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell10002203) = true :=
  adaptiveCoverCheck_succ_of_children 9 (childHL thetaAboveCell10002203)
    e24KC2ThetaAboveLeaf1000220320 e24KC2ThetaAboveLeaf1000220321 e24KC2ThetaAboveLeaf1000220322
      e24KC2ThetaAboveLeaf1000220323

theorem e24KC2ThetaAboveNode100022033 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell10002203) = true :=
  adaptiveCoverCheck_succ_of_children 9 (childHH thetaAboveCell10002203)
    e24KC2ThetaAboveLeaf1000220330 e24KC2ThetaAboveLeaf1000220331 e24KC2ThetaAboveLeaf1000220332
      e24KC2ThetaAboveLeaf1000220333

theorem e24KC2ThetaAboveNode100022120 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell10002212) = true :=
  adaptiveCoverCheck_succ_of_children 9 (childLL thetaAboveCell10002212)
    e24KC2ThetaAboveLeaf1000221200 e24KC2ThetaAboveLeaf1000221201 e24KC2ThetaAboveLeaf1000221202
      e24KC2ThetaAboveLeaf1000221203

theorem e24KC2ThetaAboveNode100022121 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell10002212) = true :=
  adaptiveCoverCheck_succ_of_children 9 (childLH thetaAboveCell10002212)
    e24KC2ThetaAboveLeaf1000221210 e24KC2ThetaAboveLeaf1000221211 e24KC2ThetaAboveLeaf1000221212
      e24KC2ThetaAboveLeaf1000221213

theorem e24KC2ThetaAboveNode100022122 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell10002212) = true :=
  adaptiveCoverCheck_succ_of_children 9 (childHL thetaAboveCell10002212)
    e24KC2ThetaAboveLeaf1000221220 e24KC2ThetaAboveLeaf1000221221 e24KC2ThetaAboveLeaf1000221222
      e24KC2ThetaAboveLeaf1000221223

theorem e24KC2ThetaAboveNode100022123 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell10002212) = true :=
  adaptiveCoverCheck_succ_of_children 9 (childHH thetaAboveCell10002212)
    e24KC2ThetaAboveLeaf1000221230 e24KC2ThetaAboveLeaf1000221231 e24KC2ThetaAboveLeaf1000221232
      e24KC2ThetaAboveLeaf1000221233

theorem e24KC2ThetaAboveNode100022130 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell10002213) = true :=
  adaptiveCoverCheck_succ_of_children 9 (childLL thetaAboveCell10002213)
    e24KC2ThetaAboveLeaf1000221300 e24KC2ThetaAboveLeaf1000221301 e24KC2ThetaAboveLeaf1000221302
      e24KC2ThetaAboveLeaf1000221303

theorem e24KC2ThetaAboveNode100022131 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell10002213) = true :=
  adaptiveCoverCheck_succ_of_children 9 (childLH thetaAboveCell10002213)
    e24KC2ThetaAboveLeaf1000221310 e24KC2ThetaAboveLeaf1000221311 e24KC2ThetaAboveLeaf1000221312
      e24KC2ThetaAboveLeaf1000221313

theorem e24KC2ThetaAboveNode100022132 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell10002213) = true :=
  adaptiveCoverCheck_succ_of_children 9 (childHL thetaAboveCell10002213)
    e24KC2ThetaAboveLeaf1000221320 e24KC2ThetaAboveLeaf1000221321 e24KC2ThetaAboveLeaf1000221322
      e24KC2ThetaAboveLeaf1000221323

theorem e24KC2ThetaAboveNode100022133 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell10002213) = true :=
  adaptiveCoverCheck_succ_of_children 9 (childHH thetaAboveCell10002213)
    e24KC2ThetaAboveLeaf1000221330 e24KC2ThetaAboveLeaf1000221331 e24KC2ThetaAboveLeaf1000221332
      e24KC2ThetaAboveLeaf1000221333

theorem e24KC2ThetaAboveNode100023020 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell10002302) = true :=
  adaptiveCoverCheck_succ_of_children 9 (childLL thetaAboveCell10002302)
    e24KC2ThetaAboveLeaf1000230200 e24KC2ThetaAboveLeaf1000230201 e24KC2ThetaAboveLeaf1000230202
      e24KC2ThetaAboveLeaf1000230203

theorem e24KC2ThetaAboveNode100023021 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell10002302) = true :=
  adaptiveCoverCheck_succ_of_children 9 (childLH thetaAboveCell10002302)
    e24KC2ThetaAboveLeaf1000230210 e24KC2ThetaAboveLeaf1000230211 e24KC2ThetaAboveLeaf1000230212
      e24KC2ThetaAboveLeaf1000230213

theorem e24KC2ThetaAboveNode100023022 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell10002302) = true :=
  adaptiveCoverCheck_succ_of_children 9 (childHL thetaAboveCell10002302)
    e24KC2ThetaAboveLeaf1000230220 e24KC2ThetaAboveLeaf1000230221 e24KC2ThetaAboveLeaf1000230222
      e24KC2ThetaAboveLeaf1000230223

theorem e24KC2ThetaAboveNode100023023 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell10002302) = true :=
  adaptiveCoverCheck_succ_of_children 9 (childHH thetaAboveCell10002302)
    e24KC2ThetaAboveLeaf1000230230 e24KC2ThetaAboveLeaf1000230231 e24KC2ThetaAboveLeaf1000230232
      e24KC2ThetaAboveLeaf1000230233

theorem e24KC2ThetaAboveNode100023030 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell10002303) = true :=
  adaptiveCoverCheck_succ_of_children 9 (childLL thetaAboveCell10002303)
    e24KC2ThetaAboveLeaf1000230300 e24KC2ThetaAboveLeaf1000230301 e24KC2ThetaAboveLeaf1000230302
      e24KC2ThetaAboveLeaf1000230303

theorem e24KC2ThetaAboveNode100023031 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell10002303) = true :=
  adaptiveCoverCheck_succ_of_children 9 (childLH thetaAboveCell10002303)
    e24KC2ThetaAboveLeaf1000230310 e24KC2ThetaAboveLeaf1000230311 e24KC2ThetaAboveLeaf1000230312
      e24KC2ThetaAboveLeaf1000230313

theorem e24KC2ThetaAboveNode100023032 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell10002303) = true :=
  adaptiveCoverCheck_succ_of_children 9 (childHL thetaAboveCell10002303)
    e24KC2ThetaAboveLeaf1000230320 e24KC2ThetaAboveLeaf1000230321 e24KC2ThetaAboveLeaf1000230322
      e24KC2ThetaAboveLeaf1000230323

theorem e24KC2ThetaAboveNode100023033 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell10002303) = true :=
  adaptiveCoverCheck_succ_of_children 9 (childHH thetaAboveCell10002303)
    e24KC2ThetaAboveLeaf1000230330 e24KC2ThetaAboveLeaf1000230331 e24KC2ThetaAboveLeaf1000230332
      e24KC2ThetaAboveLeaf1000230333

theorem e24KC2ThetaAboveNode100023120 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell10002312) = true :=
  adaptiveCoverCheck_succ_of_children 9 (childLL thetaAboveCell10002312)
    e24KC2ThetaAboveLeaf1000231200 e24KC2ThetaAboveLeaf1000231201 e24KC2ThetaAboveLeaf1000231202
      e24KC2ThetaAboveLeaf1000231203

theorem e24KC2ThetaAboveNode100023121 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell10002312) = true :=
  adaptiveCoverCheck_succ_of_children 9 (childLH thetaAboveCell10002312)
    e24KC2ThetaAboveLeaf1000231210 e24KC2ThetaAboveLeaf1000231211 e24KC2ThetaAboveLeaf1000231212
      e24KC2ThetaAboveLeaf1000231213

theorem e24KC2ThetaAboveNode100023122 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell10002312) = true :=
  adaptiveCoverCheck_succ_of_children 9 (childHL thetaAboveCell10002312)
    e24KC2ThetaAboveLeaf1000231220 e24KC2ThetaAboveLeaf1000231221 e24KC2ThetaAboveLeaf1000231222
      e24KC2ThetaAboveLeaf1000231223

theorem e24KC2ThetaAboveNode100023123 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell10002312) = true :=
  adaptiveCoverCheck_succ_of_children 9 (childHH thetaAboveCell10002312)
    e24KC2ThetaAboveLeaf1000231230 e24KC2ThetaAboveLeaf1000231231 e24KC2ThetaAboveLeaf1000231232
      e24KC2ThetaAboveLeaf1000231233

theorem e24KC2ThetaAboveNode100023130 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell10002313) = true :=
  adaptiveCoverCheck_succ_of_children 9 (childLL thetaAboveCell10002313)
    e24KC2ThetaAboveLeaf1000231300 e24KC2ThetaAboveLeaf1000231301 e24KC2ThetaAboveLeaf1000231302
      e24KC2ThetaAboveLeaf1000231303

theorem e24KC2ThetaAboveNode100023131 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell10002313) = true :=
  adaptiveCoverCheck_succ_of_children 9 (childLH thetaAboveCell10002313)
    e24KC2ThetaAboveLeaf1000231310 e24KC2ThetaAboveLeaf1000231311 e24KC2ThetaAboveLeaf1000231312
      e24KC2ThetaAboveLeaf1000231313

theorem e24KC2ThetaAboveNode100023132 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell10002313) = true :=
  adaptiveCoverCheck_succ_of_children 9 (childHL thetaAboveCell10002313)
    e24KC2ThetaAboveLeaf1000231320 e24KC2ThetaAboveLeaf1000231321 e24KC2ThetaAboveLeaf1000231322
      e24KC2ThetaAboveLeaf1000231323

theorem e24KC2ThetaAboveNode100023133 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell10002313) = true :=
  adaptiveCoverCheck_succ_of_children 9 (childHH thetaAboveCell10002313)
    e24KC2ThetaAboveLeaf1000231330 e24KC2ThetaAboveLeaf1000231331 e24KC2ThetaAboveLeaf1000231332
      e24KC2ThetaAboveLeaf1000231333

theorem e24KC2ThetaAboveNode100032020 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell10003202) = true :=
  adaptiveCoverCheck_succ_of_children 9 (childLL thetaAboveCell10003202)
    e24KC2ThetaAboveLeaf1000320200 e24KC2ThetaAboveLeaf1000320201 e24KC2ThetaAboveLeaf1000320202
      e24KC2ThetaAboveLeaf1000320203

theorem e24KC2ThetaAboveNode100032021 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell10003202) = true :=
  adaptiveCoverCheck_succ_of_children 9 (childLH thetaAboveCell10003202)
    e24KC2ThetaAboveLeaf1000320210 e24KC2ThetaAboveLeaf1000320211 e24KC2ThetaAboveLeaf1000320212
      e24KC2ThetaAboveLeaf1000320213

theorem e24KC2ThetaAboveNode100032022 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell10003202) = true :=
  adaptiveCoverCheck_succ_of_children 9 (childHL thetaAboveCell10003202)
    e24KC2ThetaAboveLeaf1000320220 e24KC2ThetaAboveLeaf1000320221 e24KC2ThetaAboveLeaf1000320222
      e24KC2ThetaAboveLeaf1000320223

theorem e24KC2ThetaAboveNode100032023 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell10003202) = true :=
  adaptiveCoverCheck_succ_of_children 9 (childHH thetaAboveCell10003202)
    e24KC2ThetaAboveLeaf1000320230 e24KC2ThetaAboveLeaf1000320231 e24KC2ThetaAboveLeaf1000320232
      e24KC2ThetaAboveLeaf1000320233

theorem e24KC2ThetaAboveNode100032030 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell10003203) = true :=
  adaptiveCoverCheck_succ_of_children 9 (childLL thetaAboveCell10003203)
    e24KC2ThetaAboveLeaf1000320300 e24KC2ThetaAboveLeaf1000320301 e24KC2ThetaAboveLeaf1000320302
      e24KC2ThetaAboveLeaf1000320303

theorem e24KC2ThetaAboveNode100032031 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell10003203) = true :=
  adaptiveCoverCheck_succ_of_children 9 (childLH thetaAboveCell10003203)
    e24KC2ThetaAboveLeaf1000320310 e24KC2ThetaAboveLeaf1000320311 e24KC2ThetaAboveLeaf1000320312
      e24KC2ThetaAboveLeaf1000320313

theorem e24KC2ThetaAboveNode100032032 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell10003203) = true :=
  adaptiveCoverCheck_succ_of_children 9 (childHL thetaAboveCell10003203)
    e24KC2ThetaAboveLeaf1000320320 e24KC2ThetaAboveLeaf1000320321 e24KC2ThetaAboveLeaf1000320322
      e24KC2ThetaAboveLeaf1000320323

theorem e24KC2ThetaAboveNode100032033 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell10003203) = true :=
  adaptiveCoverCheck_succ_of_children 9 (childHH thetaAboveCell10003203)
    e24KC2ThetaAboveLeaf1000320330 e24KC2ThetaAboveLeaf1000320331 e24KC2ThetaAboveLeaf1000320332
      e24KC2ThetaAboveLeaf1000320333

theorem e24KC2ThetaAboveNode100032120 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell10003212) = true :=
  adaptiveCoverCheck_succ_of_children 9 (childLL thetaAboveCell10003212)
    e24KC2ThetaAboveLeaf1000321200 e24KC2ThetaAboveLeaf1000321201 e24KC2ThetaAboveLeaf1000321202
      e24KC2ThetaAboveLeaf1000321203

theorem e24KC2ThetaAboveNode100032121 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell10003212) = true :=
  adaptiveCoverCheck_succ_of_children 9 (childLH thetaAboveCell10003212)
    e24KC2ThetaAboveLeaf1000321210 e24KC2ThetaAboveLeaf1000321211 e24KC2ThetaAboveLeaf1000321212
      e24KC2ThetaAboveLeaf1000321213

theorem e24KC2ThetaAboveNode100032122 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell10003212) = true :=
  adaptiveCoverCheck_succ_of_children 9 (childHL thetaAboveCell10003212)
    e24KC2ThetaAboveLeaf1000321220 e24KC2ThetaAboveLeaf1000321221 e24KC2ThetaAboveLeaf1000321222
      e24KC2ThetaAboveLeaf1000321223

theorem e24KC2ThetaAboveNode100032123 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell10003212) = true :=
  adaptiveCoverCheck_succ_of_children 9 (childHH thetaAboveCell10003212)
    e24KC2ThetaAboveLeaf1000321230 e24KC2ThetaAboveLeaf1000321231 e24KC2ThetaAboveLeaf1000321232
      e24KC2ThetaAboveLeaf1000321233

theorem e24KC2ThetaAboveNode100032130 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell10003213) = true :=
  adaptiveCoverCheck_succ_of_children 9 (childLL thetaAboveCell10003213)
    e24KC2ThetaAboveLeaf1000321300 e24KC2ThetaAboveLeaf1000321301 e24KC2ThetaAboveLeaf1000321302
      e24KC2ThetaAboveLeaf1000321303

theorem e24KC2ThetaAboveNode100032131 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell10003213) = true :=
  adaptiveCoverCheck_succ_of_children 9 (childLH thetaAboveCell10003213)
    e24KC2ThetaAboveLeaf1000321310 e24KC2ThetaAboveLeaf1000321311 e24KC2ThetaAboveLeaf1000321312
      e24KC2ThetaAboveLeaf1000321313

theorem e24KC2ThetaAboveNode100032132 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell10003213) = true :=
  adaptiveCoverCheck_succ_of_children 9 (childHL thetaAboveCell10003213)
    e24KC2ThetaAboveLeaf1000321320 e24KC2ThetaAboveLeaf1000321321 e24KC2ThetaAboveLeaf1000321322
      e24KC2ThetaAboveLeaf1000321323

theorem e24KC2ThetaAboveNode100032133 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell10003213) = true :=
  adaptiveCoverCheck_succ_of_children 9 (childHH thetaAboveCell10003213)
    e24KC2ThetaAboveLeaf1000321330 e24KC2ThetaAboveLeaf1000321331 e24KC2ThetaAboveLeaf1000321332
      e24KC2ThetaAboveLeaf1000321333

theorem e24KC2ThetaAboveNode100033020 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell10003302) = true :=
  adaptiveCoverCheck_succ_of_children 9 (childLL thetaAboveCell10003302)
    e24KC2ThetaAboveLeaf1000330200 e24KC2ThetaAboveLeaf1000330201 e24KC2ThetaAboveLeaf1000330202
      e24KC2ThetaAboveLeaf1000330203

theorem e24KC2ThetaAboveNode100033021 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell10003302) = true :=
  adaptiveCoverCheck_succ_of_children 9 (childLH thetaAboveCell10003302)
    e24KC2ThetaAboveLeaf1000330210 e24KC2ThetaAboveLeaf1000330211 e24KC2ThetaAboveLeaf1000330212
      e24KC2ThetaAboveLeaf1000330213

theorem e24KC2ThetaAboveNode100033022 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell10003302) = true :=
  adaptiveCoverCheck_succ_of_children 9 (childHL thetaAboveCell10003302)
    e24KC2ThetaAboveLeaf1000330220 e24KC2ThetaAboveLeaf1000330221 e24KC2ThetaAboveLeaf1000330222
      e24KC2ThetaAboveLeaf1000330223

theorem e24KC2ThetaAboveNode100033023 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell10003302) = true :=
  adaptiveCoverCheck_succ_of_children 9 (childHH thetaAboveCell10003302)
    e24KC2ThetaAboveLeaf1000330230 e24KC2ThetaAboveLeaf1000330231 e24KC2ThetaAboveLeaf1000330232
      e24KC2ThetaAboveLeaf1000330233

theorem e24KC2ThetaAboveNode100033030 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell10003303) = true :=
  adaptiveCoverCheck_succ_of_children 9 (childLL thetaAboveCell10003303)
    e24KC2ThetaAboveLeaf1000330300 e24KC2ThetaAboveLeaf1000330301 e24KC2ThetaAboveLeaf1000330302
      e24KC2ThetaAboveLeaf1000330303

theorem e24KC2ThetaAboveNode100033031 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell10003303) = true :=
  adaptiveCoverCheck_succ_of_children 9 (childLH thetaAboveCell10003303)
    e24KC2ThetaAboveLeaf1000330310 e24KC2ThetaAboveLeaf1000330311 e24KC2ThetaAboveLeaf1000330312
      e24KC2ThetaAboveLeaf1000330313

theorem e24KC2ThetaAboveNode100033032 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell10003303) = true :=
  adaptiveCoverCheck_succ_of_children 9 (childHL thetaAboveCell10003303)
    e24KC2ThetaAboveLeaf1000330320 e24KC2ThetaAboveLeaf1000330321 e24KC2ThetaAboveLeaf1000330322
      e24KC2ThetaAboveLeaf1000330323

theorem e24KC2ThetaAboveNode100033033 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell10003303) = true :=
  adaptiveCoverCheck_succ_of_children 9 (childHH thetaAboveCell10003303)
    e24KC2ThetaAboveLeaf1000330330 e24KC2ThetaAboveLeaf1000330331 e24KC2ThetaAboveLeaf1000330332
      e24KC2ThetaAboveLeaf1000330333

theorem e24KC2ThetaAboveNode100033120 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell10003312) = true :=
  adaptiveCoverCheck_succ_of_children 9 (childLL thetaAboveCell10003312)
    e24KC2ThetaAboveLeaf1000331200 e24KC2ThetaAboveLeaf1000331201 e24KC2ThetaAboveLeaf1000331202
      e24KC2ThetaAboveLeaf1000331203

theorem e24KC2ThetaAboveNode100033121 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell10003312) = true :=
  adaptiveCoverCheck_succ_of_children 9 (childLH thetaAboveCell10003312)
    e24KC2ThetaAboveLeaf1000331210 e24KC2ThetaAboveLeaf1000331211 e24KC2ThetaAboveLeaf1000331212
      e24KC2ThetaAboveLeaf1000331213

theorem e24KC2ThetaAboveNode100033122 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell10003312) = true :=
  adaptiveCoverCheck_succ_of_children 9 (childHL thetaAboveCell10003312)
    e24KC2ThetaAboveLeaf1000331220 e24KC2ThetaAboveLeaf1000331221 e24KC2ThetaAboveLeaf1000331222
      e24KC2ThetaAboveLeaf1000331223

theorem e24KC2ThetaAboveNode100033123 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell10003312) = true :=
  adaptiveCoverCheck_succ_of_children 9 (childHH thetaAboveCell10003312)
    e24KC2ThetaAboveLeaf1000331230 e24KC2ThetaAboveLeaf1000331231 e24KC2ThetaAboveLeaf1000331232
      e24KC2ThetaAboveLeaf1000331233

theorem e24KC2ThetaAboveNode100033130 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell10003313) = true :=
  adaptiveCoverCheck_succ_of_children 9 (childLL thetaAboveCell10003313)
    e24KC2ThetaAboveLeaf1000331300 e24KC2ThetaAboveLeaf1000331301 e24KC2ThetaAboveLeaf1000331302
      e24KC2ThetaAboveLeaf1000331303

theorem e24KC2ThetaAboveNode100033131 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell10003313) = true :=
  adaptiveCoverCheck_succ_of_children 9 (childLH thetaAboveCell10003313)
    e24KC2ThetaAboveLeaf1000331310 e24KC2ThetaAboveLeaf1000331311 e24KC2ThetaAboveLeaf1000331312
      e24KC2ThetaAboveLeaf1000331313

theorem e24KC2ThetaAboveNode100033132 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell10003313) = true :=
  adaptiveCoverCheck_succ_of_children 9 (childHL thetaAboveCell10003313)
    e24KC2ThetaAboveLeaf1000331320 e24KC2ThetaAboveLeaf1000331321 e24KC2ThetaAboveLeaf1000331322
      e24KC2ThetaAboveLeaf1000331323

theorem e24KC2ThetaAboveNode100033133 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell10003313) = true :=
  adaptiveCoverCheck_succ_of_children 9 (childHH thetaAboveCell10003313)
    e24KC2ThetaAboveLeaf1000331330 e24KC2ThetaAboveLeaf1000331331 e24KC2ThetaAboveLeaf1000331332
      e24KC2ThetaAboveLeaf1000331333

theorem e24KC2ThetaAboveNode100033311 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell10003331) = true :=
  adaptiveCoverCheck_succ_of_children 9 (childLH thetaAboveCell10003331)
    e24KC2ThetaAboveLeaf1000333110 e24KC2ThetaAboveLeaf1000333111 e24KC2ThetaAboveLeaf1000333112
      e24KC2ThetaAboveLeaf1000333113

theorem e24KC2ThetaAboveNode100122020 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell10012202) = true :=
  adaptiveCoverCheck_succ_of_children 9 (childLL thetaAboveCell10012202)
    e24KC2ThetaAboveLeaf1001220200 e24KC2ThetaAboveLeaf1001220201 e24KC2ThetaAboveLeaf1001220202
      e24KC2ThetaAboveLeaf1001220203

theorem e24KC2ThetaAboveNode100122021 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell10012202) = true :=
  adaptiveCoverCheck_succ_of_children 9 (childLH thetaAboveCell10012202)
    e24KC2ThetaAboveLeaf1001220210 e24KC2ThetaAboveLeaf1001220211 e24KC2ThetaAboveLeaf1001220212
      e24KC2ThetaAboveLeaf1001220213

theorem e24KC2ThetaAboveNode100122022 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell10012202) = true :=
  adaptiveCoverCheck_succ_of_children 9 (childHL thetaAboveCell10012202)
    e24KC2ThetaAboveLeaf1001220220 e24KC2ThetaAboveLeaf1001220221 e24KC2ThetaAboveLeaf1001220222
      e24KC2ThetaAboveLeaf1001220223

theorem e24KC2ThetaAboveNode100122023 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell10012202) = true :=
  adaptiveCoverCheck_succ_of_children 9 (childHH thetaAboveCell10012202)
    e24KC2ThetaAboveLeaf1001220230 e24KC2ThetaAboveLeaf1001220231 e24KC2ThetaAboveLeaf1001220232
      e24KC2ThetaAboveLeaf1001220233

theorem e24KC2ThetaAboveNode100122030 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell10012203) = true :=
  adaptiveCoverCheck_succ_of_children 9 (childLL thetaAboveCell10012203)
    e24KC2ThetaAboveLeaf1001220300 e24KC2ThetaAboveLeaf1001220301 e24KC2ThetaAboveLeaf1001220302
      e24KC2ThetaAboveLeaf1001220303

theorem e24KC2ThetaAboveNode100122031 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell10012203) = true :=
  adaptiveCoverCheck_succ_of_children 9 (childLH thetaAboveCell10012203)
    e24KC2ThetaAboveLeaf1001220310 e24KC2ThetaAboveLeaf1001220311 e24KC2ThetaAboveLeaf1001220312
      e24KC2ThetaAboveLeaf1001220313

theorem e24KC2ThetaAboveNode100122032 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell10012203) = true :=
  adaptiveCoverCheck_succ_of_children 9 (childHL thetaAboveCell10012203)
    e24KC2ThetaAboveLeaf1001220320 e24KC2ThetaAboveLeaf1001220321 e24KC2ThetaAboveLeaf1001220322
      e24KC2ThetaAboveLeaf1001220323

theorem e24KC2ThetaAboveNode100122033 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell10012203) = true :=
  adaptiveCoverCheck_succ_of_children 9 (childHH thetaAboveCell10012203)
    e24KC2ThetaAboveLeaf1001220330 e24KC2ThetaAboveLeaf1001220331 e24KC2ThetaAboveLeaf1001220332
      e24KC2ThetaAboveLeaf1001220333

theorem e24KC2ThetaAboveNode100122120 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell10012212) = true :=
  adaptiveCoverCheck_succ_of_children 9 (childLL thetaAboveCell10012212)
    e24KC2ThetaAboveLeaf1001221200 e24KC2ThetaAboveLeaf1001221201 e24KC2ThetaAboveLeaf1001221202
      e24KC2ThetaAboveLeaf1001221203

theorem e24KC2ThetaAboveNode100122121 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell10012212) = true :=
  adaptiveCoverCheck_succ_of_children 9 (childLH thetaAboveCell10012212)
    e24KC2ThetaAboveLeaf1001221210 e24KC2ThetaAboveLeaf1001221211 e24KC2ThetaAboveLeaf1001221212
      e24KC2ThetaAboveLeaf1001221213

theorem e24KC2ThetaAboveNode100122122 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell10012212) = true :=
  adaptiveCoverCheck_succ_of_children 9 (childHL thetaAboveCell10012212)
    e24KC2ThetaAboveLeaf1001221220 e24KC2ThetaAboveLeaf1001221221 e24KC2ThetaAboveLeaf1001221222
      e24KC2ThetaAboveLeaf1001221223

theorem e24KC2ThetaAboveNode100122123 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell10012212) = true :=
  adaptiveCoverCheck_succ_of_children 9 (childHH thetaAboveCell10012212)
    e24KC2ThetaAboveLeaf1001221230 e24KC2ThetaAboveLeaf1001221231 e24KC2ThetaAboveLeaf1001221232
      e24KC2ThetaAboveLeaf1001221233

theorem e24KC2ThetaAboveNode100122130 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell10012213) = true :=
  adaptiveCoverCheck_succ_of_children 9 (childLL thetaAboveCell10012213)
    e24KC2ThetaAboveLeaf1001221300 e24KC2ThetaAboveLeaf1001221301 e24KC2ThetaAboveLeaf1001221302
      e24KC2ThetaAboveLeaf1001221303

theorem e24KC2ThetaAboveNode100122131 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell10012213) = true :=
  adaptiveCoverCheck_succ_of_children 9 (childLH thetaAboveCell10012213)
    e24KC2ThetaAboveLeaf1001221310 e24KC2ThetaAboveLeaf1001221311 e24KC2ThetaAboveLeaf1001221312
      e24KC2ThetaAboveLeaf1001221313

theorem e24KC2ThetaAboveNode100122132 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell10012213) = true :=
  adaptiveCoverCheck_succ_of_children 9 (childHL thetaAboveCell10012213)
    e24KC2ThetaAboveLeaf1001221320 e24KC2ThetaAboveLeaf1001221321 e24KC2ThetaAboveLeaf1001221322
      e24KC2ThetaAboveLeaf1001221323

theorem e24KC2ThetaAboveNode100122133 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell10012213) = true :=
  adaptiveCoverCheck_succ_of_children 9 (childHH thetaAboveCell10012213)
    e24KC2ThetaAboveLeaf1001221330 e24KC2ThetaAboveLeaf1001221331 e24KC2ThetaAboveLeaf1001221332
      e24KC2ThetaAboveLeaf1001221333

theorem e24KC2ThetaAboveNode100122200 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell10012220) = true :=
  adaptiveCoverCheck_succ_of_children 9 (childLL thetaAboveCell10012220)
    e24KC2ThetaAboveLeaf1001222000 e24KC2ThetaAboveLeaf1001222001 e24KC2ThetaAboveLeaf1001222002
      e24KC2ThetaAboveLeaf1001222003

theorem e24KC2ThetaAboveNode100122201 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell10012220) = true :=
  adaptiveCoverCheck_succ_of_children 9 (childLH thetaAboveCell10012220)
    e24KC2ThetaAboveLeaf1001222010 e24KC2ThetaAboveLeaf1001222011 e24KC2ThetaAboveLeaf1001222012
      e24KC2ThetaAboveLeaf1001222013

theorem e24KC2ThetaAboveNode100122210 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell10012221) = true :=
  adaptiveCoverCheck_succ_of_children 9 (childLL thetaAboveCell10012221)
    e24KC2ThetaAboveLeaf1001222100 e24KC2ThetaAboveLeaf1001222101 e24KC2ThetaAboveLeaf1001222102
      e24KC2ThetaAboveLeaf1001222103

theorem e24KC2ThetaAboveNode100122211 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell10012221) = true :=
  adaptiveCoverCheck_succ_of_children 9 (childLH thetaAboveCell10012221)
    e24KC2ThetaAboveLeaf1001222110 e24KC2ThetaAboveLeaf1001222111 e24KC2ThetaAboveLeaf1001222112
      e24KC2ThetaAboveLeaf1001222113

theorem e24KC2ThetaAboveNode100122300 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell10012230) = true :=
  adaptiveCoverCheck_succ_of_children 9 (childLL thetaAboveCell10012230)
    e24KC2ThetaAboveLeaf1001223000 e24KC2ThetaAboveLeaf1001223001 e24KC2ThetaAboveLeaf1001223002
      e24KC2ThetaAboveLeaf1001223003

theorem e24KC2ThetaAboveNode100122301 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell10012230) = true :=
  adaptiveCoverCheck_succ_of_children 9 (childLH thetaAboveCell10012230)
    e24KC2ThetaAboveLeaf1001223010 e24KC2ThetaAboveLeaf1001223011 e24KC2ThetaAboveLeaf1001223012
      e24KC2ThetaAboveLeaf1001223013

theorem e24KC2ThetaAboveNode100122310 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell10012231) = true :=
  adaptiveCoverCheck_succ_of_children 9 (childLL thetaAboveCell10012231)
    e24KC2ThetaAboveLeaf1001223100 e24KC2ThetaAboveLeaf1001223101 e24KC2ThetaAboveLeaf1001223102
      e24KC2ThetaAboveLeaf1001223103

theorem e24KC2ThetaAboveNode100122311 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell10012231) = true :=
  adaptiveCoverCheck_succ_of_children 9 (childLH thetaAboveCell10012231)
    e24KC2ThetaAboveLeaf1001223110 e24KC2ThetaAboveLeaf1001223111 e24KC2ThetaAboveLeaf1001223112
      e24KC2ThetaAboveLeaf1001223113

theorem e24KC2ThetaAboveNode100123020 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell10012302) = true :=
  adaptiveCoverCheck_succ_of_children 9 (childLL thetaAboveCell10012302)
    e24KC2ThetaAboveLeaf1001230200 e24KC2ThetaAboveLeaf1001230201 e24KC2ThetaAboveLeaf1001230202
      e24KC2ThetaAboveLeaf1001230203

theorem e24KC2ThetaAboveNode100123021 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell10012302) = true :=
  adaptiveCoverCheck_succ_of_children 9 (childLH thetaAboveCell10012302)
    e24KC2ThetaAboveLeaf1001230210 e24KC2ThetaAboveLeaf1001230211 e24KC2ThetaAboveLeaf1001230212
      e24KC2ThetaAboveLeaf1001230213

theorem e24KC2ThetaAboveNode100123022 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell10012302) = true :=
  adaptiveCoverCheck_succ_of_children 9 (childHL thetaAboveCell10012302)
    e24KC2ThetaAboveLeaf1001230220 e24KC2ThetaAboveLeaf1001230221 e24KC2ThetaAboveLeaf1001230222
      e24KC2ThetaAboveLeaf1001230223

theorem e24KC2ThetaAboveNode100123023 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell10012302) = true :=
  adaptiveCoverCheck_succ_of_children 9 (childHH thetaAboveCell10012302)
    e24KC2ThetaAboveLeaf1001230230 e24KC2ThetaAboveLeaf1001230231 e24KC2ThetaAboveLeaf1001230232
      e24KC2ThetaAboveLeaf1001230233

theorem e24KC2ThetaAboveNode100123030 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell10012303) = true :=
  adaptiveCoverCheck_succ_of_children 9 (childLL thetaAboveCell10012303)
    e24KC2ThetaAboveLeaf1001230300 e24KC2ThetaAboveLeaf1001230301 e24KC2ThetaAboveLeaf1001230302
      e24KC2ThetaAboveLeaf1001230303

theorem e24KC2ThetaAboveNode100123031 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell10012303) = true :=
  adaptiveCoverCheck_succ_of_children 9 (childLH thetaAboveCell10012303)
    e24KC2ThetaAboveLeaf1001230310 e24KC2ThetaAboveLeaf1001230311 e24KC2ThetaAboveLeaf1001230312
      e24KC2ThetaAboveLeaf1001230313

theorem e24KC2ThetaAboveNode100123032 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell10012303) = true :=
  adaptiveCoverCheck_succ_of_children 9 (childHL thetaAboveCell10012303)
    e24KC2ThetaAboveLeaf1001230320 e24KC2ThetaAboveLeaf1001230321 e24KC2ThetaAboveLeaf1001230322
      e24KC2ThetaAboveLeaf1001230323

theorem e24KC2ThetaAboveNode100123033 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell10012303) = true :=
  adaptiveCoverCheck_succ_of_children 9 (childHH thetaAboveCell10012303)
    e24KC2ThetaAboveLeaf1001230330 e24KC2ThetaAboveLeaf1001230331 e24KC2ThetaAboveLeaf1001230332
      e24KC2ThetaAboveLeaf1001230333

theorem e24KC2ThetaAboveNode100123120 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell10012312) = true :=
  adaptiveCoverCheck_succ_of_children 9 (childLL thetaAboveCell10012312)
    e24KC2ThetaAboveLeaf1001231200 e24KC2ThetaAboveLeaf1001231201 e24KC2ThetaAboveLeaf1001231202
      e24KC2ThetaAboveLeaf1001231203

theorem e24KC2ThetaAboveNode100123121 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell10012312) = true :=
  adaptiveCoverCheck_succ_of_children 9 (childLH thetaAboveCell10012312)
    e24KC2ThetaAboveLeaf1001231210 e24KC2ThetaAboveLeaf1001231211 e24KC2ThetaAboveLeaf1001231212
      e24KC2ThetaAboveLeaf1001231213

theorem e24KC2ThetaAboveNode100123122 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell10012312) = true :=
  adaptiveCoverCheck_succ_of_children 9 (childHL thetaAboveCell10012312)
    e24KC2ThetaAboveLeaf1001231220 e24KC2ThetaAboveLeaf1001231221 e24KC2ThetaAboveLeaf1001231222
      e24KC2ThetaAboveLeaf1001231223

theorem e24KC2ThetaAboveNode100123123 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell10012312) = true :=
  adaptiveCoverCheck_succ_of_children 9 (childHH thetaAboveCell10012312)
    e24KC2ThetaAboveLeaf1001231230 e24KC2ThetaAboveLeaf1001231231 e24KC2ThetaAboveLeaf1001231232
      e24KC2ThetaAboveLeaf1001231233

theorem e24KC2ThetaAboveNode100123130 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell10012313) = true :=
  adaptiveCoverCheck_succ_of_children 9 (childLL thetaAboveCell10012313)
    e24KC2ThetaAboveLeaf1001231300 e24KC2ThetaAboveLeaf1001231301 e24KC2ThetaAboveLeaf1001231302
      e24KC2ThetaAboveLeaf1001231303

theorem e24KC2ThetaAboveNode100123131 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell10012313) = true :=
  adaptiveCoverCheck_succ_of_children 9 (childLH thetaAboveCell10012313)
    e24KC2ThetaAboveLeaf1001231310 e24KC2ThetaAboveLeaf1001231311 e24KC2ThetaAboveLeaf1001231312
      e24KC2ThetaAboveLeaf1001231313

theorem e24KC2ThetaAboveNode100123132 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell10012313) = true :=
  adaptiveCoverCheck_succ_of_children 9 (childHL thetaAboveCell10012313)
    e24KC2ThetaAboveLeaf1001231320 e24KC2ThetaAboveLeaf1001231321 e24KC2ThetaAboveLeaf1001231322
      e24KC2ThetaAboveLeaf1001231323

theorem e24KC2ThetaAboveNode100123133 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell10012313) = true :=
  adaptiveCoverCheck_succ_of_children 9 (childHH thetaAboveCell10012313)
    e24KC2ThetaAboveLeaf1001231330 e24KC2ThetaAboveLeaf1001231331 e24KC2ThetaAboveLeaf1001231332
      e24KC2ThetaAboveLeaf1001231333

theorem e24KC2ThetaAboveNode100123200 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell10012320) = true :=
  adaptiveCoverCheck_succ_of_children 9 (childLL thetaAboveCell10012320)
    e24KC2ThetaAboveLeaf1001232000 e24KC2ThetaAboveLeaf1001232001 e24KC2ThetaAboveLeaf1001232002
      e24KC2ThetaAboveLeaf1001232003

theorem e24KC2ThetaAboveNode100123201 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell10012320) = true :=
  adaptiveCoverCheck_succ_of_children 9 (childLH thetaAboveCell10012320)
    e24KC2ThetaAboveLeaf1001232010 e24KC2ThetaAboveLeaf1001232011 e24KC2ThetaAboveLeaf1001232012
      e24KC2ThetaAboveLeaf1001232013

theorem e24KC2ThetaAboveNode100123210 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell10012321) = true :=
  adaptiveCoverCheck_succ_of_children 9 (childLL thetaAboveCell10012321)
    e24KC2ThetaAboveLeaf1001232100 e24KC2ThetaAboveLeaf1001232101 e24KC2ThetaAboveLeaf1001232102
      e24KC2ThetaAboveLeaf1001232103

theorem e24KC2ThetaAboveNode100123211 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell10012321) = true :=
  adaptiveCoverCheck_succ_of_children 9 (childLH thetaAboveCell10012321)
    e24KC2ThetaAboveLeaf1001232110 e24KC2ThetaAboveLeaf1001232111 e24KC2ThetaAboveLeaf1001232112
      e24KC2ThetaAboveLeaf1001232113

theorem e24KC2ThetaAboveNode100123300 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell10012330) = true :=
  adaptiveCoverCheck_succ_of_children 9 (childLL thetaAboveCell10012330)
    e24KC2ThetaAboveLeaf1001233000 e24KC2ThetaAboveLeaf1001233001 e24KC2ThetaAboveLeaf1001233002
      e24KC2ThetaAboveLeaf1001233003

theorem e24KC2ThetaAboveNode100123301 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell10012330) = true :=
  adaptiveCoverCheck_succ_of_children 9 (childLH thetaAboveCell10012330)
    e24KC2ThetaAboveLeaf1001233010 e24KC2ThetaAboveLeaf1001233011 e24KC2ThetaAboveLeaf1001233012
      e24KC2ThetaAboveLeaf1001233013

theorem e24KC2ThetaAboveNode100123310 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell10012331) = true :=
  adaptiveCoverCheck_succ_of_children 9 (childLL thetaAboveCell10012331)
    e24KC2ThetaAboveLeaf1001233100 e24KC2ThetaAboveLeaf1001233101 e24KC2ThetaAboveLeaf1001233102
      e24KC2ThetaAboveLeaf1001233103

theorem e24KC2ThetaAboveNode100123311 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell10012331) = true :=
  adaptiveCoverCheck_succ_of_children 9 (childLH thetaAboveCell10012331)
    e24KC2ThetaAboveLeaf1001233110 e24KC2ThetaAboveLeaf1001233111 e24KC2ThetaAboveLeaf1001233112
      e24KC2ThetaAboveLeaf1001233113

theorem e24KC2ThetaAboveNode100132020 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell10013202) = true :=
  adaptiveCoverCheck_succ_of_children 9 (childLL thetaAboveCell10013202)
    e24KC2ThetaAboveLeaf1001320200 e24KC2ThetaAboveLeaf1001320201 e24KC2ThetaAboveLeaf1001320202
      e24KC2ThetaAboveLeaf1001320203

theorem e24KC2ThetaAboveNode100132021 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell10013202) = true :=
  adaptiveCoverCheck_succ_of_children 9 (childLH thetaAboveCell10013202)
    e24KC2ThetaAboveLeaf1001320210 e24KC2ThetaAboveLeaf1001320211 e24KC2ThetaAboveLeaf1001320212
      e24KC2ThetaAboveLeaf1001320213

theorem e24KC2ThetaAboveNode100132022 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell10013202) = true :=
  adaptiveCoverCheck_succ_of_children 9 (childHL thetaAboveCell10013202)
    e24KC2ThetaAboveLeaf1001320220 e24KC2ThetaAboveLeaf1001320221 e24KC2ThetaAboveLeaf1001320222
      e24KC2ThetaAboveLeaf1001320223

theorem e24KC2ThetaAboveNode100132023 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell10013202) = true :=
  adaptiveCoverCheck_succ_of_children 9 (childHH thetaAboveCell10013202)
    e24KC2ThetaAboveLeaf1001320230 e24KC2ThetaAboveLeaf1001320231 e24KC2ThetaAboveLeaf1001320232
      e24KC2ThetaAboveLeaf1001320233

theorem e24KC2ThetaAboveNode100132030 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell10013203) = true :=
  adaptiveCoverCheck_succ_of_children 9 (childLL thetaAboveCell10013203)
    e24KC2ThetaAboveLeaf1001320300 e24KC2ThetaAboveLeaf1001320301 e24KC2ThetaAboveLeaf1001320302
      e24KC2ThetaAboveLeaf1001320303

theorem e24KC2ThetaAboveNode100132031 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell10013203) = true :=
  adaptiveCoverCheck_succ_of_children 9 (childLH thetaAboveCell10013203)
    e24KC2ThetaAboveLeaf1001320310 e24KC2ThetaAboveLeaf1001320311 e24KC2ThetaAboveLeaf1001320312
      e24KC2ThetaAboveLeaf1001320313

theorem e24KC2ThetaAboveNode100132032 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell10013203) = true :=
  adaptiveCoverCheck_succ_of_children 9 (childHL thetaAboveCell10013203)
    e24KC2ThetaAboveLeaf1001320320 e24KC2ThetaAboveLeaf1001320321 e24KC2ThetaAboveLeaf1001320322
      e24KC2ThetaAboveLeaf1001320323

theorem e24KC2ThetaAboveNode100132033 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell10013203) = true :=
  adaptiveCoverCheck_succ_of_children 9 (childHH thetaAboveCell10013203)
    e24KC2ThetaAboveLeaf1001320330 e24KC2ThetaAboveLeaf1001320331 e24KC2ThetaAboveLeaf1001320332
      e24KC2ThetaAboveLeaf1001320333

theorem e24KC2ThetaAboveNode100132120 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell10013212) = true :=
  adaptiveCoverCheck_succ_of_children 9 (childLL thetaAboveCell10013212)
    e24KC2ThetaAboveLeaf1001321200 e24KC2ThetaAboveLeaf1001321201 e24KC2ThetaAboveLeaf1001321202
      e24KC2ThetaAboveLeaf1001321203

theorem e24KC2ThetaAboveNode100132121 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell10013212) = true :=
  adaptiveCoverCheck_succ_of_children 9 (childLH thetaAboveCell10013212)
    e24KC2ThetaAboveLeaf1001321210 e24KC2ThetaAboveLeaf1001321211 e24KC2ThetaAboveLeaf1001321212
      e24KC2ThetaAboveLeaf1001321213

theorem e24KC2ThetaAboveNode100132122 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell10013212) = true :=
  adaptiveCoverCheck_succ_of_children 9 (childHL thetaAboveCell10013212)
    e24KC2ThetaAboveLeaf1001321220 e24KC2ThetaAboveLeaf1001321221 e24KC2ThetaAboveLeaf1001321222
      e24KC2ThetaAboveLeaf1001321223

theorem e24KC2ThetaAboveNode100132123 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell10013212) = true :=
  adaptiveCoverCheck_succ_of_children 9 (childHH thetaAboveCell10013212)
    e24KC2ThetaAboveLeaf1001321230 e24KC2ThetaAboveLeaf1001321231 e24KC2ThetaAboveLeaf1001321232
      e24KC2ThetaAboveLeaf1001321233

theorem e24KC2ThetaAboveNode100132130 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell10013213) = true :=
  adaptiveCoverCheck_succ_of_children 9 (childLL thetaAboveCell10013213)
    e24KC2ThetaAboveLeaf1001321300 e24KC2ThetaAboveLeaf1001321301 e24KC2ThetaAboveLeaf1001321302
      e24KC2ThetaAboveLeaf1001321303

theorem e24KC2ThetaAboveNode100132131 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell10013213) = true :=
  adaptiveCoverCheck_succ_of_children 9 (childLH thetaAboveCell10013213)
    e24KC2ThetaAboveLeaf1001321310 e24KC2ThetaAboveLeaf1001321311 e24KC2ThetaAboveLeaf1001321312
      e24KC2ThetaAboveLeaf1001321313

theorem e24KC2ThetaAboveNode100132132 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell10013213) = true :=
  adaptiveCoverCheck_succ_of_children 9 (childHL thetaAboveCell10013213)
    e24KC2ThetaAboveLeaf1001321320 e24KC2ThetaAboveLeaf1001321321 e24KC2ThetaAboveLeaf1001321322
      e24KC2ThetaAboveLeaf1001321323

theorem e24KC2ThetaAboveNode100132133 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell10013213) = true :=
  adaptiveCoverCheck_succ_of_children 9 (childHH thetaAboveCell10013213)
    e24KC2ThetaAboveLeaf1001321330 e24KC2ThetaAboveLeaf1001321331 e24KC2ThetaAboveLeaf1001321332
      e24KC2ThetaAboveLeaf1001321333

theorem e24KC2ThetaAboveNode100132200 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell10013220) = true :=
  adaptiveCoverCheck_succ_of_children 9 (childLL thetaAboveCell10013220)
    e24KC2ThetaAboveLeaf1001322000 e24KC2ThetaAboveLeaf1001322001 e24KC2ThetaAboveLeaf1001322002
      e24KC2ThetaAboveLeaf1001322003

theorem e24KC2ThetaAboveNode100132201 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell10013220) = true :=
  adaptiveCoverCheck_succ_of_children 9 (childLH thetaAboveCell10013220)
    e24KC2ThetaAboveLeaf1001322010 e24KC2ThetaAboveLeaf1001322011 e24KC2ThetaAboveLeaf1001322012
      e24KC2ThetaAboveLeaf1001322013

theorem e24KC2ThetaAboveNode100132210 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell10013221) = true :=
  adaptiveCoverCheck_succ_of_children 9 (childLL thetaAboveCell10013221)
    e24KC2ThetaAboveLeaf1001322100 e24KC2ThetaAboveLeaf1001322101 e24KC2ThetaAboveLeaf1001322102
      e24KC2ThetaAboveLeaf1001322103

theorem e24KC2ThetaAboveNode100132211 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell10013221) = true :=
  adaptiveCoverCheck_succ_of_children 9 (childLH thetaAboveCell10013221)
    e24KC2ThetaAboveLeaf1001322110 e24KC2ThetaAboveLeaf1001322111 e24KC2ThetaAboveLeaf1001322112
      e24KC2ThetaAboveLeaf1001322113

theorem e24KC2ThetaAboveNode100132300 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell10013230) = true :=
  adaptiveCoverCheck_succ_of_children 9 (childLL thetaAboveCell10013230)
    e24KC2ThetaAboveLeaf1001323000 e24KC2ThetaAboveLeaf1001323001 e24KC2ThetaAboveLeaf1001323002
      e24KC2ThetaAboveLeaf1001323003

theorem e24KC2ThetaAboveNode100132301 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell10013230) = true :=
  adaptiveCoverCheck_succ_of_children 9 (childLH thetaAboveCell10013230)
    e24KC2ThetaAboveLeaf1001323010 e24KC2ThetaAboveLeaf1001323011 e24KC2ThetaAboveLeaf1001323012
      e24KC2ThetaAboveLeaf1001323013

theorem e24KC2ThetaAboveNode100133020 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell10013302) = true :=
  adaptiveCoverCheck_succ_of_children 9 (childLL thetaAboveCell10013302)
    e24KC2ThetaAboveLeaf1001330200 e24KC2ThetaAboveLeaf1001330201 e24KC2ThetaAboveLeaf1001330202
      e24KC2ThetaAboveLeaf1001330203

theorem e24KC2ThetaAboveNode100133021 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell10013302) = true :=
  adaptiveCoverCheck_succ_of_children 9 (childLH thetaAboveCell10013302)
    e24KC2ThetaAboveLeaf1001330210 e24KC2ThetaAboveLeaf1001330211 e24KC2ThetaAboveLeaf1001330212
      e24KC2ThetaAboveLeaf1001330213

theorem e24KC2ThetaAboveNode100133022 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell10013302) = true :=
  adaptiveCoverCheck_succ_of_children 9 (childHL thetaAboveCell10013302)
    e24KC2ThetaAboveLeaf1001330220 e24KC2ThetaAboveLeaf1001330221 e24KC2ThetaAboveLeaf1001330222
      e24KC2ThetaAboveLeaf1001330223

theorem e24KC2ThetaAboveNode100133023 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell10013302) = true :=
  adaptiveCoverCheck_succ_of_children 9 (childHH thetaAboveCell10013302)
    e24KC2ThetaAboveLeaf1001330230 e24KC2ThetaAboveLeaf1001330231 e24KC2ThetaAboveLeaf1001330232
      e24KC2ThetaAboveLeaf1001330233

theorem e24KC2ThetaAboveNode100133030 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell10013303) = true :=
  adaptiveCoverCheck_succ_of_children 9 (childLL thetaAboveCell10013303)
    e24KC2ThetaAboveLeaf1001330300 e24KC2ThetaAboveLeaf1001330301 e24KC2ThetaAboveLeaf1001330302
      e24KC2ThetaAboveLeaf1001330303

theorem e24KC2ThetaAboveNode100133031 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell10013303) = true :=
  adaptiveCoverCheck_succ_of_children 9 (childLH thetaAboveCell10013303)
    e24KC2ThetaAboveLeaf1001330310 e24KC2ThetaAboveLeaf1001330311 e24KC2ThetaAboveLeaf1001330312
      e24KC2ThetaAboveLeaf1001330313

theorem e24KC2ThetaAboveNode100133032 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell10013303) = true :=
  adaptiveCoverCheck_succ_of_children 9 (childHL thetaAboveCell10013303)
    e24KC2ThetaAboveLeaf1001330320 e24KC2ThetaAboveLeaf1001330321 e24KC2ThetaAboveLeaf1001330322
      e24KC2ThetaAboveLeaf1001330323

theorem e24KC2ThetaAboveNode100133033 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell10013303) = true :=
  adaptiveCoverCheck_succ_of_children 9 (childHH thetaAboveCell10013303)
    e24KC2ThetaAboveLeaf1001330330 e24KC2ThetaAboveLeaf1001330331 e24KC2ThetaAboveLeaf1001330332
      e24KC2ThetaAboveLeaf1001330333

theorem e24KC2ThetaAboveNode100133120 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell10013312) = true :=
  adaptiveCoverCheck_succ_of_children 9 (childLL thetaAboveCell10013312)
    e24KC2ThetaAboveLeaf1001331200 e24KC2ThetaAboveLeaf1001331201 e24KC2ThetaAboveLeaf1001331202
      e24KC2ThetaAboveLeaf1001331203

theorem e24KC2ThetaAboveNode100133121 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell10013312) = true :=
  adaptiveCoverCheck_succ_of_children 9 (childLH thetaAboveCell10013312)
    e24KC2ThetaAboveLeaf1001331210 e24KC2ThetaAboveLeaf1001331211 e24KC2ThetaAboveLeaf1001331212
      e24KC2ThetaAboveLeaf1001331213

theorem e24KC2ThetaAboveNode100133122 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell10013312) = true :=
  adaptiveCoverCheck_succ_of_children 9 (childHL thetaAboveCell10013312)
    e24KC2ThetaAboveLeaf1001331220 e24KC2ThetaAboveLeaf1001331221 e24KC2ThetaAboveLeaf1001331222
      e24KC2ThetaAboveLeaf1001331223

theorem e24KC2ThetaAboveNode100133123 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell10013312) = true :=
  adaptiveCoverCheck_succ_of_children 9 (childHH thetaAboveCell10013312)
    e24KC2ThetaAboveLeaf1001331230 e24KC2ThetaAboveLeaf1001331231 e24KC2ThetaAboveLeaf1001331232
      e24KC2ThetaAboveLeaf1001331233

theorem e24KC2ThetaAboveNode100133130 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell10013313) = true :=
  adaptiveCoverCheck_succ_of_children 9 (childLL thetaAboveCell10013313)
    e24KC2ThetaAboveLeaf1001331300 e24KC2ThetaAboveLeaf1001331301 e24KC2ThetaAboveLeaf1001331302
      e24KC2ThetaAboveLeaf1001331303

theorem e24KC2ThetaAboveNode100133131 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell10013313) = true :=
  adaptiveCoverCheck_succ_of_children 9 (childLH thetaAboveCell10013313)
    e24KC2ThetaAboveLeaf1001331310 e24KC2ThetaAboveLeaf1001331311 e24KC2ThetaAboveLeaf1001331312
      e24KC2ThetaAboveLeaf1001331313

theorem e24KC2ThetaAboveNode100133132 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell10013313) = true :=
  adaptiveCoverCheck_succ_of_children 9 (childHL thetaAboveCell10013313)
    e24KC2ThetaAboveLeaf1001331320 e24KC2ThetaAboveLeaf1001331321 e24KC2ThetaAboveLeaf1001331322
      e24KC2ThetaAboveLeaf1001331323

theorem e24KC2ThetaAboveNode100133133 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell10013313) = true :=
  adaptiveCoverCheck_succ_of_children 9 (childHH thetaAboveCell10013313)
    e24KC2ThetaAboveLeaf1001331330 e24KC2ThetaAboveLeaf1001331331 e24KC2ThetaAboveLeaf1001331332
      e24KC2ThetaAboveLeaf1001331333

theorem e24KC2ThetaAboveNode101022020 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell10102202) = true :=
  adaptiveCoverCheck_succ_of_children 9 (childLL thetaAboveCell10102202)
    e24KC2ThetaAboveLeaf1010220200 e24KC2ThetaAboveLeaf1010220201 e24KC2ThetaAboveLeaf1010220202
      e24KC2ThetaAboveLeaf1010220203

theorem e24KC2ThetaAboveNode101022021 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell10102202) = true :=
  adaptiveCoverCheck_succ_of_children 9 (childLH thetaAboveCell10102202)
    e24KC2ThetaAboveLeaf1010220210 e24KC2ThetaAboveLeaf1010220211 e24KC2ThetaAboveLeaf1010220212
      e24KC2ThetaAboveLeaf1010220213

theorem e24KC2ThetaAboveNode101022022 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell10102202) = true :=
  adaptiveCoverCheck_succ_of_children 9 (childHL thetaAboveCell10102202)
    e24KC2ThetaAboveLeaf1010220220 e24KC2ThetaAboveLeaf1010220221 e24KC2ThetaAboveLeaf1010220222
      e24KC2ThetaAboveLeaf1010220223

theorem e24KC2ThetaAboveNode101022023 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell10102202) = true :=
  adaptiveCoverCheck_succ_of_children 9 (childHH thetaAboveCell10102202)
    e24KC2ThetaAboveLeaf1010220230 e24KC2ThetaAboveLeaf1010220231 e24KC2ThetaAboveLeaf1010220232
      e24KC2ThetaAboveLeaf1010220233

theorem e24KC2ThetaAboveNode101022030 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell10102203) = true :=
  adaptiveCoverCheck_succ_of_children 9 (childLL thetaAboveCell10102203)
    e24KC2ThetaAboveLeaf1010220300 e24KC2ThetaAboveLeaf1010220301 e24KC2ThetaAboveLeaf1010220302
      e24KC2ThetaAboveLeaf1010220303

theorem e24KC2ThetaAboveNode101022031 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell10102203) = true :=
  adaptiveCoverCheck_succ_of_children 9 (childLH thetaAboveCell10102203)
    e24KC2ThetaAboveLeaf1010220310 e24KC2ThetaAboveLeaf1010220311 e24KC2ThetaAboveLeaf1010220312
      e24KC2ThetaAboveLeaf1010220313

theorem e24KC2ThetaAboveNode101022032 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell10102203) = true :=
  adaptiveCoverCheck_succ_of_children 9 (childHL thetaAboveCell10102203)
    e24KC2ThetaAboveLeaf1010220320 e24KC2ThetaAboveLeaf1010220321 e24KC2ThetaAboveLeaf1010220322
      e24KC2ThetaAboveLeaf1010220323

theorem e24KC2ThetaAboveNode101022033 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell10102203) = true :=
  adaptiveCoverCheck_succ_of_children 9 (childHH thetaAboveCell10102203)
    e24KC2ThetaAboveLeaf1010220330 e24KC2ThetaAboveLeaf1010220331 e24KC2ThetaAboveLeaf1010220332
      e24KC2ThetaAboveLeaf1010220333

theorem e24KC2ThetaAboveNode101022120 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell10102212) = true :=
  adaptiveCoverCheck_succ_of_children 9 (childLL thetaAboveCell10102212)
    e24KC2ThetaAboveLeaf1010221200 e24KC2ThetaAboveLeaf1010221201 e24KC2ThetaAboveLeaf1010221202
      e24KC2ThetaAboveLeaf1010221203

theorem e24KC2ThetaAboveNode101022121 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell10102212) = true :=
  adaptiveCoverCheck_succ_of_children 9 (childLH thetaAboveCell10102212)
    e24KC2ThetaAboveLeaf1010221210 e24KC2ThetaAboveLeaf1010221211 e24KC2ThetaAboveLeaf1010221212
      e24KC2ThetaAboveLeaf1010221213

theorem e24KC2ThetaAboveNode101022122 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell10102212) = true :=
  adaptiveCoverCheck_succ_of_children 9 (childHL thetaAboveCell10102212)
    e24KC2ThetaAboveLeaf1010221220 e24KC2ThetaAboveLeaf1010221221 e24KC2ThetaAboveLeaf1010221222
      e24KC2ThetaAboveLeaf1010221223

theorem e24KC2ThetaAboveNode101022123 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell10102212) = true :=
  adaptiveCoverCheck_succ_of_children 9 (childHH thetaAboveCell10102212)
    e24KC2ThetaAboveLeaf1010221230 e24KC2ThetaAboveLeaf1010221231 e24KC2ThetaAboveLeaf1010221232
      e24KC2ThetaAboveLeaf1010221233

theorem e24KC2ThetaAboveNode101022130 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell10102213) = true :=
  adaptiveCoverCheck_succ_of_children 9 (childLL thetaAboveCell10102213)
    e24KC2ThetaAboveLeaf1010221300 e24KC2ThetaAboveLeaf1010221301 e24KC2ThetaAboveLeaf1010221302
      e24KC2ThetaAboveLeaf1010221303

theorem e24KC2ThetaAboveNode101022131 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell10102213) = true :=
  adaptiveCoverCheck_succ_of_children 9 (childLH thetaAboveCell10102213)
    e24KC2ThetaAboveLeaf1010221310 e24KC2ThetaAboveLeaf1010221311 e24KC2ThetaAboveLeaf1010221312
      e24KC2ThetaAboveLeaf1010221313

theorem e24KC2ThetaAboveNode101022132 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell10102213) = true :=
  adaptiveCoverCheck_succ_of_children 9 (childHL thetaAboveCell10102213)
    e24KC2ThetaAboveLeaf1010221320 e24KC2ThetaAboveLeaf1010221321 e24KC2ThetaAboveLeaf1010221322
      e24KC2ThetaAboveLeaf1010221323

theorem e24KC2ThetaAboveNode101023020 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell10102302) = true :=
  adaptiveCoverCheck_succ_of_children 9 (childLL thetaAboveCell10102302)
    e24KC2ThetaAboveLeaf1010230200 e24KC2ThetaAboveLeaf1010230201 e24KC2ThetaAboveLeaf1010230202
      e24KC2ThetaAboveLeaf1010230203

theorem e24KC2ThetaAboveNode101023021 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell10102302) = true :=
  adaptiveCoverCheck_succ_of_children 9 (childLH thetaAboveCell10102302)
    e24KC2ThetaAboveLeaf1010230210 e24KC2ThetaAboveLeaf1010230211 e24KC2ThetaAboveLeaf1010230212
      e24KC2ThetaAboveLeaf1010230213

theorem e24KC2ThetaAboveNode101023030 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell10102303) = true :=
  adaptiveCoverCheck_succ_of_children 9 (childLL thetaAboveCell10102303)
    e24KC2ThetaAboveLeaf1010230300 e24KC2ThetaAboveLeaf1010230301 e24KC2ThetaAboveLeaf1010230302
      e24KC2ThetaAboveLeaf1010230303

theorem e24KC2ThetaAboveNode101023031 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell10102303) = true :=
  adaptiveCoverCheck_succ_of_children 9 (childLH thetaAboveCell10102303)
    e24KC2ThetaAboveLeaf1010230310 e24KC2ThetaAboveLeaf1010230311 e24KC2ThetaAboveLeaf1010230312
      e24KC2ThetaAboveLeaf1010230313

theorem e24KC2ThetaAboveNode101023120 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell10102312) = true :=
  adaptiveCoverCheck_succ_of_children 9 (childLL thetaAboveCell10102312)
    e24KC2ThetaAboveLeaf1010231200 e24KC2ThetaAboveLeaf1010231201 e24KC2ThetaAboveLeaf1010231202
      e24KC2ThetaAboveLeaf1010231203

theorem e24KC2ThetaAboveNode101023121 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell10102312) = true :=
  adaptiveCoverCheck_succ_of_children 9 (childLH thetaAboveCell10102312)
    e24KC2ThetaAboveLeaf1010231210 e24KC2ThetaAboveLeaf1010231211 e24KC2ThetaAboveLeaf1010231212
      e24KC2ThetaAboveLeaf1010231213

theorem e24KC2ThetaAboveNode101023130 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell10102313) = true :=
  adaptiveCoverCheck_succ_of_children 9 (childLL thetaAboveCell10102313)
    e24KC2ThetaAboveLeaf1010231300 e24KC2ThetaAboveLeaf1010231301 e24KC2ThetaAboveLeaf1010231302
      e24KC2ThetaAboveLeaf1010231303

theorem e24KC2ThetaAboveNode101023131 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell10102313) = true :=
  adaptiveCoverCheck_succ_of_children 9 (childLH thetaAboveCell10102313)
    e24KC2ThetaAboveLeaf1010231310 e24KC2ThetaAboveLeaf1010231311 e24KC2ThetaAboveLeaf1010231312
      e24KC2ThetaAboveLeaf1010231313

theorem e24KC2ThetaAboveNode101032020 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell10103202) = true :=
  adaptiveCoverCheck_succ_of_children 9 (childLL thetaAboveCell10103202)
    e24KC2ThetaAboveLeaf1010320200 e24KC2ThetaAboveLeaf1010320201 e24KC2ThetaAboveLeaf1010320202
      e24KC2ThetaAboveLeaf1010320203

theorem e24KC2ThetaAboveNode101032021 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell10103202) = true :=
  adaptiveCoverCheck_succ_of_children 9 (childLH thetaAboveCell10103202)
    e24KC2ThetaAboveLeaf1010320210 e24KC2ThetaAboveLeaf1010320211 e24KC2ThetaAboveLeaf1010320212
      e24KC2ThetaAboveLeaf1010320213

theorem e24KC2ThetaAboveNode101032030 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell10103203) = true :=
  adaptiveCoverCheck_succ_of_children 9 (childLL thetaAboveCell10103203)
    e24KC2ThetaAboveLeaf1010320300 e24KC2ThetaAboveLeaf1010320301 e24KC2ThetaAboveLeaf1010320302
      e24KC2ThetaAboveLeaf1010320303

theorem e24KC2ThetaAboveNode101032031 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell10103203) = true :=
  adaptiveCoverCheck_succ_of_children 9 (childLH thetaAboveCell10103203)
    e24KC2ThetaAboveLeaf1010320310 e24KC2ThetaAboveLeaf1010320311 e24KC2ThetaAboveLeaf1010320312
      e24KC2ThetaAboveLeaf1010320313

theorem e24KC2ThetaAboveNode101032120 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell10103212) = true :=
  adaptiveCoverCheck_succ_of_children 9 (childLL thetaAboveCell10103212)
    e24KC2ThetaAboveLeaf1010321200 e24KC2ThetaAboveLeaf1010321201 e24KC2ThetaAboveLeaf1010321202
      e24KC2ThetaAboveLeaf1010321203

theorem e24KC2ThetaAboveNode101032121 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell10103212) = true :=
  adaptiveCoverCheck_succ_of_children 9 (childLH thetaAboveCell10103212)
    e24KC2ThetaAboveLeaf1010321210 e24KC2ThetaAboveLeaf1010321211 e24KC2ThetaAboveLeaf1010321212
      e24KC2ThetaAboveLeaf1010321213

theorem e24KC2ThetaAboveNode101032130 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell10103213) = true :=
  adaptiveCoverCheck_succ_of_children 9 (childLL thetaAboveCell10103213)
    e24KC2ThetaAboveLeaf1010321300 e24KC2ThetaAboveLeaf1010321301 e24KC2ThetaAboveLeaf1010321302
      e24KC2ThetaAboveLeaf1010321303

theorem e24KC2ThetaAboveNode101032131 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell10103213) = true :=
  adaptiveCoverCheck_succ_of_children 9 (childLH thetaAboveCell10103213)
    e24KC2ThetaAboveLeaf1010321310 e24KC2ThetaAboveLeaf1010321311 e24KC2ThetaAboveLeaf1010321312
      e24KC2ThetaAboveLeaf1010321313

theorem e24KC2ThetaAboveNode101033020 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell10103302) = true :=
  adaptiveCoverCheck_succ_of_children 9 (childLL thetaAboveCell10103302)
    e24KC2ThetaAboveLeaf1010330200 e24KC2ThetaAboveLeaf1010330201 e24KC2ThetaAboveLeaf1010330202
      e24KC2ThetaAboveLeaf1010330203

theorem e24KC2ThetaAboveNode00002022 :
    adaptiveCoverCheck 11 thetaAboveCell00002022 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell00002022
    e24KC2ThetaAboveLeaf000020220 e24KC2ThetaAboveLeaf000020221 e24KC2ThetaAboveLeaf000020222
      e24KC2ThetaAboveLeaf000020223

theorem e24KC2ThetaAboveNode00002023 :
    adaptiveCoverCheck 11 thetaAboveCell00002023 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell00002023
    e24KC2ThetaAboveLeaf000020230 e24KC2ThetaAboveLeaf000020231 e24KC2ThetaAboveLeaf000020232
      e24KC2ThetaAboveLeaf000020233

theorem e24KC2ThetaAboveNode00002032 :
    adaptiveCoverCheck 11 thetaAboveCell00002032 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell00002032
    e24KC2ThetaAboveLeaf000020320 e24KC2ThetaAboveLeaf000020321 e24KC2ThetaAboveLeaf000020322
      e24KC2ThetaAboveLeaf000020323

theorem e24KC2ThetaAboveNode00002033 :
    adaptiveCoverCheck 11 thetaAboveCell00002033 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell00002033
    e24KC2ThetaAboveLeaf000020330 e24KC2ThetaAboveLeaf000020331 e24KC2ThetaAboveLeaf000020332
      e24KC2ThetaAboveLeaf000020333

theorem e24KC2ThetaAboveNode00002122 :
    adaptiveCoverCheck 11 thetaAboveCell00002122 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell00002122
    e24KC2ThetaAboveLeaf000021220 e24KC2ThetaAboveLeaf000021221 e24KC2ThetaAboveLeaf000021222
      e24KC2ThetaAboveLeaf000021223

theorem e24KC2ThetaAboveNode00002123 :
    adaptiveCoverCheck 11 thetaAboveCell00002123 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell00002123
    e24KC2ThetaAboveLeaf000021230 e24KC2ThetaAboveLeaf000021231 e24KC2ThetaAboveLeaf000021232
      e24KC2ThetaAboveLeaf000021233

theorem e24KC2ThetaAboveNode00002132 :
    adaptiveCoverCheck 11 thetaAboveCell00002132 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell00002132
    e24KC2ThetaAboveLeaf000021320 e24KC2ThetaAboveLeaf000021321 e24KC2ThetaAboveLeaf000021322
      e24KC2ThetaAboveLeaf000021323

theorem e24KC2ThetaAboveNode00002133 :
    adaptiveCoverCheck 11 thetaAboveCell00002133 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell00002133
    e24KC2ThetaAboveLeaf000021330 e24KC2ThetaAboveLeaf000021331 e24KC2ThetaAboveLeaf000021332
      e24KC2ThetaAboveLeaf000021333

theorem e24KC2ThetaAboveNode00002200 :
    adaptiveCoverCheck 11 thetaAboveCell00002200 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell00002200
    e24KC2ThetaAboveNode000022000 e24KC2ThetaAboveNode000022001 e24KC2ThetaAboveNode000022002
      e24KC2ThetaAboveNode000022003

theorem e24KC2ThetaAboveNode00002201 :
    adaptiveCoverCheck 11 thetaAboveCell00002201 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell00002201
    e24KC2ThetaAboveNode000022010 e24KC2ThetaAboveNode000022011 e24KC2ThetaAboveNode000022012
      e24KC2ThetaAboveNode000022013

theorem e24KC2ThetaAboveNode00002202 :
    adaptiveCoverCheck 11 thetaAboveCell00002202 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell00002202
    e24KC2ThetaAboveLeaf000022020 e24KC2ThetaAboveLeaf000022021 e24KC2ThetaAboveLeaf000022022
      e24KC2ThetaAboveLeaf000022023

theorem e24KC2ThetaAboveNode00002203 :
    adaptiveCoverCheck 11 thetaAboveCell00002203 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell00002203
    e24KC2ThetaAboveLeaf000022030 e24KC2ThetaAboveLeaf000022031 e24KC2ThetaAboveLeaf000022032
      e24KC2ThetaAboveLeaf000022033

theorem e24KC2ThetaAboveNode00002210 :
    adaptiveCoverCheck 11 thetaAboveCell00002210 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell00002210
    e24KC2ThetaAboveNode000022100 e24KC2ThetaAboveNode000022101 e24KC2ThetaAboveNode000022102
      e24KC2ThetaAboveNode000022103

theorem e24KC2ThetaAboveNode00002211 :
    adaptiveCoverCheck 11 thetaAboveCell00002211 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell00002211
    e24KC2ThetaAboveNode000022110 e24KC2ThetaAboveNode000022111 e24KC2ThetaAboveNode000022112
      e24KC2ThetaAboveNode000022113

theorem e24KC2ThetaAboveNode00002212 :
    adaptiveCoverCheck 11 thetaAboveCell00002212 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell00002212
    e24KC2ThetaAboveLeaf000022120 e24KC2ThetaAboveLeaf000022121 e24KC2ThetaAboveLeaf000022122
      e24KC2ThetaAboveLeaf000022123

theorem e24KC2ThetaAboveNode00002213 :
    adaptiveCoverCheck 11 thetaAboveCell00002213 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell00002213
    e24KC2ThetaAboveLeaf000022130 e24KC2ThetaAboveNode000022131 e24KC2ThetaAboveLeaf000022132
      e24KC2ThetaAboveLeaf000022133

theorem e24KC2ThetaAboveNode00002300 :
    adaptiveCoverCheck 11 thetaAboveCell00002300 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell00002300
    e24KC2ThetaAboveNode000023000 e24KC2ThetaAboveNode000023001 e24KC2ThetaAboveNode000023002
      e24KC2ThetaAboveNode000023003

theorem e24KC2ThetaAboveNode00002301 :
    adaptiveCoverCheck 11 thetaAboveCell00002301 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell00002301
    e24KC2ThetaAboveNode000023010 e24KC2ThetaAboveNode000023011 e24KC2ThetaAboveNode000023012
      e24KC2ThetaAboveNode000023013

theorem e24KC2ThetaAboveNode00002302 :
    adaptiveCoverCheck 11 thetaAboveCell00002302 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell00002302
    e24KC2ThetaAboveNode000023020 e24KC2ThetaAboveNode000023021 e24KC2ThetaAboveLeaf000023022
      e24KC2ThetaAboveLeaf000023023

theorem e24KC2ThetaAboveNode00002303 :
    adaptiveCoverCheck 11 thetaAboveCell00002303 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell00002303
    e24KC2ThetaAboveNode000023030 e24KC2ThetaAboveNode000023031 e24KC2ThetaAboveLeaf000023032
      e24KC2ThetaAboveLeaf000023033

theorem e24KC2ThetaAboveNode00002310 :
    adaptiveCoverCheck 11 thetaAboveCell00002310 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell00002310
    e24KC2ThetaAboveNode000023100 e24KC2ThetaAboveNode000023101 e24KC2ThetaAboveNode000023102
      e24KC2ThetaAboveNode000023103

theorem e24KC2ThetaAboveNode00002311 :
    adaptiveCoverCheck 11 thetaAboveCell00002311 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell00002311
    e24KC2ThetaAboveNode000023110 e24KC2ThetaAboveNode000023111 e24KC2ThetaAboveNode000023112
      e24KC2ThetaAboveNode000023113

theorem e24KC2ThetaAboveNode00002312 :
    adaptiveCoverCheck 11 thetaAboveCell00002312 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell00002312
    e24KC2ThetaAboveNode000023120 e24KC2ThetaAboveNode000023121 e24KC2ThetaAboveLeaf000023122
      e24KC2ThetaAboveLeaf000023123

theorem e24KC2ThetaAboveNode00002313 :
    adaptiveCoverCheck 11 thetaAboveCell00002313 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell00002313
    e24KC2ThetaAboveNode000023130 e24KC2ThetaAboveNode000023131 e24KC2ThetaAboveLeaf000023132
      e24KC2ThetaAboveLeaf000023133

theorem e24KC2ThetaAboveNode00003022 :
    adaptiveCoverCheck 11 thetaAboveCell00003022 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell00003022
    e24KC2ThetaAboveLeaf000030220 e24KC2ThetaAboveLeaf000030221 e24KC2ThetaAboveLeaf000030222
      e24KC2ThetaAboveLeaf000030223

theorem e24KC2ThetaAboveNode00003023 :
    adaptiveCoverCheck 11 thetaAboveCell00003023 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell00003023
    e24KC2ThetaAboveLeaf000030230 e24KC2ThetaAboveLeaf000030231 e24KC2ThetaAboveLeaf000030232
      e24KC2ThetaAboveLeaf000030233

theorem e24KC2ThetaAboveNode00003032 :
    adaptiveCoverCheck 11 thetaAboveCell00003032 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell00003032
    e24KC2ThetaAboveLeaf000030320 e24KC2ThetaAboveLeaf000030321 e24KC2ThetaAboveLeaf000030322
      e24KC2ThetaAboveLeaf000030323

theorem e24KC2ThetaAboveNode00003033 :
    adaptiveCoverCheck 11 thetaAboveCell00003033 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell00003033
    e24KC2ThetaAboveLeaf000030330 e24KC2ThetaAboveLeaf000030331 e24KC2ThetaAboveLeaf000030332
      e24KC2ThetaAboveLeaf000030333

theorem e24KC2ThetaAboveNode00003122 :
    adaptiveCoverCheck 11 thetaAboveCell00003122 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell00003122
    e24KC2ThetaAboveLeaf000031220 e24KC2ThetaAboveLeaf000031221 e24KC2ThetaAboveLeaf000031222
      e24KC2ThetaAboveLeaf000031223

theorem e24KC2ThetaAboveNode00003123 :
    adaptiveCoverCheck 11 thetaAboveCell00003123 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell00003123
    e24KC2ThetaAboveLeaf000031230 e24KC2ThetaAboveLeaf000031231 e24KC2ThetaAboveLeaf000031232
      e24KC2ThetaAboveLeaf000031233

theorem e24KC2ThetaAboveNode00003132 :
    adaptiveCoverCheck 11 thetaAboveCell00003132 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell00003132
    e24KC2ThetaAboveLeaf000031320 e24KC2ThetaAboveLeaf000031321 e24KC2ThetaAboveLeaf000031322
      e24KC2ThetaAboveLeaf000031323

theorem e24KC2ThetaAboveNode00003133 :
    adaptiveCoverCheck 11 thetaAboveCell00003133 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell00003133
    e24KC2ThetaAboveLeaf000031330 e24KC2ThetaAboveLeaf000031331 e24KC2ThetaAboveLeaf000031332
      e24KC2ThetaAboveLeaf000031333

theorem e24KC2ThetaAboveNode00003200 :
    adaptiveCoverCheck 11 thetaAboveCell00003200 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell00003200
    e24KC2ThetaAboveNode000032000 e24KC2ThetaAboveNode000032001 e24KC2ThetaAboveNode000032002
      e24KC2ThetaAboveNode000032003

theorem e24KC2ThetaAboveNode00003201 :
    adaptiveCoverCheck 11 thetaAboveCell00003201 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell00003201
    e24KC2ThetaAboveNode000032010 e24KC2ThetaAboveNode000032011 e24KC2ThetaAboveNode000032012
      e24KC2ThetaAboveNode000032013

theorem e24KC2ThetaAboveNode00003202 :
    adaptiveCoverCheck 11 thetaAboveCell00003202 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell00003202
    e24KC2ThetaAboveNode000032020 e24KC2ThetaAboveNode000032021 e24KC2ThetaAboveLeaf000032022
      e24KC2ThetaAboveLeaf000032023

theorem e24KC2ThetaAboveNode00003203 :
    adaptiveCoverCheck 11 thetaAboveCell00003203 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell00003203
    e24KC2ThetaAboveNode000032030 e24KC2ThetaAboveNode000032031 e24KC2ThetaAboveLeaf000032032
      e24KC2ThetaAboveLeaf000032033

theorem e24KC2ThetaAboveNode00003210 :
    adaptiveCoverCheck 11 thetaAboveCell00003210 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell00003210
    e24KC2ThetaAboveNode000032100 e24KC2ThetaAboveNode000032101 e24KC2ThetaAboveNode000032102
      e24KC2ThetaAboveNode000032103

theorem e24KC2ThetaAboveNode00003211 :
    adaptiveCoverCheck 11 thetaAboveCell00003211 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell00003211
    e24KC2ThetaAboveNode000032110 e24KC2ThetaAboveNode000032111 e24KC2ThetaAboveNode000032112
      e24KC2ThetaAboveNode000032113

theorem e24KC2ThetaAboveNode00003212 :
    adaptiveCoverCheck 11 thetaAboveCell00003212 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell00003212
    e24KC2ThetaAboveNode000032120 e24KC2ThetaAboveNode000032121 e24KC2ThetaAboveLeaf000032122
      e24KC2ThetaAboveLeaf000032123

theorem e24KC2ThetaAboveNode00003213 :
    adaptiveCoverCheck 11 thetaAboveCell00003213 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell00003213
    e24KC2ThetaAboveNode000032130 e24KC2ThetaAboveNode000032131 e24KC2ThetaAboveLeaf000032132
      e24KC2ThetaAboveLeaf000032133

theorem e24KC2ThetaAboveNode00003300 :
    adaptiveCoverCheck 11 thetaAboveCell00003300 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell00003300
    e24KC2ThetaAboveNode000033000 e24KC2ThetaAboveNode000033001 e24KC2ThetaAboveNode000033002
      e24KC2ThetaAboveNode000033003

theorem e24KC2ThetaAboveNode00003301 :
    adaptiveCoverCheck 11 thetaAboveCell00003301 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell00003301
    e24KC2ThetaAboveNode000033010 e24KC2ThetaAboveNode000033011 e24KC2ThetaAboveNode000033012
      e24KC2ThetaAboveNode000033013

theorem e24KC2ThetaAboveNode00003302 :
    adaptiveCoverCheck 11 thetaAboveCell00003302 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell00003302
    e24KC2ThetaAboveNode000033020 e24KC2ThetaAboveNode000033021 e24KC2ThetaAboveLeaf000033022
      e24KC2ThetaAboveLeaf000033023

theorem e24KC2ThetaAboveNode00003303 :
    adaptiveCoverCheck 11 thetaAboveCell00003303 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell00003303
    e24KC2ThetaAboveNode000033030 e24KC2ThetaAboveNode000033031 e24KC2ThetaAboveLeaf000033032
      e24KC2ThetaAboveLeaf000033033

theorem e24KC2ThetaAboveNode00003310 :
    adaptiveCoverCheck 11 thetaAboveCell00003310 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell00003310
    e24KC2ThetaAboveNode000033100 e24KC2ThetaAboveNode000033101 e24KC2ThetaAboveNode000033102
      e24KC2ThetaAboveNode000033103

theorem e24KC2ThetaAboveNode00003311 :
    adaptiveCoverCheck 11 thetaAboveCell00003311 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell00003311
    e24KC2ThetaAboveNode000033110 e24KC2ThetaAboveNode000033111 e24KC2ThetaAboveNode000033112
      e24KC2ThetaAboveNode000033113

theorem e24KC2ThetaAboveNode00003312 :
    adaptiveCoverCheck 11 thetaAboveCell00003312 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell00003312
    e24KC2ThetaAboveNode000033120 e24KC2ThetaAboveNode000033121 e24KC2ThetaAboveLeaf000033122
      e24KC2ThetaAboveLeaf000033123

theorem e24KC2ThetaAboveNode00003313 :
    adaptiveCoverCheck 11 thetaAboveCell00003313 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell00003313
    e24KC2ThetaAboveNode000033130 e24KC2ThetaAboveNode000033131 e24KC2ThetaAboveLeaf000033132
      e24KC2ThetaAboveLeaf000033133

theorem e24KC2ThetaAboveNode00012022 :
    adaptiveCoverCheck 11 thetaAboveCell00012022 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell00012022
    e24KC2ThetaAboveLeaf000120220 e24KC2ThetaAboveLeaf000120221 e24KC2ThetaAboveLeaf000120222
      e24KC2ThetaAboveLeaf000120223

theorem e24KC2ThetaAboveNode00012023 :
    adaptiveCoverCheck 11 thetaAboveCell00012023 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell00012023
    e24KC2ThetaAboveLeaf000120230 e24KC2ThetaAboveLeaf000120231 e24KC2ThetaAboveLeaf000120232
      e24KC2ThetaAboveLeaf000120233

theorem e24KC2ThetaAboveNode00012032 :
    adaptiveCoverCheck 11 thetaAboveCell00012032 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell00012032
    e24KC2ThetaAboveLeaf000120320 e24KC2ThetaAboveLeaf000120321 e24KC2ThetaAboveLeaf000120322
      e24KC2ThetaAboveLeaf000120323

theorem e24KC2ThetaAboveNode00012033 :
    adaptiveCoverCheck 11 thetaAboveCell00012033 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell00012033
    e24KC2ThetaAboveLeaf000120330 e24KC2ThetaAboveLeaf000120331 e24KC2ThetaAboveLeaf000120332
      e24KC2ThetaAboveLeaf000120333

theorem e24KC2ThetaAboveNode00012122 :
    adaptiveCoverCheck 11 thetaAboveCell00012122 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell00012122
    e24KC2ThetaAboveLeaf000121220 e24KC2ThetaAboveLeaf000121221 e24KC2ThetaAboveLeaf000121222
      e24KC2ThetaAboveLeaf000121223

theorem e24KC2ThetaAboveNode00012123 :
    adaptiveCoverCheck 11 thetaAboveCell00012123 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell00012123
    e24KC2ThetaAboveLeaf000121230 e24KC2ThetaAboveLeaf000121231 e24KC2ThetaAboveLeaf000121232
      e24KC2ThetaAboveLeaf000121233

theorem e24KC2ThetaAboveNode00012132 :
    adaptiveCoverCheck 11 thetaAboveCell00012132 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell00012132
    e24KC2ThetaAboveLeaf000121320 e24KC2ThetaAboveLeaf000121321 e24KC2ThetaAboveLeaf000121322
      e24KC2ThetaAboveLeaf000121323

theorem e24KC2ThetaAboveNode00012133 :
    adaptiveCoverCheck 11 thetaAboveCell00012133 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell00012133
    e24KC2ThetaAboveLeaf000121330 e24KC2ThetaAboveLeaf000121331 e24KC2ThetaAboveLeaf000121332
      e24KC2ThetaAboveLeaf000121333

theorem e24KC2ThetaAboveNode00012200 :
    adaptiveCoverCheck 11 thetaAboveCell00012200 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell00012200
    e24KC2ThetaAboveNode000122000 e24KC2ThetaAboveNode000122001 e24KC2ThetaAboveNode000122002
      e24KC2ThetaAboveNode000122003

theorem e24KC2ThetaAboveNode00012201 :
    adaptiveCoverCheck 11 thetaAboveCell00012201 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell00012201
    e24KC2ThetaAboveNode000122010 e24KC2ThetaAboveNode000122011 e24KC2ThetaAboveNode000122012
      e24KC2ThetaAboveNode000122013

theorem e24KC2ThetaAboveNode00012202 :
    adaptiveCoverCheck 11 thetaAboveCell00012202 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell00012202
    e24KC2ThetaAboveNode000122020 e24KC2ThetaAboveNode000122021 e24KC2ThetaAboveLeaf000122022
      e24KC2ThetaAboveLeaf000122023

theorem e24KC2ThetaAboveNode00012203 :
    adaptiveCoverCheck 11 thetaAboveCell00012203 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell00012203
    e24KC2ThetaAboveNode000122030 e24KC2ThetaAboveNode000122031 e24KC2ThetaAboveLeaf000122032
      e24KC2ThetaAboveLeaf000122033

theorem e24KC2ThetaAboveNode00012210 :
    adaptiveCoverCheck 11 thetaAboveCell00012210 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell00012210
    e24KC2ThetaAboveNode000122100 e24KC2ThetaAboveNode000122101 e24KC2ThetaAboveNode000122102
      e24KC2ThetaAboveNode000122103

theorem e24KC2ThetaAboveNode00012211 :
    adaptiveCoverCheck 11 thetaAboveCell00012211 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell00012211
    e24KC2ThetaAboveNode000122110 e24KC2ThetaAboveNode000122111 e24KC2ThetaAboveNode000122112
      e24KC2ThetaAboveNode000122113

theorem e24KC2ThetaAboveNode00012212 :
    adaptiveCoverCheck 11 thetaAboveCell00012212 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell00012212
    e24KC2ThetaAboveNode000122120 e24KC2ThetaAboveNode000122121 e24KC2ThetaAboveLeaf000122122
      e24KC2ThetaAboveLeaf000122123

theorem e24KC2ThetaAboveNode00012213 :
    adaptiveCoverCheck 11 thetaAboveCell00012213 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell00012213
    e24KC2ThetaAboveNode000122130 e24KC2ThetaAboveNode000122131 e24KC2ThetaAboveLeaf000122132
      e24KC2ThetaAboveLeaf000122133

theorem e24KC2ThetaAboveNode00012300 :
    adaptiveCoverCheck 11 thetaAboveCell00012300 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell00012300
    e24KC2ThetaAboveNode000123000 e24KC2ThetaAboveNode000123001 e24KC2ThetaAboveNode000123002
      e24KC2ThetaAboveNode000123003

theorem e24KC2ThetaAboveNode00012301 :
    adaptiveCoverCheck 11 thetaAboveCell00012301 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell00012301
    e24KC2ThetaAboveNode000123010 e24KC2ThetaAboveNode000123011 e24KC2ThetaAboveNode000123012
      e24KC2ThetaAboveNode000123013

theorem e24KC2ThetaAboveNode00012302 :
    adaptiveCoverCheck 11 thetaAboveCell00012302 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell00012302
    e24KC2ThetaAboveNode000123020 e24KC2ThetaAboveNode000123021 e24KC2ThetaAboveLeaf000123022
      e24KC2ThetaAboveLeaf000123023

theorem e24KC2ThetaAboveNode00012303 :
    adaptiveCoverCheck 11 thetaAboveCell00012303 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell00012303
    e24KC2ThetaAboveNode000123030 e24KC2ThetaAboveNode000123031 e24KC2ThetaAboveLeaf000123032
      e24KC2ThetaAboveLeaf000123033

theorem e24KC2ThetaAboveNode00012310 :
    adaptiveCoverCheck 11 thetaAboveCell00012310 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell00012310
    e24KC2ThetaAboveNode000123100 e24KC2ThetaAboveNode000123101 e24KC2ThetaAboveNode000123102
      e24KC2ThetaAboveNode000123103

theorem e24KC2ThetaAboveNode00012311 :
    adaptiveCoverCheck 11 thetaAboveCell00012311 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell00012311
    e24KC2ThetaAboveNode000123110 e24KC2ThetaAboveNode000123111 e24KC2ThetaAboveNode000123112
      e24KC2ThetaAboveNode000123113

theorem e24KC2ThetaAboveNode00012312 :
    adaptiveCoverCheck 11 thetaAboveCell00012312 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell00012312
    e24KC2ThetaAboveNode000123120 e24KC2ThetaAboveNode000123121 e24KC2ThetaAboveLeaf000123122
      e24KC2ThetaAboveLeaf000123123

theorem e24KC2ThetaAboveNode00012313 :
    adaptiveCoverCheck 11 thetaAboveCell00012313 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell00012313
    e24KC2ThetaAboveNode000123130 e24KC2ThetaAboveNode000123131 e24KC2ThetaAboveLeaf000123132
      e24KC2ThetaAboveLeaf000123133

theorem e24KC2ThetaAboveNode00013022 :
    adaptiveCoverCheck 11 thetaAboveCell00013022 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell00013022
    e24KC2ThetaAboveLeaf000130220 e24KC2ThetaAboveLeaf000130221 e24KC2ThetaAboveLeaf000130222
      e24KC2ThetaAboveLeaf000130223

theorem e24KC2ThetaAboveNode00013023 :
    adaptiveCoverCheck 11 thetaAboveCell00013023 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell00013023
    e24KC2ThetaAboveLeaf000130230 e24KC2ThetaAboveLeaf000130231 e24KC2ThetaAboveLeaf000130232
      e24KC2ThetaAboveLeaf000130233

theorem e24KC2ThetaAboveNode00013032 :
    adaptiveCoverCheck 11 thetaAboveCell00013032 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell00013032
    e24KC2ThetaAboveLeaf000130320 e24KC2ThetaAboveLeaf000130321 e24KC2ThetaAboveLeaf000130322
      e24KC2ThetaAboveLeaf000130323

theorem e24KC2ThetaAboveNode00013033 :
    adaptiveCoverCheck 11 thetaAboveCell00013033 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell00013033
    e24KC2ThetaAboveLeaf000130330 e24KC2ThetaAboveLeaf000130331 e24KC2ThetaAboveLeaf000130332
      e24KC2ThetaAboveLeaf000130333

theorem e24KC2ThetaAboveNode00013122 :
    adaptiveCoverCheck 11 thetaAboveCell00013122 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell00013122
    e24KC2ThetaAboveLeaf000131220 e24KC2ThetaAboveLeaf000131221 e24KC2ThetaAboveLeaf000131222
      e24KC2ThetaAboveLeaf000131223

theorem e24KC2ThetaAboveNode00013123 :
    adaptiveCoverCheck 11 thetaAboveCell00013123 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell00013123
    e24KC2ThetaAboveLeaf000131230 e24KC2ThetaAboveLeaf000131231 e24KC2ThetaAboveLeaf000131232
      e24KC2ThetaAboveLeaf000131233

theorem e24KC2ThetaAboveNode00013132 :
    adaptiveCoverCheck 11 thetaAboveCell00013132 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell00013132
    e24KC2ThetaAboveLeaf000131320 e24KC2ThetaAboveLeaf000131321 e24KC2ThetaAboveLeaf000131322
      e24KC2ThetaAboveLeaf000131323

theorem e24KC2ThetaAboveNode00013133 :
    adaptiveCoverCheck 11 thetaAboveCell00013133 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell00013133
    e24KC2ThetaAboveLeaf000131330 e24KC2ThetaAboveLeaf000131331 e24KC2ThetaAboveLeaf000131332
      e24KC2ThetaAboveLeaf000131333

theorem e24KC2ThetaAboveNode00013200 :
    adaptiveCoverCheck 11 thetaAboveCell00013200 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell00013200
    e24KC2ThetaAboveNode000132000 e24KC2ThetaAboveNode000132001 e24KC2ThetaAboveNode000132002
      e24KC2ThetaAboveNode000132003

theorem e24KC2ThetaAboveNode00013201 :
    adaptiveCoverCheck 11 thetaAboveCell00013201 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell00013201
    e24KC2ThetaAboveNode000132010 e24KC2ThetaAboveNode000132011 e24KC2ThetaAboveNode000132012
      e24KC2ThetaAboveNode000132013

theorem e24KC2ThetaAboveNode00013202 :
    adaptiveCoverCheck 11 thetaAboveCell00013202 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell00013202
    e24KC2ThetaAboveNode000132020 e24KC2ThetaAboveNode000132021 e24KC2ThetaAboveLeaf000132022
      e24KC2ThetaAboveLeaf000132023

theorem e24KC2ThetaAboveNode00013203 :
    adaptiveCoverCheck 11 thetaAboveCell00013203 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell00013203
    e24KC2ThetaAboveNode000132030 e24KC2ThetaAboveNode000132031 e24KC2ThetaAboveLeaf000132032
      e24KC2ThetaAboveLeaf000132033

theorem e24KC2ThetaAboveNode00013210 :
    adaptiveCoverCheck 11 thetaAboveCell00013210 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell00013210
    e24KC2ThetaAboveNode000132100 e24KC2ThetaAboveNode000132101 e24KC2ThetaAboveNode000132102
      e24KC2ThetaAboveNode000132103

theorem e24KC2ThetaAboveNode00013211 :
    adaptiveCoverCheck 11 thetaAboveCell00013211 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell00013211
    e24KC2ThetaAboveNode000132110 e24KC2ThetaAboveNode000132111 e24KC2ThetaAboveNode000132112
      e24KC2ThetaAboveNode000132113

theorem e24KC2ThetaAboveNode00013212 :
    adaptiveCoverCheck 11 thetaAboveCell00013212 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell00013212
    e24KC2ThetaAboveNode000132120 e24KC2ThetaAboveNode000132121 e24KC2ThetaAboveLeaf000132122
      e24KC2ThetaAboveLeaf000132123

theorem e24KC2ThetaAboveNode00013213 :
    adaptiveCoverCheck 11 thetaAboveCell00013213 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell00013213
    e24KC2ThetaAboveNode000132130 e24KC2ThetaAboveNode000132131 e24KC2ThetaAboveLeaf000132132
      e24KC2ThetaAboveLeaf000132133

theorem e24KC2ThetaAboveNode00013300 :
    adaptiveCoverCheck 11 thetaAboveCell00013300 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell00013300
    e24KC2ThetaAboveNode000133000 e24KC2ThetaAboveNode000133001 e24KC2ThetaAboveNode000133002
      e24KC2ThetaAboveNode000133003

theorem e24KC2ThetaAboveNode00013301 :
    adaptiveCoverCheck 11 thetaAboveCell00013301 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell00013301
    e24KC2ThetaAboveNode000133010 e24KC2ThetaAboveNode000133011 e24KC2ThetaAboveNode000133012
      e24KC2ThetaAboveNode000133013

theorem e24KC2ThetaAboveNode00013302 :
    adaptiveCoverCheck 11 thetaAboveCell00013302 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell00013302
    e24KC2ThetaAboveNode000133020 e24KC2ThetaAboveNode000133021 e24KC2ThetaAboveLeaf000133022
      e24KC2ThetaAboveLeaf000133023

theorem e24KC2ThetaAboveNode00013303 :
    adaptiveCoverCheck 11 thetaAboveCell00013303 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell00013303
    e24KC2ThetaAboveNode000133030 e24KC2ThetaAboveNode000133031 e24KC2ThetaAboveLeaf000133032
      e24KC2ThetaAboveLeaf000133033

theorem e24KC2ThetaAboveNode00013310 :
    adaptiveCoverCheck 11 thetaAboveCell00013310 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell00013310
    e24KC2ThetaAboveNode000133100 e24KC2ThetaAboveNode000133101 e24KC2ThetaAboveNode000133102
      e24KC2ThetaAboveNode000133103

theorem e24KC2ThetaAboveNode00013311 :
    adaptiveCoverCheck 11 thetaAboveCell00013311 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell00013311
    e24KC2ThetaAboveNode000133110 e24KC2ThetaAboveNode000133111 e24KC2ThetaAboveNode000133112
      e24KC2ThetaAboveNode000133113

theorem e24KC2ThetaAboveNode00013312 :
    adaptiveCoverCheck 11 thetaAboveCell00013312 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell00013312
    e24KC2ThetaAboveNode000133120 e24KC2ThetaAboveNode000133121 e24KC2ThetaAboveLeaf000133122
      e24KC2ThetaAboveLeaf000133123

theorem e24KC2ThetaAboveNode00013313 :
    adaptiveCoverCheck 11 thetaAboveCell00013313 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell00013313
    e24KC2ThetaAboveNode000133130 e24KC2ThetaAboveNode000133131 e24KC2ThetaAboveLeaf000133132
      e24KC2ThetaAboveLeaf000133133

theorem e24KC2ThetaAboveNode00102022 :
    adaptiveCoverCheck 11 thetaAboveCell00102022 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell00102022
    e24KC2ThetaAboveLeaf001020220 e24KC2ThetaAboveLeaf001020221 e24KC2ThetaAboveLeaf001020222
      e24KC2ThetaAboveLeaf001020223

theorem e24KC2ThetaAboveNode00102023 :
    adaptiveCoverCheck 11 thetaAboveCell00102023 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell00102023
    e24KC2ThetaAboveLeaf001020230 e24KC2ThetaAboveLeaf001020231 e24KC2ThetaAboveLeaf001020232
      e24KC2ThetaAboveLeaf001020233

theorem e24KC2ThetaAboveNode00102032 :
    adaptiveCoverCheck 11 thetaAboveCell00102032 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell00102032
    e24KC2ThetaAboveLeaf001020320 e24KC2ThetaAboveLeaf001020321 e24KC2ThetaAboveLeaf001020322
      e24KC2ThetaAboveLeaf001020323

theorem e24KC2ThetaAboveNode00102033 :
    adaptiveCoverCheck 11 thetaAboveCell00102033 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell00102033
    e24KC2ThetaAboveLeaf001020330 e24KC2ThetaAboveLeaf001020331 e24KC2ThetaAboveLeaf001020332
      e24KC2ThetaAboveLeaf001020333

theorem e24KC2ThetaAboveNode00102122 :
    adaptiveCoverCheck 11 thetaAboveCell00102122 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell00102122
    e24KC2ThetaAboveLeaf001021220 e24KC2ThetaAboveLeaf001021221 e24KC2ThetaAboveLeaf001021222
      e24KC2ThetaAboveLeaf001021223

theorem e24KC2ThetaAboveNode00102123 :
    adaptiveCoverCheck 11 thetaAboveCell00102123 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell00102123
    e24KC2ThetaAboveLeaf001021230 e24KC2ThetaAboveLeaf001021231 e24KC2ThetaAboveLeaf001021232
      e24KC2ThetaAboveLeaf001021233

theorem e24KC2ThetaAboveNode00102132 :
    adaptiveCoverCheck 11 thetaAboveCell00102132 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell00102132
    e24KC2ThetaAboveLeaf001021320 e24KC2ThetaAboveLeaf001021321 e24KC2ThetaAboveLeaf001021322
      e24KC2ThetaAboveLeaf001021323

theorem e24KC2ThetaAboveNode00102133 :
    adaptiveCoverCheck 11 thetaAboveCell00102133 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell00102133
    e24KC2ThetaAboveLeaf001021330 e24KC2ThetaAboveLeaf001021331 e24KC2ThetaAboveLeaf001021332
      e24KC2ThetaAboveLeaf001021333

theorem e24KC2ThetaAboveNode00102200 :
    adaptiveCoverCheck 11 thetaAboveCell00102200 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell00102200
    e24KC2ThetaAboveNode001022000 e24KC2ThetaAboveNode001022001 e24KC2ThetaAboveNode001022002
      e24KC2ThetaAboveNode001022003

theorem e24KC2ThetaAboveNode00102201 :
    adaptiveCoverCheck 11 thetaAboveCell00102201 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell00102201
    e24KC2ThetaAboveNode001022010 e24KC2ThetaAboveNode001022011 e24KC2ThetaAboveNode001022012
      e24KC2ThetaAboveNode001022013

theorem e24KC2ThetaAboveNode00102202 :
    adaptiveCoverCheck 11 thetaAboveCell00102202 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell00102202
    e24KC2ThetaAboveNode001022020 e24KC2ThetaAboveNode001022021 e24KC2ThetaAboveLeaf001022022
      e24KC2ThetaAboveLeaf001022023

theorem e24KC2ThetaAboveNode00102203 :
    adaptiveCoverCheck 11 thetaAboveCell00102203 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell00102203
    e24KC2ThetaAboveNode001022030 e24KC2ThetaAboveNode001022031 e24KC2ThetaAboveLeaf001022032
      e24KC2ThetaAboveLeaf001022033

theorem e24KC2ThetaAboveNode00102210 :
    adaptiveCoverCheck 11 thetaAboveCell00102210 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell00102210
    e24KC2ThetaAboveNode001022100 e24KC2ThetaAboveNode001022101 e24KC2ThetaAboveNode001022102
      e24KC2ThetaAboveNode001022103

theorem e24KC2ThetaAboveNode00102211 :
    adaptiveCoverCheck 11 thetaAboveCell00102211 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell00102211
    e24KC2ThetaAboveNode001022110 e24KC2ThetaAboveNode001022111 e24KC2ThetaAboveNode001022112
      e24KC2ThetaAboveNode001022113

theorem e24KC2ThetaAboveNode00102212 :
    adaptiveCoverCheck 11 thetaAboveCell00102212 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell00102212
    e24KC2ThetaAboveNode001022120 e24KC2ThetaAboveNode001022121 e24KC2ThetaAboveLeaf001022122
      e24KC2ThetaAboveLeaf001022123

theorem e24KC2ThetaAboveNode00102213 :
    adaptiveCoverCheck 11 thetaAboveCell00102213 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell00102213
    e24KC2ThetaAboveNode001022130 e24KC2ThetaAboveNode001022131 e24KC2ThetaAboveLeaf001022132
      e24KC2ThetaAboveLeaf001022133

theorem e24KC2ThetaAboveNode00102300 :
    adaptiveCoverCheck 11 thetaAboveCell00102300 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell00102300
    e24KC2ThetaAboveNode001023000 e24KC2ThetaAboveNode001023001 e24KC2ThetaAboveNode001023002
      e24KC2ThetaAboveNode001023003

theorem e24KC2ThetaAboveNode00102301 :
    adaptiveCoverCheck 11 thetaAboveCell00102301 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell00102301
    e24KC2ThetaAboveNode001023010 e24KC2ThetaAboveNode001023011 e24KC2ThetaAboveNode001023012
      e24KC2ThetaAboveNode001023013

theorem e24KC2ThetaAboveNode00102302 :
    adaptiveCoverCheck 11 thetaAboveCell00102302 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell00102302
    e24KC2ThetaAboveNode001023020 e24KC2ThetaAboveNode001023021 e24KC2ThetaAboveLeaf001023022
      e24KC2ThetaAboveLeaf001023023

theorem e24KC2ThetaAboveNode00102303 :
    adaptiveCoverCheck 11 thetaAboveCell00102303 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell00102303
    e24KC2ThetaAboveNode001023030 e24KC2ThetaAboveNode001023031 e24KC2ThetaAboveLeaf001023032
      e24KC2ThetaAboveLeaf001023033

theorem e24KC2ThetaAboveNode00102310 :
    adaptiveCoverCheck 11 thetaAboveCell00102310 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell00102310
    e24KC2ThetaAboveNode001023100 e24KC2ThetaAboveNode001023101 e24KC2ThetaAboveNode001023102
      e24KC2ThetaAboveNode001023103

theorem e24KC2ThetaAboveNode00102311 :
    adaptiveCoverCheck 11 thetaAboveCell00102311 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell00102311
    e24KC2ThetaAboveNode001023110 e24KC2ThetaAboveNode001023111 e24KC2ThetaAboveNode001023112
      e24KC2ThetaAboveNode001023113

theorem e24KC2ThetaAboveNode00102312 :
    adaptiveCoverCheck 11 thetaAboveCell00102312 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell00102312
    e24KC2ThetaAboveNode001023120 e24KC2ThetaAboveNode001023121 e24KC2ThetaAboveLeaf001023122
      e24KC2ThetaAboveLeaf001023123

theorem e24KC2ThetaAboveNode00102313 :
    adaptiveCoverCheck 11 thetaAboveCell00102313 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell00102313
    e24KC2ThetaAboveNode001023130 e24KC2ThetaAboveNode001023131 e24KC2ThetaAboveLeaf001023132
      e24KC2ThetaAboveLeaf001023133

theorem e24KC2ThetaAboveNode00103200 :
    adaptiveCoverCheck 11 thetaAboveCell00103200 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell00103200
    e24KC2ThetaAboveNode001032000 e24KC2ThetaAboveNode001032001 e24KC2ThetaAboveNode001032002
      e24KC2ThetaAboveNode001032003

theorem e24KC2ThetaAboveNode00103201 :
    adaptiveCoverCheck 11 thetaAboveCell00103201 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell00103201
    e24KC2ThetaAboveNode001032010 e24KC2ThetaAboveNode001032011 e24KC2ThetaAboveNode001032012
      e24KC2ThetaAboveNode001032013

theorem e24KC2ThetaAboveNode00103202 :
    adaptiveCoverCheck 11 thetaAboveCell00103202 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell00103202
    e24KC2ThetaAboveNode001032020 e24KC2ThetaAboveNode001032021 e24KC2ThetaAboveLeaf001032022
      e24KC2ThetaAboveLeaf001032023

theorem e24KC2ThetaAboveNode00103203 :
    adaptiveCoverCheck 11 thetaAboveCell00103203 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell00103203
    e24KC2ThetaAboveNode001032030 e24KC2ThetaAboveNode001032031 e24KC2ThetaAboveLeaf001032032
      e24KC2ThetaAboveLeaf001032033

theorem e24KC2ThetaAboveNode00103210 :
    adaptiveCoverCheck 11 thetaAboveCell00103210 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell00103210
    e24KC2ThetaAboveNode001032100 e24KC2ThetaAboveNode001032101 e24KC2ThetaAboveNode001032102
      e24KC2ThetaAboveNode001032103

theorem e24KC2ThetaAboveNode00103211 :
    adaptiveCoverCheck 11 thetaAboveCell00103211 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell00103211
    e24KC2ThetaAboveNode001032110 e24KC2ThetaAboveNode001032111 e24KC2ThetaAboveNode001032112
      e24KC2ThetaAboveNode001032113

theorem e24KC2ThetaAboveNode00103212 :
    adaptiveCoverCheck 11 thetaAboveCell00103212 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell00103212
    e24KC2ThetaAboveNode001032120 e24KC2ThetaAboveNode001032121 e24KC2ThetaAboveLeaf001032122
      e24KC2ThetaAboveLeaf001032123

theorem e24KC2ThetaAboveNode00103213 :
    adaptiveCoverCheck 11 thetaAboveCell00103213 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell00103213
    e24KC2ThetaAboveNode001032130 e24KC2ThetaAboveNode001032131 e24KC2ThetaAboveLeaf001032132
      e24KC2ThetaAboveLeaf001032133

theorem e24KC2ThetaAboveNode00103300 :
    adaptiveCoverCheck 11 thetaAboveCell00103300 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell00103300
    e24KC2ThetaAboveNode001033000 e24KC2ThetaAboveNode001033001 e24KC2ThetaAboveNode001033002
      e24KC2ThetaAboveNode001033003

theorem e24KC2ThetaAboveNode00103301 :
    adaptiveCoverCheck 11 thetaAboveCell00103301 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell00103301
    e24KC2ThetaAboveNode001033010 e24KC2ThetaAboveNode001033011 e24KC2ThetaAboveNode001033012
      e24KC2ThetaAboveNode001033013

theorem e24KC2ThetaAboveNode00103302 :
    adaptiveCoverCheck 11 thetaAboveCell00103302 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell00103302
    e24KC2ThetaAboveNode001033020 e24KC2ThetaAboveNode001033021 e24KC2ThetaAboveLeaf001033022
      e24KC2ThetaAboveLeaf001033023

theorem e24KC2ThetaAboveNode00103303 :
    adaptiveCoverCheck 11 thetaAboveCell00103303 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell00103303
    e24KC2ThetaAboveNode001033030 e24KC2ThetaAboveNode001033031 e24KC2ThetaAboveLeaf001033032
      e24KC2ThetaAboveLeaf001033033

theorem e24KC2ThetaAboveNode00103310 :
    adaptiveCoverCheck 11 thetaAboveCell00103310 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell00103310
    e24KC2ThetaAboveNode001033100 e24KC2ThetaAboveNode001033101 e24KC2ThetaAboveNode001033102
      e24KC2ThetaAboveNode001033103

theorem e24KC2ThetaAboveNode00103311 :
    adaptiveCoverCheck 11 thetaAboveCell00103311 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell00103311
    e24KC2ThetaAboveNode001033110 e24KC2ThetaAboveNode001033111 e24KC2ThetaAboveNode001033112
      e24KC2ThetaAboveNode001033113

theorem e24KC2ThetaAboveNode00103312 :
    adaptiveCoverCheck 11 thetaAboveCell00103312 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell00103312
    e24KC2ThetaAboveNode001033120 e24KC2ThetaAboveNode001033121 e24KC2ThetaAboveLeaf001033122
      e24KC2ThetaAboveLeaf001033123

theorem e24KC2ThetaAboveNode00103313 :
    adaptiveCoverCheck 11 thetaAboveCell00103313 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell00103313
    e24KC2ThetaAboveNode001033130 e24KC2ThetaAboveNode001033131 e24KC2ThetaAboveLeaf001033132
      e24KC2ThetaAboveLeaf001033133

theorem e24KC2ThetaAboveNode00112200 :
    adaptiveCoverCheck 11 thetaAboveCell00112200 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell00112200
    e24KC2ThetaAboveNode001122000 e24KC2ThetaAboveNode001122001 e24KC2ThetaAboveNode001122002
      e24KC2ThetaAboveNode001122003

theorem e24KC2ThetaAboveNode00112201 :
    adaptiveCoverCheck 11 thetaAboveCell00112201 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell00112201
    e24KC2ThetaAboveNode001122010 e24KC2ThetaAboveNode001122011 e24KC2ThetaAboveNode001122012
      e24KC2ThetaAboveNode001122013

theorem e24KC2ThetaAboveNode00112202 :
    adaptiveCoverCheck 11 thetaAboveCell00112202 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell00112202
    e24KC2ThetaAboveNode001122020 e24KC2ThetaAboveNode001122021 e24KC2ThetaAboveLeaf001122022
      e24KC2ThetaAboveLeaf001122023

theorem e24KC2ThetaAboveNode00112203 :
    adaptiveCoverCheck 11 thetaAboveCell00112203 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell00112203
    e24KC2ThetaAboveNode001122030 e24KC2ThetaAboveNode001122031 e24KC2ThetaAboveLeaf001122032
      e24KC2ThetaAboveLeaf001122033

theorem e24KC2ThetaAboveNode00112210 :
    adaptiveCoverCheck 11 thetaAboveCell00112210 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell00112210
    e24KC2ThetaAboveNode001122100 e24KC2ThetaAboveLeaf001122101 e24KC2ThetaAboveNode001122102
      e24KC2ThetaAboveNode001122103

theorem e24KC2ThetaAboveNode00112211 :
    adaptiveCoverCheck 11 thetaAboveCell00112211 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell00112211
    e24KC2ThetaAboveLeaf001122110 e24KC2ThetaAboveLeaf001122111 e24KC2ThetaAboveNode001122112
      e24KC2ThetaAboveNode001122113

theorem e24KC2ThetaAboveNode00112212 :
    adaptiveCoverCheck 11 thetaAboveCell00112212 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell00112212
    e24KC2ThetaAboveNode001122120 e24KC2ThetaAboveNode001122121 e24KC2ThetaAboveLeaf001122122
      e24KC2ThetaAboveLeaf001122123

theorem e24KC2ThetaAboveNode00112213 :
    adaptiveCoverCheck 11 thetaAboveCell00112213 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell00112213
    e24KC2ThetaAboveNode001122130 e24KC2ThetaAboveNode001122131 e24KC2ThetaAboveLeaf001122132
      e24KC2ThetaAboveLeaf001122133

theorem e24KC2ThetaAboveNode00112300 :
    adaptiveCoverCheck 11 thetaAboveCell00112300 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell00112300
    e24KC2ThetaAboveLeaf001123000 e24KC2ThetaAboveLeaf001123001 e24KC2ThetaAboveNode001123002
      e24KC2ThetaAboveNode001123003

theorem e24KC2ThetaAboveNode00112301 :
    adaptiveCoverCheck 11 thetaAboveCell00112301 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell00112301
    e24KC2ThetaAboveLeaf001123010 e24KC2ThetaAboveLeaf001123011 e24KC2ThetaAboveNode001123012
      e24KC2ThetaAboveNode001123013

theorem e24KC2ThetaAboveNode00112302 :
    adaptiveCoverCheck 11 thetaAboveCell00112302 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell00112302
    e24KC2ThetaAboveNode001123020 e24KC2ThetaAboveNode001123021 e24KC2ThetaAboveLeaf001123022
      e24KC2ThetaAboveLeaf001123023

theorem e24KC2ThetaAboveNode00112303 :
    adaptiveCoverCheck 11 thetaAboveCell00112303 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell00112303
    e24KC2ThetaAboveNode001123030 e24KC2ThetaAboveNode001123031 e24KC2ThetaAboveLeaf001123032
      e24KC2ThetaAboveLeaf001123033

theorem e24KC2ThetaAboveNode00112310 :
    adaptiveCoverCheck 11 thetaAboveCell00112310 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell00112310
    e24KC2ThetaAboveLeaf001123100 e24KC2ThetaAboveLeaf001123101 e24KC2ThetaAboveNode001123102
      e24KC2ThetaAboveNode001123103

theorem e24KC2ThetaAboveNode00112311 :
    adaptiveCoverCheck 11 thetaAboveCell00112311 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell00112311
    e24KC2ThetaAboveLeaf001123110 e24KC2ThetaAboveLeaf001123111 e24KC2ThetaAboveNode001123112
      e24KC2ThetaAboveNode001123113

theorem e24KC2ThetaAboveNode00112312 :
    adaptiveCoverCheck 11 thetaAboveCell00112312 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell00112312
    e24KC2ThetaAboveNode001123120 e24KC2ThetaAboveNode001123121 e24KC2ThetaAboveLeaf001123122
      e24KC2ThetaAboveLeaf001123123

theorem e24KC2ThetaAboveNode00112313 :
    adaptiveCoverCheck 11 thetaAboveCell00112313 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell00112313
    e24KC2ThetaAboveNode001123130 e24KC2ThetaAboveNode001123131 e24KC2ThetaAboveLeaf001123132
      e24KC2ThetaAboveLeaf001123133

theorem e24KC2ThetaAboveNode00113200 :
    adaptiveCoverCheck 11 thetaAboveCell00113200 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell00113200
    e24KC2ThetaAboveLeaf001132000 e24KC2ThetaAboveLeaf001132001 e24KC2ThetaAboveNode001132002
      e24KC2ThetaAboveNode001132003

theorem e24KC2ThetaAboveNode00113201 :
    adaptiveCoverCheck 11 thetaAboveCell00113201 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell00113201
    e24KC2ThetaAboveLeaf001132010 e24KC2ThetaAboveLeaf001132011 e24KC2ThetaAboveNode001132012
      e24KC2ThetaAboveNode001132013

theorem e24KC2ThetaAboveNode00113202 :
    adaptiveCoverCheck 11 thetaAboveCell00113202 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell00113202
    e24KC2ThetaAboveNode001132020 e24KC2ThetaAboveNode001132021 e24KC2ThetaAboveLeaf001132022
      e24KC2ThetaAboveLeaf001132023

theorem e24KC2ThetaAboveNode00113203 :
    adaptiveCoverCheck 11 thetaAboveCell00113203 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell00113203
    e24KC2ThetaAboveNode001132030 e24KC2ThetaAboveNode001132031 e24KC2ThetaAboveLeaf001132032
      e24KC2ThetaAboveLeaf001132033

theorem e24KC2ThetaAboveNode00113210 :
    adaptiveCoverCheck 11 thetaAboveCell00113210 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell00113210
    e24KC2ThetaAboveLeaf001132100 e24KC2ThetaAboveLeaf001132101 e24KC2ThetaAboveNode001132102
      e24KC2ThetaAboveNode001132103

theorem e24KC2ThetaAboveNode00113211 :
    adaptiveCoverCheck 11 thetaAboveCell00113211 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell00113211
    e24KC2ThetaAboveLeaf001132110 e24KC2ThetaAboveLeaf001132111 e24KC2ThetaAboveNode001132112
      e24KC2ThetaAboveNode001132113

theorem e24KC2ThetaAboveNode00113212 :
    adaptiveCoverCheck 11 thetaAboveCell00113212 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell00113212
    e24KC2ThetaAboveNode001132120 e24KC2ThetaAboveNode001132121 e24KC2ThetaAboveLeaf001132122
      e24KC2ThetaAboveLeaf001132123

theorem e24KC2ThetaAboveNode00113213 :
    adaptiveCoverCheck 11 thetaAboveCell00113213 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell00113213
    e24KC2ThetaAboveNode001132130 e24KC2ThetaAboveNode001132131 e24KC2ThetaAboveLeaf001132132
      e24KC2ThetaAboveLeaf001132133

theorem e24KC2ThetaAboveNode00113300 :
    adaptiveCoverCheck 11 thetaAboveCell00113300 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell00113300
    e24KC2ThetaAboveLeaf001133000 e24KC2ThetaAboveLeaf001133001 e24KC2ThetaAboveNode001133002
      e24KC2ThetaAboveNode001133003

theorem e24KC2ThetaAboveNode00113301 :
    adaptiveCoverCheck 11 thetaAboveCell00113301 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell00113301
    e24KC2ThetaAboveLeaf001133010 e24KC2ThetaAboveLeaf001133011 e24KC2ThetaAboveNode001133012
      e24KC2ThetaAboveNode001133013

theorem e24KC2ThetaAboveNode00113302 :
    adaptiveCoverCheck 11 thetaAboveCell00113302 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell00113302
    e24KC2ThetaAboveNode001133020 e24KC2ThetaAboveNode001133021 e24KC2ThetaAboveLeaf001133022
      e24KC2ThetaAboveLeaf001133023

theorem e24KC2ThetaAboveNode00113303 :
    adaptiveCoverCheck 11 thetaAboveCell00113303 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell00113303
    e24KC2ThetaAboveNode001133030 e24KC2ThetaAboveNode001133031 e24KC2ThetaAboveLeaf001133032
      e24KC2ThetaAboveLeaf001133033

theorem e24KC2ThetaAboveNode00113310 :
    adaptiveCoverCheck 11 thetaAboveCell00113310 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell00113310
    e24KC2ThetaAboveLeaf001133100 e24KC2ThetaAboveLeaf001133101 e24KC2ThetaAboveNode001133102
      e24KC2ThetaAboveNode001133103

theorem e24KC2ThetaAboveNode00113311 :
    adaptiveCoverCheck 11 thetaAboveCell00113311 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell00113311
    e24KC2ThetaAboveLeaf001133110 e24KC2ThetaAboveLeaf001133111 e24KC2ThetaAboveNode001133112
      e24KC2ThetaAboveNode001133113

theorem e24KC2ThetaAboveNode00113312 :
    adaptiveCoverCheck 11 thetaAboveCell00113312 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell00113312
    e24KC2ThetaAboveNode001133120 e24KC2ThetaAboveNode001133121 e24KC2ThetaAboveLeaf001133122
      e24KC2ThetaAboveLeaf001133123

theorem e24KC2ThetaAboveNode00113313 :
    adaptiveCoverCheck 11 thetaAboveCell00113313 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell00113313
    e24KC2ThetaAboveNode001133130 e24KC2ThetaAboveNode001133131 e24KC2ThetaAboveLeaf001133132
      e24KC2ThetaAboveLeaf001133133

theorem e24KC2ThetaAboveNode01002200 :
    adaptiveCoverCheck 11 thetaAboveCell01002200 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell01002200
    e24KC2ThetaAboveLeaf010022000 e24KC2ThetaAboveLeaf010022001 e24KC2ThetaAboveNode010022002
      e24KC2ThetaAboveNode010022003

theorem e24KC2ThetaAboveNode01002201 :
    adaptiveCoverCheck 11 thetaAboveCell01002201 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell01002201
    e24KC2ThetaAboveLeaf010022010 e24KC2ThetaAboveLeaf010022011 e24KC2ThetaAboveNode010022012
      e24KC2ThetaAboveNode010022013

theorem e24KC2ThetaAboveNode01002202 :
    adaptiveCoverCheck 11 thetaAboveCell01002202 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell01002202
    e24KC2ThetaAboveNode010022020 e24KC2ThetaAboveNode010022021 e24KC2ThetaAboveLeaf010022022
      e24KC2ThetaAboveLeaf010022023

theorem e24KC2ThetaAboveNode01002203 :
    adaptiveCoverCheck 11 thetaAboveCell01002203 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell01002203
    e24KC2ThetaAboveNode010022030 e24KC2ThetaAboveNode010022031 e24KC2ThetaAboveLeaf010022032
      e24KC2ThetaAboveLeaf010022033

theorem e24KC2ThetaAboveNode01002210 :
    adaptiveCoverCheck 11 thetaAboveCell01002210 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell01002210
    e24KC2ThetaAboveLeaf010022100 e24KC2ThetaAboveLeaf010022101 e24KC2ThetaAboveNode010022102
      e24KC2ThetaAboveNode010022103

theorem e24KC2ThetaAboveNode01002211 :
    adaptiveCoverCheck 11 thetaAboveCell01002211 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell01002211
    e24KC2ThetaAboveLeaf010022110 e24KC2ThetaAboveLeaf010022111 e24KC2ThetaAboveNode010022112
      e24KC2ThetaAboveNode010022113

theorem e24KC2ThetaAboveNode01002212 :
    adaptiveCoverCheck 11 thetaAboveCell01002212 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell01002212
    e24KC2ThetaAboveNode010022120 e24KC2ThetaAboveNode010022121 e24KC2ThetaAboveLeaf010022122
      e24KC2ThetaAboveLeaf010022123

theorem e24KC2ThetaAboveNode01002213 :
    adaptiveCoverCheck 11 thetaAboveCell01002213 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell01002213
    e24KC2ThetaAboveNode010022130 e24KC2ThetaAboveNode010022131 e24KC2ThetaAboveLeaf010022132
      e24KC2ThetaAboveLeaf010022133

theorem e24KC2ThetaAboveNode01002300 :
    adaptiveCoverCheck 11 thetaAboveCell01002300 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell01002300
    e24KC2ThetaAboveLeaf010023000 e24KC2ThetaAboveLeaf010023001 e24KC2ThetaAboveNode010023002
      e24KC2ThetaAboveNode010023003

theorem e24KC2ThetaAboveNode01002301 :
    adaptiveCoverCheck 11 thetaAboveCell01002301 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell01002301
    e24KC2ThetaAboveLeaf010023010 e24KC2ThetaAboveLeaf010023011 e24KC2ThetaAboveNode010023012
      e24KC2ThetaAboveNode010023013

theorem e24KC2ThetaAboveNode01002302 :
    adaptiveCoverCheck 11 thetaAboveCell01002302 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell01002302
    e24KC2ThetaAboveNode010023020 e24KC2ThetaAboveNode010023021 e24KC2ThetaAboveLeaf010023022
      e24KC2ThetaAboveLeaf010023023

theorem e24KC2ThetaAboveNode01002303 :
    adaptiveCoverCheck 11 thetaAboveCell01002303 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell01002303
    e24KC2ThetaAboveNode010023030 e24KC2ThetaAboveNode010023031 e24KC2ThetaAboveNode010023032
      e24KC2ThetaAboveNode010023033

theorem e24KC2ThetaAboveNode01002310 :
    adaptiveCoverCheck 11 thetaAboveCell01002310 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell01002310
    e24KC2ThetaAboveLeaf010023100 e24KC2ThetaAboveLeaf010023101 e24KC2ThetaAboveNode010023102
      e24KC2ThetaAboveNode010023103

theorem e24KC2ThetaAboveNode01002311 :
    adaptiveCoverCheck 11 thetaAboveCell01002311 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell01002311
    e24KC2ThetaAboveLeaf010023110 e24KC2ThetaAboveLeaf010023111 e24KC2ThetaAboveNode010023112
      e24KC2ThetaAboveNode010023113

theorem e24KC2ThetaAboveNode01002312 :
    adaptiveCoverCheck 11 thetaAboveCell01002312 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell01002312
    e24KC2ThetaAboveNode010023120 e24KC2ThetaAboveNode010023121 e24KC2ThetaAboveNode010023122
      e24KC2ThetaAboveNode010023123

theorem e24KC2ThetaAboveNode01002313 :
    adaptiveCoverCheck 11 thetaAboveCell01002313 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell01002313
    e24KC2ThetaAboveNode010023130 e24KC2ThetaAboveNode010023131 e24KC2ThetaAboveNode010023132
      e24KC2ThetaAboveNode010023133

theorem e24KC2ThetaAboveNode01003200 :
    adaptiveCoverCheck 11 thetaAboveCell01003200 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell01003200
    e24KC2ThetaAboveLeaf010032000 e24KC2ThetaAboveLeaf010032001 e24KC2ThetaAboveNode010032002
      e24KC2ThetaAboveNode010032003

theorem e24KC2ThetaAboveNode01003201 :
    adaptiveCoverCheck 11 thetaAboveCell01003201 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell01003201
    e24KC2ThetaAboveLeaf010032010 e24KC2ThetaAboveLeaf010032011 e24KC2ThetaAboveNode010032012
      e24KC2ThetaAboveNode010032013

theorem e24KC2ThetaAboveNode01003202 :
    adaptiveCoverCheck 11 thetaAboveCell01003202 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell01003202
    e24KC2ThetaAboveNode010032020 e24KC2ThetaAboveNode010032021 e24KC2ThetaAboveNode010032022
      e24KC2ThetaAboveNode010032023

theorem e24KC2ThetaAboveNode01003203 :
    adaptiveCoverCheck 11 thetaAboveCell01003203 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell01003203
    e24KC2ThetaAboveNode010032030 e24KC2ThetaAboveNode010032031 e24KC2ThetaAboveNode010032032
      e24KC2ThetaAboveNode010032033

theorem e24KC2ThetaAboveNode01003210 :
    adaptiveCoverCheck 11 thetaAboveCell01003210 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell01003210
    e24KC2ThetaAboveLeaf010032100 e24KC2ThetaAboveLeaf010032101 e24KC2ThetaAboveNode010032102
      e24KC2ThetaAboveNode010032103

theorem e24KC2ThetaAboveNode01003211 :
    adaptiveCoverCheck 11 thetaAboveCell01003211 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell01003211
    e24KC2ThetaAboveLeaf010032110 e24KC2ThetaAboveLeaf010032111 e24KC2ThetaAboveNode010032112
      e24KC2ThetaAboveNode010032113

theorem e24KC2ThetaAboveNode01003212 :
    adaptiveCoverCheck 11 thetaAboveCell01003212 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell01003212
    e24KC2ThetaAboveNode010032120 e24KC2ThetaAboveNode010032121 e24KC2ThetaAboveNode010032122
      e24KC2ThetaAboveNode010032123

theorem e24KC2ThetaAboveNode01003213 :
    adaptiveCoverCheck 11 thetaAboveCell01003213 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell01003213
    e24KC2ThetaAboveNode010032130 e24KC2ThetaAboveNode010032131 e24KC2ThetaAboveNode010032132
      e24KC2ThetaAboveNode010032133

theorem e24KC2ThetaAboveNode01003300 :
    adaptiveCoverCheck 11 thetaAboveCell01003300 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell01003300
    e24KC2ThetaAboveLeaf010033000 e24KC2ThetaAboveLeaf010033001 e24KC2ThetaAboveNode010033002
      e24KC2ThetaAboveNode010033003

theorem e24KC2ThetaAboveNode01003301 :
    adaptiveCoverCheck 11 thetaAboveCell01003301 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell01003301
    e24KC2ThetaAboveLeaf010033010 e24KC2ThetaAboveLeaf010033011 e24KC2ThetaAboveNode010033012
      e24KC2ThetaAboveNode010033013

theorem e24KC2ThetaAboveNode01003302 :
    adaptiveCoverCheck 11 thetaAboveCell01003302 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell01003302
    e24KC2ThetaAboveNode010033020 e24KC2ThetaAboveNode010033021 e24KC2ThetaAboveNode010033022
      e24KC2ThetaAboveNode010033023

theorem e24KC2ThetaAboveNode01003303 :
    adaptiveCoverCheck 11 thetaAboveCell01003303 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell01003303
    e24KC2ThetaAboveNode010033030 e24KC2ThetaAboveNode010033031 e24KC2ThetaAboveNode010033032
      e24KC2ThetaAboveNode010033033

theorem e24KC2ThetaAboveNode01003310 :
    adaptiveCoverCheck 11 thetaAboveCell01003310 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell01003310
    e24KC2ThetaAboveLeaf010033100 e24KC2ThetaAboveLeaf010033101 e24KC2ThetaAboveNode010033102
      e24KC2ThetaAboveNode010033103

theorem e24KC2ThetaAboveNode01003311 :
    adaptiveCoverCheck 11 thetaAboveCell01003311 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell01003311
    e24KC2ThetaAboveLeaf010033110 e24KC2ThetaAboveLeaf010033111 e24KC2ThetaAboveNode010033112
      e24KC2ThetaAboveNode010033113

theorem e24KC2ThetaAboveNode01003312 :
    adaptiveCoverCheck 11 thetaAboveCell01003312 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell01003312
    e24KC2ThetaAboveNode010033120 e24KC2ThetaAboveNode010033121 e24KC2ThetaAboveNode010033122
      e24KC2ThetaAboveNode010033123

theorem e24KC2ThetaAboveNode01003313 :
    adaptiveCoverCheck 11 thetaAboveCell01003313 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell01003313
    e24KC2ThetaAboveNode010033130 e24KC2ThetaAboveNode010033131 e24KC2ThetaAboveNode010033132
      e24KC2ThetaAboveNode010033133

theorem e24KC2ThetaAboveNode01003330 :
    adaptiveCoverCheck 11 thetaAboveCell01003330 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell01003330
    e24KC2ThetaAboveLeaf010033300 e24KC2ThetaAboveLeaf010033301 e24KC2ThetaAboveLeaf010033302
      e24KC2ThetaAboveLeaf010033303

theorem e24KC2ThetaAboveNode01003331 :
    adaptiveCoverCheck 11 thetaAboveCell01003331 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell01003331
    e24KC2ThetaAboveLeaf010033310 e24KC2ThetaAboveLeaf010033311 e24KC2ThetaAboveLeaf010033312
      e24KC2ThetaAboveLeaf010033313

theorem e24KC2ThetaAboveNode01012200 :
    adaptiveCoverCheck 11 thetaAboveCell01012200 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell01012200
    e24KC2ThetaAboveLeaf010122000 e24KC2ThetaAboveLeaf010122001 e24KC2ThetaAboveNode010122002
      e24KC2ThetaAboveNode010122003

theorem e24KC2ThetaAboveNode01012201 :
    adaptiveCoverCheck 11 thetaAboveCell01012201 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell01012201
    e24KC2ThetaAboveLeaf010122010 e24KC2ThetaAboveLeaf010122011 e24KC2ThetaAboveNode010122012
      e24KC2ThetaAboveNode010122013

theorem e24KC2ThetaAboveNode01012202 :
    adaptiveCoverCheck 11 thetaAboveCell01012202 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell01012202
    e24KC2ThetaAboveNode010122020 e24KC2ThetaAboveNode010122021 e24KC2ThetaAboveNode010122022
      e24KC2ThetaAboveNode010122023

theorem e24KC2ThetaAboveNode01012203 :
    adaptiveCoverCheck 11 thetaAboveCell01012203 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell01012203
    e24KC2ThetaAboveNode010122030 e24KC2ThetaAboveNode010122031 e24KC2ThetaAboveNode010122032
      e24KC2ThetaAboveNode010122033

theorem e24KC2ThetaAboveNode01012210 :
    adaptiveCoverCheck 11 thetaAboveCell01012210 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell01012210
    e24KC2ThetaAboveLeaf010122100 e24KC2ThetaAboveLeaf010122101 e24KC2ThetaAboveNode010122102
      e24KC2ThetaAboveNode010122103

theorem e24KC2ThetaAboveNode01012211 :
    adaptiveCoverCheck 11 thetaAboveCell01012211 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell01012211
    e24KC2ThetaAboveLeaf010122110 e24KC2ThetaAboveLeaf010122111 e24KC2ThetaAboveNode010122112
      e24KC2ThetaAboveNode010122113

theorem e24KC2ThetaAboveNode01012212 :
    adaptiveCoverCheck 11 thetaAboveCell01012212 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell01012212
    e24KC2ThetaAboveNode010122120 e24KC2ThetaAboveNode010122121 e24KC2ThetaAboveNode010122122
      e24KC2ThetaAboveNode010122123

theorem e24KC2ThetaAboveNode01012213 :
    adaptiveCoverCheck 11 thetaAboveCell01012213 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell01012213
    e24KC2ThetaAboveNode010122130 e24KC2ThetaAboveNode010122131 e24KC2ThetaAboveNode010122132
      e24KC2ThetaAboveNode010122133

theorem e24KC2ThetaAboveNode01012220 :
    adaptiveCoverCheck 11 thetaAboveCell01012220 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell01012220
    e24KC2ThetaAboveLeaf010122200 e24KC2ThetaAboveLeaf010122201 e24KC2ThetaAboveLeaf010122202
      e24KC2ThetaAboveLeaf010122203

theorem e24KC2ThetaAboveNode01012221 :
    adaptiveCoverCheck 11 thetaAboveCell01012221 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell01012221
    e24KC2ThetaAboveLeaf010122210 e24KC2ThetaAboveLeaf010122211 e24KC2ThetaAboveLeaf010122212
      e24KC2ThetaAboveLeaf010122213

theorem e24KC2ThetaAboveNode01012230 :
    adaptiveCoverCheck 11 thetaAboveCell01012230 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell01012230
    e24KC2ThetaAboveLeaf010122300 e24KC2ThetaAboveLeaf010122301 e24KC2ThetaAboveLeaf010122302
      e24KC2ThetaAboveLeaf010122303

theorem e24KC2ThetaAboveNode01012231 :
    adaptiveCoverCheck 11 thetaAboveCell01012231 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell01012231
    e24KC2ThetaAboveLeaf010122310 e24KC2ThetaAboveLeaf010122311 e24KC2ThetaAboveLeaf010122312
      e24KC2ThetaAboveLeaf010122313

theorem e24KC2ThetaAboveNode01012300 :
    adaptiveCoverCheck 11 thetaAboveCell01012300 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell01012300
    e24KC2ThetaAboveLeaf010123000 e24KC2ThetaAboveLeaf010123001 e24KC2ThetaAboveNode010123002
      e24KC2ThetaAboveNode010123003

theorem e24KC2ThetaAboveNode01012301 :
    adaptiveCoverCheck 11 thetaAboveCell01012301 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell01012301
    e24KC2ThetaAboveLeaf010123010 e24KC2ThetaAboveLeaf010123011 e24KC2ThetaAboveNode010123012
      e24KC2ThetaAboveNode010123013

theorem e24KC2ThetaAboveNode01012302 :
    adaptiveCoverCheck 11 thetaAboveCell01012302 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell01012302
    e24KC2ThetaAboveNode010123020 e24KC2ThetaAboveNode010123021 e24KC2ThetaAboveNode010123022
      e24KC2ThetaAboveNode010123023

theorem e24KC2ThetaAboveNode01012303 :
    adaptiveCoverCheck 11 thetaAboveCell01012303 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell01012303
    e24KC2ThetaAboveNode010123030 e24KC2ThetaAboveNode010123031 e24KC2ThetaAboveNode010123032
      e24KC2ThetaAboveNode010123033

theorem e24KC2ThetaAboveNode01012310 :
    adaptiveCoverCheck 11 thetaAboveCell01012310 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell01012310
    e24KC2ThetaAboveLeaf010123100 e24KC2ThetaAboveLeaf010123101 e24KC2ThetaAboveNode010123102
      e24KC2ThetaAboveNode010123103

theorem e24KC2ThetaAboveNode01012311 :
    adaptiveCoverCheck 11 thetaAboveCell01012311 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell01012311
    e24KC2ThetaAboveLeaf010123110 e24KC2ThetaAboveLeaf010123111 e24KC2ThetaAboveNode010123112
      e24KC2ThetaAboveNode010123113

theorem e24KC2ThetaAboveNode01012312 :
    adaptiveCoverCheck 11 thetaAboveCell01012312 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell01012312
    e24KC2ThetaAboveNode010123120 e24KC2ThetaAboveNode010123121 e24KC2ThetaAboveNode010123122
      e24KC2ThetaAboveNode010123123

theorem e24KC2ThetaAboveNode01012313 :
    adaptiveCoverCheck 11 thetaAboveCell01012313 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell01012313
    e24KC2ThetaAboveNode010123130 e24KC2ThetaAboveNode010123131 e24KC2ThetaAboveNode010123132
      e24KC2ThetaAboveNode010123133

theorem e24KC2ThetaAboveNode01012320 :
    adaptiveCoverCheck 11 thetaAboveCell01012320 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell01012320
    e24KC2ThetaAboveLeaf010123200 e24KC2ThetaAboveLeaf010123201 e24KC2ThetaAboveLeaf010123202
      e24KC2ThetaAboveLeaf010123203

theorem e24KC2ThetaAboveNode01012321 :
    adaptiveCoverCheck 11 thetaAboveCell01012321 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell01012321
    e24KC2ThetaAboveLeaf010123210 e24KC2ThetaAboveLeaf010123211 e24KC2ThetaAboveLeaf010123212
      e24KC2ThetaAboveLeaf010123213

theorem e24KC2ThetaAboveNode01012330 :
    adaptiveCoverCheck 11 thetaAboveCell01012330 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell01012330
    e24KC2ThetaAboveLeaf010123300 e24KC2ThetaAboveLeaf010123301 e24KC2ThetaAboveLeaf010123302
      e24KC2ThetaAboveLeaf010123303

theorem e24KC2ThetaAboveNode01012331 :
    adaptiveCoverCheck 11 thetaAboveCell01012331 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell01012331
    e24KC2ThetaAboveLeaf010123310 e24KC2ThetaAboveLeaf010123311 e24KC2ThetaAboveLeaf010123312
      e24KC2ThetaAboveLeaf010123313

theorem e24KC2ThetaAboveNode01013200 :
    adaptiveCoverCheck 11 thetaAboveCell01013200 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell01013200
    e24KC2ThetaAboveLeaf010132000 e24KC2ThetaAboveLeaf010132001 e24KC2ThetaAboveNode010132002
      e24KC2ThetaAboveNode010132003

theorem e24KC2ThetaAboveNode01013201 :
    adaptiveCoverCheck 11 thetaAboveCell01013201 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell01013201
    e24KC2ThetaAboveLeaf010132010 e24KC2ThetaAboveLeaf010132011 e24KC2ThetaAboveNode010132012
      e24KC2ThetaAboveNode010132013

theorem e24KC2ThetaAboveNode01013202 :
    adaptiveCoverCheck 11 thetaAboveCell01013202 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell01013202
    e24KC2ThetaAboveNode010132020 e24KC2ThetaAboveNode010132021 e24KC2ThetaAboveNode010132022
      e24KC2ThetaAboveNode010132023

theorem e24KC2ThetaAboveNode01013203 :
    adaptiveCoverCheck 11 thetaAboveCell01013203 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell01013203
    e24KC2ThetaAboveNode010132030 e24KC2ThetaAboveNode010132031 e24KC2ThetaAboveNode010132032
      e24KC2ThetaAboveNode010132033

theorem e24KC2ThetaAboveNode01013210 :
    adaptiveCoverCheck 11 thetaAboveCell01013210 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell01013210
    e24KC2ThetaAboveLeaf010132100 e24KC2ThetaAboveLeaf010132101 e24KC2ThetaAboveNode010132102
      e24KC2ThetaAboveNode010132103

theorem e24KC2ThetaAboveNode01013211 :
    adaptiveCoverCheck 11 thetaAboveCell01013211 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell01013211
    e24KC2ThetaAboveLeaf010132110 e24KC2ThetaAboveLeaf010132111 e24KC2ThetaAboveNode010132112
      e24KC2ThetaAboveNode010132113

theorem e24KC2ThetaAboveNode01013212 :
    adaptiveCoverCheck 11 thetaAboveCell01013212 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell01013212
    e24KC2ThetaAboveNode010132120 e24KC2ThetaAboveNode010132121 e24KC2ThetaAboveNode010132122
      e24KC2ThetaAboveNode010132123

theorem e24KC2ThetaAboveNode01013213 :
    adaptiveCoverCheck 11 thetaAboveCell01013213 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell01013213
    e24KC2ThetaAboveNode010132130 e24KC2ThetaAboveNode010132131 e24KC2ThetaAboveNode010132132
      e24KC2ThetaAboveNode010132133

theorem e24KC2ThetaAboveNode01013220 :
    adaptiveCoverCheck 11 thetaAboveCell01013220 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell01013220
    e24KC2ThetaAboveLeaf010132200 e24KC2ThetaAboveLeaf010132201 e24KC2ThetaAboveLeaf010132202
      e24KC2ThetaAboveLeaf010132203

theorem e24KC2ThetaAboveNode01013221 :
    adaptiveCoverCheck 11 thetaAboveCell01013221 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell01013221
    e24KC2ThetaAboveLeaf010132210 e24KC2ThetaAboveLeaf010132211 e24KC2ThetaAboveLeaf010132212
      e24KC2ThetaAboveLeaf010132213

theorem e24KC2ThetaAboveNode01013230 :
    adaptiveCoverCheck 11 thetaAboveCell01013230 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell01013230
    e24KC2ThetaAboveLeaf010132300 e24KC2ThetaAboveLeaf010132301 e24KC2ThetaAboveLeaf010132302
      e24KC2ThetaAboveLeaf010132303

theorem e24KC2ThetaAboveNode01013231 :
    adaptiveCoverCheck 11 thetaAboveCell01013231 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell01013231
    e24KC2ThetaAboveLeaf010132310 e24KC2ThetaAboveLeaf010132311 e24KC2ThetaAboveLeaf010132312
      e24KC2ThetaAboveLeaf010132313

theorem e24KC2ThetaAboveNode01013300 :
    adaptiveCoverCheck 11 thetaAboveCell01013300 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell01013300
    e24KC2ThetaAboveLeaf010133000 e24KC2ThetaAboveLeaf010133001 e24KC2ThetaAboveNode010133002
      e24KC2ThetaAboveNode010133003

theorem e24KC2ThetaAboveNode01013301 :
    adaptiveCoverCheck 11 thetaAboveCell01013301 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell01013301
    e24KC2ThetaAboveLeaf010133010 e24KC2ThetaAboveLeaf010133011 e24KC2ThetaAboveNode010133012
      e24KC2ThetaAboveNode010133013

theorem e24KC2ThetaAboveNode01013302 :
    adaptiveCoverCheck 11 thetaAboveCell01013302 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell01013302
    e24KC2ThetaAboveNode010133020 e24KC2ThetaAboveNode010133021 e24KC2ThetaAboveNode010133022
      e24KC2ThetaAboveNode010133023

theorem e24KC2ThetaAboveNode01013303 :
    adaptiveCoverCheck 11 thetaAboveCell01013303 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell01013303
    e24KC2ThetaAboveNode010133030 e24KC2ThetaAboveNode010133031 e24KC2ThetaAboveNode010133032
      e24KC2ThetaAboveNode010133033

theorem e24KC2ThetaAboveNode01013310 :
    adaptiveCoverCheck 11 thetaAboveCell01013310 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell01013310
    e24KC2ThetaAboveLeaf010133100 e24KC2ThetaAboveLeaf010133101 e24KC2ThetaAboveNode010133102
      e24KC2ThetaAboveNode010133103

theorem e24KC2ThetaAboveNode01013311 :
    adaptiveCoverCheck 11 thetaAboveCell01013311 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell01013311
    e24KC2ThetaAboveLeaf010133110 e24KC2ThetaAboveLeaf010133111 e24KC2ThetaAboveNode010133112
      e24KC2ThetaAboveNode010133113

theorem e24KC2ThetaAboveNode01013312 :
    adaptiveCoverCheck 11 thetaAboveCell01013312 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell01013312
    e24KC2ThetaAboveNode010133120 e24KC2ThetaAboveNode010133121 e24KC2ThetaAboveNode010133122
      e24KC2ThetaAboveNode010133123

theorem e24KC2ThetaAboveNode01013313 :
    adaptiveCoverCheck 11 thetaAboveCell01013313 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell01013313
    e24KC2ThetaAboveNode010133130 e24KC2ThetaAboveNode010133131 e24KC2ThetaAboveNode010133132
      e24KC2ThetaAboveNode010133133

theorem e24KC2ThetaAboveNode01013320 :
    adaptiveCoverCheck 11 thetaAboveCell01013320 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell01013320
    e24KC2ThetaAboveLeaf010133200 e24KC2ThetaAboveLeaf010133201 e24KC2ThetaAboveLeaf010133202
      e24KC2ThetaAboveLeaf010133203

theorem e24KC2ThetaAboveNode01013321 :
    adaptiveCoverCheck 11 thetaAboveCell01013321 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell01013321
    e24KC2ThetaAboveLeaf010133210 e24KC2ThetaAboveLeaf010133211 e24KC2ThetaAboveLeaf010133212
      e24KC2ThetaAboveLeaf010133213

theorem e24KC2ThetaAboveNode01013330 :
    adaptiveCoverCheck 11 thetaAboveCell01013330 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell01013330
    e24KC2ThetaAboveLeaf010133300 e24KC2ThetaAboveLeaf010133301 e24KC2ThetaAboveLeaf010133302
      e24KC2ThetaAboveLeaf010133303

theorem e24KC2ThetaAboveNode01013331 :
    adaptiveCoverCheck 11 thetaAboveCell01013331 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell01013331
    e24KC2ThetaAboveLeaf010133310 e24KC2ThetaAboveLeaf010133311 e24KC2ThetaAboveLeaf010133312
      e24KC2ThetaAboveLeaf010133313

theorem e24KC2ThetaAboveNode01102200 :
    adaptiveCoverCheck 11 thetaAboveCell01102200 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell01102200
    e24KC2ThetaAboveLeaf011022000 e24KC2ThetaAboveLeaf011022001 e24KC2ThetaAboveNode011022002
      e24KC2ThetaAboveNode011022003

theorem e24KC2ThetaAboveNode01102201 :
    adaptiveCoverCheck 11 thetaAboveCell01102201 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell01102201
    e24KC2ThetaAboveLeaf011022010 e24KC2ThetaAboveLeaf011022011 e24KC2ThetaAboveNode011022012
      e24KC2ThetaAboveNode011022013

theorem e24KC2ThetaAboveNode01102202 :
    adaptiveCoverCheck 11 thetaAboveCell01102202 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell01102202
    e24KC2ThetaAboveNode011022020 e24KC2ThetaAboveNode011022021 e24KC2ThetaAboveNode011022022
      e24KC2ThetaAboveNode011022023

theorem e24KC2ThetaAboveNode01102203 :
    adaptiveCoverCheck 11 thetaAboveCell01102203 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell01102203
    e24KC2ThetaAboveNode011022030 e24KC2ThetaAboveNode011022031 e24KC2ThetaAboveNode011022032
      e24KC2ThetaAboveNode011022033

theorem e24KC2ThetaAboveNode01102210 :
    adaptiveCoverCheck 11 thetaAboveCell01102210 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell01102210
    e24KC2ThetaAboveLeaf011022100 e24KC2ThetaAboveLeaf011022101 e24KC2ThetaAboveNode011022102
      e24KC2ThetaAboveNode011022103

theorem e24KC2ThetaAboveNode01102211 :
    adaptiveCoverCheck 11 thetaAboveCell01102211 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell01102211
    e24KC2ThetaAboveLeaf011022110 e24KC2ThetaAboveLeaf011022111 e24KC2ThetaAboveNode011022112
      e24KC2ThetaAboveNode011022113

theorem e24KC2ThetaAboveNode01102212 :
    adaptiveCoverCheck 11 thetaAboveCell01102212 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell01102212
    e24KC2ThetaAboveNode011022120 e24KC2ThetaAboveNode011022121 e24KC2ThetaAboveNode011022122
      e24KC2ThetaAboveNode011022123

theorem e24KC2ThetaAboveNode01102213 :
    adaptiveCoverCheck 11 thetaAboveCell01102213 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell01102213
    e24KC2ThetaAboveNode011022130 e24KC2ThetaAboveNode011022131 e24KC2ThetaAboveNode011022132
      e24KC2ThetaAboveNode011022133

theorem e24KC2ThetaAboveNode01102220 :
    adaptiveCoverCheck 11 thetaAboveCell01102220 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell01102220
    e24KC2ThetaAboveLeaf011022200 e24KC2ThetaAboveLeaf011022201 e24KC2ThetaAboveLeaf011022202
      e24KC2ThetaAboveLeaf011022203

theorem e24KC2ThetaAboveNode01102221 :
    adaptiveCoverCheck 11 thetaAboveCell01102221 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell01102221
    e24KC2ThetaAboveLeaf011022210 e24KC2ThetaAboveLeaf011022211 e24KC2ThetaAboveLeaf011022212
      e24KC2ThetaAboveLeaf011022213

theorem e24KC2ThetaAboveNode01102230 :
    adaptiveCoverCheck 11 thetaAboveCell01102230 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell01102230
    e24KC2ThetaAboveLeaf011022300 e24KC2ThetaAboveLeaf011022301 e24KC2ThetaAboveLeaf011022302
      e24KC2ThetaAboveLeaf011022303

theorem e24KC2ThetaAboveNode01102231 :
    adaptiveCoverCheck 11 thetaAboveCell01102231 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell01102231
    e24KC2ThetaAboveLeaf011022310 e24KC2ThetaAboveLeaf011022311 e24KC2ThetaAboveLeaf011022312
      e24KC2ThetaAboveLeaf011022313

theorem e24KC2ThetaAboveNode01102300 :
    adaptiveCoverCheck 11 thetaAboveCell01102300 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell01102300
    e24KC2ThetaAboveLeaf011023000 e24KC2ThetaAboveLeaf011023001 e24KC2ThetaAboveNode011023002
      e24KC2ThetaAboveNode011023003

theorem e24KC2ThetaAboveNode01102301 :
    adaptiveCoverCheck 11 thetaAboveCell01102301 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell01102301
    e24KC2ThetaAboveLeaf011023010 e24KC2ThetaAboveLeaf011023011 e24KC2ThetaAboveNode011023012
      e24KC2ThetaAboveNode011023013

theorem e24KC2ThetaAboveNode01102302 :
    adaptiveCoverCheck 11 thetaAboveCell01102302 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell01102302
    e24KC2ThetaAboveNode011023020 e24KC2ThetaAboveNode011023021 e24KC2ThetaAboveNode011023022
      e24KC2ThetaAboveNode011023023

theorem e24KC2ThetaAboveNode01102303 :
    adaptiveCoverCheck 11 thetaAboveCell01102303 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell01102303
    e24KC2ThetaAboveNode011023030 e24KC2ThetaAboveNode011023031 e24KC2ThetaAboveNode011023032
      e24KC2ThetaAboveNode011023033

theorem e24KC2ThetaAboveNode01102310 :
    adaptiveCoverCheck 11 thetaAboveCell01102310 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell01102310
    e24KC2ThetaAboveLeaf011023100 e24KC2ThetaAboveLeaf011023101 e24KC2ThetaAboveNode011023102
      e24KC2ThetaAboveNode011023103

theorem e24KC2ThetaAboveNode01102311 :
    adaptiveCoverCheck 11 thetaAboveCell01102311 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell01102311
    e24KC2ThetaAboveLeaf011023110 e24KC2ThetaAboveLeaf011023111 e24KC2ThetaAboveNode011023112
      e24KC2ThetaAboveNode011023113

theorem e24KC2ThetaAboveNode01102312 :
    adaptiveCoverCheck 11 thetaAboveCell01102312 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell01102312
    e24KC2ThetaAboveNode011023120 e24KC2ThetaAboveNode011023121 e24KC2ThetaAboveNode011023122
      e24KC2ThetaAboveNode011023123

theorem e24KC2ThetaAboveNode01102313 :
    adaptiveCoverCheck 11 thetaAboveCell01102313 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell01102313
    e24KC2ThetaAboveNode011023130 e24KC2ThetaAboveNode011023131 e24KC2ThetaAboveNode011023132
      e24KC2ThetaAboveNode011023133

theorem e24KC2ThetaAboveNode01102320 :
    adaptiveCoverCheck 11 thetaAboveCell01102320 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell01102320
    e24KC2ThetaAboveLeaf011023200 e24KC2ThetaAboveLeaf011023201 e24KC2ThetaAboveLeaf011023202
      e24KC2ThetaAboveLeaf011023203

theorem e24KC2ThetaAboveNode01102321 :
    adaptiveCoverCheck 11 thetaAboveCell01102321 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell01102321
    e24KC2ThetaAboveLeaf011023210 e24KC2ThetaAboveLeaf011023211 e24KC2ThetaAboveLeaf011023212
      e24KC2ThetaAboveLeaf011023213

theorem e24KC2ThetaAboveNode01102330 :
    adaptiveCoverCheck 11 thetaAboveCell01102330 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell01102330
    e24KC2ThetaAboveLeaf011023300 e24KC2ThetaAboveLeaf011023301 e24KC2ThetaAboveLeaf011023302
      e24KC2ThetaAboveLeaf011023303

theorem e24KC2ThetaAboveNode01102331 :
    adaptiveCoverCheck 11 thetaAboveCell01102331 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell01102331
    e24KC2ThetaAboveLeaf011023310 e24KC2ThetaAboveLeaf011023311 e24KC2ThetaAboveLeaf011023312
      e24KC2ThetaAboveLeaf011023313

theorem e24KC2ThetaAboveNode01103200 :
    adaptiveCoverCheck 11 thetaAboveCell01103200 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell01103200
    e24KC2ThetaAboveLeaf011032000 e24KC2ThetaAboveLeaf011032001 e24KC2ThetaAboveNode011032002
      e24KC2ThetaAboveNode011032003

theorem e24KC2ThetaAboveNode01103201 :
    adaptiveCoverCheck 11 thetaAboveCell01103201 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell01103201
    e24KC2ThetaAboveLeaf011032010 e24KC2ThetaAboveLeaf011032011 e24KC2ThetaAboveNode011032012
      e24KC2ThetaAboveNode011032013

theorem e24KC2ThetaAboveNode01103202 :
    adaptiveCoverCheck 11 thetaAboveCell01103202 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell01103202
    e24KC2ThetaAboveNode011032020 e24KC2ThetaAboveNode011032021 e24KC2ThetaAboveNode011032022
      e24KC2ThetaAboveNode011032023

theorem e24KC2ThetaAboveNode01103203 :
    adaptiveCoverCheck 11 thetaAboveCell01103203 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell01103203
    e24KC2ThetaAboveNode011032030 e24KC2ThetaAboveNode011032031 e24KC2ThetaAboveNode011032032
      e24KC2ThetaAboveNode011032033

theorem e24KC2ThetaAboveNode01103210 :
    adaptiveCoverCheck 11 thetaAboveCell01103210 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell01103210
    e24KC2ThetaAboveLeaf011032100 e24KC2ThetaAboveLeaf011032101 e24KC2ThetaAboveNode011032102
      e24KC2ThetaAboveNode011032103

theorem e24KC2ThetaAboveNode01103211 :
    adaptiveCoverCheck 11 thetaAboveCell01103211 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell01103211
    e24KC2ThetaAboveLeaf011032110 e24KC2ThetaAboveLeaf011032111 e24KC2ThetaAboveNode011032112
      e24KC2ThetaAboveNode011032113

theorem e24KC2ThetaAboveNode01103212 :
    adaptiveCoverCheck 11 thetaAboveCell01103212 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell01103212
    e24KC2ThetaAboveNode011032120 e24KC2ThetaAboveNode011032121 e24KC2ThetaAboveNode011032122
      e24KC2ThetaAboveNode011032123

theorem e24KC2ThetaAboveNode01103213 :
    adaptiveCoverCheck 11 thetaAboveCell01103213 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell01103213
    e24KC2ThetaAboveNode011032130 e24KC2ThetaAboveNode011032131 e24KC2ThetaAboveNode011032132
      e24KC2ThetaAboveNode011032133

theorem e24KC2ThetaAboveNode01103220 :
    adaptiveCoverCheck 11 thetaAboveCell01103220 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell01103220
    e24KC2ThetaAboveLeaf011032200 e24KC2ThetaAboveLeaf011032201 e24KC2ThetaAboveLeaf011032202
      e24KC2ThetaAboveLeaf011032203

theorem e24KC2ThetaAboveNode01103221 :
    adaptiveCoverCheck 11 thetaAboveCell01103221 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell01103221
    e24KC2ThetaAboveLeaf011032210 e24KC2ThetaAboveLeaf011032211 e24KC2ThetaAboveLeaf011032212
      e24KC2ThetaAboveLeaf011032213

theorem e24KC2ThetaAboveNode01103230 :
    adaptiveCoverCheck 11 thetaAboveCell01103230 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell01103230
    e24KC2ThetaAboveLeaf011032300 e24KC2ThetaAboveLeaf011032301 e24KC2ThetaAboveLeaf011032302
      e24KC2ThetaAboveLeaf011032303

theorem e24KC2ThetaAboveNode01103231 :
    adaptiveCoverCheck 11 thetaAboveCell01103231 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell01103231
    e24KC2ThetaAboveLeaf011032310 e24KC2ThetaAboveLeaf011032311 e24KC2ThetaAboveLeaf011032312
      e24KC2ThetaAboveLeaf011032313

theorem e24KC2ThetaAboveNode01103300 :
    adaptiveCoverCheck 11 thetaAboveCell01103300 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell01103300
    e24KC2ThetaAboveLeaf011033000 e24KC2ThetaAboveLeaf011033001 e24KC2ThetaAboveNode011033002
      e24KC2ThetaAboveNode011033003

theorem e24KC2ThetaAboveNode01103301 :
    adaptiveCoverCheck 11 thetaAboveCell01103301 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell01103301
    e24KC2ThetaAboveLeaf011033010 e24KC2ThetaAboveLeaf011033011 e24KC2ThetaAboveNode011033012
      e24KC2ThetaAboveNode011033013

theorem e24KC2ThetaAboveNode01103302 :
    adaptiveCoverCheck 11 thetaAboveCell01103302 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell01103302
    e24KC2ThetaAboveNode011033020 e24KC2ThetaAboveNode011033021 e24KC2ThetaAboveNode011033022
      e24KC2ThetaAboveNode011033023

theorem e24KC2ThetaAboveNode01103303 :
    adaptiveCoverCheck 11 thetaAboveCell01103303 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell01103303
    e24KC2ThetaAboveNode011033030 e24KC2ThetaAboveNode011033031 e24KC2ThetaAboveNode011033032
      e24KC2ThetaAboveNode011033033

theorem e24KC2ThetaAboveNode01103310 :
    adaptiveCoverCheck 11 thetaAboveCell01103310 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell01103310
    e24KC2ThetaAboveLeaf011033100 e24KC2ThetaAboveLeaf011033101 e24KC2ThetaAboveNode011033102
      e24KC2ThetaAboveNode011033103

theorem e24KC2ThetaAboveNode01103311 :
    adaptiveCoverCheck 11 thetaAboveCell01103311 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell01103311
    e24KC2ThetaAboveLeaf011033110 e24KC2ThetaAboveLeaf011033111 e24KC2ThetaAboveNode011033112
      e24KC2ThetaAboveNode011033113

theorem e24KC2ThetaAboveNode01103312 :
    adaptiveCoverCheck 11 thetaAboveCell01103312 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell01103312
    e24KC2ThetaAboveNode011033120 e24KC2ThetaAboveNode011033121 e24KC2ThetaAboveNode011033122
      e24KC2ThetaAboveNode011033123

theorem e24KC2ThetaAboveNode01103313 :
    adaptiveCoverCheck 11 thetaAboveCell01103313 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell01103313
    e24KC2ThetaAboveNode011033130 e24KC2ThetaAboveNode011033131 e24KC2ThetaAboveNode011033132
      e24KC2ThetaAboveNode011033133

theorem e24KC2ThetaAboveNode01103320 :
    adaptiveCoverCheck 11 thetaAboveCell01103320 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell01103320
    e24KC2ThetaAboveLeaf011033200 e24KC2ThetaAboveLeaf011033201 e24KC2ThetaAboveLeaf011033202
      e24KC2ThetaAboveLeaf011033203

theorem e24KC2ThetaAboveNode01103321 :
    adaptiveCoverCheck 11 thetaAboveCell01103321 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell01103321
    e24KC2ThetaAboveLeaf011033210 e24KC2ThetaAboveLeaf011033211 e24KC2ThetaAboveLeaf011033212
      e24KC2ThetaAboveLeaf011033213

theorem e24KC2ThetaAboveNode01103330 :
    adaptiveCoverCheck 11 thetaAboveCell01103330 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell01103330
    e24KC2ThetaAboveLeaf011033300 e24KC2ThetaAboveLeaf011033301 e24KC2ThetaAboveLeaf011033302
      e24KC2ThetaAboveLeaf011033303

theorem e24KC2ThetaAboveNode01103331 :
    adaptiveCoverCheck 11 thetaAboveCell01103331 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell01103331
    e24KC2ThetaAboveLeaf011033310 e24KC2ThetaAboveLeaf011033311 e24KC2ThetaAboveLeaf011033312
      e24KC2ThetaAboveLeaf011033313

theorem e24KC2ThetaAboveNode01112200 :
    adaptiveCoverCheck 11 thetaAboveCell01112200 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell01112200
    e24KC2ThetaAboveLeaf011122000 e24KC2ThetaAboveLeaf011122001 e24KC2ThetaAboveNode011122002
      e24KC2ThetaAboveNode011122003

theorem e24KC2ThetaAboveNode01112201 :
    adaptiveCoverCheck 11 thetaAboveCell01112201 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell01112201
    e24KC2ThetaAboveLeaf011122010 e24KC2ThetaAboveLeaf011122011 e24KC2ThetaAboveNode011122012
      e24KC2ThetaAboveNode011122013

theorem e24KC2ThetaAboveNode01112202 :
    adaptiveCoverCheck 11 thetaAboveCell01112202 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell01112202
    e24KC2ThetaAboveNode011122020 e24KC2ThetaAboveNode011122021 e24KC2ThetaAboveNode011122022
      e24KC2ThetaAboveNode011122023

theorem e24KC2ThetaAboveNode01112203 :
    adaptiveCoverCheck 11 thetaAboveCell01112203 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell01112203
    e24KC2ThetaAboveNode011122030 e24KC2ThetaAboveNode011122031 e24KC2ThetaAboveNode011122032
      e24KC2ThetaAboveNode011122033

theorem e24KC2ThetaAboveNode01112210 :
    adaptiveCoverCheck 11 thetaAboveCell01112210 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell01112210
    e24KC2ThetaAboveLeaf011122100 e24KC2ThetaAboveLeaf011122101 e24KC2ThetaAboveNode011122102
      e24KC2ThetaAboveNode011122103

theorem e24KC2ThetaAboveNode01112211 :
    adaptiveCoverCheck 11 thetaAboveCell01112211 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell01112211
    e24KC2ThetaAboveLeaf011122110 e24KC2ThetaAboveLeaf011122111 e24KC2ThetaAboveNode011122112
      e24KC2ThetaAboveNode011122113

theorem e24KC2ThetaAboveNode01112212 :
    adaptiveCoverCheck 11 thetaAboveCell01112212 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell01112212
    e24KC2ThetaAboveNode011122120 e24KC2ThetaAboveNode011122121 e24KC2ThetaAboveNode011122122
      e24KC2ThetaAboveNode011122123

theorem e24KC2ThetaAboveNode01112213 :
    adaptiveCoverCheck 11 thetaAboveCell01112213 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell01112213
    e24KC2ThetaAboveNode011122130 e24KC2ThetaAboveNode011122131 e24KC2ThetaAboveNode011122132
      e24KC2ThetaAboveNode011122133

theorem e24KC2ThetaAboveNode01112220 :
    adaptiveCoverCheck 11 thetaAboveCell01112220 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell01112220
    e24KC2ThetaAboveLeaf011122200 e24KC2ThetaAboveLeaf011122201 e24KC2ThetaAboveLeaf011122202
      e24KC2ThetaAboveLeaf011122203

theorem e24KC2ThetaAboveNode01112221 :
    adaptiveCoverCheck 11 thetaAboveCell01112221 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell01112221
    e24KC2ThetaAboveLeaf011122210 e24KC2ThetaAboveLeaf011122211 e24KC2ThetaAboveLeaf011122212
      e24KC2ThetaAboveLeaf011122213

theorem e24KC2ThetaAboveNode01112230 :
    adaptiveCoverCheck 11 thetaAboveCell01112230 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell01112230
    e24KC2ThetaAboveLeaf011122300 e24KC2ThetaAboveLeaf011122301 e24KC2ThetaAboveLeaf011122302
      e24KC2ThetaAboveLeaf011122303

theorem e24KC2ThetaAboveNode01112231 :
    adaptiveCoverCheck 11 thetaAboveCell01112231 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell01112231
    e24KC2ThetaAboveLeaf011122310 e24KC2ThetaAboveLeaf011122311 e24KC2ThetaAboveLeaf011122312
      e24KC2ThetaAboveLeaf011122313

theorem e24KC2ThetaAboveNode01112300 :
    adaptiveCoverCheck 11 thetaAboveCell01112300 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell01112300
    e24KC2ThetaAboveLeaf011123000 e24KC2ThetaAboveLeaf011123001 e24KC2ThetaAboveNode011123002
      e24KC2ThetaAboveNode011123003

theorem e24KC2ThetaAboveNode01112301 :
    adaptiveCoverCheck 11 thetaAboveCell01112301 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell01112301
    e24KC2ThetaAboveLeaf011123010 e24KC2ThetaAboveLeaf011123011 e24KC2ThetaAboveNode011123012
      e24KC2ThetaAboveNode011123013

theorem e24KC2ThetaAboveNode01112302 :
    adaptiveCoverCheck 11 thetaAboveCell01112302 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell01112302
    e24KC2ThetaAboveNode011123020 e24KC2ThetaAboveNode011123021 e24KC2ThetaAboveNode011123022
      e24KC2ThetaAboveNode011123023

theorem e24KC2ThetaAboveNode01112303 :
    adaptiveCoverCheck 11 thetaAboveCell01112303 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell01112303
    e24KC2ThetaAboveNode011123030 e24KC2ThetaAboveNode011123031 e24KC2ThetaAboveNode011123032
      e24KC2ThetaAboveNode011123033

theorem e24KC2ThetaAboveNode01112310 :
    adaptiveCoverCheck 11 thetaAboveCell01112310 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell01112310
    e24KC2ThetaAboveLeaf011123100 e24KC2ThetaAboveLeaf011123101 e24KC2ThetaAboveNode011123102
      e24KC2ThetaAboveNode011123103

theorem e24KC2ThetaAboveNode01112311 :
    adaptiveCoverCheck 11 thetaAboveCell01112311 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell01112311
    e24KC2ThetaAboveLeaf011123110 e24KC2ThetaAboveLeaf011123111 e24KC2ThetaAboveNode011123112
      e24KC2ThetaAboveNode011123113

theorem e24KC2ThetaAboveNode01112312 :
    adaptiveCoverCheck 11 thetaAboveCell01112312 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell01112312
    e24KC2ThetaAboveNode011123120 e24KC2ThetaAboveNode011123121 e24KC2ThetaAboveNode011123122
      e24KC2ThetaAboveNode011123123

theorem e24KC2ThetaAboveNode01112313 :
    adaptiveCoverCheck 11 thetaAboveCell01112313 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell01112313
    e24KC2ThetaAboveNode011123130 e24KC2ThetaAboveNode011123131 e24KC2ThetaAboveNode011123132
      e24KC2ThetaAboveNode011123133

theorem e24KC2ThetaAboveNode01112320 :
    adaptiveCoverCheck 11 thetaAboveCell01112320 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell01112320
    e24KC2ThetaAboveLeaf011123200 e24KC2ThetaAboveLeaf011123201 e24KC2ThetaAboveLeaf011123202
      e24KC2ThetaAboveLeaf011123203

theorem e24KC2ThetaAboveNode01112321 :
    adaptiveCoverCheck 11 thetaAboveCell01112321 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell01112321
    e24KC2ThetaAboveLeaf011123210 e24KC2ThetaAboveLeaf011123211 e24KC2ThetaAboveLeaf011123212
      e24KC2ThetaAboveLeaf011123213

theorem e24KC2ThetaAboveNode01112330 :
    adaptiveCoverCheck 11 thetaAboveCell01112330 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell01112330
    e24KC2ThetaAboveLeaf011123300 e24KC2ThetaAboveLeaf011123301 e24KC2ThetaAboveLeaf011123302
      e24KC2ThetaAboveLeaf011123303

theorem e24KC2ThetaAboveNode01112331 :
    adaptiveCoverCheck 11 thetaAboveCell01112331 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell01112331
    e24KC2ThetaAboveLeaf011123310 e24KC2ThetaAboveLeaf011123311 e24KC2ThetaAboveLeaf011123312
      e24KC2ThetaAboveLeaf011123313

theorem e24KC2ThetaAboveNode01113200 :
    adaptiveCoverCheck 11 thetaAboveCell01113200 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell01113200
    e24KC2ThetaAboveLeaf011132000 e24KC2ThetaAboveLeaf011132001 e24KC2ThetaAboveNode011132002
      e24KC2ThetaAboveNode011132003

theorem e24KC2ThetaAboveNode01113201 :
    adaptiveCoverCheck 11 thetaAboveCell01113201 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell01113201
    e24KC2ThetaAboveLeaf011132010 e24KC2ThetaAboveLeaf011132011 e24KC2ThetaAboveNode011132012
      e24KC2ThetaAboveNode011132013

theorem e24KC2ThetaAboveNode01113202 :
    adaptiveCoverCheck 11 thetaAboveCell01113202 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell01113202
    e24KC2ThetaAboveNode011132020 e24KC2ThetaAboveNode011132021 e24KC2ThetaAboveNode011132022
      e24KC2ThetaAboveNode011132023

theorem e24KC2ThetaAboveNode01113203 :
    adaptiveCoverCheck 11 thetaAboveCell01113203 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell01113203
    e24KC2ThetaAboveNode011132030 e24KC2ThetaAboveNode011132031 e24KC2ThetaAboveNode011132032
      e24KC2ThetaAboveNode011132033

theorem e24KC2ThetaAboveNode01113210 :
    adaptiveCoverCheck 11 thetaAboveCell01113210 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell01113210
    e24KC2ThetaAboveLeaf011132100 e24KC2ThetaAboveLeaf011132101 e24KC2ThetaAboveLeaf011132102
      e24KC2ThetaAboveLeaf011132103

theorem e24KC2ThetaAboveNode01113211 :
    adaptiveCoverCheck 11 thetaAboveCell01113211 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell01113211
    e24KC2ThetaAboveLeaf011132110 e24KC2ThetaAboveLeaf011132111 e24KC2ThetaAboveLeaf011132112
      e24KC2ThetaAboveLeaf011132113

theorem e24KC2ThetaAboveNode01113212 :
    adaptiveCoverCheck 11 thetaAboveCell01113212 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell01113212
    e24KC2ThetaAboveNode011132120 e24KC2ThetaAboveNode011132121 e24KC2ThetaAboveNode011132122
      e24KC2ThetaAboveNode011132123

theorem e24KC2ThetaAboveNode01113213 :
    adaptiveCoverCheck 11 thetaAboveCell01113213 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell01113213
    e24KC2ThetaAboveNode011132130 e24KC2ThetaAboveNode011132131 e24KC2ThetaAboveNode011132132
      e24KC2ThetaAboveNode011132133

theorem e24KC2ThetaAboveNode01113220 :
    adaptiveCoverCheck 11 thetaAboveCell01113220 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell01113220
    e24KC2ThetaAboveLeaf011132200 e24KC2ThetaAboveLeaf011132201 e24KC2ThetaAboveLeaf011132202
      e24KC2ThetaAboveLeaf011132203

theorem e24KC2ThetaAboveNode01113221 :
    adaptiveCoverCheck 11 thetaAboveCell01113221 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell01113221
    e24KC2ThetaAboveLeaf011132210 e24KC2ThetaAboveLeaf011132211 e24KC2ThetaAboveLeaf011132212
      e24KC2ThetaAboveLeaf011132213

theorem e24KC2ThetaAboveNode01113230 :
    adaptiveCoverCheck 11 thetaAboveCell01113230 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell01113230
    e24KC2ThetaAboveLeaf011132300 e24KC2ThetaAboveLeaf011132301 e24KC2ThetaAboveLeaf011132302
      e24KC2ThetaAboveLeaf011132303

theorem e24KC2ThetaAboveNode01113231 :
    adaptiveCoverCheck 11 thetaAboveCell01113231 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell01113231
    e24KC2ThetaAboveLeaf011132310 e24KC2ThetaAboveLeaf011132311 e24KC2ThetaAboveLeaf011132312
      e24KC2ThetaAboveLeaf011132313

theorem e24KC2ThetaAboveNode01113300 :
    adaptiveCoverCheck 11 thetaAboveCell01113300 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell01113300
    e24KC2ThetaAboveLeaf011133000 e24KC2ThetaAboveLeaf011133001 e24KC2ThetaAboveLeaf011133002
      e24KC2ThetaAboveLeaf011133003

theorem e24KC2ThetaAboveNode01113301 :
    adaptiveCoverCheck 11 thetaAboveCell01113301 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell01113301
    e24KC2ThetaAboveLeaf011133010 e24KC2ThetaAboveLeaf011133011 e24KC2ThetaAboveLeaf011133012
      e24KC2ThetaAboveLeaf011133013

theorem e24KC2ThetaAboveNode01113302 :
    adaptiveCoverCheck 11 thetaAboveCell01113302 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell01113302
    e24KC2ThetaAboveNode011133020 e24KC2ThetaAboveNode011133021 e24KC2ThetaAboveNode011133022
      e24KC2ThetaAboveNode011133023

theorem e24KC2ThetaAboveNode01113303 :
    adaptiveCoverCheck 11 thetaAboveCell01113303 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell01113303
    e24KC2ThetaAboveNode011133030 e24KC2ThetaAboveNode011133031 e24KC2ThetaAboveNode011133032
      e24KC2ThetaAboveNode011133033

theorem e24KC2ThetaAboveNode01113310 :
    adaptiveCoverCheck 11 thetaAboveCell01113310 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell01113310
    e24KC2ThetaAboveLeaf011133100 e24KC2ThetaAboveLeaf011133101 e24KC2ThetaAboveLeaf011133102
      e24KC2ThetaAboveLeaf011133103

theorem e24KC2ThetaAboveNode01113311 :
    adaptiveCoverCheck 11 thetaAboveCell01113311 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell01113311
    e24KC2ThetaAboveLeaf011133110 e24KC2ThetaAboveLeaf011133111 e24KC2ThetaAboveLeaf011133112
      e24KC2ThetaAboveLeaf011133113

theorem e24KC2ThetaAboveNode01113312 :
    adaptiveCoverCheck 11 thetaAboveCell01113312 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell01113312
    e24KC2ThetaAboveNode011133120 e24KC2ThetaAboveNode011133121 e24KC2ThetaAboveNode011133122
      e24KC2ThetaAboveNode011133123

theorem e24KC2ThetaAboveNode01113313 :
    adaptiveCoverCheck 11 thetaAboveCell01113313 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell01113313
    e24KC2ThetaAboveNode011133130 e24KC2ThetaAboveNode011133131 e24KC2ThetaAboveNode011133132
      e24KC2ThetaAboveNode011133133

theorem e24KC2ThetaAboveNode01113320 :
    adaptiveCoverCheck 11 thetaAboveCell01113320 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell01113320
    e24KC2ThetaAboveLeaf011133200 e24KC2ThetaAboveLeaf011133201 e24KC2ThetaAboveLeaf011133202
      e24KC2ThetaAboveLeaf011133203

theorem e24KC2ThetaAboveNode01113321 :
    adaptiveCoverCheck 11 thetaAboveCell01113321 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell01113321
    e24KC2ThetaAboveLeaf011133210 e24KC2ThetaAboveLeaf011133211 e24KC2ThetaAboveLeaf011133212
      e24KC2ThetaAboveLeaf011133213

theorem e24KC2ThetaAboveNode01113330 :
    adaptiveCoverCheck 11 thetaAboveCell01113330 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell01113330
    e24KC2ThetaAboveLeaf011133300 e24KC2ThetaAboveLeaf011133301 e24KC2ThetaAboveLeaf011133302
      e24KC2ThetaAboveLeaf011133303

theorem e24KC2ThetaAboveNode01113331 :
    adaptiveCoverCheck 11 thetaAboveCell01113331 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell01113331
    e24KC2ThetaAboveLeaf011133310 e24KC2ThetaAboveLeaf011133311 e24KC2ThetaAboveLeaf011133312
      e24KC2ThetaAboveLeaf011133313

theorem e24KC2ThetaAboveNode10002200 :
    adaptiveCoverCheck 11 thetaAboveCell10002200 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell10002200
    e24KC2ThetaAboveLeaf100022000 e24KC2ThetaAboveLeaf100022001 e24KC2ThetaAboveLeaf100022002
      e24KC2ThetaAboveLeaf100022003

theorem e24KC2ThetaAboveNode10002201 :
    adaptiveCoverCheck 11 thetaAboveCell10002201 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell10002201
    e24KC2ThetaAboveLeaf100022010 e24KC2ThetaAboveLeaf100022011 e24KC2ThetaAboveLeaf100022012
      e24KC2ThetaAboveLeaf100022013

theorem e24KC2ThetaAboveNode10002202 :
    adaptiveCoverCheck 11 thetaAboveCell10002202 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell10002202
    e24KC2ThetaAboveNode100022020 e24KC2ThetaAboveNode100022021 e24KC2ThetaAboveNode100022022
      e24KC2ThetaAboveNode100022023

theorem e24KC2ThetaAboveNode10002203 :
    adaptiveCoverCheck 11 thetaAboveCell10002203 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell10002203
    e24KC2ThetaAboveNode100022030 e24KC2ThetaAboveNode100022031 e24KC2ThetaAboveNode100022032
      e24KC2ThetaAboveNode100022033

theorem e24KC2ThetaAboveNode10002210 :
    adaptiveCoverCheck 11 thetaAboveCell10002210 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell10002210
    e24KC2ThetaAboveLeaf100022100 e24KC2ThetaAboveLeaf100022101 e24KC2ThetaAboveLeaf100022102
      e24KC2ThetaAboveLeaf100022103

theorem e24KC2ThetaAboveNode10002211 :
    adaptiveCoverCheck 11 thetaAboveCell10002211 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell10002211
    e24KC2ThetaAboveLeaf100022110 e24KC2ThetaAboveLeaf100022111 e24KC2ThetaAboveLeaf100022112
      e24KC2ThetaAboveLeaf100022113

theorem e24KC2ThetaAboveNode10002212 :
    adaptiveCoverCheck 11 thetaAboveCell10002212 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell10002212
    e24KC2ThetaAboveNode100022120 e24KC2ThetaAboveNode100022121 e24KC2ThetaAboveNode100022122
      e24KC2ThetaAboveNode100022123

theorem e24KC2ThetaAboveNode10002213 :
    adaptiveCoverCheck 11 thetaAboveCell10002213 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell10002213
    e24KC2ThetaAboveNode100022130 e24KC2ThetaAboveNode100022131 e24KC2ThetaAboveNode100022132
      e24KC2ThetaAboveNode100022133

theorem e24KC2ThetaAboveNode10002220 :
    adaptiveCoverCheck 11 thetaAboveCell10002220 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell10002220
    e24KC2ThetaAboveLeaf100022200 e24KC2ThetaAboveLeaf100022201 e24KC2ThetaAboveLeaf100022202
      e24KC2ThetaAboveLeaf100022203

theorem e24KC2ThetaAboveNode10002221 :
    adaptiveCoverCheck 11 thetaAboveCell10002221 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell10002221
    e24KC2ThetaAboveLeaf100022210 e24KC2ThetaAboveLeaf100022211 e24KC2ThetaAboveLeaf100022212
      e24KC2ThetaAboveLeaf100022213

theorem e24KC2ThetaAboveNode10002230 :
    adaptiveCoverCheck 11 thetaAboveCell10002230 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell10002230
    e24KC2ThetaAboveLeaf100022300 e24KC2ThetaAboveLeaf100022301 e24KC2ThetaAboveLeaf100022302
      e24KC2ThetaAboveLeaf100022303

theorem e24KC2ThetaAboveNode10002231 :
    adaptiveCoverCheck 11 thetaAboveCell10002231 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell10002231
    e24KC2ThetaAboveLeaf100022310 e24KC2ThetaAboveLeaf100022311 e24KC2ThetaAboveLeaf100022312
      e24KC2ThetaAboveLeaf100022313

theorem e24KC2ThetaAboveNode10002300 :
    adaptiveCoverCheck 11 thetaAboveCell10002300 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell10002300
    e24KC2ThetaAboveLeaf100023000 e24KC2ThetaAboveLeaf100023001 e24KC2ThetaAboveLeaf100023002
      e24KC2ThetaAboveLeaf100023003

theorem e24KC2ThetaAboveNode10002301 :
    adaptiveCoverCheck 11 thetaAboveCell10002301 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell10002301
    e24KC2ThetaAboveLeaf100023010 e24KC2ThetaAboveLeaf100023011 e24KC2ThetaAboveLeaf100023012
      e24KC2ThetaAboveLeaf100023013

theorem e24KC2ThetaAboveNode10002302 :
    adaptiveCoverCheck 11 thetaAboveCell10002302 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell10002302
    e24KC2ThetaAboveNode100023020 e24KC2ThetaAboveNode100023021 e24KC2ThetaAboveNode100023022
      e24KC2ThetaAboveNode100023023

theorem e24KC2ThetaAboveNode10002303 :
    adaptiveCoverCheck 11 thetaAboveCell10002303 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell10002303
    e24KC2ThetaAboveNode100023030 e24KC2ThetaAboveNode100023031 e24KC2ThetaAboveNode100023032
      e24KC2ThetaAboveNode100023033

theorem e24KC2ThetaAboveNode10002310 :
    adaptiveCoverCheck 11 thetaAboveCell10002310 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell10002310
    e24KC2ThetaAboveLeaf100023100 e24KC2ThetaAboveLeaf100023101 e24KC2ThetaAboveLeaf100023102
      e24KC2ThetaAboveLeaf100023103

theorem e24KC2ThetaAboveNode10002311 :
    adaptiveCoverCheck 11 thetaAboveCell10002311 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell10002311
    e24KC2ThetaAboveLeaf100023110 e24KC2ThetaAboveLeaf100023111 e24KC2ThetaAboveLeaf100023112
      e24KC2ThetaAboveLeaf100023113

theorem e24KC2ThetaAboveNode10002312 :
    adaptiveCoverCheck 11 thetaAboveCell10002312 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell10002312
    e24KC2ThetaAboveNode100023120 e24KC2ThetaAboveNode100023121 e24KC2ThetaAboveNode100023122
      e24KC2ThetaAboveNode100023123

theorem e24KC2ThetaAboveNode10002313 :
    adaptiveCoverCheck 11 thetaAboveCell10002313 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell10002313
    e24KC2ThetaAboveNode100023130 e24KC2ThetaAboveNode100023131 e24KC2ThetaAboveNode100023132
      e24KC2ThetaAboveNode100023133

theorem e24KC2ThetaAboveNode10002320 :
    adaptiveCoverCheck 11 thetaAboveCell10002320 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell10002320
    e24KC2ThetaAboveLeaf100023200 e24KC2ThetaAboveLeaf100023201 e24KC2ThetaAboveLeaf100023202
      e24KC2ThetaAboveLeaf100023203

theorem e24KC2ThetaAboveNode10002321 :
    adaptiveCoverCheck 11 thetaAboveCell10002321 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell10002321
    e24KC2ThetaAboveLeaf100023210 e24KC2ThetaAboveLeaf100023211 e24KC2ThetaAboveLeaf100023212
      e24KC2ThetaAboveLeaf100023213

theorem e24KC2ThetaAboveNode10002330 :
    adaptiveCoverCheck 11 thetaAboveCell10002330 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell10002330
    e24KC2ThetaAboveLeaf100023300 e24KC2ThetaAboveLeaf100023301 e24KC2ThetaAboveLeaf100023302
      e24KC2ThetaAboveLeaf100023303

theorem e24KC2ThetaAboveNode10002331 :
    adaptiveCoverCheck 11 thetaAboveCell10002331 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell10002331
    e24KC2ThetaAboveLeaf100023310 e24KC2ThetaAboveLeaf100023311 e24KC2ThetaAboveLeaf100023312
      e24KC2ThetaAboveLeaf100023313

theorem e24KC2ThetaAboveNode10003200 :
    adaptiveCoverCheck 11 thetaAboveCell10003200 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell10003200
    e24KC2ThetaAboveLeaf100032000 e24KC2ThetaAboveLeaf100032001 e24KC2ThetaAboveLeaf100032002
      e24KC2ThetaAboveLeaf100032003

theorem e24KC2ThetaAboveNode10003201 :
    adaptiveCoverCheck 11 thetaAboveCell10003201 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell10003201
    e24KC2ThetaAboveLeaf100032010 e24KC2ThetaAboveLeaf100032011 e24KC2ThetaAboveLeaf100032012
      e24KC2ThetaAboveLeaf100032013

theorem e24KC2ThetaAboveNode10003202 :
    adaptiveCoverCheck 11 thetaAboveCell10003202 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell10003202
    e24KC2ThetaAboveNode100032020 e24KC2ThetaAboveNode100032021 e24KC2ThetaAboveNode100032022
      e24KC2ThetaAboveNode100032023

theorem e24KC2ThetaAboveNode10003203 :
    adaptiveCoverCheck 11 thetaAboveCell10003203 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell10003203
    e24KC2ThetaAboveNode100032030 e24KC2ThetaAboveNode100032031 e24KC2ThetaAboveNode100032032
      e24KC2ThetaAboveNode100032033

theorem e24KC2ThetaAboveNode10003210 :
    adaptiveCoverCheck 11 thetaAboveCell10003210 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell10003210
    e24KC2ThetaAboveLeaf100032100 e24KC2ThetaAboveLeaf100032101 e24KC2ThetaAboveLeaf100032102
      e24KC2ThetaAboveLeaf100032103

theorem e24KC2ThetaAboveNode10003211 :
    adaptiveCoverCheck 11 thetaAboveCell10003211 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell10003211
    e24KC2ThetaAboveLeaf100032110 e24KC2ThetaAboveLeaf100032111 e24KC2ThetaAboveLeaf100032112
      e24KC2ThetaAboveLeaf100032113

theorem e24KC2ThetaAboveNode10003212 :
    adaptiveCoverCheck 11 thetaAboveCell10003212 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell10003212
    e24KC2ThetaAboveNode100032120 e24KC2ThetaAboveNode100032121 e24KC2ThetaAboveNode100032122
      e24KC2ThetaAboveNode100032123

theorem e24KC2ThetaAboveNode10003213 :
    adaptiveCoverCheck 11 thetaAboveCell10003213 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell10003213
    e24KC2ThetaAboveNode100032130 e24KC2ThetaAboveNode100032131 e24KC2ThetaAboveNode100032132
      e24KC2ThetaAboveNode100032133

theorem e24KC2ThetaAboveNode10003220 :
    adaptiveCoverCheck 11 thetaAboveCell10003220 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell10003220
    e24KC2ThetaAboveLeaf100032200 e24KC2ThetaAboveLeaf100032201 e24KC2ThetaAboveLeaf100032202
      e24KC2ThetaAboveLeaf100032203

theorem e24KC2ThetaAboveNode10003221 :
    adaptiveCoverCheck 11 thetaAboveCell10003221 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell10003221
    e24KC2ThetaAboveLeaf100032210 e24KC2ThetaAboveLeaf100032211 e24KC2ThetaAboveLeaf100032212
      e24KC2ThetaAboveLeaf100032213

theorem e24KC2ThetaAboveNode10003230 :
    adaptiveCoverCheck 11 thetaAboveCell10003230 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell10003230
    e24KC2ThetaAboveLeaf100032300 e24KC2ThetaAboveLeaf100032301 e24KC2ThetaAboveLeaf100032302
      e24KC2ThetaAboveLeaf100032303

theorem e24KC2ThetaAboveNode10003231 :
    adaptiveCoverCheck 11 thetaAboveCell10003231 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell10003231
    e24KC2ThetaAboveLeaf100032310 e24KC2ThetaAboveLeaf100032311 e24KC2ThetaAboveLeaf100032312
      e24KC2ThetaAboveLeaf100032313

theorem e24KC2ThetaAboveNode10003300 :
    adaptiveCoverCheck 11 thetaAboveCell10003300 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell10003300
    e24KC2ThetaAboveLeaf100033000 e24KC2ThetaAboveLeaf100033001 e24KC2ThetaAboveLeaf100033002
      e24KC2ThetaAboveLeaf100033003

theorem e24KC2ThetaAboveNode10003301 :
    adaptiveCoverCheck 11 thetaAboveCell10003301 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell10003301
    e24KC2ThetaAboveLeaf100033010 e24KC2ThetaAboveLeaf100033011 e24KC2ThetaAboveLeaf100033012
      e24KC2ThetaAboveLeaf100033013

theorem e24KC2ThetaAboveNode10003302 :
    adaptiveCoverCheck 11 thetaAboveCell10003302 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell10003302
    e24KC2ThetaAboveNode100033020 e24KC2ThetaAboveNode100033021 e24KC2ThetaAboveNode100033022
      e24KC2ThetaAboveNode100033023

theorem e24KC2ThetaAboveNode10003303 :
    adaptiveCoverCheck 11 thetaAboveCell10003303 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell10003303
    e24KC2ThetaAboveNode100033030 e24KC2ThetaAboveNode100033031 e24KC2ThetaAboveNode100033032
      e24KC2ThetaAboveNode100033033

theorem e24KC2ThetaAboveNode10003310 :
    adaptiveCoverCheck 11 thetaAboveCell10003310 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell10003310
    e24KC2ThetaAboveLeaf100033100 e24KC2ThetaAboveLeaf100033101 e24KC2ThetaAboveLeaf100033102
      e24KC2ThetaAboveLeaf100033103

theorem e24KC2ThetaAboveNode10003311 :
    adaptiveCoverCheck 11 thetaAboveCell10003311 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell10003311
    e24KC2ThetaAboveLeaf100033110 e24KC2ThetaAboveLeaf100033111 e24KC2ThetaAboveLeaf100033112
      e24KC2ThetaAboveLeaf100033113

theorem e24KC2ThetaAboveNode10003312 :
    adaptiveCoverCheck 11 thetaAboveCell10003312 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell10003312
    e24KC2ThetaAboveNode100033120 e24KC2ThetaAboveNode100033121 e24KC2ThetaAboveNode100033122
      e24KC2ThetaAboveNode100033123

theorem e24KC2ThetaAboveNode10003313 :
    adaptiveCoverCheck 11 thetaAboveCell10003313 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell10003313
    e24KC2ThetaAboveNode100033130 e24KC2ThetaAboveNode100033131 e24KC2ThetaAboveNode100033132
      e24KC2ThetaAboveNode100033133

theorem e24KC2ThetaAboveNode10003320 :
    adaptiveCoverCheck 11 thetaAboveCell10003320 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell10003320
    e24KC2ThetaAboveLeaf100033200 e24KC2ThetaAboveLeaf100033201 e24KC2ThetaAboveLeaf100033202
      e24KC2ThetaAboveLeaf100033203

theorem e24KC2ThetaAboveNode10003321 :
    adaptiveCoverCheck 11 thetaAboveCell10003321 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell10003321
    e24KC2ThetaAboveLeaf100033210 e24KC2ThetaAboveLeaf100033211 e24KC2ThetaAboveLeaf100033212
      e24KC2ThetaAboveLeaf100033213

theorem e24KC2ThetaAboveNode10003330 :
    adaptiveCoverCheck 11 thetaAboveCell10003330 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell10003330
    e24KC2ThetaAboveLeaf100033300 e24KC2ThetaAboveLeaf100033301 e24KC2ThetaAboveLeaf100033302
      e24KC2ThetaAboveLeaf100033303

theorem e24KC2ThetaAboveNode10003331 :
    adaptiveCoverCheck 11 thetaAboveCell10003331 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell10003331
    e24KC2ThetaAboveLeaf100033310 e24KC2ThetaAboveNode100033311 e24KC2ThetaAboveLeaf100033312
      e24KC2ThetaAboveLeaf100033313

theorem e24KC2ThetaAboveNode10012200 :
    adaptiveCoverCheck 11 thetaAboveCell10012200 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell10012200
    e24KC2ThetaAboveLeaf100122000 e24KC2ThetaAboveLeaf100122001 e24KC2ThetaAboveLeaf100122002
      e24KC2ThetaAboveLeaf100122003

theorem e24KC2ThetaAboveNode10012201 :
    adaptiveCoverCheck 11 thetaAboveCell10012201 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell10012201
    e24KC2ThetaAboveLeaf100122010 e24KC2ThetaAboveLeaf100122011 e24KC2ThetaAboveLeaf100122012
      e24KC2ThetaAboveLeaf100122013

theorem e24KC2ThetaAboveNode10012202 :
    adaptiveCoverCheck 11 thetaAboveCell10012202 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell10012202
    e24KC2ThetaAboveNode100122020 e24KC2ThetaAboveNode100122021 e24KC2ThetaAboveNode100122022
      e24KC2ThetaAboveNode100122023

theorem e24KC2ThetaAboveNode10012203 :
    adaptiveCoverCheck 11 thetaAboveCell10012203 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell10012203
    e24KC2ThetaAboveNode100122030 e24KC2ThetaAboveNode100122031 e24KC2ThetaAboveNode100122032
      e24KC2ThetaAboveNode100122033

theorem e24KC2ThetaAboveNode10012210 :
    adaptiveCoverCheck 11 thetaAboveCell10012210 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell10012210
    e24KC2ThetaAboveLeaf100122100 e24KC2ThetaAboveLeaf100122101 e24KC2ThetaAboveLeaf100122102
      e24KC2ThetaAboveLeaf100122103

theorem e24KC2ThetaAboveNode10012211 :
    adaptiveCoverCheck 11 thetaAboveCell10012211 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell10012211
    e24KC2ThetaAboveLeaf100122110 e24KC2ThetaAboveLeaf100122111 e24KC2ThetaAboveLeaf100122112
      e24KC2ThetaAboveLeaf100122113

theorem e24KC2ThetaAboveNode10012212 :
    adaptiveCoverCheck 11 thetaAboveCell10012212 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell10012212
    e24KC2ThetaAboveNode100122120 e24KC2ThetaAboveNode100122121 e24KC2ThetaAboveNode100122122
      e24KC2ThetaAboveNode100122123

theorem e24KC2ThetaAboveNode10012213 :
    adaptiveCoverCheck 11 thetaAboveCell10012213 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell10012213
    e24KC2ThetaAboveNode100122130 e24KC2ThetaAboveNode100122131 e24KC2ThetaAboveNode100122132
      e24KC2ThetaAboveNode100122133

theorem e24KC2ThetaAboveNode10012220 :
    adaptiveCoverCheck 11 thetaAboveCell10012220 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell10012220
    e24KC2ThetaAboveNode100122200 e24KC2ThetaAboveNode100122201 e24KC2ThetaAboveLeaf100122202
      e24KC2ThetaAboveLeaf100122203

theorem e24KC2ThetaAboveNode10012221 :
    adaptiveCoverCheck 11 thetaAboveCell10012221 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell10012221
    e24KC2ThetaAboveNode100122210 e24KC2ThetaAboveNode100122211 e24KC2ThetaAboveLeaf100122212
      e24KC2ThetaAboveLeaf100122213

theorem e24KC2ThetaAboveNode10012230 :
    adaptiveCoverCheck 11 thetaAboveCell10012230 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell10012230
    e24KC2ThetaAboveNode100122300 e24KC2ThetaAboveNode100122301 e24KC2ThetaAboveLeaf100122302
      e24KC2ThetaAboveLeaf100122303

theorem e24KC2ThetaAboveNode10012231 :
    adaptiveCoverCheck 11 thetaAboveCell10012231 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell10012231
    e24KC2ThetaAboveNode100122310 e24KC2ThetaAboveNode100122311 e24KC2ThetaAboveLeaf100122312
      e24KC2ThetaAboveLeaf100122313

theorem e24KC2ThetaAboveNode10012300 :
    adaptiveCoverCheck 11 thetaAboveCell10012300 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell10012300
    e24KC2ThetaAboveLeaf100123000 e24KC2ThetaAboveLeaf100123001 e24KC2ThetaAboveLeaf100123002
      e24KC2ThetaAboveLeaf100123003

theorem e24KC2ThetaAboveNode10012301 :
    adaptiveCoverCheck 11 thetaAboveCell10012301 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell10012301
    e24KC2ThetaAboveLeaf100123010 e24KC2ThetaAboveLeaf100123011 e24KC2ThetaAboveLeaf100123012
      e24KC2ThetaAboveLeaf100123013

theorem e24KC2ThetaAboveNode10012302 :
    adaptiveCoverCheck 11 thetaAboveCell10012302 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell10012302
    e24KC2ThetaAboveNode100123020 e24KC2ThetaAboveNode100123021 e24KC2ThetaAboveNode100123022
      e24KC2ThetaAboveNode100123023

theorem e24KC2ThetaAboveNode10012303 :
    adaptiveCoverCheck 11 thetaAboveCell10012303 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell10012303
    e24KC2ThetaAboveNode100123030 e24KC2ThetaAboveNode100123031 e24KC2ThetaAboveNode100123032
      e24KC2ThetaAboveNode100123033

theorem e24KC2ThetaAboveNode10012310 :
    adaptiveCoverCheck 11 thetaAboveCell10012310 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell10012310
    e24KC2ThetaAboveLeaf100123100 e24KC2ThetaAboveLeaf100123101 e24KC2ThetaAboveLeaf100123102
      e24KC2ThetaAboveLeaf100123103

theorem e24KC2ThetaAboveNode10012311 :
    adaptiveCoverCheck 11 thetaAboveCell10012311 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell10012311
    e24KC2ThetaAboveLeaf100123110 e24KC2ThetaAboveLeaf100123111 e24KC2ThetaAboveLeaf100123112
      e24KC2ThetaAboveLeaf100123113

theorem e24KC2ThetaAboveNode10012312 :
    adaptiveCoverCheck 11 thetaAboveCell10012312 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell10012312
    e24KC2ThetaAboveNode100123120 e24KC2ThetaAboveNode100123121 e24KC2ThetaAboveNode100123122
      e24KC2ThetaAboveNode100123123

theorem e24KC2ThetaAboveNode10012313 :
    adaptiveCoverCheck 11 thetaAboveCell10012313 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell10012313
    e24KC2ThetaAboveNode100123130 e24KC2ThetaAboveNode100123131 e24KC2ThetaAboveNode100123132
      e24KC2ThetaAboveNode100123133

theorem e24KC2ThetaAboveNode10012320 :
    adaptiveCoverCheck 11 thetaAboveCell10012320 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell10012320
    e24KC2ThetaAboveNode100123200 e24KC2ThetaAboveNode100123201 e24KC2ThetaAboveLeaf100123202
      e24KC2ThetaAboveLeaf100123203

theorem e24KC2ThetaAboveNode10012321 :
    adaptiveCoverCheck 11 thetaAboveCell10012321 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell10012321
    e24KC2ThetaAboveNode100123210 e24KC2ThetaAboveNode100123211 e24KC2ThetaAboveLeaf100123212
      e24KC2ThetaAboveLeaf100123213

theorem e24KC2ThetaAboveNode10012330 :
    adaptiveCoverCheck 11 thetaAboveCell10012330 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell10012330
    e24KC2ThetaAboveNode100123300 e24KC2ThetaAboveNode100123301 e24KC2ThetaAboveLeaf100123302
      e24KC2ThetaAboveLeaf100123303

theorem e24KC2ThetaAboveNode10012331 :
    adaptiveCoverCheck 11 thetaAboveCell10012331 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell10012331
    e24KC2ThetaAboveNode100123310 e24KC2ThetaAboveNode100123311 e24KC2ThetaAboveLeaf100123312
      e24KC2ThetaAboveLeaf100123313

theorem e24KC2ThetaAboveNode10013200 :
    adaptiveCoverCheck 11 thetaAboveCell10013200 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell10013200
    e24KC2ThetaAboveLeaf100132000 e24KC2ThetaAboveLeaf100132001 e24KC2ThetaAboveLeaf100132002
      e24KC2ThetaAboveLeaf100132003

theorem e24KC2ThetaAboveNode10013201 :
    adaptiveCoverCheck 11 thetaAboveCell10013201 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell10013201
    e24KC2ThetaAboveLeaf100132010 e24KC2ThetaAboveLeaf100132011 e24KC2ThetaAboveLeaf100132012
      e24KC2ThetaAboveLeaf100132013

theorem e24KC2ThetaAboveNode10013202 :
    adaptiveCoverCheck 11 thetaAboveCell10013202 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell10013202
    e24KC2ThetaAboveNode100132020 e24KC2ThetaAboveNode100132021 e24KC2ThetaAboveNode100132022
      e24KC2ThetaAboveNode100132023

theorem e24KC2ThetaAboveNode10013203 :
    adaptiveCoverCheck 11 thetaAboveCell10013203 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell10013203
    e24KC2ThetaAboveNode100132030 e24KC2ThetaAboveNode100132031 e24KC2ThetaAboveNode100132032
      e24KC2ThetaAboveNode100132033

theorem e24KC2ThetaAboveNode10013210 :
    adaptiveCoverCheck 11 thetaAboveCell10013210 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell10013210
    e24KC2ThetaAboveLeaf100132100 e24KC2ThetaAboveLeaf100132101 e24KC2ThetaAboveLeaf100132102
      e24KC2ThetaAboveLeaf100132103

theorem e24KC2ThetaAboveNode10013211 :
    adaptiveCoverCheck 11 thetaAboveCell10013211 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell10013211
    e24KC2ThetaAboveLeaf100132110 e24KC2ThetaAboveLeaf100132111 e24KC2ThetaAboveLeaf100132112
      e24KC2ThetaAboveLeaf100132113

theorem e24KC2ThetaAboveNode10013212 :
    adaptiveCoverCheck 11 thetaAboveCell10013212 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell10013212
    e24KC2ThetaAboveNode100132120 e24KC2ThetaAboveNode100132121 e24KC2ThetaAboveNode100132122
      e24KC2ThetaAboveNode100132123

theorem e24KC2ThetaAboveNode10013213 :
    adaptiveCoverCheck 11 thetaAboveCell10013213 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell10013213
    e24KC2ThetaAboveNode100132130 e24KC2ThetaAboveNode100132131 e24KC2ThetaAboveNode100132132
      e24KC2ThetaAboveNode100132133

theorem e24KC2ThetaAboveNode10013220 :
    adaptiveCoverCheck 11 thetaAboveCell10013220 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell10013220
    e24KC2ThetaAboveNode100132200 e24KC2ThetaAboveNode100132201 e24KC2ThetaAboveLeaf100132202
      e24KC2ThetaAboveLeaf100132203

theorem e24KC2ThetaAboveNode10013221 :
    adaptiveCoverCheck 11 thetaAboveCell10013221 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell10013221
    e24KC2ThetaAboveNode100132210 e24KC2ThetaAboveNode100132211 e24KC2ThetaAboveLeaf100132212
      e24KC2ThetaAboveLeaf100132213

theorem e24KC2ThetaAboveNode10013230 :
    adaptiveCoverCheck 11 thetaAboveCell10013230 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell10013230
    e24KC2ThetaAboveNode100132300 e24KC2ThetaAboveNode100132301 e24KC2ThetaAboveLeaf100132302
      e24KC2ThetaAboveLeaf100132303

theorem e24KC2ThetaAboveNode10013231 :
    adaptiveCoverCheck 11 thetaAboveCell10013231 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell10013231
    e24KC2ThetaAboveLeaf100132310 e24KC2ThetaAboveLeaf100132311 e24KC2ThetaAboveLeaf100132312
      e24KC2ThetaAboveLeaf100132313

theorem e24KC2ThetaAboveNode10013300 :
    adaptiveCoverCheck 11 thetaAboveCell10013300 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell10013300
    e24KC2ThetaAboveLeaf100133000 e24KC2ThetaAboveLeaf100133001 e24KC2ThetaAboveLeaf100133002
      e24KC2ThetaAboveLeaf100133003

theorem e24KC2ThetaAboveNode10013301 :
    adaptiveCoverCheck 11 thetaAboveCell10013301 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell10013301
    e24KC2ThetaAboveLeaf100133010 e24KC2ThetaAboveLeaf100133011 e24KC2ThetaAboveLeaf100133012
      e24KC2ThetaAboveLeaf100133013

theorem e24KC2ThetaAboveNode10013302 :
    adaptiveCoverCheck 11 thetaAboveCell10013302 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell10013302
    e24KC2ThetaAboveNode100133020 e24KC2ThetaAboveNode100133021 e24KC2ThetaAboveNode100133022
      e24KC2ThetaAboveNode100133023

theorem e24KC2ThetaAboveNode10013303 :
    adaptiveCoverCheck 11 thetaAboveCell10013303 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell10013303
    e24KC2ThetaAboveNode100133030 e24KC2ThetaAboveNode100133031 e24KC2ThetaAboveNode100133032
      e24KC2ThetaAboveNode100133033

theorem e24KC2ThetaAboveNode10013310 :
    adaptiveCoverCheck 11 thetaAboveCell10013310 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell10013310
    e24KC2ThetaAboveLeaf100133100 e24KC2ThetaAboveLeaf100133101 e24KC2ThetaAboveLeaf100133102
      e24KC2ThetaAboveLeaf100133103

theorem e24KC2ThetaAboveNode10013311 :
    adaptiveCoverCheck 11 thetaAboveCell10013311 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell10013311
    e24KC2ThetaAboveLeaf100133110 e24KC2ThetaAboveLeaf100133111 e24KC2ThetaAboveLeaf100133112
      e24KC2ThetaAboveLeaf100133113

theorem e24KC2ThetaAboveNode10013312 :
    adaptiveCoverCheck 11 thetaAboveCell10013312 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell10013312
    e24KC2ThetaAboveNode100133120 e24KC2ThetaAboveNode100133121 e24KC2ThetaAboveNode100133122
      e24KC2ThetaAboveNode100133123

theorem e24KC2ThetaAboveNode10013313 :
    adaptiveCoverCheck 11 thetaAboveCell10013313 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell10013313
    e24KC2ThetaAboveNode100133130 e24KC2ThetaAboveNode100133131 e24KC2ThetaAboveNode100133132
      e24KC2ThetaAboveNode100133133

theorem e24KC2ThetaAboveNode10013320 :
    adaptiveCoverCheck 11 thetaAboveCell10013320 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell10013320
    e24KC2ThetaAboveLeaf100133200 e24KC2ThetaAboveLeaf100133201 e24KC2ThetaAboveLeaf100133202
      e24KC2ThetaAboveLeaf100133203

theorem e24KC2ThetaAboveNode10013321 :
    adaptiveCoverCheck 11 thetaAboveCell10013321 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell10013321
    e24KC2ThetaAboveLeaf100133210 e24KC2ThetaAboveLeaf100133211 e24KC2ThetaAboveLeaf100133212
      e24KC2ThetaAboveLeaf100133213

theorem e24KC2ThetaAboveNode10013330 :
    adaptiveCoverCheck 11 thetaAboveCell10013330 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell10013330
    e24KC2ThetaAboveLeaf100133300 e24KC2ThetaAboveLeaf100133301 e24KC2ThetaAboveLeaf100133302
      e24KC2ThetaAboveLeaf100133303

theorem e24KC2ThetaAboveNode10013331 :
    adaptiveCoverCheck 11 thetaAboveCell10013331 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell10013331
    e24KC2ThetaAboveLeaf100133310 e24KC2ThetaAboveLeaf100133311 e24KC2ThetaAboveLeaf100133312
      e24KC2ThetaAboveLeaf100133313

theorem e24KC2ThetaAboveNode10102200 :
    adaptiveCoverCheck 11 thetaAboveCell10102200 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell10102200
    e24KC2ThetaAboveLeaf101022000 e24KC2ThetaAboveLeaf101022001 e24KC2ThetaAboveLeaf101022002
      e24KC2ThetaAboveLeaf101022003

theorem e24KC2ThetaAboveNode10102201 :
    adaptiveCoverCheck 11 thetaAboveCell10102201 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell10102201
    e24KC2ThetaAboveLeaf101022010 e24KC2ThetaAboveLeaf101022011 e24KC2ThetaAboveLeaf101022012
      e24KC2ThetaAboveLeaf101022013

theorem e24KC2ThetaAboveNode10102202 :
    adaptiveCoverCheck 11 thetaAboveCell10102202 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell10102202
    e24KC2ThetaAboveNode101022020 e24KC2ThetaAboveNode101022021 e24KC2ThetaAboveNode101022022
      e24KC2ThetaAboveNode101022023

theorem e24KC2ThetaAboveNode10102203 :
    adaptiveCoverCheck 11 thetaAboveCell10102203 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell10102203
    e24KC2ThetaAboveNode101022030 e24KC2ThetaAboveNode101022031 e24KC2ThetaAboveNode101022032
      e24KC2ThetaAboveNode101022033

theorem e24KC2ThetaAboveNode10102210 :
    adaptiveCoverCheck 11 thetaAboveCell10102210 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell10102210
    e24KC2ThetaAboveLeaf101022100 e24KC2ThetaAboveLeaf101022101 e24KC2ThetaAboveLeaf101022102
      e24KC2ThetaAboveLeaf101022103

theorem e24KC2ThetaAboveNode10102211 :
    adaptiveCoverCheck 11 thetaAboveCell10102211 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell10102211
    e24KC2ThetaAboveLeaf101022110 e24KC2ThetaAboveLeaf101022111 e24KC2ThetaAboveLeaf101022112
      e24KC2ThetaAboveLeaf101022113

theorem e24KC2ThetaAboveNode10102212 :
    adaptiveCoverCheck 11 thetaAboveCell10102212 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell10102212
    e24KC2ThetaAboveNode101022120 e24KC2ThetaAboveNode101022121 e24KC2ThetaAboveNode101022122
      e24KC2ThetaAboveNode101022123

theorem e24KC2ThetaAboveNode10102213 :
    adaptiveCoverCheck 11 thetaAboveCell10102213 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell10102213
    e24KC2ThetaAboveNode101022130 e24KC2ThetaAboveNode101022131 e24KC2ThetaAboveNode101022132
      e24KC2ThetaAboveLeaf101022133

theorem e24KC2ThetaAboveNode10102220 :
    adaptiveCoverCheck 11 thetaAboveCell10102220 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell10102220
    e24KC2ThetaAboveLeaf101022200 e24KC2ThetaAboveLeaf101022201 e24KC2ThetaAboveLeaf101022202
      e24KC2ThetaAboveLeaf101022203

theorem e24KC2ThetaAboveNode10102221 :
    adaptiveCoverCheck 11 thetaAboveCell10102221 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell10102221
    e24KC2ThetaAboveLeaf101022210 e24KC2ThetaAboveLeaf101022211 e24KC2ThetaAboveLeaf101022212
      e24KC2ThetaAboveLeaf101022213

theorem e24KC2ThetaAboveNode10102230 :
    adaptiveCoverCheck 11 thetaAboveCell10102230 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell10102230
    e24KC2ThetaAboveLeaf101022300 e24KC2ThetaAboveLeaf101022301 e24KC2ThetaAboveLeaf101022302
      e24KC2ThetaAboveLeaf101022303

theorem e24KC2ThetaAboveNode10102231 :
    adaptiveCoverCheck 11 thetaAboveCell10102231 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell10102231
    e24KC2ThetaAboveLeaf101022310 e24KC2ThetaAboveLeaf101022311 e24KC2ThetaAboveLeaf101022312
      e24KC2ThetaAboveLeaf101022313

theorem e24KC2ThetaAboveNode10102300 :
    adaptiveCoverCheck 11 thetaAboveCell10102300 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell10102300
    e24KC2ThetaAboveLeaf101023000 e24KC2ThetaAboveLeaf101023001 e24KC2ThetaAboveLeaf101023002
      e24KC2ThetaAboveLeaf101023003

theorem e24KC2ThetaAboveNode10102301 :
    adaptiveCoverCheck 11 thetaAboveCell10102301 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell10102301
    e24KC2ThetaAboveLeaf101023010 e24KC2ThetaAboveLeaf101023011 e24KC2ThetaAboveLeaf101023012
      e24KC2ThetaAboveLeaf101023013

theorem e24KC2ThetaAboveNode10102302 :
    adaptiveCoverCheck 11 thetaAboveCell10102302 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell10102302
    e24KC2ThetaAboveNode101023020 e24KC2ThetaAboveNode101023021 e24KC2ThetaAboveLeaf101023022
      e24KC2ThetaAboveLeaf101023023

theorem e24KC2ThetaAboveNode10102303 :
    adaptiveCoverCheck 11 thetaAboveCell10102303 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell10102303
    e24KC2ThetaAboveNode101023030 e24KC2ThetaAboveNode101023031 e24KC2ThetaAboveLeaf101023032
      e24KC2ThetaAboveLeaf101023033

theorem e24KC2ThetaAboveNode10102310 :
    adaptiveCoverCheck 11 thetaAboveCell10102310 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell10102310
    e24KC2ThetaAboveLeaf101023100 e24KC2ThetaAboveLeaf101023101 e24KC2ThetaAboveLeaf101023102
      e24KC2ThetaAboveLeaf101023103

theorem e24KC2ThetaAboveNode10102311 :
    adaptiveCoverCheck 11 thetaAboveCell10102311 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell10102311
    e24KC2ThetaAboveLeaf101023110 e24KC2ThetaAboveLeaf101023111 e24KC2ThetaAboveLeaf101023112
      e24KC2ThetaAboveLeaf101023113

theorem e24KC2ThetaAboveNode10102312 :
    adaptiveCoverCheck 11 thetaAboveCell10102312 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell10102312
    e24KC2ThetaAboveNode101023120 e24KC2ThetaAboveNode101023121 e24KC2ThetaAboveLeaf101023122
      e24KC2ThetaAboveLeaf101023123

theorem e24KC2ThetaAboveNode10102313 :
    adaptiveCoverCheck 11 thetaAboveCell10102313 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell10102313
    e24KC2ThetaAboveNode101023130 e24KC2ThetaAboveNode101023131 e24KC2ThetaAboveLeaf101023132
      e24KC2ThetaAboveLeaf101023133

theorem e24KC2ThetaAboveNode10102320 :
    adaptiveCoverCheck 11 thetaAboveCell10102320 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell10102320
    e24KC2ThetaAboveLeaf101023200 e24KC2ThetaAboveLeaf101023201 e24KC2ThetaAboveLeaf101023202
      e24KC2ThetaAboveLeaf101023203

theorem e24KC2ThetaAboveNode10102321 :
    adaptiveCoverCheck 11 thetaAboveCell10102321 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell10102321
    e24KC2ThetaAboveLeaf101023210 e24KC2ThetaAboveLeaf101023211 e24KC2ThetaAboveLeaf101023212
      e24KC2ThetaAboveLeaf101023213

theorem e24KC2ThetaAboveNode10102330 :
    adaptiveCoverCheck 11 thetaAboveCell10102330 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell10102330
    e24KC2ThetaAboveLeaf101023300 e24KC2ThetaAboveLeaf101023301 e24KC2ThetaAboveLeaf101023302
      e24KC2ThetaAboveLeaf101023303

theorem e24KC2ThetaAboveNode10102331 :
    adaptiveCoverCheck 11 thetaAboveCell10102331 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell10102331
    e24KC2ThetaAboveLeaf101023310 e24KC2ThetaAboveLeaf101023311 e24KC2ThetaAboveLeaf101023312
      e24KC2ThetaAboveLeaf101023313

theorem e24KC2ThetaAboveNode10103200 :
    adaptiveCoverCheck 11 thetaAboveCell10103200 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell10103200
    e24KC2ThetaAboveLeaf101032000 e24KC2ThetaAboveLeaf101032001 e24KC2ThetaAboveLeaf101032002
      e24KC2ThetaAboveLeaf101032003

theorem e24KC2ThetaAboveNode10103201 :
    adaptiveCoverCheck 11 thetaAboveCell10103201 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell10103201
    e24KC2ThetaAboveLeaf101032010 e24KC2ThetaAboveLeaf101032011 e24KC2ThetaAboveLeaf101032012
      e24KC2ThetaAboveLeaf101032013

theorem e24KC2ThetaAboveNode10103202 :
    adaptiveCoverCheck 11 thetaAboveCell10103202 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell10103202
    e24KC2ThetaAboveNode101032020 e24KC2ThetaAboveNode101032021 e24KC2ThetaAboveLeaf101032022
      e24KC2ThetaAboveLeaf101032023

theorem e24KC2ThetaAboveNode10103203 :
    adaptiveCoverCheck 11 thetaAboveCell10103203 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell10103203
    e24KC2ThetaAboveNode101032030 e24KC2ThetaAboveNode101032031 e24KC2ThetaAboveLeaf101032032
      e24KC2ThetaAboveLeaf101032033

theorem e24KC2ThetaAboveNode10103210 :
    adaptiveCoverCheck 11 thetaAboveCell10103210 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell10103210
    e24KC2ThetaAboveLeaf101032100 e24KC2ThetaAboveLeaf101032101 e24KC2ThetaAboveLeaf101032102
      e24KC2ThetaAboveLeaf101032103

theorem e24KC2ThetaAboveNode10103211 :
    adaptiveCoverCheck 11 thetaAboveCell10103211 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell10103211
    e24KC2ThetaAboveLeaf101032110 e24KC2ThetaAboveLeaf101032111 e24KC2ThetaAboveLeaf101032112
      e24KC2ThetaAboveLeaf101032113

theorem e24KC2ThetaAboveNode10103212 :
    adaptiveCoverCheck 11 thetaAboveCell10103212 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell10103212
    e24KC2ThetaAboveNode101032120 e24KC2ThetaAboveNode101032121 e24KC2ThetaAboveLeaf101032122
      e24KC2ThetaAboveLeaf101032123

theorem e24KC2ThetaAboveNode10103213 :
    adaptiveCoverCheck 11 thetaAboveCell10103213 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell10103213
    e24KC2ThetaAboveNode101032130 e24KC2ThetaAboveNode101032131 e24KC2ThetaAboveLeaf101032132
      e24KC2ThetaAboveLeaf101032133

theorem e24KC2ThetaAboveNode10103220 :
    adaptiveCoverCheck 11 thetaAboveCell10103220 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell10103220
    e24KC2ThetaAboveLeaf101032200 e24KC2ThetaAboveLeaf101032201 e24KC2ThetaAboveLeaf101032202
      e24KC2ThetaAboveLeaf101032203

theorem e24KC2ThetaAboveNode10103221 :
    adaptiveCoverCheck 11 thetaAboveCell10103221 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell10103221
    e24KC2ThetaAboveLeaf101032210 e24KC2ThetaAboveLeaf101032211 e24KC2ThetaAboveLeaf101032212
      e24KC2ThetaAboveLeaf101032213

theorem e24KC2ThetaAboveNode10103230 :
    adaptiveCoverCheck 11 thetaAboveCell10103230 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell10103230
    e24KC2ThetaAboveLeaf101032300 e24KC2ThetaAboveLeaf101032301 e24KC2ThetaAboveLeaf101032302
      e24KC2ThetaAboveLeaf101032303

theorem e24KC2ThetaAboveNode10103231 :
    adaptiveCoverCheck 11 thetaAboveCell10103231 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell10103231
    e24KC2ThetaAboveLeaf101032310 e24KC2ThetaAboveLeaf101032311 e24KC2ThetaAboveLeaf101032312
      e24KC2ThetaAboveLeaf101032313

theorem e24KC2ThetaAboveNode10103300 :
    adaptiveCoverCheck 11 thetaAboveCell10103300 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell10103300
    e24KC2ThetaAboveLeaf101033000 e24KC2ThetaAboveLeaf101033001 e24KC2ThetaAboveLeaf101033002
      e24KC2ThetaAboveLeaf101033003

theorem e24KC2ThetaAboveNode10103301 :
    adaptiveCoverCheck 11 thetaAboveCell10103301 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell10103301
    e24KC2ThetaAboveLeaf101033010 e24KC2ThetaAboveLeaf101033011 e24KC2ThetaAboveLeaf101033012
      e24KC2ThetaAboveLeaf101033013

theorem e24KC2ThetaAboveNode10103302 :
    adaptiveCoverCheck 11 thetaAboveCell10103302 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell10103302
    e24KC2ThetaAboveNode101033020 e24KC2ThetaAboveLeaf101033021 e24KC2ThetaAboveLeaf101033022
      e24KC2ThetaAboveLeaf101033023

theorem e24KC2ThetaAboveNode10103303 :
    adaptiveCoverCheck 11 thetaAboveCell10103303 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell10103303
    e24KC2ThetaAboveLeaf101033030 e24KC2ThetaAboveLeaf101033031 e24KC2ThetaAboveLeaf101033032
      e24KC2ThetaAboveLeaf101033033

theorem e24KC2ThetaAboveNode10103310 :
    adaptiveCoverCheck 11 thetaAboveCell10103310 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell10103310
    e24KC2ThetaAboveLeaf101033100 e24KC2ThetaAboveLeaf101033101 e24KC2ThetaAboveLeaf101033102
      e24KC2ThetaAboveLeaf101033103

theorem e24KC2ThetaAboveNode10103311 :
    adaptiveCoverCheck 11 thetaAboveCell10103311 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell10103311
    e24KC2ThetaAboveLeaf101033110 e24KC2ThetaAboveLeaf101033111 e24KC2ThetaAboveLeaf101033112
      e24KC2ThetaAboveLeaf101033113

theorem e24KC2ThetaAboveNode10103312 :
    adaptiveCoverCheck 11 thetaAboveCell10103312 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell10103312
    e24KC2ThetaAboveLeaf101033120 e24KC2ThetaAboveLeaf101033121 e24KC2ThetaAboveLeaf101033122
      e24KC2ThetaAboveLeaf101033123

theorem e24KC2ThetaAboveNode10103313 :
    adaptiveCoverCheck 11 thetaAboveCell10103313 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell10103313
    e24KC2ThetaAboveLeaf101033130 e24KC2ThetaAboveLeaf101033131 e24KC2ThetaAboveLeaf101033132
      e24KC2ThetaAboveLeaf101033133

theorem e24KC2ThetaAboveNode10103320 :
    adaptiveCoverCheck 11 thetaAboveCell10103320 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell10103320
    e24KC2ThetaAboveLeaf101033200 e24KC2ThetaAboveLeaf101033201 e24KC2ThetaAboveLeaf101033202
      e24KC2ThetaAboveLeaf101033203

theorem e24KC2ThetaAboveNode10103321 :
    adaptiveCoverCheck 11 thetaAboveCell10103321 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell10103321
    e24KC2ThetaAboveLeaf101033210 e24KC2ThetaAboveLeaf101033211 e24KC2ThetaAboveLeaf101033212
      e24KC2ThetaAboveLeaf101033213

theorem e24KC2ThetaAboveNode10103330 :
    adaptiveCoverCheck 11 thetaAboveCell10103330 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell10103330
    e24KC2ThetaAboveLeaf101033300 e24KC2ThetaAboveLeaf101033301 e24KC2ThetaAboveLeaf101033302
      e24KC2ThetaAboveLeaf101033303

theorem e24KC2ThetaAboveNode10103331 :
    adaptiveCoverCheck 11 thetaAboveCell10103331 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell10103331
    e24KC2ThetaAboveLeaf101033310 e24KC2ThetaAboveLeaf101033311 e24KC2ThetaAboveLeaf101033312
      e24KC2ThetaAboveLeaf101033313

theorem e24KC2ThetaAboveNode10112200 :
    adaptiveCoverCheck 11 thetaAboveCell10112200 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell10112200
    e24KC2ThetaAboveLeaf101122000 e24KC2ThetaAboveLeaf101122001 e24KC2ThetaAboveLeaf101122002
      e24KC2ThetaAboveLeaf101122003

theorem e24KC2ThetaAboveNode10112201 :
    adaptiveCoverCheck 11 thetaAboveCell10112201 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell10112201
    e24KC2ThetaAboveLeaf101122010 e24KC2ThetaAboveLeaf101122011 e24KC2ThetaAboveLeaf101122012
      e24KC2ThetaAboveLeaf101122013

theorem e24KC2ThetaAboveNode10112202 :
    adaptiveCoverCheck 11 thetaAboveCell10112202 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell10112202
    e24KC2ThetaAboveLeaf101122020 e24KC2ThetaAboveLeaf101122021 e24KC2ThetaAboveLeaf101122022
      e24KC2ThetaAboveLeaf101122023

theorem e24KC2ThetaAboveNode10112203 :
    adaptiveCoverCheck 11 thetaAboveCell10112203 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell10112203
    e24KC2ThetaAboveLeaf101122030 e24KC2ThetaAboveLeaf101122031 e24KC2ThetaAboveLeaf101122032
      e24KC2ThetaAboveLeaf101122033

theorem e24KC2ThetaAboveNode10112210 :
    adaptiveCoverCheck 11 thetaAboveCell10112210 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell10112210
    e24KC2ThetaAboveLeaf101122100 e24KC2ThetaAboveLeaf101122101 e24KC2ThetaAboveLeaf101122102
      e24KC2ThetaAboveLeaf101122103

theorem e24KC2ThetaAboveNode10112211 :
    adaptiveCoverCheck 11 thetaAboveCell10112211 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell10112211
    e24KC2ThetaAboveLeaf101122110 e24KC2ThetaAboveLeaf101122111 e24KC2ThetaAboveLeaf101122112
      e24KC2ThetaAboveLeaf101122113

theorem e24KC2ThetaAboveNode10112212 :
    adaptiveCoverCheck 11 thetaAboveCell10112212 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell10112212
    e24KC2ThetaAboveLeaf101122120 e24KC2ThetaAboveLeaf101122121 e24KC2ThetaAboveLeaf101122122
      e24KC2ThetaAboveLeaf101122123

theorem e24KC2ThetaAboveNode10112213 :
    adaptiveCoverCheck 11 thetaAboveCell10112213 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell10112213
    e24KC2ThetaAboveLeaf101122130 e24KC2ThetaAboveLeaf101122131 e24KC2ThetaAboveLeaf101122132
      e24KC2ThetaAboveLeaf101122133

theorem e24KC2ThetaAboveNode10112220 :
    adaptiveCoverCheck 11 thetaAboveCell10112220 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell10112220
    e24KC2ThetaAboveLeaf101122200 e24KC2ThetaAboveLeaf101122201 e24KC2ThetaAboveLeaf101122202
      e24KC2ThetaAboveLeaf101122203

theorem e24KC2ThetaAboveNode10112221 :
    adaptiveCoverCheck 11 thetaAboveCell10112221 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell10112221
    e24KC2ThetaAboveLeaf101122210 e24KC2ThetaAboveLeaf101122211 e24KC2ThetaAboveLeaf101122212
      e24KC2ThetaAboveLeaf101122213

theorem e24KC2ThetaAboveNode10112230 :
    adaptiveCoverCheck 11 thetaAboveCell10112230 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell10112230
    e24KC2ThetaAboveLeaf101122300 e24KC2ThetaAboveLeaf101122301 e24KC2ThetaAboveLeaf101122302
      e24KC2ThetaAboveLeaf101122303

theorem e24KC2ThetaAboveNode10112231 :
    adaptiveCoverCheck 11 thetaAboveCell10112231 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell10112231
    e24KC2ThetaAboveLeaf101122310 e24KC2ThetaAboveLeaf101122311 e24KC2ThetaAboveLeaf101122312
      e24KC2ThetaAboveLeaf101122313

theorem e24KC2ThetaAboveNode10112300 :
    adaptiveCoverCheck 11 thetaAboveCell10112300 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell10112300
    e24KC2ThetaAboveLeaf101123000 e24KC2ThetaAboveLeaf101123001 e24KC2ThetaAboveLeaf101123002
      e24KC2ThetaAboveLeaf101123003

theorem e24KC2ThetaAboveNode10112301 :
    adaptiveCoverCheck 11 thetaAboveCell10112301 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell10112301
    e24KC2ThetaAboveLeaf101123010 e24KC2ThetaAboveLeaf101123011 e24KC2ThetaAboveLeaf101123012
      e24KC2ThetaAboveLeaf101123013

theorem e24KC2ThetaAboveNode10112302 :
    adaptiveCoverCheck 11 thetaAboveCell10112302 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell10112302
    e24KC2ThetaAboveLeaf101123020 e24KC2ThetaAboveLeaf101123021 e24KC2ThetaAboveLeaf101123022
      e24KC2ThetaAboveLeaf101123023

theorem e24KC2ThetaAboveNode10112303 :
    adaptiveCoverCheck 11 thetaAboveCell10112303 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell10112303
    e24KC2ThetaAboveLeaf101123030 e24KC2ThetaAboveLeaf101123031 e24KC2ThetaAboveLeaf101123032
      e24KC2ThetaAboveLeaf101123033

theorem e24KC2ThetaAboveNode10112310 :
    adaptiveCoverCheck 11 thetaAboveCell10112310 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell10112310
    e24KC2ThetaAboveLeaf101123100 e24KC2ThetaAboveLeaf101123101 e24KC2ThetaAboveLeaf101123102
      e24KC2ThetaAboveLeaf101123103

theorem e24KC2ThetaAboveNode10112311 :
    adaptiveCoverCheck 11 thetaAboveCell10112311 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell10112311
    e24KC2ThetaAboveLeaf101123110 e24KC2ThetaAboveLeaf101123111 e24KC2ThetaAboveLeaf101123112
      e24KC2ThetaAboveLeaf101123113

theorem e24KC2ThetaAboveNode10112312 :
    adaptiveCoverCheck 11 thetaAboveCell10112312 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell10112312
    e24KC2ThetaAboveLeaf101123120 e24KC2ThetaAboveLeaf101123121 e24KC2ThetaAboveLeaf101123122
      e24KC2ThetaAboveLeaf101123123

theorem e24KC2ThetaAboveNode10112313 :
    adaptiveCoverCheck 11 thetaAboveCell10112313 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell10112313
    e24KC2ThetaAboveLeaf101123130 e24KC2ThetaAboveLeaf101123131 e24KC2ThetaAboveLeaf101123132
      e24KC2ThetaAboveLeaf101123133

theorem e24KC2ThetaAboveNode10112320 :
    adaptiveCoverCheck 11 thetaAboveCell10112320 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell10112320
    e24KC2ThetaAboveLeaf101123200 e24KC2ThetaAboveLeaf101123201 e24KC2ThetaAboveLeaf101123202
      e24KC2ThetaAboveLeaf101123203

theorem e24KC2ThetaAboveNode10112321 :
    adaptiveCoverCheck 11 thetaAboveCell10112321 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell10112321
    e24KC2ThetaAboveLeaf101123210 e24KC2ThetaAboveLeaf101123211 e24KC2ThetaAboveLeaf101123212
      e24KC2ThetaAboveLeaf101123213

theorem e24KC2ThetaAboveNode10112330 :
    adaptiveCoverCheck 11 thetaAboveCell10112330 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell10112330
    e24KC2ThetaAboveLeaf101123300 e24KC2ThetaAboveLeaf101123301 e24KC2ThetaAboveLeaf101123302
      e24KC2ThetaAboveLeaf101123303

theorem e24KC2ThetaAboveNode10112331 :
    adaptiveCoverCheck 11 thetaAboveCell10112331 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell10112331
    e24KC2ThetaAboveLeaf101123310 e24KC2ThetaAboveLeaf101123311 e24KC2ThetaAboveLeaf101123312
      e24KC2ThetaAboveLeaf101123313

theorem e24KC2ThetaAboveNode10113200 :
    adaptiveCoverCheck 11 thetaAboveCell10113200 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell10113200
    e24KC2ThetaAboveLeaf101132000 e24KC2ThetaAboveLeaf101132001 e24KC2ThetaAboveLeaf101132002
      e24KC2ThetaAboveLeaf101132003

theorem e24KC2ThetaAboveNode10113201 :
    adaptiveCoverCheck 11 thetaAboveCell10113201 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell10113201
    e24KC2ThetaAboveLeaf101132010 e24KC2ThetaAboveLeaf101132011 e24KC2ThetaAboveLeaf101132012
      e24KC2ThetaAboveLeaf101132013

theorem e24KC2ThetaAboveNode10113202 :
    adaptiveCoverCheck 11 thetaAboveCell10113202 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell10113202
    e24KC2ThetaAboveLeaf101132020 e24KC2ThetaAboveLeaf101132021 e24KC2ThetaAboveLeaf101132022
      e24KC2ThetaAboveLeaf101132023

theorem e24KC2ThetaAboveNode10113203 :
    adaptiveCoverCheck 11 thetaAboveCell10113203 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell10113203
    e24KC2ThetaAboveLeaf101132030 e24KC2ThetaAboveLeaf101132031 e24KC2ThetaAboveLeaf101132032
      e24KC2ThetaAboveLeaf101132033

theorem e24KC2ThetaAboveNode10113210 :
    adaptiveCoverCheck 11 thetaAboveCell10113210 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell10113210
    e24KC2ThetaAboveLeaf101132100 e24KC2ThetaAboveLeaf101132101 e24KC2ThetaAboveLeaf101132102
      e24KC2ThetaAboveLeaf101132103

theorem e24KC2ThetaAboveNode10113211 :
    adaptiveCoverCheck 11 thetaAboveCell10113211 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell10113211
    e24KC2ThetaAboveLeaf101132110 e24KC2ThetaAboveLeaf101132111 e24KC2ThetaAboveLeaf101132112
      e24KC2ThetaAboveLeaf101132113

theorem e24KC2ThetaAboveNode10113212 :
    adaptiveCoverCheck 11 thetaAboveCell10113212 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell10113212
    e24KC2ThetaAboveLeaf101132120 e24KC2ThetaAboveLeaf101132121 e24KC2ThetaAboveLeaf101132122
      e24KC2ThetaAboveLeaf101132123

theorem e24KC2ThetaAboveNode10113213 :
    adaptiveCoverCheck 11 thetaAboveCell10113213 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell10113213
    e24KC2ThetaAboveLeaf101132130 e24KC2ThetaAboveLeaf101132131 e24KC2ThetaAboveLeaf101132132
      e24KC2ThetaAboveLeaf101132133

theorem e24KC2ThetaAboveNode10113220 :
    adaptiveCoverCheck 11 thetaAboveCell10113220 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell10113220
    e24KC2ThetaAboveLeaf101132200 e24KC2ThetaAboveLeaf101132201 e24KC2ThetaAboveLeaf101132202
      e24KC2ThetaAboveLeaf101132203

theorem e24KC2ThetaAboveNode10113221 :
    adaptiveCoverCheck 11 thetaAboveCell10113221 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell10113221
    e24KC2ThetaAboveLeaf101132210 e24KC2ThetaAboveLeaf101132211 e24KC2ThetaAboveLeaf101132212
      e24KC2ThetaAboveLeaf101132213

theorem e24KC2ThetaAboveNode10113230 :
    adaptiveCoverCheck 11 thetaAboveCell10113230 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell10113230
    e24KC2ThetaAboveLeaf101132300 e24KC2ThetaAboveLeaf101132301 e24KC2ThetaAboveLeaf101132302
      e24KC2ThetaAboveLeaf101132303

theorem e24KC2ThetaAboveNode10113231 :
    adaptiveCoverCheck 11 thetaAboveCell10113231 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell10113231
    e24KC2ThetaAboveLeaf101132310 e24KC2ThetaAboveLeaf101132311 e24KC2ThetaAboveLeaf101132312
      e24KC2ThetaAboveLeaf101132313

theorem e24KC2ThetaAboveNode10113300 :
    adaptiveCoverCheck 11 thetaAboveCell10113300 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell10113300
    e24KC2ThetaAboveLeaf101133000 e24KC2ThetaAboveLeaf101133001 e24KC2ThetaAboveLeaf101133002
      e24KC2ThetaAboveLeaf101133003

theorem e24KC2ThetaAboveNode10113301 :
    adaptiveCoverCheck 11 thetaAboveCell10113301 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell10113301
    e24KC2ThetaAboveLeaf101133010 e24KC2ThetaAboveLeaf101133011 e24KC2ThetaAboveLeaf101133012
      e24KC2ThetaAboveLeaf101133013

theorem e24KC2ThetaAboveNode10113302 :
    adaptiveCoverCheck 11 thetaAboveCell10113302 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell10113302
    e24KC2ThetaAboveLeaf101133020 e24KC2ThetaAboveLeaf101133021 e24KC2ThetaAboveLeaf101133022
      e24KC2ThetaAboveLeaf101133023

theorem e24KC2ThetaAboveNode10113303 :
    adaptiveCoverCheck 11 thetaAboveCell10113303 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell10113303
    e24KC2ThetaAboveLeaf101133030 e24KC2ThetaAboveLeaf101133031 e24KC2ThetaAboveLeaf101133032
      e24KC2ThetaAboveLeaf101133033

theorem e24KC2ThetaAboveNode10113310 :
    adaptiveCoverCheck 11 thetaAboveCell10113310 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell10113310
    e24KC2ThetaAboveLeaf101133100 e24KC2ThetaAboveLeaf101133101 e24KC2ThetaAboveLeaf101133102
      e24KC2ThetaAboveLeaf101133103

theorem e24KC2ThetaAboveNode10113311 :
    adaptiveCoverCheck 11 thetaAboveCell10113311 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell10113311
    e24KC2ThetaAboveLeaf101133110 e24KC2ThetaAboveLeaf101133111 e24KC2ThetaAboveLeaf101133112
      e24KC2ThetaAboveLeaf101133113

theorem e24KC2ThetaAboveNode10113312 :
    adaptiveCoverCheck 11 thetaAboveCell10113312 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell10113312
    e24KC2ThetaAboveLeaf101133120 e24KC2ThetaAboveLeaf101133121 e24KC2ThetaAboveLeaf101133122
      e24KC2ThetaAboveLeaf101133123

theorem e24KC2ThetaAboveNode10113313 :
    adaptiveCoverCheck 11 thetaAboveCell10113313 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell10113313
    e24KC2ThetaAboveLeaf101133130 e24KC2ThetaAboveLeaf101133131 e24KC2ThetaAboveLeaf101133132
      e24KC2ThetaAboveLeaf101133133

theorem e24KC2ThetaAboveNode10113320 :
    adaptiveCoverCheck 11 thetaAboveCell10113320 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell10113320
    e24KC2ThetaAboveLeaf101133200 e24KC2ThetaAboveLeaf101133201 e24KC2ThetaAboveLeaf101133202
      e24KC2ThetaAboveLeaf101133203

theorem e24KC2ThetaAboveNode10113321 :
    adaptiveCoverCheck 11 thetaAboveCell10113321 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell10113321
    e24KC2ThetaAboveLeaf101133210 e24KC2ThetaAboveLeaf101133211 e24KC2ThetaAboveLeaf101133212
      e24KC2ThetaAboveLeaf101133213

theorem e24KC2ThetaAboveNode10113330 :
    adaptiveCoverCheck 11 thetaAboveCell10113330 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell10113330
    e24KC2ThetaAboveLeaf101133300 e24KC2ThetaAboveLeaf101133301 e24KC2ThetaAboveLeaf101133302
      e24KC2ThetaAboveLeaf101133303

theorem e24KC2ThetaAboveNode10113331 :
    adaptiveCoverCheck 11 thetaAboveCell10113331 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell10113331
    e24KC2ThetaAboveLeaf101133310 e24KC2ThetaAboveLeaf101133311 e24KC2ThetaAboveLeaf101133312
      e24KC2ThetaAboveLeaf101133313

theorem e24KC2ThetaAboveNode11002202 :
    adaptiveCoverCheck 11 thetaAboveCell11002202 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell11002202
    e24KC2ThetaAboveLeaf110022020 e24KC2ThetaAboveLeaf110022021 e24KC2ThetaAboveLeaf110022022
      e24KC2ThetaAboveLeaf110022023

theorem e24KC2ThetaAboveNode11002203 :
    adaptiveCoverCheck 11 thetaAboveCell11002203 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell11002203
    e24KC2ThetaAboveLeaf110022030 e24KC2ThetaAboveLeaf110022031 e24KC2ThetaAboveLeaf110022032
      e24KC2ThetaAboveLeaf110022033

theorem e24KC2ThetaAboveNode11002212 :
    adaptiveCoverCheck 11 thetaAboveCell11002212 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell11002212
    e24KC2ThetaAboveLeaf110022120 e24KC2ThetaAboveLeaf110022121 e24KC2ThetaAboveLeaf110022122
      e24KC2ThetaAboveLeaf110022123

theorem e24KC2ThetaAboveNode11002213 :
    adaptiveCoverCheck 11 thetaAboveCell11002213 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell11002213
    e24KC2ThetaAboveLeaf110022130 e24KC2ThetaAboveLeaf110022131 e24KC2ThetaAboveLeaf110022132
      e24KC2ThetaAboveLeaf110022133

theorem e24KC2ThetaAboveNode11002220 :
    adaptiveCoverCheck 11 thetaAboveCell11002220 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell11002220
    e24KC2ThetaAboveLeaf110022200 e24KC2ThetaAboveLeaf110022201 e24KC2ThetaAboveLeaf110022202
      e24KC2ThetaAboveLeaf110022203

theorem e24KC2ThetaAboveNode11002221 :
    adaptiveCoverCheck 11 thetaAboveCell11002221 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell11002221
    e24KC2ThetaAboveLeaf110022210 e24KC2ThetaAboveLeaf110022211 e24KC2ThetaAboveLeaf110022212
      e24KC2ThetaAboveLeaf110022213

theorem e24KC2ThetaAboveNode11002230 :
    adaptiveCoverCheck 11 thetaAboveCell11002230 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell11002230
    e24KC2ThetaAboveLeaf110022300 e24KC2ThetaAboveLeaf110022301 e24KC2ThetaAboveLeaf110022302
      e24KC2ThetaAboveLeaf110022303

theorem e24KC2ThetaAboveNode11002231 :
    adaptiveCoverCheck 11 thetaAboveCell11002231 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell11002231
    e24KC2ThetaAboveLeaf110022310 e24KC2ThetaAboveLeaf110022311 e24KC2ThetaAboveLeaf110022312
      e24KC2ThetaAboveLeaf110022313

theorem e24KC2ThetaAboveNode11002302 :
    adaptiveCoverCheck 11 thetaAboveCell11002302 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell11002302
    e24KC2ThetaAboveLeaf110023020 e24KC2ThetaAboveLeaf110023021 e24KC2ThetaAboveLeaf110023022
      e24KC2ThetaAboveLeaf110023023

theorem e24KC2ThetaAboveNode11002303 :
    adaptiveCoverCheck 11 thetaAboveCell11002303 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell11002303
    e24KC2ThetaAboveLeaf110023030 e24KC2ThetaAboveLeaf110023031 e24KC2ThetaAboveLeaf110023032
      e24KC2ThetaAboveLeaf110023033

theorem e24KC2ThetaAboveNode11002312 :
    adaptiveCoverCheck 11 thetaAboveCell11002312 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell11002312
    e24KC2ThetaAboveLeaf110023120 e24KC2ThetaAboveLeaf110023121 e24KC2ThetaAboveLeaf110023122
      e24KC2ThetaAboveLeaf110023123

theorem e24KC2ThetaAboveNode11002313 :
    adaptiveCoverCheck 11 thetaAboveCell11002313 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell11002313
    e24KC2ThetaAboveLeaf110023130 e24KC2ThetaAboveLeaf110023131 e24KC2ThetaAboveLeaf110023132
      e24KC2ThetaAboveLeaf110023133

theorem e24KC2ThetaAboveNode11002320 :
    adaptiveCoverCheck 11 thetaAboveCell11002320 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell11002320
    e24KC2ThetaAboveLeaf110023200 e24KC2ThetaAboveLeaf110023201 e24KC2ThetaAboveLeaf110023202
      e24KC2ThetaAboveLeaf110023203

theorem e24KC2ThetaAboveNode11002321 :
    adaptiveCoverCheck 11 thetaAboveCell11002321 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell11002321
    e24KC2ThetaAboveLeaf110023210 e24KC2ThetaAboveLeaf110023211 e24KC2ThetaAboveLeaf110023212
      e24KC2ThetaAboveLeaf110023213

theorem e24KC2ThetaAboveNode11002330 :
    adaptiveCoverCheck 11 thetaAboveCell11002330 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell11002330
    e24KC2ThetaAboveLeaf110023300 e24KC2ThetaAboveLeaf110023301 e24KC2ThetaAboveLeaf110023302
      e24KC2ThetaAboveLeaf110023303

theorem e24KC2ThetaAboveNode11002331 :
    adaptiveCoverCheck 11 thetaAboveCell11002331 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell11002331
    e24KC2ThetaAboveLeaf110023310 e24KC2ThetaAboveLeaf110023311 e24KC2ThetaAboveLeaf110023312
      e24KC2ThetaAboveLeaf110023313

theorem e24KC2ThetaAboveNode11003202 :
    adaptiveCoverCheck 11 thetaAboveCell11003202 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell11003202
    e24KC2ThetaAboveLeaf110032020 e24KC2ThetaAboveLeaf110032021 e24KC2ThetaAboveLeaf110032022
      e24KC2ThetaAboveLeaf110032023

theorem e24KC2ThetaAboveNode11003203 :
    adaptiveCoverCheck 11 thetaAboveCell11003203 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell11003203
    e24KC2ThetaAboveLeaf110032030 e24KC2ThetaAboveLeaf110032031 e24KC2ThetaAboveLeaf110032032
      e24KC2ThetaAboveLeaf110032033

theorem e24KC2ThetaAboveNode11003212 :
    adaptiveCoverCheck 11 thetaAboveCell11003212 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell11003212
    e24KC2ThetaAboveLeaf110032120 e24KC2ThetaAboveLeaf110032121 e24KC2ThetaAboveLeaf110032122
      e24KC2ThetaAboveLeaf110032123

theorem e24KC2ThetaAboveNode11003213 :
    adaptiveCoverCheck 11 thetaAboveCell11003213 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell11003213
    e24KC2ThetaAboveLeaf110032130 e24KC2ThetaAboveLeaf110032131 e24KC2ThetaAboveLeaf110032132
      e24KC2ThetaAboveLeaf110032133

theorem e24KC2ThetaAboveNode11003220 :
    adaptiveCoverCheck 11 thetaAboveCell11003220 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell11003220
    e24KC2ThetaAboveLeaf110032200 e24KC2ThetaAboveLeaf110032201 e24KC2ThetaAboveLeaf110032202
      e24KC2ThetaAboveLeaf110032203

theorem e24KC2ThetaAboveNode11003221 :
    adaptiveCoverCheck 11 thetaAboveCell11003221 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell11003221
    e24KC2ThetaAboveLeaf110032210 e24KC2ThetaAboveLeaf110032211 e24KC2ThetaAboveLeaf110032212
      e24KC2ThetaAboveLeaf110032213

theorem e24KC2ThetaAboveNode11003230 :
    adaptiveCoverCheck 11 thetaAboveCell11003230 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell11003230
    e24KC2ThetaAboveLeaf110032300 e24KC2ThetaAboveLeaf110032301 e24KC2ThetaAboveLeaf110032302
      e24KC2ThetaAboveLeaf110032303

theorem e24KC2ThetaAboveNode11003231 :
    adaptiveCoverCheck 11 thetaAboveCell11003231 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell11003231
    e24KC2ThetaAboveLeaf110032310 e24KC2ThetaAboveLeaf110032311 e24KC2ThetaAboveLeaf110032312
      e24KC2ThetaAboveLeaf110032313

theorem e24KC2ThetaAboveNode11003302 :
    adaptiveCoverCheck 11 thetaAboveCell11003302 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell11003302
    e24KC2ThetaAboveLeaf110033020 e24KC2ThetaAboveLeaf110033021 e24KC2ThetaAboveLeaf110033022
      e24KC2ThetaAboveLeaf110033023

theorem e24KC2ThetaAboveNode11003303 :
    adaptiveCoverCheck 11 thetaAboveCell11003303 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell11003303
    e24KC2ThetaAboveLeaf110033030 e24KC2ThetaAboveLeaf110033031 e24KC2ThetaAboveLeaf110033032
      e24KC2ThetaAboveLeaf110033033

theorem e24KC2ThetaAboveNode11003312 :
    adaptiveCoverCheck 11 thetaAboveCell11003312 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell11003312
    e24KC2ThetaAboveLeaf110033120 e24KC2ThetaAboveLeaf110033121 e24KC2ThetaAboveLeaf110033122
      e24KC2ThetaAboveLeaf110033123

theorem e24KC2ThetaAboveNode11003313 :
    adaptiveCoverCheck 11 thetaAboveCell11003313 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell11003313
    e24KC2ThetaAboveLeaf110033130 e24KC2ThetaAboveLeaf110033131 e24KC2ThetaAboveLeaf110033132
      e24KC2ThetaAboveLeaf110033133

theorem e24KC2ThetaAboveNode11003320 :
    adaptiveCoverCheck 11 thetaAboveCell11003320 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell11003320
    e24KC2ThetaAboveLeaf110033200 e24KC2ThetaAboveLeaf110033201 e24KC2ThetaAboveLeaf110033202
      e24KC2ThetaAboveLeaf110033203

theorem e24KC2ThetaAboveNode11003321 :
    adaptiveCoverCheck 11 thetaAboveCell11003321 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell11003321
    e24KC2ThetaAboveLeaf110033210 e24KC2ThetaAboveLeaf110033211 e24KC2ThetaAboveLeaf110033212
      e24KC2ThetaAboveLeaf110033213

theorem e24KC2ThetaAboveNode11003330 :
    adaptiveCoverCheck 11 thetaAboveCell11003330 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell11003330
    e24KC2ThetaAboveLeaf110033300 e24KC2ThetaAboveLeaf110033301 e24KC2ThetaAboveLeaf110033302
      e24KC2ThetaAboveLeaf110033303

theorem e24KC2ThetaAboveNode11003331 :
    adaptiveCoverCheck 11 thetaAboveCell11003331 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell11003331
    e24KC2ThetaAboveLeaf110033310 e24KC2ThetaAboveLeaf110033311 e24KC2ThetaAboveLeaf110033312
      e24KC2ThetaAboveLeaf110033313

theorem e24KC2ThetaAboveNode11012202 :
    adaptiveCoverCheck 11 thetaAboveCell11012202 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell11012202
    e24KC2ThetaAboveLeaf110122020 e24KC2ThetaAboveLeaf110122021 e24KC2ThetaAboveLeaf110122022
      e24KC2ThetaAboveLeaf110122023

theorem e24KC2ThetaAboveNode11012203 :
    adaptiveCoverCheck 11 thetaAboveCell11012203 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell11012203
    e24KC2ThetaAboveLeaf110122030 e24KC2ThetaAboveLeaf110122031 e24KC2ThetaAboveLeaf110122032
      e24KC2ThetaAboveLeaf110122033

theorem e24KC2ThetaAboveNode11012212 :
    adaptiveCoverCheck 11 thetaAboveCell11012212 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell11012212
    e24KC2ThetaAboveLeaf110122120 e24KC2ThetaAboveLeaf110122121 e24KC2ThetaAboveLeaf110122122
      e24KC2ThetaAboveLeaf110122123

theorem e24KC2ThetaAboveNode11012213 :
    adaptiveCoverCheck 11 thetaAboveCell11012213 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell11012213
    e24KC2ThetaAboveLeaf110122130 e24KC2ThetaAboveLeaf110122131 e24KC2ThetaAboveLeaf110122132
      e24KC2ThetaAboveLeaf110122133

theorem e24KC2ThetaAboveNode11012220 :
    adaptiveCoverCheck 11 thetaAboveCell11012220 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell11012220
    e24KC2ThetaAboveLeaf110122200 e24KC2ThetaAboveLeaf110122201 e24KC2ThetaAboveLeaf110122202
      e24KC2ThetaAboveLeaf110122203

theorem e24KC2ThetaAboveNode11012221 :
    adaptiveCoverCheck 11 thetaAboveCell11012221 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell11012221
    e24KC2ThetaAboveLeaf110122210 e24KC2ThetaAboveLeaf110122211 e24KC2ThetaAboveLeaf110122212
      e24KC2ThetaAboveLeaf110122213

theorem e24KC2ThetaAboveNode11012230 :
    adaptiveCoverCheck 11 thetaAboveCell11012230 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell11012230
    e24KC2ThetaAboveLeaf110122300 e24KC2ThetaAboveLeaf110122301 e24KC2ThetaAboveLeaf110122302
      e24KC2ThetaAboveLeaf110122303

theorem e24KC2ThetaAboveNode11012231 :
    adaptiveCoverCheck 11 thetaAboveCell11012231 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell11012231
    e24KC2ThetaAboveLeaf110122310 e24KC2ThetaAboveLeaf110122311 e24KC2ThetaAboveLeaf110122312
      e24KC2ThetaAboveLeaf110122313

theorem e24KC2ThetaAboveNode11012302 :
    adaptiveCoverCheck 11 thetaAboveCell11012302 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell11012302
    e24KC2ThetaAboveLeaf110123020 e24KC2ThetaAboveLeaf110123021 e24KC2ThetaAboveLeaf110123022
      e24KC2ThetaAboveLeaf110123023

theorem e24KC2ThetaAboveNode11012303 :
    adaptiveCoverCheck 11 thetaAboveCell11012303 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell11012303
    e24KC2ThetaAboveLeaf110123030 e24KC2ThetaAboveLeaf110123031 e24KC2ThetaAboveLeaf110123032
      e24KC2ThetaAboveLeaf110123033

theorem e24KC2ThetaAboveNode11012312 :
    adaptiveCoverCheck 11 thetaAboveCell11012312 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell11012312
    e24KC2ThetaAboveLeaf110123120 e24KC2ThetaAboveLeaf110123121 e24KC2ThetaAboveLeaf110123122
      e24KC2ThetaAboveLeaf110123123

theorem e24KC2ThetaAboveNode11012313 :
    adaptiveCoverCheck 11 thetaAboveCell11012313 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell11012313
    e24KC2ThetaAboveLeaf110123130 e24KC2ThetaAboveLeaf110123131 e24KC2ThetaAboveLeaf110123132
      e24KC2ThetaAboveLeaf110123133

theorem e24KC2ThetaAboveNode11012320 :
    adaptiveCoverCheck 11 thetaAboveCell11012320 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell11012320
    e24KC2ThetaAboveLeaf110123200 e24KC2ThetaAboveLeaf110123201 e24KC2ThetaAboveLeaf110123202
      e24KC2ThetaAboveLeaf110123203

theorem e24KC2ThetaAboveNode11012321 :
    adaptiveCoverCheck 11 thetaAboveCell11012321 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell11012321
    e24KC2ThetaAboveLeaf110123210 e24KC2ThetaAboveLeaf110123211 e24KC2ThetaAboveLeaf110123212
      e24KC2ThetaAboveLeaf110123213

theorem e24KC2ThetaAboveNode11012330 :
    adaptiveCoverCheck 11 thetaAboveCell11012330 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell11012330
    e24KC2ThetaAboveLeaf110123300 e24KC2ThetaAboveLeaf110123301 e24KC2ThetaAboveLeaf110123302
      e24KC2ThetaAboveLeaf110123303

theorem e24KC2ThetaAboveNode11012331 :
    adaptiveCoverCheck 11 thetaAboveCell11012331 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell11012331
    e24KC2ThetaAboveLeaf110123310 e24KC2ThetaAboveLeaf110123311 e24KC2ThetaAboveLeaf110123312
      e24KC2ThetaAboveLeaf110123313

theorem e24KC2ThetaAboveNode11013202 :
    adaptiveCoverCheck 11 thetaAboveCell11013202 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell11013202
    e24KC2ThetaAboveLeaf110132020 e24KC2ThetaAboveLeaf110132021 e24KC2ThetaAboveLeaf110132022
      e24KC2ThetaAboveLeaf110132023

theorem e24KC2ThetaAboveNode11013203 :
    adaptiveCoverCheck 11 thetaAboveCell11013203 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell11013203
    e24KC2ThetaAboveLeaf110132030 e24KC2ThetaAboveLeaf110132031 e24KC2ThetaAboveLeaf110132032
      e24KC2ThetaAboveLeaf110132033

theorem e24KC2ThetaAboveNode11013212 :
    adaptiveCoverCheck 11 thetaAboveCell11013212 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell11013212
    e24KC2ThetaAboveLeaf110132120 e24KC2ThetaAboveLeaf110132121 e24KC2ThetaAboveLeaf110132122
      e24KC2ThetaAboveLeaf110132123

theorem e24KC2ThetaAboveNode11013213 :
    adaptiveCoverCheck 11 thetaAboveCell11013213 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell11013213
    e24KC2ThetaAboveLeaf110132130 e24KC2ThetaAboveLeaf110132131 e24KC2ThetaAboveLeaf110132132
      e24KC2ThetaAboveLeaf110132133

theorem e24KC2ThetaAboveNode11013220 :
    adaptiveCoverCheck 11 thetaAboveCell11013220 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell11013220
    e24KC2ThetaAboveLeaf110132200 e24KC2ThetaAboveLeaf110132201 e24KC2ThetaAboveLeaf110132202
      e24KC2ThetaAboveLeaf110132203

theorem e24KC2ThetaAboveNode11013221 :
    adaptiveCoverCheck 11 thetaAboveCell11013221 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell11013221
    e24KC2ThetaAboveLeaf110132210 e24KC2ThetaAboveLeaf110132211 e24KC2ThetaAboveLeaf110132212
      e24KC2ThetaAboveLeaf110132213

theorem e24KC2ThetaAboveNode11013230 :
    adaptiveCoverCheck 11 thetaAboveCell11013230 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell11013230
    e24KC2ThetaAboveLeaf110132300 e24KC2ThetaAboveLeaf110132301 e24KC2ThetaAboveLeaf110132302
      e24KC2ThetaAboveLeaf110132303

theorem e24KC2ThetaAboveNode11013231 :
    adaptiveCoverCheck 11 thetaAboveCell11013231 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell11013231
    e24KC2ThetaAboveLeaf110132310 e24KC2ThetaAboveLeaf110132311 e24KC2ThetaAboveLeaf110132312
      e24KC2ThetaAboveLeaf110132313

theorem e24KC2ThetaAboveNode11013302 :
    adaptiveCoverCheck 11 thetaAboveCell11013302 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell11013302
    e24KC2ThetaAboveLeaf110133020 e24KC2ThetaAboveLeaf110133021 e24KC2ThetaAboveLeaf110133022
      e24KC2ThetaAboveLeaf110133023

theorem e24KC2ThetaAboveNode11013303 :
    adaptiveCoverCheck 11 thetaAboveCell11013303 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell11013303
    e24KC2ThetaAboveLeaf110133030 e24KC2ThetaAboveLeaf110133031 e24KC2ThetaAboveLeaf110133032
      e24KC2ThetaAboveLeaf110133033

theorem e24KC2ThetaAboveNode11013312 :
    adaptiveCoverCheck 11 thetaAboveCell11013312 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell11013312
    e24KC2ThetaAboveLeaf110133120 e24KC2ThetaAboveLeaf110133121 e24KC2ThetaAboveLeaf110133122
      e24KC2ThetaAboveLeaf110133123

theorem e24KC2ThetaAboveNode11013313 :
    adaptiveCoverCheck 11 thetaAboveCell11013313 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell11013313
    e24KC2ThetaAboveLeaf110133130 e24KC2ThetaAboveLeaf110133131 e24KC2ThetaAboveLeaf110133132
      e24KC2ThetaAboveLeaf110133133

theorem e24KC2ThetaAboveNode11013320 :
    adaptiveCoverCheck 11 thetaAboveCell11013320 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell11013320
    e24KC2ThetaAboveLeaf110133200 e24KC2ThetaAboveLeaf110133201 e24KC2ThetaAboveLeaf110133202
      e24KC2ThetaAboveLeaf110133203

theorem e24KC2ThetaAboveNode11013321 :
    adaptiveCoverCheck 11 thetaAboveCell11013321 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell11013321
    e24KC2ThetaAboveLeaf110133210 e24KC2ThetaAboveLeaf110133211 e24KC2ThetaAboveLeaf110133212
      e24KC2ThetaAboveLeaf110133213

theorem e24KC2ThetaAboveNode11013330 :
    adaptiveCoverCheck 11 thetaAboveCell11013330 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell11013330
    e24KC2ThetaAboveLeaf110133300 e24KC2ThetaAboveLeaf110133301 e24KC2ThetaAboveLeaf110133302
      e24KC2ThetaAboveLeaf110133303

theorem e24KC2ThetaAboveNode11013331 :
    adaptiveCoverCheck 11 thetaAboveCell11013331 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell11013331
    e24KC2ThetaAboveLeaf110133310 e24KC2ThetaAboveLeaf110133311 e24KC2ThetaAboveLeaf110133312
      e24KC2ThetaAboveLeaf110133313

theorem e24KC2ThetaAboveNode11102202 :
    adaptiveCoverCheck 11 thetaAboveCell11102202 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell11102202
    e24KC2ThetaAboveLeaf111022020 e24KC2ThetaAboveLeaf111022021 e24KC2ThetaAboveLeaf111022022
      e24KC2ThetaAboveLeaf111022023

theorem e24KC2ThetaAboveNode11102203 :
    adaptiveCoverCheck 11 thetaAboveCell11102203 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell11102203
    e24KC2ThetaAboveLeaf111022030 e24KC2ThetaAboveLeaf111022031 e24KC2ThetaAboveLeaf111022032
      e24KC2ThetaAboveLeaf111022033

theorem e24KC2ThetaAboveNode11102212 :
    adaptiveCoverCheck 11 thetaAboveCell11102212 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell11102212
    e24KC2ThetaAboveLeaf111022120 e24KC2ThetaAboveLeaf111022121 e24KC2ThetaAboveLeaf111022122
      e24KC2ThetaAboveLeaf111022123

theorem e24KC2ThetaAboveNode11102213 :
    adaptiveCoverCheck 11 thetaAboveCell11102213 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell11102213
    e24KC2ThetaAboveLeaf111022130 e24KC2ThetaAboveLeaf111022131 e24KC2ThetaAboveLeaf111022132
      e24KC2ThetaAboveLeaf111022133

theorem e24KC2ThetaAboveNode11102220 :
    adaptiveCoverCheck 11 thetaAboveCell11102220 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell11102220
    e24KC2ThetaAboveLeaf111022200 e24KC2ThetaAboveLeaf111022201 e24KC2ThetaAboveLeaf111022202
      e24KC2ThetaAboveLeaf111022203

theorem e24KC2ThetaAboveNode11102221 :
    adaptiveCoverCheck 11 thetaAboveCell11102221 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell11102221
    e24KC2ThetaAboveLeaf111022210 e24KC2ThetaAboveLeaf111022211 e24KC2ThetaAboveLeaf111022212
      e24KC2ThetaAboveLeaf111022213

theorem e24KC2ThetaAboveNode11102230 :
    adaptiveCoverCheck 11 thetaAboveCell11102230 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell11102230
    e24KC2ThetaAboveLeaf111022300 e24KC2ThetaAboveLeaf111022301 e24KC2ThetaAboveLeaf111022302
      e24KC2ThetaAboveLeaf111022303

theorem e24KC2ThetaAboveNode11102231 :
    adaptiveCoverCheck 11 thetaAboveCell11102231 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell11102231
    e24KC2ThetaAboveLeaf111022310 e24KC2ThetaAboveLeaf111022311 e24KC2ThetaAboveLeaf111022312
      e24KC2ThetaAboveLeaf111022313

theorem e24KC2ThetaAboveNode11102302 :
    adaptiveCoverCheck 11 thetaAboveCell11102302 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell11102302
    e24KC2ThetaAboveLeaf111023020 e24KC2ThetaAboveLeaf111023021 e24KC2ThetaAboveLeaf111023022
      e24KC2ThetaAboveLeaf111023023

theorem e24KC2ThetaAboveNode11102303 :
    adaptiveCoverCheck 11 thetaAboveCell11102303 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell11102303
    e24KC2ThetaAboveLeaf111023030 e24KC2ThetaAboveLeaf111023031 e24KC2ThetaAboveLeaf111023032
      e24KC2ThetaAboveLeaf111023033

theorem e24KC2ThetaAboveNode11102312 :
    adaptiveCoverCheck 11 thetaAboveCell11102312 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell11102312
    e24KC2ThetaAboveLeaf111023120 e24KC2ThetaAboveLeaf111023121 e24KC2ThetaAboveLeaf111023122
      e24KC2ThetaAboveLeaf111023123

theorem e24KC2ThetaAboveNode11102313 :
    adaptiveCoverCheck 11 thetaAboveCell11102313 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell11102313
    e24KC2ThetaAboveLeaf111023130 e24KC2ThetaAboveLeaf111023131 e24KC2ThetaAboveLeaf111023132
      e24KC2ThetaAboveLeaf111023133

theorem e24KC2ThetaAboveNode11102320 :
    adaptiveCoverCheck 11 thetaAboveCell11102320 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell11102320
    e24KC2ThetaAboveLeaf111023200 e24KC2ThetaAboveLeaf111023201 e24KC2ThetaAboveLeaf111023202
      e24KC2ThetaAboveLeaf111023203

theorem e24KC2ThetaAboveNode11102321 :
    adaptiveCoverCheck 11 thetaAboveCell11102321 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell11102321
    e24KC2ThetaAboveLeaf111023210 e24KC2ThetaAboveLeaf111023211 e24KC2ThetaAboveLeaf111023212
      e24KC2ThetaAboveLeaf111023213

theorem e24KC2ThetaAboveNode11102330 :
    adaptiveCoverCheck 11 thetaAboveCell11102330 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell11102330
    e24KC2ThetaAboveLeaf111023300 e24KC2ThetaAboveLeaf111023301 e24KC2ThetaAboveLeaf111023302
      e24KC2ThetaAboveLeaf111023303

theorem e24KC2ThetaAboveNode11102331 :
    adaptiveCoverCheck 11 thetaAboveCell11102331 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell11102331
    e24KC2ThetaAboveLeaf111023310 e24KC2ThetaAboveLeaf111023311 e24KC2ThetaAboveLeaf111023312
      e24KC2ThetaAboveLeaf111023313

theorem e24KC2ThetaAboveNode11103202 :
    adaptiveCoverCheck 11 thetaAboveCell11103202 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell11103202
    e24KC2ThetaAboveLeaf111032020 e24KC2ThetaAboveLeaf111032021 e24KC2ThetaAboveLeaf111032022
      e24KC2ThetaAboveLeaf111032023

theorem e24KC2ThetaAboveNode11103203 :
    adaptiveCoverCheck 11 thetaAboveCell11103203 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell11103203
    e24KC2ThetaAboveLeaf111032030 e24KC2ThetaAboveLeaf111032031 e24KC2ThetaAboveLeaf111032032
      e24KC2ThetaAboveLeaf111032033

theorem e24KC2ThetaAboveNode11103212 :
    adaptiveCoverCheck 11 thetaAboveCell11103212 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell11103212
    e24KC2ThetaAboveLeaf111032120 e24KC2ThetaAboveLeaf111032121 e24KC2ThetaAboveLeaf111032122
      e24KC2ThetaAboveLeaf111032123

theorem e24KC2ThetaAboveNode11103213 :
    adaptiveCoverCheck 11 thetaAboveCell11103213 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell11103213
    e24KC2ThetaAboveLeaf111032130 e24KC2ThetaAboveLeaf111032131 e24KC2ThetaAboveLeaf111032132
      e24KC2ThetaAboveLeaf111032133

theorem e24KC2ThetaAboveNode11103220 :
    adaptiveCoverCheck 11 thetaAboveCell11103220 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell11103220
    e24KC2ThetaAboveLeaf111032200 e24KC2ThetaAboveLeaf111032201 e24KC2ThetaAboveLeaf111032202
      e24KC2ThetaAboveLeaf111032203

theorem e24KC2ThetaAboveNode11103221 :
    adaptiveCoverCheck 11 thetaAboveCell11103221 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell11103221
    e24KC2ThetaAboveLeaf111032210 e24KC2ThetaAboveLeaf111032211 e24KC2ThetaAboveLeaf111032212
      e24KC2ThetaAboveLeaf111032213

theorem e24KC2ThetaAboveNode11103230 :
    adaptiveCoverCheck 11 thetaAboveCell11103230 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell11103230
    e24KC2ThetaAboveLeaf111032300 e24KC2ThetaAboveLeaf111032301 e24KC2ThetaAboveLeaf111032302
      e24KC2ThetaAboveLeaf111032303

theorem e24KC2ThetaAboveNode11103231 :
    adaptiveCoverCheck 11 thetaAboveCell11103231 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell11103231
    e24KC2ThetaAboveLeaf111032310 e24KC2ThetaAboveLeaf111032311 e24KC2ThetaAboveLeaf111032312
      e24KC2ThetaAboveLeaf111032313

theorem e24KC2ThetaAboveNode11103302 :
    adaptiveCoverCheck 11 thetaAboveCell11103302 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell11103302
    e24KC2ThetaAboveLeaf111033020 e24KC2ThetaAboveLeaf111033021 e24KC2ThetaAboveLeaf111033022
      e24KC2ThetaAboveLeaf111033023

theorem e24KC2ThetaAboveNode11103303 :
    adaptiveCoverCheck 11 thetaAboveCell11103303 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell11103303
    e24KC2ThetaAboveLeaf111033030 e24KC2ThetaAboveLeaf111033031 e24KC2ThetaAboveLeaf111033032
      e24KC2ThetaAboveLeaf111033033

theorem e24KC2ThetaAboveNode11103312 :
    adaptiveCoverCheck 11 thetaAboveCell11103312 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell11103312
    e24KC2ThetaAboveLeaf111033120 e24KC2ThetaAboveLeaf111033121 e24KC2ThetaAboveLeaf111033122
      e24KC2ThetaAboveLeaf111033123

theorem e24KC2ThetaAboveNode11103313 :
    adaptiveCoverCheck 11 thetaAboveCell11103313 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell11103313
    e24KC2ThetaAboveLeaf111033130 e24KC2ThetaAboveLeaf111033131 e24KC2ThetaAboveLeaf111033132
      e24KC2ThetaAboveLeaf111033133

theorem e24KC2ThetaAboveNode11103320 :
    adaptiveCoverCheck 11 thetaAboveCell11103320 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell11103320
    e24KC2ThetaAboveLeaf111033200 e24KC2ThetaAboveLeaf111033201 e24KC2ThetaAboveLeaf111033202
      e24KC2ThetaAboveLeaf111033203

theorem e24KC2ThetaAboveNode11103321 :
    adaptiveCoverCheck 11 thetaAboveCell11103321 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell11103321
    e24KC2ThetaAboveLeaf111033210 e24KC2ThetaAboveLeaf111033211 e24KC2ThetaAboveLeaf111033212
      e24KC2ThetaAboveLeaf111033213

theorem e24KC2ThetaAboveNode11103330 :
    adaptiveCoverCheck 11 thetaAboveCell11103330 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell11103330
    e24KC2ThetaAboveLeaf111033300 e24KC2ThetaAboveLeaf111033301 e24KC2ThetaAboveLeaf111033302
      e24KC2ThetaAboveLeaf111033303

theorem e24KC2ThetaAboveNode11103331 :
    adaptiveCoverCheck 11 thetaAboveCell11103331 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell11103331
    e24KC2ThetaAboveLeaf111033310 e24KC2ThetaAboveLeaf111033311 e24KC2ThetaAboveLeaf111033312
      e24KC2ThetaAboveLeaf111033313

theorem e24KC2ThetaAboveNode11112202 :
    adaptiveCoverCheck 11 thetaAboveCell11112202 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell11112202
    e24KC2ThetaAboveLeaf111122020 e24KC2ThetaAboveLeaf111122021 e24KC2ThetaAboveLeaf111122022
      e24KC2ThetaAboveLeaf111122023

theorem e24KC2ThetaAboveNode11112203 :
    adaptiveCoverCheck 11 thetaAboveCell11112203 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell11112203
    e24KC2ThetaAboveLeaf111122030 e24KC2ThetaAboveLeaf111122031 e24KC2ThetaAboveLeaf111122032
      e24KC2ThetaAboveLeaf111122033

theorem e24KC2ThetaAboveNode11112212 :
    adaptiveCoverCheck 11 thetaAboveCell11112212 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell11112212
    e24KC2ThetaAboveLeaf111122120 e24KC2ThetaAboveLeaf111122121 e24KC2ThetaAboveLeaf111122122
      e24KC2ThetaAboveLeaf111122123

theorem e24KC2ThetaAboveNode11112213 :
    adaptiveCoverCheck 11 thetaAboveCell11112213 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell11112213
    e24KC2ThetaAboveLeaf111122130 e24KC2ThetaAboveLeaf111122131 e24KC2ThetaAboveLeaf111122132
      e24KC2ThetaAboveLeaf111122133

theorem e24KC2ThetaAboveNode11112220 :
    adaptiveCoverCheck 11 thetaAboveCell11112220 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell11112220
    e24KC2ThetaAboveLeaf111122200 e24KC2ThetaAboveLeaf111122201 e24KC2ThetaAboveLeaf111122202
      e24KC2ThetaAboveLeaf111122203

theorem e24KC2ThetaAboveNode11112221 :
    adaptiveCoverCheck 11 thetaAboveCell11112221 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell11112221
    e24KC2ThetaAboveLeaf111122210 e24KC2ThetaAboveLeaf111122211 e24KC2ThetaAboveLeaf111122212
      e24KC2ThetaAboveLeaf111122213

theorem e24KC2ThetaAboveNode11112230 :
    adaptiveCoverCheck 11 thetaAboveCell11112230 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell11112230
    e24KC2ThetaAboveLeaf111122300 e24KC2ThetaAboveLeaf111122301 e24KC2ThetaAboveLeaf111122302
      e24KC2ThetaAboveLeaf111122303

theorem e24KC2ThetaAboveNode11112231 :
    adaptiveCoverCheck 11 thetaAboveCell11112231 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell11112231
    e24KC2ThetaAboveLeaf111122310 e24KC2ThetaAboveLeaf111122311 e24KC2ThetaAboveLeaf111122312
      e24KC2ThetaAboveLeaf111122313

theorem e24KC2ThetaAboveNode11112302 :
    adaptiveCoverCheck 11 thetaAboveCell11112302 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell11112302
    e24KC2ThetaAboveLeaf111123020 e24KC2ThetaAboveLeaf111123021 e24KC2ThetaAboveLeaf111123022
      e24KC2ThetaAboveLeaf111123023

theorem e24KC2ThetaAboveNode11112303 :
    adaptiveCoverCheck 11 thetaAboveCell11112303 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell11112303
    e24KC2ThetaAboveLeaf111123030 e24KC2ThetaAboveLeaf111123031 e24KC2ThetaAboveLeaf111123032
      e24KC2ThetaAboveLeaf111123033

theorem e24KC2ThetaAboveNode11112312 :
    adaptiveCoverCheck 11 thetaAboveCell11112312 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell11112312
    e24KC2ThetaAboveLeaf111123120 e24KC2ThetaAboveLeaf111123121 e24KC2ThetaAboveLeaf111123122
      e24KC2ThetaAboveLeaf111123123

theorem e24KC2ThetaAboveNode11112313 :
    adaptiveCoverCheck 11 thetaAboveCell11112313 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell11112313
    e24KC2ThetaAboveLeaf111123130 e24KC2ThetaAboveLeaf111123131 e24KC2ThetaAboveLeaf111123132
      e24KC2ThetaAboveLeaf111123133

theorem e24KC2ThetaAboveNode11112320 :
    adaptiveCoverCheck 11 thetaAboveCell11112320 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell11112320
    e24KC2ThetaAboveLeaf111123200 e24KC2ThetaAboveLeaf111123201 e24KC2ThetaAboveLeaf111123202
      e24KC2ThetaAboveLeaf111123203

theorem e24KC2ThetaAboveNode11112321 :
    adaptiveCoverCheck 11 thetaAboveCell11112321 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell11112321
    e24KC2ThetaAboveLeaf111123210 e24KC2ThetaAboveLeaf111123211 e24KC2ThetaAboveLeaf111123212
      e24KC2ThetaAboveLeaf111123213

theorem e24KC2ThetaAboveNode11112330 :
    adaptiveCoverCheck 11 thetaAboveCell11112330 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell11112330
    e24KC2ThetaAboveLeaf111123300 e24KC2ThetaAboveLeaf111123301 e24KC2ThetaAboveLeaf111123302
      e24KC2ThetaAboveLeaf111123303

theorem e24KC2ThetaAboveNode11112331 :
    adaptiveCoverCheck 11 thetaAboveCell11112331 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell11112331
    e24KC2ThetaAboveLeaf111123310 e24KC2ThetaAboveLeaf111123311 e24KC2ThetaAboveLeaf111123312
      e24KC2ThetaAboveLeaf111123313

theorem e24KC2ThetaAboveNode11112332 :
    adaptiveCoverCheck 11 thetaAboveCell11112332 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell11112332
    e24KC2ThetaAboveLeaf111123320 e24KC2ThetaAboveLeaf111123321 e24KC2ThetaAboveLeaf111123322
      e24KC2ThetaAboveLeaf111123323

theorem e24KC2ThetaAboveNode11112333 :
    adaptiveCoverCheck 11 thetaAboveCell11112333 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell11112333
    e24KC2ThetaAboveLeaf111123330 e24KC2ThetaAboveLeaf111123331 e24KC2ThetaAboveLeaf111123332
      e24KC2ThetaAboveLeaf111123333

theorem e24KC2ThetaAboveNode11113202 :
    adaptiveCoverCheck 11 thetaAboveCell11113202 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell11113202
    e24KC2ThetaAboveLeaf111132020 e24KC2ThetaAboveLeaf111132021 e24KC2ThetaAboveLeaf111132022
      e24KC2ThetaAboveLeaf111132023

theorem e24KC2ThetaAboveNode11113203 :
    adaptiveCoverCheck 11 thetaAboveCell11113203 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell11113203
    e24KC2ThetaAboveLeaf111132030 e24KC2ThetaAboveLeaf111132031 e24KC2ThetaAboveLeaf111132032
      e24KC2ThetaAboveLeaf111132033

theorem e24KC2ThetaAboveNode11113212 :
    adaptiveCoverCheck 11 thetaAboveCell11113212 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell11113212
    e24KC2ThetaAboveLeaf111132120 e24KC2ThetaAboveLeaf111132121 e24KC2ThetaAboveLeaf111132122
      e24KC2ThetaAboveLeaf111132123

theorem e24KC2ThetaAboveNode11113213 :
    adaptiveCoverCheck 11 thetaAboveCell11113213 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell11113213
    e24KC2ThetaAboveLeaf111132130 e24KC2ThetaAboveLeaf111132131 e24KC2ThetaAboveLeaf111132132
      e24KC2ThetaAboveLeaf111132133

theorem e24KC2ThetaAboveNode11113220 :
    adaptiveCoverCheck 11 thetaAboveCell11113220 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell11113220
    e24KC2ThetaAboveLeaf111132200 e24KC2ThetaAboveLeaf111132201 e24KC2ThetaAboveLeaf111132202
      e24KC2ThetaAboveLeaf111132203

theorem e24KC2ThetaAboveNode11113221 :
    adaptiveCoverCheck 11 thetaAboveCell11113221 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell11113221
    e24KC2ThetaAboveLeaf111132210 e24KC2ThetaAboveLeaf111132211 e24KC2ThetaAboveLeaf111132212
      e24KC2ThetaAboveLeaf111132213

theorem e24KC2ThetaAboveNode11113222 :
    adaptiveCoverCheck 11 thetaAboveCell11113222 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell11113222
    e24KC2ThetaAboveLeaf111132220 e24KC2ThetaAboveLeaf111132221 e24KC2ThetaAboveLeaf111132222
      e24KC2ThetaAboveLeaf111132223

theorem e24KC2ThetaAboveNode11113223 :
    adaptiveCoverCheck 11 thetaAboveCell11113223 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell11113223
    e24KC2ThetaAboveLeaf111132230 e24KC2ThetaAboveLeaf111132231 e24KC2ThetaAboveLeaf111132232
      e24KC2ThetaAboveLeaf111132233

theorem e24KC2ThetaAboveNode11113230 :
    adaptiveCoverCheck 11 thetaAboveCell11113230 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell11113230
    e24KC2ThetaAboveLeaf111132300 e24KC2ThetaAboveLeaf111132301 e24KC2ThetaAboveLeaf111132302
      e24KC2ThetaAboveLeaf111132303

theorem e24KC2ThetaAboveNode11113231 :
    adaptiveCoverCheck 11 thetaAboveCell11113231 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell11113231
    e24KC2ThetaAboveLeaf111132310 e24KC2ThetaAboveLeaf111132311 e24KC2ThetaAboveLeaf111132312
      e24KC2ThetaAboveLeaf111132313

theorem e24KC2ThetaAboveNode11113232 :
    adaptiveCoverCheck 11 thetaAboveCell11113232 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell11113232
    e24KC2ThetaAboveLeaf111132320 e24KC2ThetaAboveLeaf111132321 e24KC2ThetaAboveLeaf111132322
      e24KC2ThetaAboveLeaf111132323

theorem e24KC2ThetaAboveNode11113233 :
    adaptiveCoverCheck 11 thetaAboveCell11113233 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell11113233
    e24KC2ThetaAboveLeaf111132330 e24KC2ThetaAboveLeaf111132331 e24KC2ThetaAboveLeaf111132332
      e24KC2ThetaAboveLeaf111132333

theorem e24KC2ThetaAboveNode11113302 :
    adaptiveCoverCheck 11 thetaAboveCell11113302 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell11113302
    e24KC2ThetaAboveLeaf111133020 e24KC2ThetaAboveLeaf111133021 e24KC2ThetaAboveLeaf111133022
      e24KC2ThetaAboveLeaf111133023

theorem e24KC2ThetaAboveNode11113303 :
    adaptiveCoverCheck 11 thetaAboveCell11113303 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell11113303
    e24KC2ThetaAboveLeaf111133030 e24KC2ThetaAboveLeaf111133031 e24KC2ThetaAboveLeaf111133032
      e24KC2ThetaAboveLeaf111133033

theorem e24KC2ThetaAboveNode11113312 :
    adaptiveCoverCheck 11 thetaAboveCell11113312 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell11113312
    e24KC2ThetaAboveLeaf111133120 e24KC2ThetaAboveLeaf111133121 e24KC2ThetaAboveLeaf111133122
      e24KC2ThetaAboveLeaf111133123

theorem e24KC2ThetaAboveNode11113313 :
    adaptiveCoverCheck 11 thetaAboveCell11113313 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell11113313
    e24KC2ThetaAboveLeaf111133130 e24KC2ThetaAboveLeaf111133131 e24KC2ThetaAboveLeaf111133132
      e24KC2ThetaAboveLeaf111133133

theorem e24KC2ThetaAboveNode11113320 :
    adaptiveCoverCheck 11 thetaAboveCell11113320 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell11113320
    e24KC2ThetaAboveLeaf111133200 e24KC2ThetaAboveLeaf111133201 e24KC2ThetaAboveLeaf111133202
      e24KC2ThetaAboveLeaf111133203

theorem e24KC2ThetaAboveNode11113321 :
    adaptiveCoverCheck 11 thetaAboveCell11113321 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell11113321
    e24KC2ThetaAboveLeaf111133210 e24KC2ThetaAboveLeaf111133211 e24KC2ThetaAboveLeaf111133212
      e24KC2ThetaAboveLeaf111133213

theorem e24KC2ThetaAboveNode11113322 :
    adaptiveCoverCheck 11 thetaAboveCell11113322 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell11113322
    e24KC2ThetaAboveLeaf111133220 e24KC2ThetaAboveLeaf111133221 e24KC2ThetaAboveLeaf111133222
      e24KC2ThetaAboveLeaf111133223

theorem e24KC2ThetaAboveNode11113323 :
    adaptiveCoverCheck 11 thetaAboveCell11113323 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell11113323
    e24KC2ThetaAboveLeaf111133230 e24KC2ThetaAboveLeaf111133231 e24KC2ThetaAboveLeaf111133232
      e24KC2ThetaAboveLeaf111133233

theorem e24KC2ThetaAboveNode11113330 :
    adaptiveCoverCheck 11 thetaAboveCell11113330 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell11113330
    e24KC2ThetaAboveLeaf111133300 e24KC2ThetaAboveLeaf111133301 e24KC2ThetaAboveLeaf111133302
      e24KC2ThetaAboveLeaf111133303

theorem e24KC2ThetaAboveNode11113331 :
    adaptiveCoverCheck 11 thetaAboveCell11113331 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell11113331
    e24KC2ThetaAboveLeaf111133310 e24KC2ThetaAboveLeaf111133311 e24KC2ThetaAboveLeaf111133312
      e24KC2ThetaAboveLeaf111133313

theorem e24KC2ThetaAboveNode11113332 :
    adaptiveCoverCheck 11 thetaAboveCell11113332 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell11113332
    e24KC2ThetaAboveLeaf111133320 e24KC2ThetaAboveLeaf111133321 e24KC2ThetaAboveLeaf111133322
      e24KC2ThetaAboveLeaf111133323

theorem e24KC2ThetaAboveNode11113333 :
    adaptiveCoverCheck 11 thetaAboveCell11113333 = true :=
  adaptiveCoverCheck_succ_of_children 10 thetaAboveCell11113333
    e24KC2ThetaAboveLeaf111133330 e24KC2ThetaAboveLeaf111133331 e24KC2ThetaAboveLeaf111133332
      e24KC2ThetaAboveLeaf111133333

theorem e24KC2ThetaAboveNode0000202 :
    adaptiveCoverCheck 12 (childHL (childLL (childHL thetaAboveCell0000))) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childHL (childLL (childHL thetaAboveCell0000)))
    e24KC2ThetaAboveLeaf00002020 e24KC2ThetaAboveLeaf00002021 e24KC2ThetaAboveNode00002022
      e24KC2ThetaAboveNode00002023

theorem e24KC2ThetaAboveNode0000203 :
    adaptiveCoverCheck 12 (childHH (childLL (childHL thetaAboveCell0000))) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childHH (childLL (childHL thetaAboveCell0000)))
    e24KC2ThetaAboveLeaf00002030 e24KC2ThetaAboveLeaf00002031 e24KC2ThetaAboveNode00002032
      e24KC2ThetaAboveNode00002033

theorem e24KC2ThetaAboveNode0000212 :
    adaptiveCoverCheck 12 (childHL (childLH (childHL thetaAboveCell0000))) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childHL (childLH (childHL thetaAboveCell0000)))
    e24KC2ThetaAboveLeaf00002120 e24KC2ThetaAboveLeaf00002121 e24KC2ThetaAboveNode00002122
      e24KC2ThetaAboveNode00002123

theorem e24KC2ThetaAboveNode0000213 :
    adaptiveCoverCheck 12 (childHH (childLH (childHL thetaAboveCell0000))) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childHH (childLH (childHL thetaAboveCell0000)))
    e24KC2ThetaAboveLeaf00002130 e24KC2ThetaAboveLeaf00002131 e24KC2ThetaAboveNode00002132
      e24KC2ThetaAboveNode00002133

theorem e24KC2ThetaAboveNode0000220 :
    adaptiveCoverCheck 12 (childLL (childHL (childHL thetaAboveCell0000))) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childLL (childHL (childHL thetaAboveCell0000)))
    e24KC2ThetaAboveNode00002200 e24KC2ThetaAboveNode00002201 e24KC2ThetaAboveNode00002202
      e24KC2ThetaAboveNode00002203

theorem e24KC2ThetaAboveNode0000221 :
    adaptiveCoverCheck 12 (childLH (childHL (childHL thetaAboveCell0000))) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childLH (childHL (childHL thetaAboveCell0000)))
    e24KC2ThetaAboveNode00002210 e24KC2ThetaAboveNode00002211 e24KC2ThetaAboveNode00002212
      e24KC2ThetaAboveNode00002213

theorem e24KC2ThetaAboveNode0000222 :
    adaptiveCoverCheck 12 (childHL (childHL (childHL thetaAboveCell0000))) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childHL (childHL (childHL thetaAboveCell0000)))
    e24KC2ThetaAboveLeaf00002220 e24KC2ThetaAboveLeaf00002221 e24KC2ThetaAboveLeaf00002222
      e24KC2ThetaAboveLeaf00002223

theorem e24KC2ThetaAboveNode0000223 :
    adaptiveCoverCheck 12 (childHH (childHL (childHL thetaAboveCell0000))) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childHH (childHL (childHL thetaAboveCell0000)))
    e24KC2ThetaAboveLeaf00002230 e24KC2ThetaAboveLeaf00002231 e24KC2ThetaAboveLeaf00002232
      e24KC2ThetaAboveLeaf00002233

theorem e24KC2ThetaAboveNode0000230 :
    adaptiveCoverCheck 12 (childLL (childHH (childHL thetaAboveCell0000))) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childLL (childHH (childHL thetaAboveCell0000)))
    e24KC2ThetaAboveNode00002300 e24KC2ThetaAboveNode00002301 e24KC2ThetaAboveNode00002302
      e24KC2ThetaAboveNode00002303

theorem e24KC2ThetaAboveNode0000231 :
    adaptiveCoverCheck 12 (childLH (childHH (childHL thetaAboveCell0000))) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childLH (childHH (childHL thetaAboveCell0000)))
    e24KC2ThetaAboveNode00002310 e24KC2ThetaAboveNode00002311 e24KC2ThetaAboveNode00002312
      e24KC2ThetaAboveNode00002313

theorem e24KC2ThetaAboveNode0000232 :
    adaptiveCoverCheck 12 (childHL (childHH (childHL thetaAboveCell0000))) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childHL (childHH (childHL thetaAboveCell0000)))
    e24KC2ThetaAboveLeaf00002320 e24KC2ThetaAboveLeaf00002321 e24KC2ThetaAboveLeaf00002322
      e24KC2ThetaAboveLeaf00002323

theorem e24KC2ThetaAboveNode0000233 :
    adaptiveCoverCheck 12 (childHH (childHH (childHL thetaAboveCell0000))) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childHH (childHH (childHL thetaAboveCell0000)))
    e24KC2ThetaAboveLeaf00002330 e24KC2ThetaAboveLeaf00002331 e24KC2ThetaAboveLeaf00002332
      e24KC2ThetaAboveLeaf00002333

theorem e24KC2ThetaAboveNode0000302 :
    adaptiveCoverCheck 12 (childHL (childLL (childHH thetaAboveCell0000))) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childHL (childLL (childHH thetaAboveCell0000)))
    e24KC2ThetaAboveLeaf00003020 e24KC2ThetaAboveLeaf00003021 e24KC2ThetaAboveNode00003022
      e24KC2ThetaAboveNode00003023

theorem e24KC2ThetaAboveNode0000303 :
    adaptiveCoverCheck 12 (childHH (childLL (childHH thetaAboveCell0000))) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childHH (childLL (childHH thetaAboveCell0000)))
    e24KC2ThetaAboveLeaf00003030 e24KC2ThetaAboveLeaf00003031 e24KC2ThetaAboveNode00003032
      e24KC2ThetaAboveNode00003033

theorem e24KC2ThetaAboveNode0000312 :
    adaptiveCoverCheck 12 (childHL (childLH (childHH thetaAboveCell0000))) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childHL (childLH (childHH thetaAboveCell0000)))
    e24KC2ThetaAboveLeaf00003120 e24KC2ThetaAboveLeaf00003121 e24KC2ThetaAboveNode00003122
      e24KC2ThetaAboveNode00003123

theorem e24KC2ThetaAboveNode0000313 :
    adaptiveCoverCheck 12 (childHH (childLH (childHH thetaAboveCell0000))) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childHH (childLH (childHH thetaAboveCell0000)))
    e24KC2ThetaAboveLeaf00003130 e24KC2ThetaAboveLeaf00003131 e24KC2ThetaAboveNode00003132
      e24KC2ThetaAboveNode00003133

end PartE
end GerverSofa

end

end

end

section

/-!
# Reconstruction of the upper theta cover
-/

public section

noncomputable section

namespace GerverSofa
namespace PartE

open CertificateCells1a75b359b5

theorem e24KC2ThetaAboveNode0000320 :
    adaptiveCoverCheck 12 (childLL (childHL (childHH thetaAboveCell0000))) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childLL (childHL (childHH thetaAboveCell0000)))
    e24KC2ThetaAboveNode00003200 e24KC2ThetaAboveNode00003201 e24KC2ThetaAboveNode00003202
      e24KC2ThetaAboveNode00003203

theorem e24KC2ThetaAboveNode0000321 :
    adaptiveCoverCheck 12 (childLH (childHL (childHH thetaAboveCell0000))) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childLH (childHL (childHH thetaAboveCell0000)))
    e24KC2ThetaAboveNode00003210 e24KC2ThetaAboveNode00003211 e24KC2ThetaAboveNode00003212
      e24KC2ThetaAboveNode00003213

theorem e24KC2ThetaAboveNode0000322 :
    adaptiveCoverCheck 12 (childHL (childHL (childHH thetaAboveCell0000))) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childHL (childHL (childHH thetaAboveCell0000)))
    e24KC2ThetaAboveLeaf00003220 e24KC2ThetaAboveLeaf00003221 e24KC2ThetaAboveLeaf00003222
      e24KC2ThetaAboveLeaf00003223

theorem e24KC2ThetaAboveNode0000323 :
    adaptiveCoverCheck 12 (childHH (childHL (childHH thetaAboveCell0000))) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childHH (childHL (childHH thetaAboveCell0000)))
    e24KC2ThetaAboveLeaf00003230 e24KC2ThetaAboveLeaf00003231 e24KC2ThetaAboveLeaf00003232
      e24KC2ThetaAboveLeaf00003233

theorem e24KC2ThetaAboveNode0000330 :
    adaptiveCoverCheck 12 (childLL (childHH (childHH thetaAboveCell0000))) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childLL (childHH (childHH thetaAboveCell0000)))
    e24KC2ThetaAboveNode00003300 e24KC2ThetaAboveNode00003301 e24KC2ThetaAboveNode00003302
      e24KC2ThetaAboveNode00003303

theorem e24KC2ThetaAboveNode0000331 :
    adaptiveCoverCheck 12 (childLH (childHH (childHH thetaAboveCell0000))) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childLH (childHH (childHH thetaAboveCell0000)))
    e24KC2ThetaAboveNode00003310 e24KC2ThetaAboveNode00003311 e24KC2ThetaAboveNode00003312
      e24KC2ThetaAboveNode00003313

theorem e24KC2ThetaAboveNode0000332 :
    adaptiveCoverCheck 12 (childHL (childHH (childHH thetaAboveCell0000))) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childHL (childHH (childHH thetaAboveCell0000)))
    e24KC2ThetaAboveLeaf00003320 e24KC2ThetaAboveLeaf00003321 e24KC2ThetaAboveLeaf00003322
      e24KC2ThetaAboveLeaf00003323

theorem e24KC2ThetaAboveNode0000333 :
    adaptiveCoverCheck 12 (childHH (childHH (childHH thetaAboveCell0000))) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childHH (childHH (childHH thetaAboveCell0000)))
    e24KC2ThetaAboveLeaf00003330 e24KC2ThetaAboveLeaf00003331 e24KC2ThetaAboveLeaf00003332
      e24KC2ThetaAboveLeaf00003333

theorem e24KC2ThetaAboveNode0001202 :
    adaptiveCoverCheck 12 (childHL (childLL (childHL thetaAboveCell0001))) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childHL (childLL (childHL thetaAboveCell0001)))
    e24KC2ThetaAboveLeaf00012020 e24KC2ThetaAboveLeaf00012021 e24KC2ThetaAboveNode00012022
      e24KC2ThetaAboveNode00012023

theorem e24KC2ThetaAboveNode0001203 :
    adaptiveCoverCheck 12 (childHH (childLL (childHL thetaAboveCell0001))) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childHH (childLL (childHL thetaAboveCell0001)))
    e24KC2ThetaAboveLeaf00012030 e24KC2ThetaAboveLeaf00012031 e24KC2ThetaAboveNode00012032
      e24KC2ThetaAboveNode00012033

theorem e24KC2ThetaAboveNode0001212 :
    adaptiveCoverCheck 12 (childHL (childLH (childHL thetaAboveCell0001))) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childHL (childLH (childHL thetaAboveCell0001)))
    e24KC2ThetaAboveLeaf00012120 e24KC2ThetaAboveLeaf00012121 e24KC2ThetaAboveNode00012122
      e24KC2ThetaAboveNode00012123

theorem e24KC2ThetaAboveNode0001213 :
    adaptiveCoverCheck 12 (childHH (childLH (childHL thetaAboveCell0001))) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childHH (childLH (childHL thetaAboveCell0001)))
    e24KC2ThetaAboveLeaf00012130 e24KC2ThetaAboveLeaf00012131 e24KC2ThetaAboveNode00012132
      e24KC2ThetaAboveNode00012133

theorem e24KC2ThetaAboveNode0001220 :
    adaptiveCoverCheck 12 (childLL (childHL (childHL thetaAboveCell0001))) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childLL (childHL (childHL thetaAboveCell0001)))
    e24KC2ThetaAboveNode00012200 e24KC2ThetaAboveNode00012201 e24KC2ThetaAboveNode00012202
      e24KC2ThetaAboveNode00012203

theorem e24KC2ThetaAboveNode0001221 :
    adaptiveCoverCheck 12 (childLH (childHL (childHL thetaAboveCell0001))) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childLH (childHL (childHL thetaAboveCell0001)))
    e24KC2ThetaAboveNode00012210 e24KC2ThetaAboveNode00012211 e24KC2ThetaAboveNode00012212
      e24KC2ThetaAboveNode00012213

theorem e24KC2ThetaAboveNode0001222 :
    adaptiveCoverCheck 12 (childHL (childHL (childHL thetaAboveCell0001))) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childHL (childHL (childHL thetaAboveCell0001)))
    e24KC2ThetaAboveLeaf00012220 e24KC2ThetaAboveLeaf00012221 e24KC2ThetaAboveLeaf00012222
      e24KC2ThetaAboveLeaf00012223

theorem e24KC2ThetaAboveNode0001223 :
    adaptiveCoverCheck 12 (childHH (childHL (childHL thetaAboveCell0001))) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childHH (childHL (childHL thetaAboveCell0001)))
    e24KC2ThetaAboveLeaf00012230 e24KC2ThetaAboveLeaf00012231 e24KC2ThetaAboveLeaf00012232
      e24KC2ThetaAboveLeaf00012233

theorem e24KC2ThetaAboveNode0001230 :
    adaptiveCoverCheck 12 (childLL (childHH (childHL thetaAboveCell0001))) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childLL (childHH (childHL thetaAboveCell0001)))
    e24KC2ThetaAboveNode00012300 e24KC2ThetaAboveNode00012301 e24KC2ThetaAboveNode00012302
      e24KC2ThetaAboveNode00012303

theorem e24KC2ThetaAboveNode0001231 :
    adaptiveCoverCheck 12 (childLH (childHH (childHL thetaAboveCell0001))) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childLH (childHH (childHL thetaAboveCell0001)))
    e24KC2ThetaAboveNode00012310 e24KC2ThetaAboveNode00012311 e24KC2ThetaAboveNode00012312
      e24KC2ThetaAboveNode00012313

theorem e24KC2ThetaAboveNode0001232 :
    adaptiveCoverCheck 12 (childHL (childHH (childHL thetaAboveCell0001))) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childHL (childHH (childHL thetaAboveCell0001)))
    e24KC2ThetaAboveLeaf00012320 e24KC2ThetaAboveLeaf00012321 e24KC2ThetaAboveLeaf00012322
      e24KC2ThetaAboveLeaf00012323

theorem e24KC2ThetaAboveNode0001233 :
    adaptiveCoverCheck 12 (childHH (childHH (childHL thetaAboveCell0001))) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childHH (childHH (childHL thetaAboveCell0001)))
    e24KC2ThetaAboveLeaf00012330 e24KC2ThetaAboveLeaf00012331 e24KC2ThetaAboveLeaf00012332
      e24KC2ThetaAboveLeaf00012333

theorem e24KC2ThetaAboveNode0001302 :
    adaptiveCoverCheck 12 (childHL (childLL (childHH thetaAboveCell0001))) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childHL (childLL (childHH thetaAboveCell0001)))
    e24KC2ThetaAboveLeaf00013020 e24KC2ThetaAboveLeaf00013021 e24KC2ThetaAboveNode00013022
      e24KC2ThetaAboveNode00013023

theorem e24KC2ThetaAboveNode0001303 :
    adaptiveCoverCheck 12 (childHH (childLL (childHH thetaAboveCell0001))) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childHH (childLL (childHH thetaAboveCell0001)))
    e24KC2ThetaAboveLeaf00013030 e24KC2ThetaAboveLeaf00013031 e24KC2ThetaAboveNode00013032
      e24KC2ThetaAboveNode00013033

theorem e24KC2ThetaAboveNode0001312 :
    adaptiveCoverCheck 12 (childHL (childLH (childHH thetaAboveCell0001))) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childHL (childLH (childHH thetaAboveCell0001)))
    e24KC2ThetaAboveLeaf00013120 e24KC2ThetaAboveLeaf00013121 e24KC2ThetaAboveNode00013122
      e24KC2ThetaAboveNode00013123

theorem e24KC2ThetaAboveNode0001313 :
    adaptiveCoverCheck 12 (childHH (childLH (childHH thetaAboveCell0001))) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childHH (childLH (childHH thetaAboveCell0001)))
    e24KC2ThetaAboveLeaf00013130 e24KC2ThetaAboveLeaf00013131 e24KC2ThetaAboveNode00013132
      e24KC2ThetaAboveNode00013133

theorem e24KC2ThetaAboveNode0001320 :
    adaptiveCoverCheck 12 (childLL (childHL (childHH thetaAboveCell0001))) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childLL (childHL (childHH thetaAboveCell0001)))
    e24KC2ThetaAboveNode00013200 e24KC2ThetaAboveNode00013201 e24KC2ThetaAboveNode00013202
      e24KC2ThetaAboveNode00013203

theorem e24KC2ThetaAboveNode0001321 :
    adaptiveCoverCheck 12 (childLH (childHL (childHH thetaAboveCell0001))) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childLH (childHL (childHH thetaAboveCell0001)))
    e24KC2ThetaAboveNode00013210 e24KC2ThetaAboveNode00013211 e24KC2ThetaAboveNode00013212
      e24KC2ThetaAboveNode00013213

theorem e24KC2ThetaAboveNode0001322 :
    adaptiveCoverCheck 12 (childHL (childHL (childHH thetaAboveCell0001))) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childHL (childHL (childHH thetaAboveCell0001)))
    e24KC2ThetaAboveLeaf00013220 e24KC2ThetaAboveLeaf00013221 e24KC2ThetaAboveLeaf00013222
      e24KC2ThetaAboveLeaf00013223

theorem e24KC2ThetaAboveNode0001323 :
    adaptiveCoverCheck 12 (childHH (childHL (childHH thetaAboveCell0001))) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childHH (childHL (childHH thetaAboveCell0001)))
    e24KC2ThetaAboveLeaf00013230 e24KC2ThetaAboveLeaf00013231 e24KC2ThetaAboveLeaf00013232
      e24KC2ThetaAboveLeaf00013233

theorem e24KC2ThetaAboveNode0001330 :
    adaptiveCoverCheck 12 (childLL (childHH (childHH thetaAboveCell0001))) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childLL (childHH (childHH thetaAboveCell0001)))
    e24KC2ThetaAboveNode00013300 e24KC2ThetaAboveNode00013301 e24KC2ThetaAboveNode00013302
      e24KC2ThetaAboveNode00013303

theorem e24KC2ThetaAboveNode0001331 :
    adaptiveCoverCheck 12 (childLH (childHH (childHH thetaAboveCell0001))) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childLH (childHH (childHH thetaAboveCell0001)))
    e24KC2ThetaAboveNode00013310 e24KC2ThetaAboveNode00013311 e24KC2ThetaAboveNode00013312
      e24KC2ThetaAboveNode00013313

theorem e24KC2ThetaAboveNode0001332 :
    adaptiveCoverCheck 12 (childHL (childHH (childHH thetaAboveCell0001))) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childHL (childHH (childHH thetaAboveCell0001)))
    e24KC2ThetaAboveLeaf00013320 e24KC2ThetaAboveLeaf00013321 e24KC2ThetaAboveLeaf00013322
      e24KC2ThetaAboveLeaf00013323

theorem e24KC2ThetaAboveNode0001333 :
    adaptiveCoverCheck 12 (childHH (childHH (childHH thetaAboveCell0001))) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childHH (childHH (childHH thetaAboveCell0001)))
    e24KC2ThetaAboveLeaf00013330 e24KC2ThetaAboveLeaf00013331 e24KC2ThetaAboveLeaf00013332
      e24KC2ThetaAboveLeaf00013333

theorem e24KC2ThetaAboveNode0010202 :
    adaptiveCoverCheck 12 (childHL (childLL (childHL thetaAboveCell0010))) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childHL (childLL (childHL thetaAboveCell0010)))
    e24KC2ThetaAboveLeaf00102020 e24KC2ThetaAboveLeaf00102021 e24KC2ThetaAboveNode00102022
      e24KC2ThetaAboveNode00102023

theorem e24KC2ThetaAboveNode0010203 :
    adaptiveCoverCheck 12 (childHH (childLL (childHL thetaAboveCell0010))) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childHH (childLL (childHL thetaAboveCell0010)))
    e24KC2ThetaAboveLeaf00102030 e24KC2ThetaAboveLeaf00102031 e24KC2ThetaAboveNode00102032
      e24KC2ThetaAboveNode00102033

theorem e24KC2ThetaAboveNode0010212 :
    adaptiveCoverCheck 12 (childHL (childLH (childHL thetaAboveCell0010))) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childHL (childLH (childHL thetaAboveCell0010)))
    e24KC2ThetaAboveLeaf00102120 e24KC2ThetaAboveLeaf00102121 e24KC2ThetaAboveNode00102122
      e24KC2ThetaAboveNode00102123

theorem e24KC2ThetaAboveNode0010213 :
    adaptiveCoverCheck 12 (childHH (childLH (childHL thetaAboveCell0010))) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childHH (childLH (childHL thetaAboveCell0010)))
    e24KC2ThetaAboveLeaf00102130 e24KC2ThetaAboveLeaf00102131 e24KC2ThetaAboveNode00102132
      e24KC2ThetaAboveNode00102133

theorem e24KC2ThetaAboveNode0010220 :
    adaptiveCoverCheck 12 (childLL (childHL (childHL thetaAboveCell0010))) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childLL (childHL (childHL thetaAboveCell0010)))
    e24KC2ThetaAboveNode00102200 e24KC2ThetaAboveNode00102201 e24KC2ThetaAboveNode00102202
      e24KC2ThetaAboveNode00102203

theorem e24KC2ThetaAboveNode0010221 :
    adaptiveCoverCheck 12 (childLH (childHL (childHL thetaAboveCell0010))) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childLH (childHL (childHL thetaAboveCell0010)))
    e24KC2ThetaAboveNode00102210 e24KC2ThetaAboveNode00102211 e24KC2ThetaAboveNode00102212
      e24KC2ThetaAboveNode00102213

theorem e24KC2ThetaAboveNode0010222 :
    adaptiveCoverCheck 12 (childHL (childHL (childHL thetaAboveCell0010))) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childHL (childHL (childHL thetaAboveCell0010)))
    e24KC2ThetaAboveLeaf00102220 e24KC2ThetaAboveLeaf00102221 e24KC2ThetaAboveLeaf00102222
      e24KC2ThetaAboveLeaf00102223

theorem e24KC2ThetaAboveNode0010223 :
    adaptiveCoverCheck 12 (childHH (childHL (childHL thetaAboveCell0010))) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childHH (childHL (childHL thetaAboveCell0010)))
    e24KC2ThetaAboveLeaf00102230 e24KC2ThetaAboveLeaf00102231 e24KC2ThetaAboveLeaf00102232
      e24KC2ThetaAboveLeaf00102233

theorem e24KC2ThetaAboveNode0010230 :
    adaptiveCoverCheck 12 (childLL (childHH (childHL thetaAboveCell0010))) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childLL (childHH (childHL thetaAboveCell0010)))
    e24KC2ThetaAboveNode00102300 e24KC2ThetaAboveNode00102301 e24KC2ThetaAboveNode00102302
      e24KC2ThetaAboveNode00102303

theorem e24KC2ThetaAboveNode0010231 :
    adaptiveCoverCheck 12 (childLH (childHH (childHL thetaAboveCell0010))) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childLH (childHH (childHL thetaAboveCell0010)))
    e24KC2ThetaAboveNode00102310 e24KC2ThetaAboveNode00102311 e24KC2ThetaAboveNode00102312
      e24KC2ThetaAboveNode00102313

theorem e24KC2ThetaAboveNode0010232 :
    adaptiveCoverCheck 12 (childHL (childHH (childHL thetaAboveCell0010))) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childHL (childHH (childHL thetaAboveCell0010)))
    e24KC2ThetaAboveLeaf00102320 e24KC2ThetaAboveLeaf00102321 e24KC2ThetaAboveLeaf00102322
      e24KC2ThetaAboveLeaf00102323

theorem e24KC2ThetaAboveNode0010233 :
    adaptiveCoverCheck 12 (childHH (childHH (childHL thetaAboveCell0010))) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childHH (childHH (childHL thetaAboveCell0010)))
    e24KC2ThetaAboveLeaf00102330 e24KC2ThetaAboveLeaf00102331 e24KC2ThetaAboveLeaf00102332
      e24KC2ThetaAboveLeaf00102333

theorem e24KC2ThetaAboveNode0010302 :
    adaptiveCoverCheck 12 (childHL (childLL (childHH thetaAboveCell0010))) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childHL (childLL (childHH thetaAboveCell0010)))
    e24KC2ThetaAboveLeaf00103020 e24KC2ThetaAboveLeaf00103021 e24KC2ThetaAboveLeaf00103022
      e24KC2ThetaAboveLeaf00103023

theorem e24KC2ThetaAboveNode0010303 :
    adaptiveCoverCheck 12 (childHH (childLL (childHH thetaAboveCell0010))) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childHH (childLL (childHH thetaAboveCell0010)))
    e24KC2ThetaAboveLeaf00103030 e24KC2ThetaAboveLeaf00103031 e24KC2ThetaAboveLeaf00103032
      e24KC2ThetaAboveLeaf00103033

theorem e24KC2ThetaAboveNode0010312 :
    adaptiveCoverCheck 12 (childHL (childLH (childHH thetaAboveCell0010))) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childHL (childLH (childHH thetaAboveCell0010)))
    e24KC2ThetaAboveLeaf00103120 e24KC2ThetaAboveLeaf00103121 e24KC2ThetaAboveLeaf00103122
      e24KC2ThetaAboveLeaf00103123

theorem e24KC2ThetaAboveNode0010313 :
    adaptiveCoverCheck 12 (childHH (childLH (childHH thetaAboveCell0010))) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childHH (childLH (childHH thetaAboveCell0010)))
    e24KC2ThetaAboveLeaf00103130 e24KC2ThetaAboveLeaf00103131 e24KC2ThetaAboveLeaf00103132
      e24KC2ThetaAboveLeaf00103133

theorem e24KC2ThetaAboveNode0010320 :
    adaptiveCoverCheck 12 (childLL (childHL (childHH thetaAboveCell0010))) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childLL (childHL (childHH thetaAboveCell0010)))
    e24KC2ThetaAboveNode00103200 e24KC2ThetaAboveNode00103201 e24KC2ThetaAboveNode00103202
      e24KC2ThetaAboveNode00103203

theorem e24KC2ThetaAboveNode0010321 :
    adaptiveCoverCheck 12 (childLH (childHL (childHH thetaAboveCell0010))) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childLH (childHL (childHH thetaAboveCell0010)))
    e24KC2ThetaAboveNode00103210 e24KC2ThetaAboveNode00103211 e24KC2ThetaAboveNode00103212
      e24KC2ThetaAboveNode00103213

theorem e24KC2ThetaAboveNode0010322 :
    adaptiveCoverCheck 12 (childHL (childHL (childHH thetaAboveCell0010))) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childHL (childHL (childHH thetaAboveCell0010)))
    e24KC2ThetaAboveLeaf00103220 e24KC2ThetaAboveLeaf00103221 e24KC2ThetaAboveLeaf00103222
      e24KC2ThetaAboveLeaf00103223

theorem e24KC2ThetaAboveNode0010323 :
    adaptiveCoverCheck 12 (childHH (childHL (childHH thetaAboveCell0010))) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childHH (childHL (childHH thetaAboveCell0010)))
    e24KC2ThetaAboveLeaf00103230 e24KC2ThetaAboveLeaf00103231 e24KC2ThetaAboveLeaf00103232
      e24KC2ThetaAboveLeaf00103233

theorem e24KC2ThetaAboveNode0010330 :
    adaptiveCoverCheck 12 (childLL (childHH (childHH thetaAboveCell0010))) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childLL (childHH (childHH thetaAboveCell0010)))
    e24KC2ThetaAboveNode00103300 e24KC2ThetaAboveNode00103301 e24KC2ThetaAboveNode00103302
      e24KC2ThetaAboveNode00103303

theorem e24KC2ThetaAboveNode0010331 :
    adaptiveCoverCheck 12 (childLH (childHH (childHH thetaAboveCell0010))) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childLH (childHH (childHH thetaAboveCell0010)))
    e24KC2ThetaAboveNode00103310 e24KC2ThetaAboveNode00103311 e24KC2ThetaAboveNode00103312
      e24KC2ThetaAboveNode00103313

theorem e24KC2ThetaAboveNode0010332 :
    adaptiveCoverCheck 12 (childHL (childHH (childHH thetaAboveCell0010))) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childHL (childHH (childHH thetaAboveCell0010)))
    e24KC2ThetaAboveLeaf00103320 e24KC2ThetaAboveLeaf00103321 e24KC2ThetaAboveLeaf00103322
      e24KC2ThetaAboveLeaf00103323

theorem e24KC2ThetaAboveNode0010333 :
    adaptiveCoverCheck 12 (childHH (childHH (childHH thetaAboveCell0010))) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childHH (childHH (childHH thetaAboveCell0010)))
    e24KC2ThetaAboveLeaf00103330 e24KC2ThetaAboveLeaf00103331 e24KC2ThetaAboveLeaf00103332
      e24KC2ThetaAboveLeaf00103333

theorem e24KC2ThetaAboveNode0011202 :
    adaptiveCoverCheck 12 (childHL (childLL (childHL thetaAboveCell0011))) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childHL (childLL (childHL thetaAboveCell0011)))
    e24KC2ThetaAboveLeaf00112020 e24KC2ThetaAboveLeaf00112021 e24KC2ThetaAboveLeaf00112022
      e24KC2ThetaAboveLeaf00112023

theorem e24KC2ThetaAboveNode0011203 :
    adaptiveCoverCheck 12 (childHH (childLL (childHL thetaAboveCell0011))) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childHH (childLL (childHL thetaAboveCell0011)))
    e24KC2ThetaAboveLeaf00112030 e24KC2ThetaAboveLeaf00112031 e24KC2ThetaAboveLeaf00112032
      e24KC2ThetaAboveLeaf00112033

theorem e24KC2ThetaAboveNode0011212 :
    adaptiveCoverCheck 12 (childHL (childLH (childHL thetaAboveCell0011))) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childHL (childLH (childHL thetaAboveCell0011)))
    e24KC2ThetaAboveLeaf00112120 e24KC2ThetaAboveLeaf00112121 e24KC2ThetaAboveLeaf00112122
      e24KC2ThetaAboveLeaf00112123

theorem e24KC2ThetaAboveNode0011213 :
    adaptiveCoverCheck 12 (childHH (childLH (childHL thetaAboveCell0011))) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childHH (childLH (childHL thetaAboveCell0011)))
    e24KC2ThetaAboveLeaf00112130 e24KC2ThetaAboveLeaf00112131 e24KC2ThetaAboveLeaf00112132
      e24KC2ThetaAboveLeaf00112133

theorem e24KC2ThetaAboveNode0011220 :
    adaptiveCoverCheck 12 (childLL (childHL (childHL thetaAboveCell0011))) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childLL (childHL (childHL thetaAboveCell0011)))
    e24KC2ThetaAboveNode00112200 e24KC2ThetaAboveNode00112201 e24KC2ThetaAboveNode00112202
      e24KC2ThetaAboveNode00112203

theorem e24KC2ThetaAboveNode0011221 :
    adaptiveCoverCheck 12 (childLH (childHL (childHL thetaAboveCell0011))) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childLH (childHL (childHL thetaAboveCell0011)))
    e24KC2ThetaAboveNode00112210 e24KC2ThetaAboveNode00112211 e24KC2ThetaAboveNode00112212
      e24KC2ThetaAboveNode00112213

theorem e24KC2ThetaAboveNode0011222 :
    adaptiveCoverCheck 12 (childHL (childHL (childHL thetaAboveCell0011))) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childHL (childHL (childHL thetaAboveCell0011)))
    e24KC2ThetaAboveLeaf00112220 e24KC2ThetaAboveLeaf00112221 e24KC2ThetaAboveLeaf00112222
      e24KC2ThetaAboveLeaf00112223

theorem e24KC2ThetaAboveNode0011223 :
    adaptiveCoverCheck 12 (childHH (childHL (childHL thetaAboveCell0011))) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childHH (childHL (childHL thetaAboveCell0011)))
    e24KC2ThetaAboveLeaf00112230 e24KC2ThetaAboveLeaf00112231 e24KC2ThetaAboveLeaf00112232
      e24KC2ThetaAboveLeaf00112233

theorem e24KC2ThetaAboveNode0011230 :
    adaptiveCoverCheck 12 (childLL (childHH (childHL thetaAboveCell0011))) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childLL (childHH (childHL thetaAboveCell0011)))
    e24KC2ThetaAboveNode00112300 e24KC2ThetaAboveNode00112301 e24KC2ThetaAboveNode00112302
      e24KC2ThetaAboveNode00112303

theorem e24KC2ThetaAboveNode0011231 :
    adaptiveCoverCheck 12 (childLH (childHH (childHL thetaAboveCell0011))) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childLH (childHH (childHL thetaAboveCell0011)))
    e24KC2ThetaAboveNode00112310 e24KC2ThetaAboveNode00112311 e24KC2ThetaAboveNode00112312
      e24KC2ThetaAboveNode00112313

theorem e24KC2ThetaAboveNode0011232 :
    adaptiveCoverCheck 12 (childHL (childHH (childHL thetaAboveCell0011))) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childHL (childHH (childHL thetaAboveCell0011)))
    e24KC2ThetaAboveLeaf00112320 e24KC2ThetaAboveLeaf00112321 e24KC2ThetaAboveLeaf00112322
      e24KC2ThetaAboveLeaf00112323

theorem e24KC2ThetaAboveNode0011233 :
    adaptiveCoverCheck 12 (childHH (childHH (childHL thetaAboveCell0011))) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childHH (childHH (childHL thetaAboveCell0011)))
    e24KC2ThetaAboveLeaf00112330 e24KC2ThetaAboveLeaf00112331 e24KC2ThetaAboveLeaf00112332
      e24KC2ThetaAboveLeaf00112333

theorem e24KC2ThetaAboveNode0011302 :
    adaptiveCoverCheck 12 (childHL (childLL (childHH thetaAboveCell0011))) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childHL (childLL (childHH thetaAboveCell0011)))
    e24KC2ThetaAboveLeaf00113020 e24KC2ThetaAboveLeaf00113021 e24KC2ThetaAboveLeaf00113022
      e24KC2ThetaAboveLeaf00113023

theorem e24KC2ThetaAboveNode0011303 :
    adaptiveCoverCheck 12 (childHH (childLL (childHH thetaAboveCell0011))) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childHH (childLL (childHH thetaAboveCell0011)))
    e24KC2ThetaAboveLeaf00113030 e24KC2ThetaAboveLeaf00113031 e24KC2ThetaAboveLeaf00113032
      e24KC2ThetaAboveLeaf00113033

theorem e24KC2ThetaAboveNode0011312 :
    adaptiveCoverCheck 12 (childHL (childLH (childHH thetaAboveCell0011))) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childHL (childLH (childHH thetaAboveCell0011)))
    e24KC2ThetaAboveLeaf00113120 e24KC2ThetaAboveLeaf00113121 e24KC2ThetaAboveLeaf00113122
      e24KC2ThetaAboveLeaf00113123

theorem e24KC2ThetaAboveNode0011313 :
    adaptiveCoverCheck 12 (childHH (childLH (childHH thetaAboveCell0011))) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childHH (childLH (childHH thetaAboveCell0011)))
    e24KC2ThetaAboveLeaf00113130 e24KC2ThetaAboveLeaf00113131 e24KC2ThetaAboveLeaf00113132
      e24KC2ThetaAboveLeaf00113133

theorem e24KC2ThetaAboveNode0011320 :
    adaptiveCoverCheck 12 (childLL (childHL (childHH thetaAboveCell0011))) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childLL (childHL (childHH thetaAboveCell0011)))
    e24KC2ThetaAboveNode00113200 e24KC2ThetaAboveNode00113201 e24KC2ThetaAboveNode00113202
      e24KC2ThetaAboveNode00113203

theorem e24KC2ThetaAboveNode0011321 :
    adaptiveCoverCheck 12 (childLH (childHL (childHH thetaAboveCell0011))) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childLH (childHL (childHH thetaAboveCell0011)))
    e24KC2ThetaAboveNode00113210 e24KC2ThetaAboveNode00113211 e24KC2ThetaAboveNode00113212
      e24KC2ThetaAboveNode00113213

theorem e24KC2ThetaAboveNode0011322 :
    adaptiveCoverCheck 12 (childHL (childHL (childHH thetaAboveCell0011))) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childHL (childHL (childHH thetaAboveCell0011)))
    e24KC2ThetaAboveLeaf00113220 e24KC2ThetaAboveLeaf00113221 e24KC2ThetaAboveLeaf00113222
      e24KC2ThetaAboveLeaf00113223

theorem e24KC2ThetaAboveNode0011323 :
    adaptiveCoverCheck 12 (childHH (childHL (childHH thetaAboveCell0011))) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childHH (childHL (childHH thetaAboveCell0011)))
    e24KC2ThetaAboveLeaf00113230 e24KC2ThetaAboveLeaf00113231 e24KC2ThetaAboveLeaf00113232
      e24KC2ThetaAboveLeaf00113233

theorem e24KC2ThetaAboveNode0011330 :
    adaptiveCoverCheck 12 (childLL (childHH (childHH thetaAboveCell0011))) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childLL (childHH (childHH thetaAboveCell0011)))
    e24KC2ThetaAboveNode00113300 e24KC2ThetaAboveNode00113301 e24KC2ThetaAboveNode00113302
      e24KC2ThetaAboveNode00113303

theorem e24KC2ThetaAboveNode0011331 :
    adaptiveCoverCheck 12 (childLH (childHH (childHH thetaAboveCell0011))) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childLH (childHH (childHH thetaAboveCell0011)))
    e24KC2ThetaAboveNode00113310 e24KC2ThetaAboveNode00113311 e24KC2ThetaAboveNode00113312
      e24KC2ThetaAboveNode00113313

theorem e24KC2ThetaAboveNode0011332 :
    adaptiveCoverCheck 12 (childHL (childHH (childHH thetaAboveCell0011))) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childHL (childHH (childHH thetaAboveCell0011)))
    e24KC2ThetaAboveLeaf00113320 e24KC2ThetaAboveLeaf00113321 e24KC2ThetaAboveLeaf00113322
      e24KC2ThetaAboveLeaf00113323

theorem e24KC2ThetaAboveNode0011333 :
    adaptiveCoverCheck 12 (childHH (childHH (childHH thetaAboveCell0011))) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childHH (childHH (childHH thetaAboveCell0011)))
    e24KC2ThetaAboveLeaf00113330 e24KC2ThetaAboveLeaf00113331 e24KC2ThetaAboveLeaf00113332
      e24KC2ThetaAboveLeaf00113333

theorem e24KC2ThetaAboveNode0100202 :
    adaptiveCoverCheck 12 (childHL (childLL (childHL thetaAboveCell0100))) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childHL (childLL (childHL thetaAboveCell0100)))
    e24KC2ThetaAboveLeaf01002020 e24KC2ThetaAboveLeaf01002021 e24KC2ThetaAboveLeaf01002022
      e24KC2ThetaAboveLeaf01002023

theorem e24KC2ThetaAboveNode0100203 :
    adaptiveCoverCheck 12 (childHH (childLL (childHL thetaAboveCell0100))) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childHH (childLL (childHL thetaAboveCell0100)))
    e24KC2ThetaAboveLeaf01002030 e24KC2ThetaAboveLeaf01002031 e24KC2ThetaAboveLeaf01002032
      e24KC2ThetaAboveLeaf01002033

theorem e24KC2ThetaAboveNode0100212 :
    adaptiveCoverCheck 12 (childHL (childLH (childHL thetaAboveCell0100))) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childHL (childLH (childHL thetaAboveCell0100)))
    e24KC2ThetaAboveLeaf01002120 e24KC2ThetaAboveLeaf01002121 e24KC2ThetaAboveLeaf01002122
      e24KC2ThetaAboveLeaf01002123

theorem e24KC2ThetaAboveNode0100213 :
    adaptiveCoverCheck 12 (childHH (childLH (childHL thetaAboveCell0100))) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childHH (childLH (childHL thetaAboveCell0100)))
    e24KC2ThetaAboveLeaf01002130 e24KC2ThetaAboveLeaf01002131 e24KC2ThetaAboveLeaf01002132
      e24KC2ThetaAboveLeaf01002133

theorem e24KC2ThetaAboveNode0100220 :
    adaptiveCoverCheck 12 (childLL (childHL (childHL thetaAboveCell0100))) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childLL (childHL (childHL thetaAboveCell0100)))
    e24KC2ThetaAboveNode01002200 e24KC2ThetaAboveNode01002201 e24KC2ThetaAboveNode01002202
      e24KC2ThetaAboveNode01002203

theorem e24KC2ThetaAboveNode0100221 :
    adaptiveCoverCheck 12 (childLH (childHL (childHL thetaAboveCell0100))) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childLH (childHL (childHL thetaAboveCell0100)))
    e24KC2ThetaAboveNode01002210 e24KC2ThetaAboveNode01002211 e24KC2ThetaAboveNode01002212
      e24KC2ThetaAboveNode01002213

theorem e24KC2ThetaAboveNode0100222 :
    adaptiveCoverCheck 12 (childHL (childHL (childHL thetaAboveCell0100))) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childHL (childHL (childHL thetaAboveCell0100)))
    e24KC2ThetaAboveLeaf01002220 e24KC2ThetaAboveLeaf01002221 e24KC2ThetaAboveLeaf01002222
      e24KC2ThetaAboveLeaf01002223

theorem e24KC2ThetaAboveNode0100223 :
    adaptiveCoverCheck 12 (childHH (childHL (childHL thetaAboveCell0100))) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childHH (childHL (childHL thetaAboveCell0100)))
    e24KC2ThetaAboveLeaf01002230 e24KC2ThetaAboveLeaf01002231 e24KC2ThetaAboveLeaf01002232
      e24KC2ThetaAboveLeaf01002233

theorem e24KC2ThetaAboveNode0100230 :
    adaptiveCoverCheck 12 (childLL (childHH (childHL thetaAboveCell0100))) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childLL (childHH (childHL thetaAboveCell0100)))
    e24KC2ThetaAboveNode01002300 e24KC2ThetaAboveNode01002301 e24KC2ThetaAboveNode01002302
      e24KC2ThetaAboveNode01002303

theorem e24KC2ThetaAboveNode0100231 :
    adaptiveCoverCheck 12 (childLH (childHH (childHL thetaAboveCell0100))) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childLH (childHH (childHL thetaAboveCell0100)))
    e24KC2ThetaAboveNode01002310 e24KC2ThetaAboveNode01002311 e24KC2ThetaAboveNode01002312
      e24KC2ThetaAboveNode01002313

theorem e24KC2ThetaAboveNode0100232 :
    adaptiveCoverCheck 12 (childHL (childHH (childHL thetaAboveCell0100))) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childHL (childHH (childHL thetaAboveCell0100)))
    e24KC2ThetaAboveLeaf01002320 e24KC2ThetaAboveLeaf01002321 e24KC2ThetaAboveLeaf01002322
      e24KC2ThetaAboveLeaf01002323

theorem e24KC2ThetaAboveNode0100233 :
    adaptiveCoverCheck 12 (childHH (childHH (childHL thetaAboveCell0100))) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childHH (childHH (childHL thetaAboveCell0100)))
    e24KC2ThetaAboveLeaf01002330 e24KC2ThetaAboveLeaf01002331 e24KC2ThetaAboveLeaf01002332
      e24KC2ThetaAboveLeaf01002333

theorem e24KC2ThetaAboveNode0100302 :
    adaptiveCoverCheck 12 (childHL (childLL (childHH thetaAboveCell0100))) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childHL (childLL (childHH thetaAboveCell0100)))
    e24KC2ThetaAboveLeaf01003020 e24KC2ThetaAboveLeaf01003021 e24KC2ThetaAboveLeaf01003022
      e24KC2ThetaAboveLeaf01003023

theorem e24KC2ThetaAboveNode0100303 :
    adaptiveCoverCheck 12 (childHH (childLL (childHH thetaAboveCell0100))) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childHH (childLL (childHH thetaAboveCell0100)))
    e24KC2ThetaAboveLeaf01003030 e24KC2ThetaAboveLeaf01003031 e24KC2ThetaAboveLeaf01003032
      e24KC2ThetaAboveLeaf01003033

theorem e24KC2ThetaAboveNode0100312 :
    adaptiveCoverCheck 12 (childHL (childLH (childHH thetaAboveCell0100))) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childHL (childLH (childHH thetaAboveCell0100)))
    e24KC2ThetaAboveLeaf01003120 e24KC2ThetaAboveLeaf01003121 e24KC2ThetaAboveLeaf01003122
      e24KC2ThetaAboveLeaf01003123

theorem e24KC2ThetaAboveNode0100313 :
    adaptiveCoverCheck 12 (childHH (childLH (childHH thetaAboveCell0100))) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childHH (childLH (childHH thetaAboveCell0100)))
    e24KC2ThetaAboveLeaf01003130 e24KC2ThetaAboveLeaf01003131 e24KC2ThetaAboveLeaf01003132
      e24KC2ThetaAboveLeaf01003133

theorem e24KC2ThetaAboveNode0100320 :
    adaptiveCoverCheck 12 (childLL (childHL (childHH thetaAboveCell0100))) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childLL (childHL (childHH thetaAboveCell0100)))
    e24KC2ThetaAboveNode01003200 e24KC2ThetaAboveNode01003201 e24KC2ThetaAboveNode01003202
      e24KC2ThetaAboveNode01003203

theorem e24KC2ThetaAboveNode0100321 :
    adaptiveCoverCheck 12 (childLH (childHL (childHH thetaAboveCell0100))) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childLH (childHL (childHH thetaAboveCell0100)))
    e24KC2ThetaAboveNode01003210 e24KC2ThetaAboveNode01003211 e24KC2ThetaAboveNode01003212
      e24KC2ThetaAboveNode01003213

theorem e24KC2ThetaAboveNode0100322 :
    adaptiveCoverCheck 12 (childHL (childHL (childHH thetaAboveCell0100))) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childHL (childHL (childHH thetaAboveCell0100)))
    e24KC2ThetaAboveLeaf01003220 e24KC2ThetaAboveLeaf01003221 e24KC2ThetaAboveLeaf01003222
      e24KC2ThetaAboveLeaf01003223

theorem e24KC2ThetaAboveNode0100323 :
    adaptiveCoverCheck 12 (childHH (childHL (childHH thetaAboveCell0100))) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childHH (childHL (childHH thetaAboveCell0100)))
    e24KC2ThetaAboveLeaf01003230 e24KC2ThetaAboveLeaf01003231 e24KC2ThetaAboveLeaf01003232
      e24KC2ThetaAboveLeaf01003233

theorem e24KC2ThetaAboveNode0100330 :
    adaptiveCoverCheck 12 (childLL (childHH (childHH thetaAboveCell0100))) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childLL (childHH (childHH thetaAboveCell0100)))
    e24KC2ThetaAboveNode01003300 e24KC2ThetaAboveNode01003301 e24KC2ThetaAboveNode01003302
      e24KC2ThetaAboveNode01003303

theorem e24KC2ThetaAboveNode0100331 :
    adaptiveCoverCheck 12 (childLH (childHH (childHH thetaAboveCell0100))) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childLH (childHH (childHH thetaAboveCell0100)))
    e24KC2ThetaAboveNode01003310 e24KC2ThetaAboveNode01003311 e24KC2ThetaAboveNode01003312
      e24KC2ThetaAboveNode01003313

theorem e24KC2ThetaAboveNode0100332 :
    adaptiveCoverCheck 12 (childHL (childHH (childHH thetaAboveCell0100))) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childHL (childHH (childHH thetaAboveCell0100)))
    e24KC2ThetaAboveLeaf01003320 e24KC2ThetaAboveLeaf01003321 e24KC2ThetaAboveLeaf01003322
      e24KC2ThetaAboveLeaf01003323

theorem e24KC2ThetaAboveNode0100333 :
    adaptiveCoverCheck 12 (childHH (childHH (childHH thetaAboveCell0100))) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childHH (childHH (childHH thetaAboveCell0100)))
    e24KC2ThetaAboveNode01003330 e24KC2ThetaAboveNode01003331 e24KC2ThetaAboveLeaf01003332
      e24KC2ThetaAboveLeaf01003333

theorem e24KC2ThetaAboveNode0101202 :
    adaptiveCoverCheck 12 (childHL (childLL (childHL thetaAboveCell0101))) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childHL (childLL (childHL thetaAboveCell0101)))
    e24KC2ThetaAboveLeaf01012020 e24KC2ThetaAboveLeaf01012021 e24KC2ThetaAboveLeaf01012022
      e24KC2ThetaAboveLeaf01012023

theorem e24KC2ThetaAboveNode0101203 :
    adaptiveCoverCheck 12 (childHH (childLL (childHL thetaAboveCell0101))) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childHH (childLL (childHL thetaAboveCell0101)))
    e24KC2ThetaAboveLeaf01012030 e24KC2ThetaAboveLeaf01012031 e24KC2ThetaAboveLeaf01012032
      e24KC2ThetaAboveLeaf01012033

theorem e24KC2ThetaAboveNode0101212 :
    adaptiveCoverCheck 12 (childHL (childLH (childHL thetaAboveCell0101))) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childHL (childLH (childHL thetaAboveCell0101)))
    e24KC2ThetaAboveLeaf01012120 e24KC2ThetaAboveLeaf01012121 e24KC2ThetaAboveLeaf01012122
      e24KC2ThetaAboveLeaf01012123

theorem e24KC2ThetaAboveNode0101213 :
    adaptiveCoverCheck 12 (childHH (childLH (childHL thetaAboveCell0101))) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childHH (childLH (childHL thetaAboveCell0101)))
    e24KC2ThetaAboveLeaf01012130 e24KC2ThetaAboveLeaf01012131 e24KC2ThetaAboveLeaf01012132
      e24KC2ThetaAboveLeaf01012133

theorem e24KC2ThetaAboveNode0101220 :
    adaptiveCoverCheck 12 (childLL (childHL (childHL thetaAboveCell0101))) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childLL (childHL (childHL thetaAboveCell0101)))
    e24KC2ThetaAboveNode01012200 e24KC2ThetaAboveNode01012201 e24KC2ThetaAboveNode01012202
      e24KC2ThetaAboveNode01012203

theorem e24KC2ThetaAboveNode0101221 :
    adaptiveCoverCheck 12 (childLH (childHL (childHL thetaAboveCell0101))) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childLH (childHL (childHL thetaAboveCell0101)))
    e24KC2ThetaAboveNode01012210 e24KC2ThetaAboveNode01012211 e24KC2ThetaAboveNode01012212
      e24KC2ThetaAboveNode01012213

theorem e24KC2ThetaAboveNode0101222 :
    adaptiveCoverCheck 12 (childHL (childHL (childHL thetaAboveCell0101))) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childHL (childHL (childHL thetaAboveCell0101)))
    e24KC2ThetaAboveNode01012220 e24KC2ThetaAboveNode01012221 e24KC2ThetaAboveLeaf01012222
      e24KC2ThetaAboveLeaf01012223

theorem e24KC2ThetaAboveNode0101223 :
    adaptiveCoverCheck 12 (childHH (childHL (childHL thetaAboveCell0101))) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childHH (childHL (childHL thetaAboveCell0101)))
    e24KC2ThetaAboveNode01012230 e24KC2ThetaAboveNode01012231 e24KC2ThetaAboveLeaf01012232
      e24KC2ThetaAboveLeaf01012233

theorem e24KC2ThetaAboveNode0101230 :
    adaptiveCoverCheck 12 (childLL (childHH (childHL thetaAboveCell0101))) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childLL (childHH (childHL thetaAboveCell0101)))
    e24KC2ThetaAboveNode01012300 e24KC2ThetaAboveNode01012301 e24KC2ThetaAboveNode01012302
      e24KC2ThetaAboveNode01012303

theorem e24KC2ThetaAboveNode0101231 :
    adaptiveCoverCheck 12 (childLH (childHH (childHL thetaAboveCell0101))) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childLH (childHH (childHL thetaAboveCell0101)))
    e24KC2ThetaAboveNode01012310 e24KC2ThetaAboveNode01012311 e24KC2ThetaAboveNode01012312
      e24KC2ThetaAboveNode01012313

theorem e24KC2ThetaAboveNode0101232 :
    adaptiveCoverCheck 12 (childHL (childHH (childHL thetaAboveCell0101))) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childHL (childHH (childHL thetaAboveCell0101)))
    e24KC2ThetaAboveNode01012320 e24KC2ThetaAboveNode01012321 e24KC2ThetaAboveLeaf01012322
      e24KC2ThetaAboveLeaf01012323

theorem e24KC2ThetaAboveNode0101233 :
    adaptiveCoverCheck 12 (childHH (childHH (childHL thetaAboveCell0101))) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childHH (childHH (childHL thetaAboveCell0101)))
    e24KC2ThetaAboveNode01012330 e24KC2ThetaAboveNode01012331 e24KC2ThetaAboveLeaf01012332
      e24KC2ThetaAboveLeaf01012333

theorem e24KC2ThetaAboveNode0101302 :
    adaptiveCoverCheck 12 (childHL (childLL (childHH thetaAboveCell0101))) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childHL (childLL (childHH thetaAboveCell0101)))
    e24KC2ThetaAboveLeaf01013020 e24KC2ThetaAboveLeaf01013021 e24KC2ThetaAboveLeaf01013022
      e24KC2ThetaAboveLeaf01013023

theorem e24KC2ThetaAboveNode0101303 :
    adaptiveCoverCheck 12 (childHH (childLL (childHH thetaAboveCell0101))) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childHH (childLL (childHH thetaAboveCell0101)))
    e24KC2ThetaAboveLeaf01013030 e24KC2ThetaAboveLeaf01013031 e24KC2ThetaAboveLeaf01013032
      e24KC2ThetaAboveLeaf01013033

theorem e24KC2ThetaAboveNode0101312 :
    adaptiveCoverCheck 12 (childHL (childLH (childHH thetaAboveCell0101))) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childHL (childLH (childHH thetaAboveCell0101)))
    e24KC2ThetaAboveLeaf01013120 e24KC2ThetaAboveLeaf01013121 e24KC2ThetaAboveLeaf01013122
      e24KC2ThetaAboveLeaf01013123

theorem e24KC2ThetaAboveNode0101313 :
    adaptiveCoverCheck 12 (childHH (childLH (childHH thetaAboveCell0101))) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childHH (childLH (childHH thetaAboveCell0101)))
    e24KC2ThetaAboveLeaf01013130 e24KC2ThetaAboveLeaf01013131 e24KC2ThetaAboveLeaf01013132
      e24KC2ThetaAboveLeaf01013133

theorem e24KC2ThetaAboveNode0101320 :
    adaptiveCoverCheck 12 (childLL (childHL (childHH thetaAboveCell0101))) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childLL (childHL (childHH thetaAboveCell0101)))
    e24KC2ThetaAboveNode01013200 e24KC2ThetaAboveNode01013201 e24KC2ThetaAboveNode01013202
      e24KC2ThetaAboveNode01013203

theorem e24KC2ThetaAboveNode0101321 :
    adaptiveCoverCheck 12 (childLH (childHL (childHH thetaAboveCell0101))) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childLH (childHL (childHH thetaAboveCell0101)))
    e24KC2ThetaAboveNode01013210 e24KC2ThetaAboveNode01013211 e24KC2ThetaAboveNode01013212
      e24KC2ThetaAboveNode01013213

theorem e24KC2ThetaAboveNode0101322 :
    adaptiveCoverCheck 12 (childHL (childHL (childHH thetaAboveCell0101))) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childHL (childHL (childHH thetaAboveCell0101)))
    e24KC2ThetaAboveNode01013220 e24KC2ThetaAboveNode01013221 e24KC2ThetaAboveLeaf01013222
      e24KC2ThetaAboveLeaf01013223

theorem e24KC2ThetaAboveNode0101323 :
    adaptiveCoverCheck 12 (childHH (childHL (childHH thetaAboveCell0101))) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childHH (childHL (childHH thetaAboveCell0101)))
    e24KC2ThetaAboveNode01013230 e24KC2ThetaAboveNode01013231 e24KC2ThetaAboveLeaf01013232
      e24KC2ThetaAboveLeaf01013233

theorem e24KC2ThetaAboveNode0101330 :
    adaptiveCoverCheck 12 (childLL (childHH (childHH thetaAboveCell0101))) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childLL (childHH (childHH thetaAboveCell0101)))
    e24KC2ThetaAboveNode01013300 e24KC2ThetaAboveNode01013301 e24KC2ThetaAboveNode01013302
      e24KC2ThetaAboveNode01013303

theorem e24KC2ThetaAboveNode0101331 :
    adaptiveCoverCheck 12 (childLH (childHH (childHH thetaAboveCell0101))) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childLH (childHH (childHH thetaAboveCell0101)))
    e24KC2ThetaAboveNode01013310 e24KC2ThetaAboveNode01013311 e24KC2ThetaAboveNode01013312
      e24KC2ThetaAboveNode01013313

theorem e24KC2ThetaAboveNode0101332 :
    adaptiveCoverCheck 12 (childHL (childHH (childHH thetaAboveCell0101))) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childHL (childHH (childHH thetaAboveCell0101)))
    e24KC2ThetaAboveNode01013320 e24KC2ThetaAboveNode01013321 e24KC2ThetaAboveLeaf01013322
      e24KC2ThetaAboveLeaf01013323

theorem e24KC2ThetaAboveNode0101333 :
    adaptiveCoverCheck 12 (childHH (childHH (childHH thetaAboveCell0101))) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childHH (childHH (childHH thetaAboveCell0101)))
    e24KC2ThetaAboveNode01013330 e24KC2ThetaAboveNode01013331 e24KC2ThetaAboveLeaf01013332
      e24KC2ThetaAboveLeaf01013333

theorem e24KC2ThetaAboveNode0110202 :
    adaptiveCoverCheck 12 (childHL (childLL (childHL thetaAboveCell0110))) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childHL (childLL (childHL thetaAboveCell0110)))
    e24KC2ThetaAboveLeaf01102020 e24KC2ThetaAboveLeaf01102021 e24KC2ThetaAboveLeaf01102022
      e24KC2ThetaAboveLeaf01102023

theorem e24KC2ThetaAboveNode0110203 :
    adaptiveCoverCheck 12 (childHH (childLL (childHL thetaAboveCell0110))) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childHH (childLL (childHL thetaAboveCell0110)))
    e24KC2ThetaAboveLeaf01102030 e24KC2ThetaAboveLeaf01102031 e24KC2ThetaAboveLeaf01102032
      e24KC2ThetaAboveLeaf01102033

theorem e24KC2ThetaAboveNode0110212 :
    adaptiveCoverCheck 12 (childHL (childLH (childHL thetaAboveCell0110))) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childHL (childLH (childHL thetaAboveCell0110)))
    e24KC2ThetaAboveLeaf01102120 e24KC2ThetaAboveLeaf01102121 e24KC2ThetaAboveLeaf01102122
      e24KC2ThetaAboveLeaf01102123

theorem e24KC2ThetaAboveNode0110213 :
    adaptiveCoverCheck 12 (childHH (childLH (childHL thetaAboveCell0110))) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childHH (childLH (childHL thetaAboveCell0110)))
    e24KC2ThetaAboveLeaf01102130 e24KC2ThetaAboveLeaf01102131 e24KC2ThetaAboveLeaf01102132
      e24KC2ThetaAboveLeaf01102133

theorem e24KC2ThetaAboveNode0110220 :
    adaptiveCoverCheck 12 (childLL (childHL (childHL thetaAboveCell0110))) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childLL (childHL (childHL thetaAboveCell0110)))
    e24KC2ThetaAboveNode01102200 e24KC2ThetaAboveNode01102201 e24KC2ThetaAboveNode01102202
      e24KC2ThetaAboveNode01102203

theorem e24KC2ThetaAboveNode0110221 :
    adaptiveCoverCheck 12 (childLH (childHL (childHL thetaAboveCell0110))) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childLH (childHL (childHL thetaAboveCell0110)))
    e24KC2ThetaAboveNode01102210 e24KC2ThetaAboveNode01102211 e24KC2ThetaAboveNode01102212
      e24KC2ThetaAboveNode01102213

theorem e24KC2ThetaAboveNode0110222 :
    adaptiveCoverCheck 12 (childHL (childHL (childHL thetaAboveCell0110))) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childHL (childHL (childHL thetaAboveCell0110)))
    e24KC2ThetaAboveNode01102220 e24KC2ThetaAboveNode01102221 e24KC2ThetaAboveLeaf01102222
      e24KC2ThetaAboveLeaf01102223

theorem e24KC2ThetaAboveNode0110223 :
    adaptiveCoverCheck 12 (childHH (childHL (childHL thetaAboveCell0110))) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childHH (childHL (childHL thetaAboveCell0110)))
    e24KC2ThetaAboveNode01102230 e24KC2ThetaAboveNode01102231 e24KC2ThetaAboveLeaf01102232
      e24KC2ThetaAboveLeaf01102233

theorem e24KC2ThetaAboveNode0110230 :
    adaptiveCoverCheck 12 (childLL (childHH (childHL thetaAboveCell0110))) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childLL (childHH (childHL thetaAboveCell0110)))
    e24KC2ThetaAboveNode01102300 e24KC2ThetaAboveNode01102301 e24KC2ThetaAboveNode01102302
      e24KC2ThetaAboveNode01102303

theorem e24KC2ThetaAboveNode0110231 :
    adaptiveCoverCheck 12 (childLH (childHH (childHL thetaAboveCell0110))) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childLH (childHH (childHL thetaAboveCell0110)))
    e24KC2ThetaAboveNode01102310 e24KC2ThetaAboveNode01102311 e24KC2ThetaAboveNode01102312
      e24KC2ThetaAboveNode01102313

theorem e24KC2ThetaAboveNode0110232 :
    adaptiveCoverCheck 12 (childHL (childHH (childHL thetaAboveCell0110))) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childHL (childHH (childHL thetaAboveCell0110)))
    e24KC2ThetaAboveNode01102320 e24KC2ThetaAboveNode01102321 e24KC2ThetaAboveLeaf01102322
      e24KC2ThetaAboveLeaf01102323

theorem e24KC2ThetaAboveNode0110233 :
    adaptiveCoverCheck 12 (childHH (childHH (childHL thetaAboveCell0110))) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childHH (childHH (childHL thetaAboveCell0110)))
    e24KC2ThetaAboveNode01102330 e24KC2ThetaAboveNode01102331 e24KC2ThetaAboveLeaf01102332
      e24KC2ThetaAboveLeaf01102333

theorem e24KC2ThetaAboveNode0110302 :
    adaptiveCoverCheck 12 (childHL (childLL (childHH thetaAboveCell0110))) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childHL (childLL (childHH thetaAboveCell0110)))
    e24KC2ThetaAboveLeaf01103020 e24KC2ThetaAboveLeaf01103021 e24KC2ThetaAboveLeaf01103022
      e24KC2ThetaAboveLeaf01103023

theorem e24KC2ThetaAboveNode0110303 :
    adaptiveCoverCheck 12 (childHH (childLL (childHH thetaAboveCell0110))) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childHH (childLL (childHH thetaAboveCell0110)))
    e24KC2ThetaAboveLeaf01103030 e24KC2ThetaAboveLeaf01103031 e24KC2ThetaAboveLeaf01103032
      e24KC2ThetaAboveLeaf01103033

theorem e24KC2ThetaAboveNode0110312 :
    adaptiveCoverCheck 12 (childHL (childLH (childHH thetaAboveCell0110))) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childHL (childLH (childHH thetaAboveCell0110)))
    e24KC2ThetaAboveLeaf01103120 e24KC2ThetaAboveLeaf01103121 e24KC2ThetaAboveLeaf01103122
      e24KC2ThetaAboveLeaf01103123

theorem e24KC2ThetaAboveNode0110313 :
    adaptiveCoverCheck 12 (childHH (childLH (childHH thetaAboveCell0110))) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childHH (childLH (childHH thetaAboveCell0110)))
    e24KC2ThetaAboveLeaf01103130 e24KC2ThetaAboveLeaf01103131 e24KC2ThetaAboveLeaf01103132
      e24KC2ThetaAboveLeaf01103133

theorem e24KC2ThetaAboveNode0110320 :
    adaptiveCoverCheck 12 (childLL (childHL (childHH thetaAboveCell0110))) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childLL (childHL (childHH thetaAboveCell0110)))
    e24KC2ThetaAboveNode01103200 e24KC2ThetaAboveNode01103201 e24KC2ThetaAboveNode01103202
      e24KC2ThetaAboveNode01103203

theorem e24KC2ThetaAboveNode0110321 :
    adaptiveCoverCheck 12 (childLH (childHL (childHH thetaAboveCell0110))) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childLH (childHL (childHH thetaAboveCell0110)))
    e24KC2ThetaAboveNode01103210 e24KC2ThetaAboveNode01103211 e24KC2ThetaAboveNode01103212
      e24KC2ThetaAboveNode01103213

theorem e24KC2ThetaAboveNode0110322 :
    adaptiveCoverCheck 12 (childHL (childHL (childHH thetaAboveCell0110))) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childHL (childHL (childHH thetaAboveCell0110)))
    e24KC2ThetaAboveNode01103220 e24KC2ThetaAboveNode01103221 e24KC2ThetaAboveLeaf01103222
      e24KC2ThetaAboveLeaf01103223

theorem e24KC2ThetaAboveNode0110323 :
    adaptiveCoverCheck 12 (childHH (childHL (childHH thetaAboveCell0110))) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childHH (childHL (childHH thetaAboveCell0110)))
    e24KC2ThetaAboveNode01103230 e24KC2ThetaAboveNode01103231 e24KC2ThetaAboveLeaf01103232
      e24KC2ThetaAboveLeaf01103233

theorem e24KC2ThetaAboveNode0110330 :
    adaptiveCoverCheck 12 (childLL (childHH (childHH thetaAboveCell0110))) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childLL (childHH (childHH thetaAboveCell0110)))
    e24KC2ThetaAboveNode01103300 e24KC2ThetaAboveNode01103301 e24KC2ThetaAboveNode01103302
      e24KC2ThetaAboveNode01103303

theorem e24KC2ThetaAboveNode0110331 :
    adaptiveCoverCheck 12 (childLH (childHH (childHH thetaAboveCell0110))) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childLH (childHH (childHH thetaAboveCell0110)))
    e24KC2ThetaAboveNode01103310 e24KC2ThetaAboveNode01103311 e24KC2ThetaAboveNode01103312
      e24KC2ThetaAboveNode01103313

theorem e24KC2ThetaAboveNode0110332 :
    adaptiveCoverCheck 12 (childHL (childHH (childHH thetaAboveCell0110))) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childHL (childHH (childHH thetaAboveCell0110)))
    e24KC2ThetaAboveNode01103320 e24KC2ThetaAboveNode01103321 e24KC2ThetaAboveLeaf01103322
      e24KC2ThetaAboveLeaf01103323

theorem e24KC2ThetaAboveNode0110333 :
    adaptiveCoverCheck 12 (childHH (childHH (childHH thetaAboveCell0110))) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childHH (childHH (childHH thetaAboveCell0110)))
    e24KC2ThetaAboveNode01103330 e24KC2ThetaAboveNode01103331 e24KC2ThetaAboveLeaf01103332
      e24KC2ThetaAboveLeaf01103333

theorem e24KC2ThetaAboveNode0111202 :
    adaptiveCoverCheck 12 (childHL (childLL (childHL thetaAboveCell0111))) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childHL (childLL (childHL thetaAboveCell0111)))
    e24KC2ThetaAboveLeaf01112020 e24KC2ThetaAboveLeaf01112021 e24KC2ThetaAboveLeaf01112022
      e24KC2ThetaAboveLeaf01112023

theorem e24KC2ThetaAboveNode0111203 :
    adaptiveCoverCheck 12 (childHH (childLL (childHL thetaAboveCell0111))) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childHH (childLL (childHL thetaAboveCell0111)))
    e24KC2ThetaAboveLeaf01112030 e24KC2ThetaAboveLeaf01112031 e24KC2ThetaAboveLeaf01112032
      e24KC2ThetaAboveLeaf01112033

theorem e24KC2ThetaAboveNode0111212 :
    adaptiveCoverCheck 12 (childHL (childLH (childHL thetaAboveCell0111))) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childHL (childLH (childHL thetaAboveCell0111)))
    e24KC2ThetaAboveLeaf01112120 e24KC2ThetaAboveLeaf01112121 e24KC2ThetaAboveLeaf01112122
      e24KC2ThetaAboveLeaf01112123

theorem e24KC2ThetaAboveNode0111213 :
    adaptiveCoverCheck 12 (childHH (childLH (childHL thetaAboveCell0111))) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childHH (childLH (childHL thetaAboveCell0111)))
    e24KC2ThetaAboveLeaf01112130 e24KC2ThetaAboveLeaf01112131 e24KC2ThetaAboveLeaf01112132
      e24KC2ThetaAboveLeaf01112133

theorem e24KC2ThetaAboveNode0111220 :
    adaptiveCoverCheck 12 (childLL (childHL (childHL thetaAboveCell0111))) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childLL (childHL (childHL thetaAboveCell0111)))
    e24KC2ThetaAboveNode01112200 e24KC2ThetaAboveNode01112201 e24KC2ThetaAboveNode01112202
      e24KC2ThetaAboveNode01112203

theorem e24KC2ThetaAboveNode0111221 :
    adaptiveCoverCheck 12 (childLH (childHL (childHL thetaAboveCell0111))) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childLH (childHL (childHL thetaAboveCell0111)))
    e24KC2ThetaAboveNode01112210 e24KC2ThetaAboveNode01112211 e24KC2ThetaAboveNode01112212
      e24KC2ThetaAboveNode01112213

theorem e24KC2ThetaAboveNode0111222 :
    adaptiveCoverCheck 12 (childHL (childHL (childHL thetaAboveCell0111))) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childHL (childHL (childHL thetaAboveCell0111)))
    e24KC2ThetaAboveNode01112220 e24KC2ThetaAboveNode01112221 e24KC2ThetaAboveLeaf01112222
      e24KC2ThetaAboveLeaf01112223

theorem e24KC2ThetaAboveNode0111223 :
    adaptiveCoverCheck 12 (childHH (childHL (childHL thetaAboveCell0111))) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childHH (childHL (childHL thetaAboveCell0111)))
    e24KC2ThetaAboveNode01112230 e24KC2ThetaAboveNode01112231 e24KC2ThetaAboveLeaf01112232
      e24KC2ThetaAboveLeaf01112233

theorem e24KC2ThetaAboveNode0111230 :
    adaptiveCoverCheck 12 (childLL (childHH (childHL thetaAboveCell0111))) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childLL (childHH (childHL thetaAboveCell0111)))
    e24KC2ThetaAboveNode01112300 e24KC2ThetaAboveNode01112301 e24KC2ThetaAboveNode01112302
      e24KC2ThetaAboveNode01112303

theorem e24KC2ThetaAboveNode0111231 :
    adaptiveCoverCheck 12 (childLH (childHH (childHL thetaAboveCell0111))) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childLH (childHH (childHL thetaAboveCell0111)))
    e24KC2ThetaAboveNode01112310 e24KC2ThetaAboveNode01112311 e24KC2ThetaAboveNode01112312
      e24KC2ThetaAboveNode01112313

theorem e24KC2ThetaAboveNode0111232 :
    adaptiveCoverCheck 12 (childHL (childHH (childHL thetaAboveCell0111))) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childHL (childHH (childHL thetaAboveCell0111)))
    e24KC2ThetaAboveNode01112320 e24KC2ThetaAboveNode01112321 e24KC2ThetaAboveLeaf01112322
      e24KC2ThetaAboveLeaf01112323

theorem e24KC2ThetaAboveNode0111233 :
    adaptiveCoverCheck 12 (childHH (childHH (childHL thetaAboveCell0111))) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childHH (childHH (childHL thetaAboveCell0111)))
    e24KC2ThetaAboveNode01112330 e24KC2ThetaAboveNode01112331 e24KC2ThetaAboveLeaf01112332
      e24KC2ThetaAboveLeaf01112333

theorem e24KC2ThetaAboveNode0111302 :
    adaptiveCoverCheck 12 (childHL (childLL (childHH thetaAboveCell0111))) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childHL (childLL (childHH thetaAboveCell0111)))
    e24KC2ThetaAboveLeaf01113020 e24KC2ThetaAboveLeaf01113021 e24KC2ThetaAboveLeaf01113022
      e24KC2ThetaAboveLeaf01113023

theorem e24KC2ThetaAboveNode0111303 :
    adaptiveCoverCheck 12 (childHH (childLL (childHH thetaAboveCell0111))) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childHH (childLL (childHH thetaAboveCell0111)))
    e24KC2ThetaAboveLeaf01113030 e24KC2ThetaAboveLeaf01113031 e24KC2ThetaAboveLeaf01113032
      e24KC2ThetaAboveLeaf01113033

theorem e24KC2ThetaAboveNode0111312 :
    adaptiveCoverCheck 12 (childHL (childLH (childHH thetaAboveCell0111))) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childHL (childLH (childHH thetaAboveCell0111)))
    e24KC2ThetaAboveLeaf01113120 e24KC2ThetaAboveLeaf01113121 e24KC2ThetaAboveLeaf01113122
      e24KC2ThetaAboveLeaf01113123

theorem e24KC2ThetaAboveNode0111313 :
    adaptiveCoverCheck 12 (childHH (childLH (childHH thetaAboveCell0111))) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childHH (childLH (childHH thetaAboveCell0111)))
    e24KC2ThetaAboveLeaf01113130 e24KC2ThetaAboveLeaf01113131 e24KC2ThetaAboveLeaf01113132
      e24KC2ThetaAboveLeaf01113133

theorem e24KC2ThetaAboveNode0111320 :
    adaptiveCoverCheck 12 (childLL (childHL (childHH thetaAboveCell0111))) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childLL (childHL (childHH thetaAboveCell0111)))
    e24KC2ThetaAboveNode01113200 e24KC2ThetaAboveNode01113201 e24KC2ThetaAboveNode01113202
      e24KC2ThetaAboveNode01113203

theorem e24KC2ThetaAboveNode0111321 :
    adaptiveCoverCheck 12 (childLH (childHL (childHH thetaAboveCell0111))) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childLH (childHL (childHH thetaAboveCell0111)))
    e24KC2ThetaAboveNode01113210 e24KC2ThetaAboveNode01113211 e24KC2ThetaAboveNode01113212
      e24KC2ThetaAboveNode01113213

theorem e24KC2ThetaAboveNode0111322 :
    adaptiveCoverCheck 12 (childHL (childHL (childHH thetaAboveCell0111))) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childHL (childHL (childHH thetaAboveCell0111)))
    e24KC2ThetaAboveNode01113220 e24KC2ThetaAboveNode01113221 e24KC2ThetaAboveLeaf01113222
      e24KC2ThetaAboveLeaf01113223

theorem e24KC2ThetaAboveNode0111323 :
    adaptiveCoverCheck 12 (childHH (childHL (childHH thetaAboveCell0111))) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childHH (childHL (childHH thetaAboveCell0111)))
    e24KC2ThetaAboveNode01113230 e24KC2ThetaAboveNode01113231 e24KC2ThetaAboveLeaf01113232
      e24KC2ThetaAboveLeaf01113233

theorem e24KC2ThetaAboveNode0111330 :
    adaptiveCoverCheck 12 (childLL (childHH (childHH thetaAboveCell0111))) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childLL (childHH (childHH thetaAboveCell0111)))
    e24KC2ThetaAboveNode01113300 e24KC2ThetaAboveNode01113301 e24KC2ThetaAboveNode01113302
      e24KC2ThetaAboveNode01113303

theorem e24KC2ThetaAboveNode0111331 :
    adaptiveCoverCheck 12 (childLH (childHH (childHH thetaAboveCell0111))) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childLH (childHH (childHH thetaAboveCell0111)))
    e24KC2ThetaAboveNode01113310 e24KC2ThetaAboveNode01113311 e24KC2ThetaAboveNode01113312
      e24KC2ThetaAboveNode01113313

theorem e24KC2ThetaAboveNode0111332 :
    adaptiveCoverCheck 12 (childHL (childHH (childHH thetaAboveCell0111))) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childHL (childHH (childHH thetaAboveCell0111)))
    e24KC2ThetaAboveNode01113320 e24KC2ThetaAboveNode01113321 e24KC2ThetaAboveLeaf01113322
      e24KC2ThetaAboveLeaf01113323

theorem e24KC2ThetaAboveNode0111333 :
    adaptiveCoverCheck 12 (childHH (childHH (childHH thetaAboveCell0111))) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childHH (childHH (childHH thetaAboveCell0111)))
    e24KC2ThetaAboveNode01113330 e24KC2ThetaAboveNode01113331 e24KC2ThetaAboveLeaf01113332
      e24KC2ThetaAboveLeaf01113333

theorem e24KC2ThetaAboveNode1000202 :
    adaptiveCoverCheck 12 (childHL (childLL (childHL thetaAboveCell1000))) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childHL (childLL (childHL thetaAboveCell1000)))
    e24KC2ThetaAboveLeaf10002020 e24KC2ThetaAboveLeaf10002021 e24KC2ThetaAboveLeaf10002022
      e24KC2ThetaAboveLeaf10002023

theorem e24KC2ThetaAboveNode1000203 :
    adaptiveCoverCheck 12 (childHH (childLL (childHL thetaAboveCell1000))) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childHH (childLL (childHL thetaAboveCell1000)))
    e24KC2ThetaAboveLeaf10002030 e24KC2ThetaAboveLeaf10002031 e24KC2ThetaAboveLeaf10002032
      e24KC2ThetaAboveLeaf10002033

theorem e24KC2ThetaAboveNode1000212 :
    adaptiveCoverCheck 12 (childHL (childLH (childHL thetaAboveCell1000))) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childHL (childLH (childHL thetaAboveCell1000)))
    e24KC2ThetaAboveLeaf10002120 e24KC2ThetaAboveLeaf10002121 e24KC2ThetaAboveLeaf10002122
      e24KC2ThetaAboveLeaf10002123

theorem e24KC2ThetaAboveNode1000213 :
    adaptiveCoverCheck 12 (childHH (childLH (childHL thetaAboveCell1000))) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childHH (childLH (childHL thetaAboveCell1000)))
    e24KC2ThetaAboveLeaf10002130 e24KC2ThetaAboveLeaf10002131 e24KC2ThetaAboveLeaf10002132
      e24KC2ThetaAboveLeaf10002133

theorem e24KC2ThetaAboveNode1000220 :
    adaptiveCoverCheck 12 (childLL (childHL (childHL thetaAboveCell1000))) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childLL (childHL (childHL thetaAboveCell1000)))
    e24KC2ThetaAboveNode10002200 e24KC2ThetaAboveNode10002201 e24KC2ThetaAboveNode10002202
      e24KC2ThetaAboveNode10002203

theorem e24KC2ThetaAboveNode1000221 :
    adaptiveCoverCheck 12 (childLH (childHL (childHL thetaAboveCell1000))) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childLH (childHL (childHL thetaAboveCell1000)))
    e24KC2ThetaAboveNode10002210 e24KC2ThetaAboveNode10002211 e24KC2ThetaAboveNode10002212
      e24KC2ThetaAboveNode10002213

theorem e24KC2ThetaAboveNode1000222 :
    adaptiveCoverCheck 12 (childHL (childHL (childHL thetaAboveCell1000))) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childHL (childHL (childHL thetaAboveCell1000)))
    e24KC2ThetaAboveNode10002220 e24KC2ThetaAboveNode10002221 e24KC2ThetaAboveLeaf10002222
      e24KC2ThetaAboveLeaf10002223

theorem e24KC2ThetaAboveNode1000223 :
    adaptiveCoverCheck 12 (childHH (childHL (childHL thetaAboveCell1000))) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childHH (childHL (childHL thetaAboveCell1000)))
    e24KC2ThetaAboveNode10002230 e24KC2ThetaAboveNode10002231 e24KC2ThetaAboveLeaf10002232
      e24KC2ThetaAboveLeaf10002233

theorem e24KC2ThetaAboveNode1000230 :
    adaptiveCoverCheck 12 (childLL (childHH (childHL thetaAboveCell1000))) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childLL (childHH (childHL thetaAboveCell1000)))
    e24KC2ThetaAboveNode10002300 e24KC2ThetaAboveNode10002301 e24KC2ThetaAboveNode10002302
      e24KC2ThetaAboveNode10002303

theorem e24KC2ThetaAboveNode1000231 :
    adaptiveCoverCheck 12 (childLH (childHH (childHL thetaAboveCell1000))) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childLH (childHH (childHL thetaAboveCell1000)))
    e24KC2ThetaAboveNode10002310 e24KC2ThetaAboveNode10002311 e24KC2ThetaAboveNode10002312
      e24KC2ThetaAboveNode10002313

theorem e24KC2ThetaAboveNode1000232 :
    adaptiveCoverCheck 12 (childHL (childHH (childHL thetaAboveCell1000))) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childHL (childHH (childHL thetaAboveCell1000)))
    e24KC2ThetaAboveNode10002320 e24KC2ThetaAboveNode10002321 e24KC2ThetaAboveLeaf10002322
      e24KC2ThetaAboveLeaf10002323

theorem e24KC2ThetaAboveNode1000233 :
    adaptiveCoverCheck 12 (childHH (childHH (childHL thetaAboveCell1000))) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childHH (childHH (childHL thetaAboveCell1000)))
    e24KC2ThetaAboveNode10002330 e24KC2ThetaAboveNode10002331 e24KC2ThetaAboveLeaf10002332
      e24KC2ThetaAboveLeaf10002333

theorem e24KC2ThetaAboveNode1000302 :
    adaptiveCoverCheck 12 (childHL (childLL (childHH thetaAboveCell1000))) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childHL (childLL (childHH thetaAboveCell1000)))
    e24KC2ThetaAboveLeaf10003020 e24KC2ThetaAboveLeaf10003021 e24KC2ThetaAboveLeaf10003022
      e24KC2ThetaAboveLeaf10003023

theorem e24KC2ThetaAboveNode1000303 :
    adaptiveCoverCheck 12 (childHH (childLL (childHH thetaAboveCell1000))) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childHH (childLL (childHH thetaAboveCell1000)))
    e24KC2ThetaAboveLeaf10003030 e24KC2ThetaAboveLeaf10003031 e24KC2ThetaAboveLeaf10003032
      e24KC2ThetaAboveLeaf10003033

theorem e24KC2ThetaAboveNode1000312 :
    adaptiveCoverCheck 12 (childHL (childLH (childHH thetaAboveCell1000))) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childHL (childLH (childHH thetaAboveCell1000)))
    e24KC2ThetaAboveLeaf10003120 e24KC2ThetaAboveLeaf10003121 e24KC2ThetaAboveLeaf10003122
      e24KC2ThetaAboveLeaf10003123

theorem e24KC2ThetaAboveNode1000313 :
    adaptiveCoverCheck 12 (childHH (childLH (childHH thetaAboveCell1000))) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childHH (childLH (childHH thetaAboveCell1000)))
    e24KC2ThetaAboveLeaf10003130 e24KC2ThetaAboveLeaf10003131 e24KC2ThetaAboveLeaf10003132
      e24KC2ThetaAboveLeaf10003133

theorem e24KC2ThetaAboveNode1000320 :
    adaptiveCoverCheck 12 (childLL (childHL (childHH thetaAboveCell1000))) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childLL (childHL (childHH thetaAboveCell1000)))
    e24KC2ThetaAboveNode10003200 e24KC2ThetaAboveNode10003201 e24KC2ThetaAboveNode10003202
      e24KC2ThetaAboveNode10003203

theorem e24KC2ThetaAboveNode1000321 :
    adaptiveCoverCheck 12 (childLH (childHL (childHH thetaAboveCell1000))) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childLH (childHL (childHH thetaAboveCell1000)))
    e24KC2ThetaAboveNode10003210 e24KC2ThetaAboveNode10003211 e24KC2ThetaAboveNode10003212
      e24KC2ThetaAboveNode10003213

theorem e24KC2ThetaAboveNode1000322 :
    adaptiveCoverCheck 12 (childHL (childHL (childHH thetaAboveCell1000))) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childHL (childHL (childHH thetaAboveCell1000)))
    e24KC2ThetaAboveNode10003220 e24KC2ThetaAboveNode10003221 e24KC2ThetaAboveLeaf10003222
      e24KC2ThetaAboveLeaf10003223

theorem e24KC2ThetaAboveNode1000323 :
    adaptiveCoverCheck 12 (childHH (childHL (childHH thetaAboveCell1000))) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childHH (childHL (childHH thetaAboveCell1000)))
    e24KC2ThetaAboveNode10003230 e24KC2ThetaAboveNode10003231 e24KC2ThetaAboveLeaf10003232
      e24KC2ThetaAboveLeaf10003233

theorem e24KC2ThetaAboveNode1000330 :
    adaptiveCoverCheck 12 (childLL (childHH (childHH thetaAboveCell1000))) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childLL (childHH (childHH thetaAboveCell1000)))
    e24KC2ThetaAboveNode10003300 e24KC2ThetaAboveNode10003301 e24KC2ThetaAboveNode10003302
      e24KC2ThetaAboveNode10003303

theorem e24KC2ThetaAboveNode1000331 :
    adaptiveCoverCheck 12 (childLH (childHH (childHH thetaAboveCell1000))) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childLH (childHH (childHH thetaAboveCell1000)))
    e24KC2ThetaAboveNode10003310 e24KC2ThetaAboveNode10003311 e24KC2ThetaAboveNode10003312
      e24KC2ThetaAboveNode10003313

theorem e24KC2ThetaAboveNode1000332 :
    adaptiveCoverCheck 12 (childHL (childHH (childHH thetaAboveCell1000))) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childHL (childHH (childHH thetaAboveCell1000)))
    e24KC2ThetaAboveNode10003320 e24KC2ThetaAboveNode10003321 e24KC2ThetaAboveLeaf10003322
      e24KC2ThetaAboveLeaf10003323

theorem e24KC2ThetaAboveNode1000333 :
    adaptiveCoverCheck 12 (childHH (childHH (childHH thetaAboveCell1000))) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childHH (childHH (childHH thetaAboveCell1000)))
    e24KC2ThetaAboveNode10003330 e24KC2ThetaAboveNode10003331 e24KC2ThetaAboveLeaf10003332
      e24KC2ThetaAboveLeaf10003333

theorem e24KC2ThetaAboveNode1001202 :
    adaptiveCoverCheck 12 (childHL (childLL (childHL thetaAboveCell1001))) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childHL (childLL (childHL thetaAboveCell1001)))
    e24KC2ThetaAboveLeaf10012020 e24KC2ThetaAboveLeaf10012021 e24KC2ThetaAboveLeaf10012022
      e24KC2ThetaAboveLeaf10012023

theorem e24KC2ThetaAboveNode1001203 :
    adaptiveCoverCheck 12 (childHH (childLL (childHL thetaAboveCell1001))) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childHH (childLL (childHL thetaAboveCell1001)))
    e24KC2ThetaAboveLeaf10012030 e24KC2ThetaAboveLeaf10012031 e24KC2ThetaAboveLeaf10012032
      e24KC2ThetaAboveLeaf10012033

theorem e24KC2ThetaAboveNode1001212 :
    adaptiveCoverCheck 12 (childHL (childLH (childHL thetaAboveCell1001))) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childHL (childLH (childHL thetaAboveCell1001)))
    e24KC2ThetaAboveLeaf10012120 e24KC2ThetaAboveLeaf10012121 e24KC2ThetaAboveLeaf10012122
      e24KC2ThetaAboveLeaf10012123

theorem e24KC2ThetaAboveNode1001213 :
    adaptiveCoverCheck 12 (childHH (childLH (childHL thetaAboveCell1001))) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childHH (childLH (childHL thetaAboveCell1001)))
    e24KC2ThetaAboveLeaf10012130 e24KC2ThetaAboveLeaf10012131 e24KC2ThetaAboveLeaf10012132
      e24KC2ThetaAboveLeaf10012133

theorem e24KC2ThetaAboveNode1001220 :
    adaptiveCoverCheck 12 (childLL (childHL (childHL thetaAboveCell1001))) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childLL (childHL (childHL thetaAboveCell1001)))
    e24KC2ThetaAboveNode10012200 e24KC2ThetaAboveNode10012201 e24KC2ThetaAboveNode10012202
      e24KC2ThetaAboveNode10012203

theorem e24KC2ThetaAboveNode1001221 :
    adaptiveCoverCheck 12 (childLH (childHL (childHL thetaAboveCell1001))) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childLH (childHL (childHL thetaAboveCell1001)))
    e24KC2ThetaAboveNode10012210 e24KC2ThetaAboveNode10012211 e24KC2ThetaAboveNode10012212
      e24KC2ThetaAboveNode10012213

theorem e24KC2ThetaAboveNode1001222 :
    adaptiveCoverCheck 12 (childHL (childHL (childHL thetaAboveCell1001))) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childHL (childHL (childHL thetaAboveCell1001)))
    e24KC2ThetaAboveNode10012220 e24KC2ThetaAboveNode10012221 e24KC2ThetaAboveLeaf10012222
      e24KC2ThetaAboveLeaf10012223

theorem e24KC2ThetaAboveNode1001223 :
    adaptiveCoverCheck 12 (childHH (childHL (childHL thetaAboveCell1001))) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childHH (childHL (childHL thetaAboveCell1001)))
    e24KC2ThetaAboveNode10012230 e24KC2ThetaAboveNode10012231 e24KC2ThetaAboveLeaf10012232
      e24KC2ThetaAboveLeaf10012233

theorem e24KC2ThetaAboveNode1001230 :
    adaptiveCoverCheck 12 (childLL (childHH (childHL thetaAboveCell1001))) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childLL (childHH (childHL thetaAboveCell1001)))
    e24KC2ThetaAboveNode10012300 e24KC2ThetaAboveNode10012301 e24KC2ThetaAboveNode10012302
      e24KC2ThetaAboveNode10012303

theorem e24KC2ThetaAboveNode1001231 :
    adaptiveCoverCheck 12 (childLH (childHH (childHL thetaAboveCell1001))) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childLH (childHH (childHL thetaAboveCell1001)))
    e24KC2ThetaAboveNode10012310 e24KC2ThetaAboveNode10012311 e24KC2ThetaAboveNode10012312
      e24KC2ThetaAboveNode10012313

theorem e24KC2ThetaAboveNode1001232 :
    adaptiveCoverCheck 12 (childHL (childHH (childHL thetaAboveCell1001))) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childHL (childHH (childHL thetaAboveCell1001)))
    e24KC2ThetaAboveNode10012320 e24KC2ThetaAboveNode10012321 e24KC2ThetaAboveLeaf10012322
      e24KC2ThetaAboveLeaf10012323

theorem e24KC2ThetaAboveNode1001233 :
    adaptiveCoverCheck 12 (childHH (childHH (childHL thetaAboveCell1001))) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childHH (childHH (childHL thetaAboveCell1001)))
    e24KC2ThetaAboveNode10012330 e24KC2ThetaAboveNode10012331 e24KC2ThetaAboveLeaf10012332
      e24KC2ThetaAboveLeaf10012333

theorem e24KC2ThetaAboveNode1001302 :
    adaptiveCoverCheck 12 (childHL (childLL (childHH thetaAboveCell1001))) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childHL (childLL (childHH thetaAboveCell1001)))
    e24KC2ThetaAboveLeaf10013020 e24KC2ThetaAboveLeaf10013021 e24KC2ThetaAboveLeaf10013022
      e24KC2ThetaAboveLeaf10013023

theorem e24KC2ThetaAboveNode1001303 :
    adaptiveCoverCheck 12 (childHH (childLL (childHH thetaAboveCell1001))) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childHH (childLL (childHH thetaAboveCell1001)))
    e24KC2ThetaAboveLeaf10013030 e24KC2ThetaAboveLeaf10013031 e24KC2ThetaAboveLeaf10013032
      e24KC2ThetaAboveLeaf10013033

theorem e24KC2ThetaAboveNode1001312 :
    adaptiveCoverCheck 12 (childHL (childLH (childHH thetaAboveCell1001))) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childHL (childLH (childHH thetaAboveCell1001)))
    e24KC2ThetaAboveLeaf10013120 e24KC2ThetaAboveLeaf10013121 e24KC2ThetaAboveLeaf10013122
      e24KC2ThetaAboveLeaf10013123

theorem e24KC2ThetaAboveNode1001313 :
    adaptiveCoverCheck 12 (childHH (childLH (childHH thetaAboveCell1001))) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childHH (childLH (childHH thetaAboveCell1001)))
    e24KC2ThetaAboveLeaf10013130 e24KC2ThetaAboveLeaf10013131 e24KC2ThetaAboveLeaf10013132
      e24KC2ThetaAboveLeaf10013133

theorem e24KC2ThetaAboveNode1001320 :
    adaptiveCoverCheck 12 (childLL (childHL (childHH thetaAboveCell1001))) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childLL (childHL (childHH thetaAboveCell1001)))
    e24KC2ThetaAboveNode10013200 e24KC2ThetaAboveNode10013201 e24KC2ThetaAboveNode10013202
      e24KC2ThetaAboveNode10013203

theorem e24KC2ThetaAboveNode1001321 :
    adaptiveCoverCheck 12 (childLH (childHL (childHH thetaAboveCell1001))) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childLH (childHL (childHH thetaAboveCell1001)))
    e24KC2ThetaAboveNode10013210 e24KC2ThetaAboveNode10013211 e24KC2ThetaAboveNode10013212
      e24KC2ThetaAboveNode10013213

theorem e24KC2ThetaAboveNode1001322 :
    adaptiveCoverCheck 12 (childHL (childHL (childHH thetaAboveCell1001))) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childHL (childHL (childHH thetaAboveCell1001)))
    e24KC2ThetaAboveNode10013220 e24KC2ThetaAboveNode10013221 e24KC2ThetaAboveLeaf10013222
      e24KC2ThetaAboveLeaf10013223

theorem e24KC2ThetaAboveNode1001323 :
    adaptiveCoverCheck 12 (childHH (childHL (childHH thetaAboveCell1001))) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childHH (childHL (childHH thetaAboveCell1001)))
    e24KC2ThetaAboveNode10013230 e24KC2ThetaAboveNode10013231 e24KC2ThetaAboveLeaf10013232
      e24KC2ThetaAboveLeaf10013233

theorem e24KC2ThetaAboveNode1001330 :
    adaptiveCoverCheck 12 (childLL (childHH (childHH thetaAboveCell1001))) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childLL (childHH (childHH thetaAboveCell1001)))
    e24KC2ThetaAboveNode10013300 e24KC2ThetaAboveNode10013301 e24KC2ThetaAboveNode10013302
      e24KC2ThetaAboveNode10013303

theorem e24KC2ThetaAboveNode1001331 :
    adaptiveCoverCheck 12 (childLH (childHH (childHH thetaAboveCell1001))) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childLH (childHH (childHH thetaAboveCell1001)))
    e24KC2ThetaAboveNode10013310 e24KC2ThetaAboveNode10013311 e24KC2ThetaAboveNode10013312
      e24KC2ThetaAboveNode10013313

theorem e24KC2ThetaAboveNode1001332 :
    adaptiveCoverCheck 12 (childHL (childHH (childHH thetaAboveCell1001))) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childHL (childHH (childHH thetaAboveCell1001)))
    e24KC2ThetaAboveNode10013320 e24KC2ThetaAboveNode10013321 e24KC2ThetaAboveLeaf10013322
      e24KC2ThetaAboveLeaf10013323

theorem e24KC2ThetaAboveNode1001333 :
    adaptiveCoverCheck 12 (childHH (childHH (childHH thetaAboveCell1001))) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childHH (childHH (childHH thetaAboveCell1001)))
    e24KC2ThetaAboveNode10013330 e24KC2ThetaAboveNode10013331 e24KC2ThetaAboveLeaf10013332
      e24KC2ThetaAboveLeaf10013333

theorem e24KC2ThetaAboveNode1010202 :
    adaptiveCoverCheck 12 (childHL (childLL (childHL thetaAboveCell1010))) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childHL (childLL (childHL thetaAboveCell1010)))
    e24KC2ThetaAboveLeaf10102020 e24KC2ThetaAboveLeaf10102021 e24KC2ThetaAboveLeaf10102022
      e24KC2ThetaAboveLeaf10102023

theorem e24KC2ThetaAboveNode1010203 :
    adaptiveCoverCheck 12 (childHH (childLL (childHL thetaAboveCell1010))) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childHH (childLL (childHL thetaAboveCell1010)))
    e24KC2ThetaAboveLeaf10102030 e24KC2ThetaAboveLeaf10102031 e24KC2ThetaAboveLeaf10102032
      e24KC2ThetaAboveLeaf10102033

theorem e24KC2ThetaAboveNode1010220 :
    adaptiveCoverCheck 12 (childLL (childHL (childHL thetaAboveCell1010))) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childLL (childHL (childHL thetaAboveCell1010)))
    e24KC2ThetaAboveNode10102200 e24KC2ThetaAboveNode10102201 e24KC2ThetaAboveNode10102202
      e24KC2ThetaAboveNode10102203

theorem e24KC2ThetaAboveNode1010221 :
    adaptiveCoverCheck 12 (childLH (childHL (childHL thetaAboveCell1010))) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childLH (childHL (childHL thetaAboveCell1010)))
    e24KC2ThetaAboveNode10102210 e24KC2ThetaAboveNode10102211 e24KC2ThetaAboveNode10102212
      e24KC2ThetaAboveNode10102213

theorem e24KC2ThetaAboveNode1010222 :
    adaptiveCoverCheck 12 (childHL (childHL (childHL thetaAboveCell1010))) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childHL (childHL (childHL thetaAboveCell1010)))
    e24KC2ThetaAboveNode10102220 e24KC2ThetaAboveNode10102221 e24KC2ThetaAboveLeaf10102222
      e24KC2ThetaAboveLeaf10102223

theorem e24KC2ThetaAboveNode1010223 :
    adaptiveCoverCheck 12 (childHH (childHL (childHL thetaAboveCell1010))) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childHH (childHL (childHL thetaAboveCell1010)))
    e24KC2ThetaAboveNode10102230 e24KC2ThetaAboveNode10102231 e24KC2ThetaAboveLeaf10102232
      e24KC2ThetaAboveLeaf10102233

theorem e24KC2ThetaAboveNode1010230 :
    adaptiveCoverCheck 12 (childLL (childHH (childHL thetaAboveCell1010))) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childLL (childHH (childHL thetaAboveCell1010)))
    e24KC2ThetaAboveNode10102300 e24KC2ThetaAboveNode10102301 e24KC2ThetaAboveNode10102302
      e24KC2ThetaAboveNode10102303

theorem e24KC2ThetaAboveNode1010231 :
    adaptiveCoverCheck 12 (childLH (childHH (childHL thetaAboveCell1010))) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childLH (childHH (childHL thetaAboveCell1010)))
    e24KC2ThetaAboveNode10102310 e24KC2ThetaAboveNode10102311 e24KC2ThetaAboveNode10102312
      e24KC2ThetaAboveNode10102313

theorem e24KC2ThetaAboveNode1010232 :
    adaptiveCoverCheck 12 (childHL (childHH (childHL thetaAboveCell1010))) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childHL (childHH (childHL thetaAboveCell1010)))
    e24KC2ThetaAboveNode10102320 e24KC2ThetaAboveNode10102321 e24KC2ThetaAboveLeaf10102322
      e24KC2ThetaAboveLeaf10102323

theorem e24KC2ThetaAboveNode1010233 :
    adaptiveCoverCheck 12 (childHH (childHH (childHL thetaAboveCell1010))) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childHH (childHH (childHL thetaAboveCell1010)))
    e24KC2ThetaAboveNode10102330 e24KC2ThetaAboveNode10102331 e24KC2ThetaAboveLeaf10102332
      e24KC2ThetaAboveLeaf10102333

theorem e24KC2ThetaAboveNode1010320 :
    adaptiveCoverCheck 12 (childLL (childHL (childHH thetaAboveCell1010))) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childLL (childHL (childHH thetaAboveCell1010)))
    e24KC2ThetaAboveNode10103200 e24KC2ThetaAboveNode10103201 e24KC2ThetaAboveNode10103202
      e24KC2ThetaAboveNode10103203

theorem e24KC2ThetaAboveNode1010321 :
    adaptiveCoverCheck 12 (childLH (childHL (childHH thetaAboveCell1010))) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childLH (childHL (childHH thetaAboveCell1010)))
    e24KC2ThetaAboveNode10103210 e24KC2ThetaAboveNode10103211 e24KC2ThetaAboveNode10103212
      e24KC2ThetaAboveNode10103213

theorem e24KC2ThetaAboveNode1010322 :
    adaptiveCoverCheck 12 (childHL (childHL (childHH thetaAboveCell1010))) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childHL (childHL (childHH thetaAboveCell1010)))
    e24KC2ThetaAboveNode10103220 e24KC2ThetaAboveNode10103221 e24KC2ThetaAboveLeaf10103222
      e24KC2ThetaAboveLeaf10103223

theorem e24KC2ThetaAboveNode1010323 :
    adaptiveCoverCheck 12 (childHH (childHL (childHH thetaAboveCell1010))) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childHH (childHL (childHH thetaAboveCell1010)))
    e24KC2ThetaAboveNode10103230 e24KC2ThetaAboveNode10103231 e24KC2ThetaAboveLeaf10103232
      e24KC2ThetaAboveLeaf10103233

theorem e24KC2ThetaAboveNode1010330 :
    adaptiveCoverCheck 12 (childLL (childHH (childHH thetaAboveCell1010))) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childLL (childHH (childHH thetaAboveCell1010)))
    e24KC2ThetaAboveNode10103300 e24KC2ThetaAboveNode10103301 e24KC2ThetaAboveNode10103302
      e24KC2ThetaAboveNode10103303

theorem e24KC2ThetaAboveNode1010331 :
    adaptiveCoverCheck 12 (childLH (childHH (childHH thetaAboveCell1010))) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childLH (childHH (childHH thetaAboveCell1010)))
    e24KC2ThetaAboveNode10103310 e24KC2ThetaAboveNode10103311 e24KC2ThetaAboveNode10103312
      e24KC2ThetaAboveNode10103313

theorem e24KC2ThetaAboveNode1010332 :
    adaptiveCoverCheck 12 (childHL (childHH (childHH thetaAboveCell1010))) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childHL (childHH (childHH thetaAboveCell1010)))
    e24KC2ThetaAboveNode10103320 e24KC2ThetaAboveNode10103321 e24KC2ThetaAboveLeaf10103322
      e24KC2ThetaAboveLeaf10103323

theorem e24KC2ThetaAboveNode1010333 :
    adaptiveCoverCheck 12 (childHH (childHH (childHH thetaAboveCell1010))) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childHH (childHH (childHH thetaAboveCell1010)))
    e24KC2ThetaAboveNode10103330 e24KC2ThetaAboveNode10103331 e24KC2ThetaAboveLeaf10103332
      e24KC2ThetaAboveLeaf10103333

theorem e24KC2ThetaAboveNode1011220 :
    adaptiveCoverCheck 12 (childLL (childHL (childHL thetaAboveCell1011))) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childLL (childHL (childHL thetaAboveCell1011)))
    e24KC2ThetaAboveNode10112200 e24KC2ThetaAboveNode10112201 e24KC2ThetaAboveNode10112202
      e24KC2ThetaAboveNode10112203

theorem e24KC2ThetaAboveNode1011221 :
    adaptiveCoverCheck 12 (childLH (childHL (childHL thetaAboveCell1011))) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childLH (childHL (childHL thetaAboveCell1011)))
    e24KC2ThetaAboveNode10112210 e24KC2ThetaAboveNode10112211 e24KC2ThetaAboveNode10112212
      e24KC2ThetaAboveNode10112213

theorem e24KC2ThetaAboveNode1011222 :
    adaptiveCoverCheck 12 (childHL (childHL (childHL thetaAboveCell1011))) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childHL (childHL (childHL thetaAboveCell1011)))
    e24KC2ThetaAboveNode10112220 e24KC2ThetaAboveNode10112221 e24KC2ThetaAboveLeaf10112222
      e24KC2ThetaAboveLeaf10112223

theorem e24KC2ThetaAboveNode1011223 :
    adaptiveCoverCheck 12 (childHH (childHL (childHL thetaAboveCell1011))) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childHH (childHL (childHL thetaAboveCell1011)))
    e24KC2ThetaAboveNode10112230 e24KC2ThetaAboveNode10112231 e24KC2ThetaAboveLeaf10112232
      e24KC2ThetaAboveLeaf10112233

theorem e24KC2ThetaAboveNode1011230 :
    adaptiveCoverCheck 12 (childLL (childHH (childHL thetaAboveCell1011))) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childLL (childHH (childHL thetaAboveCell1011)))
    e24KC2ThetaAboveNode10112300 e24KC2ThetaAboveNode10112301 e24KC2ThetaAboveNode10112302
      e24KC2ThetaAboveNode10112303

theorem e24KC2ThetaAboveNode1011231 :
    adaptiveCoverCheck 12 (childLH (childHH (childHL thetaAboveCell1011))) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childLH (childHH (childHL thetaAboveCell1011)))
    e24KC2ThetaAboveNode10112310 e24KC2ThetaAboveNode10112311 e24KC2ThetaAboveNode10112312
      e24KC2ThetaAboveNode10112313

theorem e24KC2ThetaAboveNode1011232 :
    adaptiveCoverCheck 12 (childHL (childHH (childHL thetaAboveCell1011))) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childHL (childHH (childHL thetaAboveCell1011)))
    e24KC2ThetaAboveNode10112320 e24KC2ThetaAboveNode10112321 e24KC2ThetaAboveLeaf10112322
      e24KC2ThetaAboveLeaf10112323

theorem e24KC2ThetaAboveNode1011233 :
    adaptiveCoverCheck 12 (childHH (childHH (childHL thetaAboveCell1011))) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childHH (childHH (childHL thetaAboveCell1011)))
    e24KC2ThetaAboveNode10112330 e24KC2ThetaAboveNode10112331 e24KC2ThetaAboveLeaf10112332
      e24KC2ThetaAboveLeaf10112333

theorem e24KC2ThetaAboveNode1011320 :
    adaptiveCoverCheck 12 (childLL (childHL (childHH thetaAboveCell1011))) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childLL (childHL (childHH thetaAboveCell1011)))
    e24KC2ThetaAboveNode10113200 e24KC2ThetaAboveNode10113201 e24KC2ThetaAboveNode10113202
      e24KC2ThetaAboveNode10113203

theorem e24KC2ThetaAboveNode1011321 :
    adaptiveCoverCheck 12 (childLH (childHL (childHH thetaAboveCell1011))) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childLH (childHL (childHH thetaAboveCell1011)))
    e24KC2ThetaAboveNode10113210 e24KC2ThetaAboveNode10113211 e24KC2ThetaAboveNode10113212
      e24KC2ThetaAboveNode10113213

theorem e24KC2ThetaAboveNode1011322 :
    adaptiveCoverCheck 12 (childHL (childHL (childHH thetaAboveCell1011))) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childHL (childHL (childHH thetaAboveCell1011)))
    e24KC2ThetaAboveNode10113220 e24KC2ThetaAboveNode10113221 e24KC2ThetaAboveLeaf10113222
      e24KC2ThetaAboveLeaf10113223

theorem e24KC2ThetaAboveNode1011323 :
    adaptiveCoverCheck 12 (childHH (childHL (childHH thetaAboveCell1011))) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childHH (childHL (childHH thetaAboveCell1011)))
    e24KC2ThetaAboveNode10113230 e24KC2ThetaAboveNode10113231 e24KC2ThetaAboveLeaf10113232
      e24KC2ThetaAboveLeaf10113233

theorem e24KC2ThetaAboveNode1011330 :
    adaptiveCoverCheck 12 (childLL (childHH (childHH thetaAboveCell1011))) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childLL (childHH (childHH thetaAboveCell1011)))
    e24KC2ThetaAboveNode10113300 e24KC2ThetaAboveNode10113301 e24KC2ThetaAboveNode10113302
      e24KC2ThetaAboveNode10113303

theorem e24KC2ThetaAboveNode1011331 :
    adaptiveCoverCheck 12 (childLH (childHH (childHH thetaAboveCell1011))) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childLH (childHH (childHH thetaAboveCell1011)))
    e24KC2ThetaAboveNode10113310 e24KC2ThetaAboveNode10113311 e24KC2ThetaAboveNode10113312
      e24KC2ThetaAboveNode10113313

theorem e24KC2ThetaAboveNode1011332 :
    adaptiveCoverCheck 12 (childHL (childHH (childHH thetaAboveCell1011))) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childHL (childHH (childHH thetaAboveCell1011)))
    e24KC2ThetaAboveNode10113320 e24KC2ThetaAboveNode10113321 e24KC2ThetaAboveLeaf10113322
      e24KC2ThetaAboveLeaf10113323

theorem e24KC2ThetaAboveNode1011333 :
    adaptiveCoverCheck 12 (childHH (childHH (childHH thetaAboveCell1011))) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childHH (childHH (childHH thetaAboveCell1011)))
    e24KC2ThetaAboveNode10113330 e24KC2ThetaAboveNode10113331 e24KC2ThetaAboveLeaf10113332
      e24KC2ThetaAboveLeaf10113333

theorem e24KC2ThetaAboveNode1100220 :
    adaptiveCoverCheck 12 (childLL (childHL (childHL thetaAboveCell1100))) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childLL (childHL (childHL thetaAboveCell1100)))
    e24KC2ThetaAboveLeaf11002200 e24KC2ThetaAboveLeaf11002201 e24KC2ThetaAboveNode11002202
      e24KC2ThetaAboveNode11002203

theorem e24KC2ThetaAboveNode1100221 :
    adaptiveCoverCheck 12 (childLH (childHL (childHL thetaAboveCell1100))) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childLH (childHL (childHL thetaAboveCell1100)))
    e24KC2ThetaAboveLeaf11002210 e24KC2ThetaAboveLeaf11002211 e24KC2ThetaAboveNode11002212
      e24KC2ThetaAboveNode11002213

theorem e24KC2ThetaAboveNode1100222 :
    adaptiveCoverCheck 12 (childHL (childHL (childHL thetaAboveCell1100))) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childHL (childHL (childHL thetaAboveCell1100)))
    e24KC2ThetaAboveNode11002220 e24KC2ThetaAboveNode11002221 e24KC2ThetaAboveLeaf11002222
      e24KC2ThetaAboveLeaf11002223

theorem e24KC2ThetaAboveNode1100223 :
    adaptiveCoverCheck 12 (childHH (childHL (childHL thetaAboveCell1100))) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childHH (childHL (childHL thetaAboveCell1100)))
    e24KC2ThetaAboveNode11002230 e24KC2ThetaAboveNode11002231 e24KC2ThetaAboveLeaf11002232
      e24KC2ThetaAboveLeaf11002233

theorem e24KC2ThetaAboveNode1100230 :
    adaptiveCoverCheck 12 (childLL (childHH (childHL thetaAboveCell1100))) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childLL (childHH (childHL thetaAboveCell1100)))
    e24KC2ThetaAboveLeaf11002300 e24KC2ThetaAboveLeaf11002301 e24KC2ThetaAboveNode11002302
      e24KC2ThetaAboveNode11002303

theorem e24KC2ThetaAboveNode1100231 :
    adaptiveCoverCheck 12 (childLH (childHH (childHL thetaAboveCell1100))) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childLH (childHH (childHL thetaAboveCell1100)))
    e24KC2ThetaAboveLeaf11002310 e24KC2ThetaAboveLeaf11002311 e24KC2ThetaAboveNode11002312
      e24KC2ThetaAboveNode11002313

theorem e24KC2ThetaAboveNode1100232 :
    adaptiveCoverCheck 12 (childHL (childHH (childHL thetaAboveCell1100))) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childHL (childHH (childHL thetaAboveCell1100)))
    e24KC2ThetaAboveNode11002320 e24KC2ThetaAboveNode11002321 e24KC2ThetaAboveLeaf11002322
      e24KC2ThetaAboveLeaf11002323

theorem e24KC2ThetaAboveNode1100233 :
    adaptiveCoverCheck 12 (childHH (childHH (childHL thetaAboveCell1100))) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childHH (childHH (childHL thetaAboveCell1100)))
    e24KC2ThetaAboveNode11002330 e24KC2ThetaAboveNode11002331 e24KC2ThetaAboveLeaf11002332
      e24KC2ThetaAboveLeaf11002333

theorem e24KC2ThetaAboveNode1100320 :
    adaptiveCoverCheck 12 (childLL (childHL (childHH thetaAboveCell1100))) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childLL (childHL (childHH thetaAboveCell1100)))
    e24KC2ThetaAboveLeaf11003200 e24KC2ThetaAboveLeaf11003201 e24KC2ThetaAboveNode11003202
      e24KC2ThetaAboveNode11003203

theorem e24KC2ThetaAboveNode1100321 :
    adaptiveCoverCheck 12 (childLH (childHL (childHH thetaAboveCell1100))) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childLH (childHL (childHH thetaAboveCell1100)))
    e24KC2ThetaAboveLeaf11003210 e24KC2ThetaAboveLeaf11003211 e24KC2ThetaAboveNode11003212
      e24KC2ThetaAboveNode11003213

theorem e24KC2ThetaAboveNode1100322 :
    adaptiveCoverCheck 12 (childHL (childHL (childHH thetaAboveCell1100))) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childHL (childHL (childHH thetaAboveCell1100)))
    e24KC2ThetaAboveNode11003220 e24KC2ThetaAboveNode11003221 e24KC2ThetaAboveLeaf11003222
      e24KC2ThetaAboveLeaf11003223

theorem e24KC2ThetaAboveNode1100323 :
    adaptiveCoverCheck 12 (childHH (childHL (childHH thetaAboveCell1100))) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childHH (childHL (childHH thetaAboveCell1100)))
    e24KC2ThetaAboveNode11003230 e24KC2ThetaAboveNode11003231 e24KC2ThetaAboveLeaf11003232
      e24KC2ThetaAboveLeaf11003233

theorem e24KC2ThetaAboveNode1100330 :
    adaptiveCoverCheck 12 (childLL (childHH (childHH thetaAboveCell1100))) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childLL (childHH (childHH thetaAboveCell1100)))
    e24KC2ThetaAboveLeaf11003300 e24KC2ThetaAboveLeaf11003301 e24KC2ThetaAboveNode11003302
      e24KC2ThetaAboveNode11003303

theorem e24KC2ThetaAboveNode1100331 :
    adaptiveCoverCheck 12 (childLH (childHH (childHH thetaAboveCell1100))) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childLH (childHH (childHH thetaAboveCell1100)))
    e24KC2ThetaAboveLeaf11003310 e24KC2ThetaAboveLeaf11003311 e24KC2ThetaAboveNode11003312
      e24KC2ThetaAboveNode11003313

theorem e24KC2ThetaAboveNode1100332 :
    adaptiveCoverCheck 12 (childHL (childHH (childHH thetaAboveCell1100))) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childHL (childHH (childHH thetaAboveCell1100)))
    e24KC2ThetaAboveNode11003320 e24KC2ThetaAboveNode11003321 e24KC2ThetaAboveLeaf11003322
      e24KC2ThetaAboveLeaf11003323

theorem e24KC2ThetaAboveNode1100333 :
    adaptiveCoverCheck 12 (childHH (childHH (childHH thetaAboveCell1100))) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childHH (childHH (childHH thetaAboveCell1100)))
    e24KC2ThetaAboveNode11003330 e24KC2ThetaAboveNode11003331 e24KC2ThetaAboveLeaf11003332
      e24KC2ThetaAboveLeaf11003333

theorem e24KC2ThetaAboveNode1101220 :
    adaptiveCoverCheck 12 (childLL (childHL (childHL thetaAboveCell1101))) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childLL (childHL (childHL thetaAboveCell1101)))
    e24KC2ThetaAboveLeaf11012200 e24KC2ThetaAboveLeaf11012201 e24KC2ThetaAboveNode11012202
      e24KC2ThetaAboveNode11012203

theorem e24KC2ThetaAboveNode1101221 :
    adaptiveCoverCheck 12 (childLH (childHL (childHL thetaAboveCell1101))) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childLH (childHL (childHL thetaAboveCell1101)))
    e24KC2ThetaAboveLeaf11012210 e24KC2ThetaAboveLeaf11012211 e24KC2ThetaAboveNode11012212
      e24KC2ThetaAboveNode11012213

theorem e24KC2ThetaAboveNode1101222 :
    adaptiveCoverCheck 12 (childHL (childHL (childHL thetaAboveCell1101))) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childHL (childHL (childHL thetaAboveCell1101)))
    e24KC2ThetaAboveNode11012220 e24KC2ThetaAboveNode11012221 e24KC2ThetaAboveLeaf11012222
      e24KC2ThetaAboveLeaf11012223

theorem e24KC2ThetaAboveNode1101223 :
    adaptiveCoverCheck 12 (childHH (childHL (childHL thetaAboveCell1101))) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childHH (childHL (childHL thetaAboveCell1101)))
    e24KC2ThetaAboveNode11012230 e24KC2ThetaAboveNode11012231 e24KC2ThetaAboveLeaf11012232
      e24KC2ThetaAboveLeaf11012233

theorem e24KC2ThetaAboveNode1101230 :
    adaptiveCoverCheck 12 (childLL (childHH (childHL thetaAboveCell1101))) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childLL (childHH (childHL thetaAboveCell1101)))
    e24KC2ThetaAboveLeaf11012300 e24KC2ThetaAboveLeaf11012301 e24KC2ThetaAboveNode11012302
      e24KC2ThetaAboveNode11012303

theorem e24KC2ThetaAboveNode1101231 :
    adaptiveCoverCheck 12 (childLH (childHH (childHL thetaAboveCell1101))) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childLH (childHH (childHL thetaAboveCell1101)))
    e24KC2ThetaAboveLeaf11012310 e24KC2ThetaAboveLeaf11012311 e24KC2ThetaAboveNode11012312
      e24KC2ThetaAboveNode11012313

theorem e24KC2ThetaAboveNode1101232 :
    adaptiveCoverCheck 12 (childHL (childHH (childHL thetaAboveCell1101))) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childHL (childHH (childHL thetaAboveCell1101)))
    e24KC2ThetaAboveNode11012320 e24KC2ThetaAboveNode11012321 e24KC2ThetaAboveLeaf11012322
      e24KC2ThetaAboveLeaf11012323

theorem e24KC2ThetaAboveNode1101233 :
    adaptiveCoverCheck 12 (childHH (childHH (childHL thetaAboveCell1101))) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childHH (childHH (childHL thetaAboveCell1101)))
    e24KC2ThetaAboveNode11012330 e24KC2ThetaAboveNode11012331 e24KC2ThetaAboveLeaf11012332
      e24KC2ThetaAboveLeaf11012333

theorem e24KC2ThetaAboveNode1101320 :
    adaptiveCoverCheck 12 (childLL (childHL (childHH thetaAboveCell1101))) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childLL (childHL (childHH thetaAboveCell1101)))
    e24KC2ThetaAboveLeaf11013200 e24KC2ThetaAboveLeaf11013201 e24KC2ThetaAboveNode11013202
      e24KC2ThetaAboveNode11013203

theorem e24KC2ThetaAboveNode1101321 :
    adaptiveCoverCheck 12 (childLH (childHL (childHH thetaAboveCell1101))) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childLH (childHL (childHH thetaAboveCell1101)))
    e24KC2ThetaAboveLeaf11013210 e24KC2ThetaAboveLeaf11013211 e24KC2ThetaAboveNode11013212
      e24KC2ThetaAboveNode11013213

theorem e24KC2ThetaAboveNode1101322 :
    adaptiveCoverCheck 12 (childHL (childHL (childHH thetaAboveCell1101))) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childHL (childHL (childHH thetaAboveCell1101)))
    e24KC2ThetaAboveNode11013220 e24KC2ThetaAboveNode11013221 e24KC2ThetaAboveLeaf11013222
      e24KC2ThetaAboveLeaf11013223

theorem e24KC2ThetaAboveNode1101323 :
    adaptiveCoverCheck 12 (childHH (childHL (childHH thetaAboveCell1101))) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childHH (childHL (childHH thetaAboveCell1101)))
    e24KC2ThetaAboveNode11013230 e24KC2ThetaAboveNode11013231 e24KC2ThetaAboveLeaf11013232
      e24KC2ThetaAboveLeaf11013233

theorem e24KC2ThetaAboveNode1101330 :
    adaptiveCoverCheck 12 (childLL (childHH (childHH thetaAboveCell1101))) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childLL (childHH (childHH thetaAboveCell1101)))
    e24KC2ThetaAboveLeaf11013300 e24KC2ThetaAboveLeaf11013301 e24KC2ThetaAboveNode11013302
      e24KC2ThetaAboveNode11013303

theorem e24KC2ThetaAboveNode1101331 :
    adaptiveCoverCheck 12 (childLH (childHH (childHH thetaAboveCell1101))) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childLH (childHH (childHH thetaAboveCell1101)))
    e24KC2ThetaAboveLeaf11013310 e24KC2ThetaAboveLeaf11013311 e24KC2ThetaAboveNode11013312
      e24KC2ThetaAboveNode11013313

theorem e24KC2ThetaAboveNode1101332 :
    adaptiveCoverCheck 12 (childHL (childHH (childHH thetaAboveCell1101))) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childHL (childHH (childHH thetaAboveCell1101)))
    e24KC2ThetaAboveNode11013320 e24KC2ThetaAboveNode11013321 e24KC2ThetaAboveLeaf11013322
      e24KC2ThetaAboveLeaf11013323

theorem e24KC2ThetaAboveNode1101333 :
    adaptiveCoverCheck 12 (childHH (childHH (childHH thetaAboveCell1101))) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childHH (childHH (childHH thetaAboveCell1101)))
    e24KC2ThetaAboveNode11013330 e24KC2ThetaAboveNode11013331 e24KC2ThetaAboveLeaf11013332
      e24KC2ThetaAboveLeaf11013333

theorem e24KC2ThetaAboveNode1110220 :
    adaptiveCoverCheck 12 (childLL (childHL (childHL thetaAboveCell1110))) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childLL (childHL (childHL thetaAboveCell1110)))
    e24KC2ThetaAboveLeaf11102200 e24KC2ThetaAboveLeaf11102201 e24KC2ThetaAboveNode11102202
      e24KC2ThetaAboveNode11102203

theorem e24KC2ThetaAboveNode1110221 :
    adaptiveCoverCheck 12 (childLH (childHL (childHL thetaAboveCell1110))) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childLH (childHL (childHL thetaAboveCell1110)))
    e24KC2ThetaAboveLeaf11102210 e24KC2ThetaAboveLeaf11102211 e24KC2ThetaAboveNode11102212
      e24KC2ThetaAboveNode11102213

theorem e24KC2ThetaAboveNode1110222 :
    adaptiveCoverCheck 12 (childHL (childHL (childHL thetaAboveCell1110))) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childHL (childHL (childHL thetaAboveCell1110)))
    e24KC2ThetaAboveNode11102220 e24KC2ThetaAboveNode11102221 e24KC2ThetaAboveLeaf11102222
      e24KC2ThetaAboveLeaf11102223

theorem e24KC2ThetaAboveNode1110223 :
    adaptiveCoverCheck 12 (childHH (childHL (childHL thetaAboveCell1110))) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childHH (childHL (childHL thetaAboveCell1110)))
    e24KC2ThetaAboveNode11102230 e24KC2ThetaAboveNode11102231 e24KC2ThetaAboveLeaf11102232
      e24KC2ThetaAboveLeaf11102233

theorem e24KC2ThetaAboveNode1110230 :
    adaptiveCoverCheck 12 (childLL (childHH (childHL thetaAboveCell1110))) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childLL (childHH (childHL thetaAboveCell1110)))
    e24KC2ThetaAboveLeaf11102300 e24KC2ThetaAboveLeaf11102301 e24KC2ThetaAboveNode11102302
      e24KC2ThetaAboveNode11102303

theorem e24KC2ThetaAboveNode1110231 :
    adaptiveCoverCheck 12 (childLH (childHH (childHL thetaAboveCell1110))) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childLH (childHH (childHL thetaAboveCell1110)))
    e24KC2ThetaAboveLeaf11102310 e24KC2ThetaAboveLeaf11102311 e24KC2ThetaAboveNode11102312
      e24KC2ThetaAboveNode11102313

theorem e24KC2ThetaAboveNode1110232 :
    adaptiveCoverCheck 12 (childHL (childHH (childHL thetaAboveCell1110))) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childHL (childHH (childHL thetaAboveCell1110)))
    e24KC2ThetaAboveNode11102320 e24KC2ThetaAboveNode11102321 e24KC2ThetaAboveLeaf11102322
      e24KC2ThetaAboveLeaf11102323

theorem e24KC2ThetaAboveNode1110233 :
    adaptiveCoverCheck 12 (childHH (childHH (childHL thetaAboveCell1110))) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childHH (childHH (childHL thetaAboveCell1110)))
    e24KC2ThetaAboveNode11102330 e24KC2ThetaAboveNode11102331 e24KC2ThetaAboveLeaf11102332
      e24KC2ThetaAboveLeaf11102333

theorem e24KC2ThetaAboveNode1110320 :
    adaptiveCoverCheck 12 (childLL (childHL (childHH thetaAboveCell1110))) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childLL (childHL (childHH thetaAboveCell1110)))
    e24KC2ThetaAboveLeaf11103200 e24KC2ThetaAboveLeaf11103201 e24KC2ThetaAboveNode11103202
      e24KC2ThetaAboveNode11103203

theorem e24KC2ThetaAboveNode1110321 :
    adaptiveCoverCheck 12 (childLH (childHL (childHH thetaAboveCell1110))) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childLH (childHL (childHH thetaAboveCell1110)))
    e24KC2ThetaAboveLeaf11103210 e24KC2ThetaAboveLeaf11103211 e24KC2ThetaAboveNode11103212
      e24KC2ThetaAboveNode11103213

theorem e24KC2ThetaAboveNode1110322 :
    adaptiveCoverCheck 12 (childHL (childHL (childHH thetaAboveCell1110))) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childHL (childHL (childHH thetaAboveCell1110)))
    e24KC2ThetaAboveNode11103220 e24KC2ThetaAboveNode11103221 e24KC2ThetaAboveLeaf11103222
      e24KC2ThetaAboveLeaf11103223

theorem e24KC2ThetaAboveNode1110323 :
    adaptiveCoverCheck 12 (childHH (childHL (childHH thetaAboveCell1110))) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childHH (childHL (childHH thetaAboveCell1110)))
    e24KC2ThetaAboveNode11103230 e24KC2ThetaAboveNode11103231 e24KC2ThetaAboveLeaf11103232
      e24KC2ThetaAboveLeaf11103233

theorem e24KC2ThetaAboveNode1110330 :
    adaptiveCoverCheck 12 (childLL (childHH (childHH thetaAboveCell1110))) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childLL (childHH (childHH thetaAboveCell1110)))
    e24KC2ThetaAboveLeaf11103300 e24KC2ThetaAboveLeaf11103301 e24KC2ThetaAboveNode11103302
      e24KC2ThetaAboveNode11103303

theorem e24KC2ThetaAboveNode1110331 :
    adaptiveCoverCheck 12 (childLH (childHH (childHH thetaAboveCell1110))) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childLH (childHH (childHH thetaAboveCell1110)))
    e24KC2ThetaAboveLeaf11103310 e24KC2ThetaAboveLeaf11103311 e24KC2ThetaAboveNode11103312
      e24KC2ThetaAboveNode11103313

theorem e24KC2ThetaAboveNode1110332 :
    adaptiveCoverCheck 12 (childHL (childHH (childHH thetaAboveCell1110))) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childHL (childHH (childHH thetaAboveCell1110)))
    e24KC2ThetaAboveNode11103320 e24KC2ThetaAboveNode11103321 e24KC2ThetaAboveLeaf11103322
      e24KC2ThetaAboveLeaf11103323

theorem e24KC2ThetaAboveNode1110333 :
    adaptiveCoverCheck 12 (childHH (childHH (childHH thetaAboveCell1110))) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childHH (childHH (childHH thetaAboveCell1110)))
    e24KC2ThetaAboveNode11103330 e24KC2ThetaAboveNode11103331 e24KC2ThetaAboveLeaf11103332
      e24KC2ThetaAboveLeaf11103333

theorem e24KC2ThetaAboveNode1111220 :
    adaptiveCoverCheck 12 (childLL (childHL (childHL thetaAboveCell1111))) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childLL (childHL (childHL thetaAboveCell1111)))
    e24KC2ThetaAboveLeaf11112200 e24KC2ThetaAboveLeaf11112201 e24KC2ThetaAboveNode11112202
      e24KC2ThetaAboveNode11112203

theorem e24KC2ThetaAboveNode1111221 :
    adaptiveCoverCheck 12 (childLH (childHL (childHL thetaAboveCell1111))) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childLH (childHL (childHL thetaAboveCell1111)))
    e24KC2ThetaAboveLeaf11112210 e24KC2ThetaAboveLeaf11112211 e24KC2ThetaAboveNode11112212
      e24KC2ThetaAboveNode11112213

theorem e24KC2ThetaAboveNode1111222 :
    adaptiveCoverCheck 12 (childHL (childHL (childHL thetaAboveCell1111))) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childHL (childHL (childHL thetaAboveCell1111)))
    e24KC2ThetaAboveNode11112220 e24KC2ThetaAboveNode11112221 e24KC2ThetaAboveLeaf11112222
      e24KC2ThetaAboveLeaf11112223

theorem e24KC2ThetaAboveNode1111223 :
    adaptiveCoverCheck 12 (childHH (childHL (childHL thetaAboveCell1111))) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childHH (childHL (childHL thetaAboveCell1111)))
    e24KC2ThetaAboveNode11112230 e24KC2ThetaAboveNode11112231 e24KC2ThetaAboveLeaf11112232
      e24KC2ThetaAboveLeaf11112233

theorem e24KC2ThetaAboveNode1111230 :
    adaptiveCoverCheck 12 (childLL (childHH (childHL thetaAboveCell1111))) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childLL (childHH (childHL thetaAboveCell1111)))
    e24KC2ThetaAboveLeaf11112300 e24KC2ThetaAboveLeaf11112301 e24KC2ThetaAboveNode11112302
      e24KC2ThetaAboveNode11112303

theorem e24KC2ThetaAboveNode1111231 :
    adaptiveCoverCheck 12 (childLH (childHH (childHL thetaAboveCell1111))) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childLH (childHH (childHL thetaAboveCell1111)))
    e24KC2ThetaAboveLeaf11112310 e24KC2ThetaAboveLeaf11112311 e24KC2ThetaAboveNode11112312
      e24KC2ThetaAboveNode11112313

theorem e24KC2ThetaAboveNode1111232 :
    adaptiveCoverCheck 12 (childHL (childHH (childHL thetaAboveCell1111))) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childHL (childHH (childHL thetaAboveCell1111)))
    e24KC2ThetaAboveNode11112320 e24KC2ThetaAboveNode11112321 e24KC2ThetaAboveLeaf11112322
      e24KC2ThetaAboveLeaf11112323

theorem e24KC2ThetaAboveNode1111233 :
    adaptiveCoverCheck 12 (childHH (childHH (childHL thetaAboveCell1111))) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childHH (childHH (childHL thetaAboveCell1111)))
    e24KC2ThetaAboveNode11112330 e24KC2ThetaAboveNode11112331 e24KC2ThetaAboveNode11112332
      e24KC2ThetaAboveNode11112333

theorem e24KC2ThetaAboveNode1111320 :
    adaptiveCoverCheck 12 (childLL (childHL (childHH thetaAboveCell1111))) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childLL (childHL (childHH thetaAboveCell1111)))
    e24KC2ThetaAboveLeaf11113200 e24KC2ThetaAboveLeaf11113201 e24KC2ThetaAboveNode11113202
      e24KC2ThetaAboveNode11113203

theorem e24KC2ThetaAboveNode1111321 :
    adaptiveCoverCheck 12 (childLH (childHL (childHH thetaAboveCell1111))) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childLH (childHL (childHH thetaAboveCell1111)))
    e24KC2ThetaAboveLeaf11113210 e24KC2ThetaAboveLeaf11113211 e24KC2ThetaAboveNode11113212
      e24KC2ThetaAboveNode11113213

theorem e24KC2ThetaAboveNode1111322 :
    adaptiveCoverCheck 12 (childHL (childHL (childHH thetaAboveCell1111))) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childHL (childHL (childHH thetaAboveCell1111)))
    e24KC2ThetaAboveNode11113220 e24KC2ThetaAboveNode11113221 e24KC2ThetaAboveNode11113222
      e24KC2ThetaAboveNode11113223

theorem e24KC2ThetaAboveNode1111323 :
    adaptiveCoverCheck 12 (childHH (childHL (childHH thetaAboveCell1111))) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childHH (childHL (childHH thetaAboveCell1111)))
    e24KC2ThetaAboveNode11113230 e24KC2ThetaAboveNode11113231 e24KC2ThetaAboveNode11113232
      e24KC2ThetaAboveNode11113233

theorem e24KC2ThetaAboveNode1111330 :
    adaptiveCoverCheck 12 (childLL (childHH (childHH thetaAboveCell1111))) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childLL (childHH (childHH thetaAboveCell1111)))
    e24KC2ThetaAboveLeaf11113300 e24KC2ThetaAboveLeaf11113301 e24KC2ThetaAboveNode11113302
      e24KC2ThetaAboveNode11113303

theorem e24KC2ThetaAboveNode1111331 :
    adaptiveCoverCheck 12 (childLH (childHH (childHH thetaAboveCell1111))) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childLH (childHH (childHH thetaAboveCell1111)))
    e24KC2ThetaAboveLeaf11113310 e24KC2ThetaAboveLeaf11113311 e24KC2ThetaAboveNode11113312
      e24KC2ThetaAboveNode11113313

theorem e24KC2ThetaAboveNode1111332 :
    adaptiveCoverCheck 12 (childHL (childHH (childHH thetaAboveCell1111))) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childHL (childHH (childHH thetaAboveCell1111)))
    e24KC2ThetaAboveNode11113320 e24KC2ThetaAboveNode11113321 e24KC2ThetaAboveNode11113322
      e24KC2ThetaAboveNode11113323

theorem e24KC2ThetaAboveNode1111333 :
    adaptiveCoverCheck 12 (childHH (childHH (childHH thetaAboveCell1111))) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childHH (childHH (childHH thetaAboveCell1111)))
    e24KC2ThetaAboveNode11113330 e24KC2ThetaAboveNode11113331 e24KC2ThetaAboveNode11113332
      e24KC2ThetaAboveNode11113333

theorem e24KC2ThetaAboveNode000020 :
    adaptiveCoverCheck 13 (childLL (childHL thetaAboveCell0000)) = true :=
  adaptiveCoverCheck_succ_of_children 12 (childLL (childHL thetaAboveCell0000))
    e24KC2ThetaAboveLeaf0000200 e24KC2ThetaAboveLeaf0000201 e24KC2ThetaAboveNode0000202
      e24KC2ThetaAboveNode0000203

theorem e24KC2ThetaAboveNode000021 :
    adaptiveCoverCheck 13 (childLH (childHL thetaAboveCell0000)) = true :=
  adaptiveCoverCheck_succ_of_children 12 (childLH (childHL thetaAboveCell0000))
    e24KC2ThetaAboveLeaf0000210 e24KC2ThetaAboveLeaf0000211 e24KC2ThetaAboveNode0000212
      e24KC2ThetaAboveNode0000213

theorem e24KC2ThetaAboveNode000022 :
    adaptiveCoverCheck 13 (childHL (childHL thetaAboveCell0000)) = true :=
  adaptiveCoverCheck_succ_of_children 12 (childHL (childHL thetaAboveCell0000))
    e24KC2ThetaAboveNode0000220 e24KC2ThetaAboveNode0000221 e24KC2ThetaAboveNode0000222
      e24KC2ThetaAboveNode0000223

theorem e24KC2ThetaAboveNode000023 :
    adaptiveCoverCheck 13 (childHH (childHL thetaAboveCell0000)) = true :=
  adaptiveCoverCheck_succ_of_children 12 (childHH (childHL thetaAboveCell0000))
    e24KC2ThetaAboveNode0000230 e24KC2ThetaAboveNode0000231 e24KC2ThetaAboveNode0000232
      e24KC2ThetaAboveNode0000233

theorem e24KC2ThetaAboveNode000030 :
    adaptiveCoverCheck 13 (childLL (childHH thetaAboveCell0000)) = true :=
  adaptiveCoverCheck_succ_of_children 12 (childLL (childHH thetaAboveCell0000))
    e24KC2ThetaAboveLeaf0000300 e24KC2ThetaAboveLeaf0000301 e24KC2ThetaAboveNode0000302
      e24KC2ThetaAboveNode0000303

theorem e24KC2ThetaAboveNode000031 :
    adaptiveCoverCheck 13 (childLH (childHH thetaAboveCell0000)) = true :=
  adaptiveCoverCheck_succ_of_children 12 (childLH (childHH thetaAboveCell0000))
    e24KC2ThetaAboveLeaf0000310 e24KC2ThetaAboveLeaf0000311 e24KC2ThetaAboveNode0000312
      e24KC2ThetaAboveNode0000313

theorem e24KC2ThetaAboveNode000032 :
    adaptiveCoverCheck 13 (childHL (childHH thetaAboveCell0000)) = true :=
  adaptiveCoverCheck_succ_of_children 12 (childHL (childHH thetaAboveCell0000))
    e24KC2ThetaAboveNode0000320 e24KC2ThetaAboveNode0000321 e24KC2ThetaAboveNode0000322
      e24KC2ThetaAboveNode0000323

theorem e24KC2ThetaAboveNode000033 :
    adaptiveCoverCheck 13 (childHH (childHH thetaAboveCell0000)) = true :=
  adaptiveCoverCheck_succ_of_children 12 (childHH (childHH thetaAboveCell0000))
    e24KC2ThetaAboveNode0000330 e24KC2ThetaAboveNode0000331 e24KC2ThetaAboveNode0000332
      e24KC2ThetaAboveNode0000333

theorem e24KC2ThetaAboveNode000120 :
    adaptiveCoverCheck 13 (childLL (childHL thetaAboveCell0001)) = true :=
  adaptiveCoverCheck_succ_of_children 12 (childLL (childHL thetaAboveCell0001))
    e24KC2ThetaAboveLeaf0001200 e24KC2ThetaAboveLeaf0001201 e24KC2ThetaAboveNode0001202
      e24KC2ThetaAboveNode0001203

theorem e24KC2ThetaAboveNode000121 :
    adaptiveCoverCheck 13 (childLH (childHL thetaAboveCell0001)) = true :=
  adaptiveCoverCheck_succ_of_children 12 (childLH (childHL thetaAboveCell0001))
    e24KC2ThetaAboveLeaf0001210 e24KC2ThetaAboveLeaf0001211 e24KC2ThetaAboveNode0001212
      e24KC2ThetaAboveNode0001213

theorem e24KC2ThetaAboveNode000122 :
    adaptiveCoverCheck 13 (childHL (childHL thetaAboveCell0001)) = true :=
  adaptiveCoverCheck_succ_of_children 12 (childHL (childHL thetaAboveCell0001))
    e24KC2ThetaAboveNode0001220 e24KC2ThetaAboveNode0001221 e24KC2ThetaAboveNode0001222
      e24KC2ThetaAboveNode0001223

theorem e24KC2ThetaAboveNode000123 :
    adaptiveCoverCheck 13 (childHH (childHL thetaAboveCell0001)) = true :=
  adaptiveCoverCheck_succ_of_children 12 (childHH (childHL thetaAboveCell0001))
    e24KC2ThetaAboveNode0001230 e24KC2ThetaAboveNode0001231 e24KC2ThetaAboveNode0001232
      e24KC2ThetaAboveNode0001233

theorem e24KC2ThetaAboveNode000130 :
    adaptiveCoverCheck 13 (childLL (childHH thetaAboveCell0001)) = true :=
  adaptiveCoverCheck_succ_of_children 12 (childLL (childHH thetaAboveCell0001))
    e24KC2ThetaAboveLeaf0001300 e24KC2ThetaAboveLeaf0001301 e24KC2ThetaAboveNode0001302
      e24KC2ThetaAboveNode0001303

theorem e24KC2ThetaAboveNode000131 :
    adaptiveCoverCheck 13 (childLH (childHH thetaAboveCell0001)) = true :=
  adaptiveCoverCheck_succ_of_children 12 (childLH (childHH thetaAboveCell0001))
    e24KC2ThetaAboveLeaf0001310 e24KC2ThetaAboveLeaf0001311 e24KC2ThetaAboveNode0001312
      e24KC2ThetaAboveNode0001313

theorem e24KC2ThetaAboveNode000132 :
    adaptiveCoverCheck 13 (childHL (childHH thetaAboveCell0001)) = true :=
  adaptiveCoverCheck_succ_of_children 12 (childHL (childHH thetaAboveCell0001))
    e24KC2ThetaAboveNode0001320 e24KC2ThetaAboveNode0001321 e24KC2ThetaAboveNode0001322
      e24KC2ThetaAboveNode0001323

theorem e24KC2ThetaAboveNode000133 :
    adaptiveCoverCheck 13 (childHH (childHH thetaAboveCell0001)) = true :=
  adaptiveCoverCheck_succ_of_children 12 (childHH (childHH thetaAboveCell0001))
    e24KC2ThetaAboveNode0001330 e24KC2ThetaAboveNode0001331 e24KC2ThetaAboveNode0001332
      e24KC2ThetaAboveNode0001333

theorem e24KC2ThetaAboveNode000200 :
    adaptiveCoverCheck 13 (childLL (childLL thetaAboveCell0002)) = true :=
  adaptiveCoverCheck_succ_of_children 12 (childLL (childLL thetaAboveCell0002))
    e24KC2ThetaAboveLeaf0002000 e24KC2ThetaAboveLeaf0002001 e24KC2ThetaAboveLeaf0002002
      e24KC2ThetaAboveLeaf0002003

theorem e24KC2ThetaAboveNode000201 :
    adaptiveCoverCheck 13 (childLH (childLL thetaAboveCell0002)) = true :=
  adaptiveCoverCheck_succ_of_children 12 (childLH (childLL thetaAboveCell0002))
    e24KC2ThetaAboveLeaf0002010 e24KC2ThetaAboveLeaf0002011 e24KC2ThetaAboveLeaf0002012
      e24KC2ThetaAboveLeaf0002013

theorem e24KC2ThetaAboveNode000210 :
    adaptiveCoverCheck 13 (childLL (childLH thetaAboveCell0002)) = true :=
  adaptiveCoverCheck_succ_of_children 12 (childLL (childLH thetaAboveCell0002))
    e24KC2ThetaAboveLeaf0002100 e24KC2ThetaAboveLeaf0002101 e24KC2ThetaAboveLeaf0002102
      e24KC2ThetaAboveLeaf0002103

theorem e24KC2ThetaAboveNode000211 :
    adaptiveCoverCheck 13 (childLH (childLH thetaAboveCell0002)) = true :=
  adaptiveCoverCheck_succ_of_children 12 (childLH (childLH thetaAboveCell0002))
    e24KC2ThetaAboveLeaf0002110 e24KC2ThetaAboveLeaf0002111 e24KC2ThetaAboveLeaf0002112
      e24KC2ThetaAboveLeaf0002113

theorem e24KC2ThetaAboveNode000300 :
    adaptiveCoverCheck 13 (childLL (childLL thetaAboveCell0003)) = true :=
  adaptiveCoverCheck_succ_of_children 12 (childLL (childLL thetaAboveCell0003))
    e24KC2ThetaAboveLeaf0003000 e24KC2ThetaAboveLeaf0003001 e24KC2ThetaAboveLeaf0003002
      e24KC2ThetaAboveLeaf0003003

theorem e24KC2ThetaAboveNode000301 :
    adaptiveCoverCheck 13 (childLH (childLL thetaAboveCell0003)) = true :=
  adaptiveCoverCheck_succ_of_children 12 (childLH (childLL thetaAboveCell0003))
    e24KC2ThetaAboveLeaf0003010 e24KC2ThetaAboveLeaf0003011 e24KC2ThetaAboveLeaf0003012
      e24KC2ThetaAboveLeaf0003013

theorem e24KC2ThetaAboveNode000310 :
    adaptiveCoverCheck 13 (childLL (childLH thetaAboveCell0003)) = true :=
  adaptiveCoverCheck_succ_of_children 12 (childLL (childLH thetaAboveCell0003))
    e24KC2ThetaAboveLeaf0003100 e24KC2ThetaAboveLeaf0003101 e24KC2ThetaAboveLeaf0003102
      e24KC2ThetaAboveLeaf0003103

theorem e24KC2ThetaAboveNode000311 :
    adaptiveCoverCheck 13 (childLH (childLH thetaAboveCell0003)) = true :=
  adaptiveCoverCheck_succ_of_children 12 (childLH (childLH thetaAboveCell0003))
    e24KC2ThetaAboveLeaf0003110 e24KC2ThetaAboveLeaf0003111 e24KC2ThetaAboveLeaf0003112
      e24KC2ThetaAboveLeaf0003113

theorem e24KC2ThetaAboveNode001020 :
    adaptiveCoverCheck 13 (childLL (childHL thetaAboveCell0010)) = true :=
  adaptiveCoverCheck_succ_of_children 12 (childLL (childHL thetaAboveCell0010))
    e24KC2ThetaAboveLeaf0010200 e24KC2ThetaAboveLeaf0010201 e24KC2ThetaAboveNode0010202
      e24KC2ThetaAboveNode0010203

theorem e24KC2ThetaAboveNode001021 :
    adaptiveCoverCheck 13 (childLH (childHL thetaAboveCell0010)) = true :=
  adaptiveCoverCheck_succ_of_children 12 (childLH (childHL thetaAboveCell0010))
    e24KC2ThetaAboveLeaf0010210 e24KC2ThetaAboveLeaf0010211 e24KC2ThetaAboveNode0010212
      e24KC2ThetaAboveNode0010213

theorem e24KC2ThetaAboveNode001022 :
    adaptiveCoverCheck 13 (childHL (childHL thetaAboveCell0010)) = true :=
  adaptiveCoverCheck_succ_of_children 12 (childHL (childHL thetaAboveCell0010))
    e24KC2ThetaAboveNode0010220 e24KC2ThetaAboveNode0010221 e24KC2ThetaAboveNode0010222
      e24KC2ThetaAboveNode0010223

theorem e24KC2ThetaAboveNode001023 :
    adaptiveCoverCheck 13 (childHH (childHL thetaAboveCell0010)) = true :=
  adaptiveCoverCheck_succ_of_children 12 (childHH (childHL thetaAboveCell0010))
    e24KC2ThetaAboveNode0010230 e24KC2ThetaAboveNode0010231 e24KC2ThetaAboveNode0010232
      e24KC2ThetaAboveNode0010233

theorem e24KC2ThetaAboveNode001030 :
    adaptiveCoverCheck 13 (childLL (childHH thetaAboveCell0010)) = true :=
  adaptiveCoverCheck_succ_of_children 12 (childLL (childHH thetaAboveCell0010))
    e24KC2ThetaAboveLeaf0010300 e24KC2ThetaAboveLeaf0010301 e24KC2ThetaAboveNode0010302
      e24KC2ThetaAboveNode0010303

theorem e24KC2ThetaAboveNode001031 :
    adaptiveCoverCheck 13 (childLH (childHH thetaAboveCell0010)) = true :=
  adaptiveCoverCheck_succ_of_children 12 (childLH (childHH thetaAboveCell0010))
    e24KC2ThetaAboveLeaf0010310 e24KC2ThetaAboveLeaf0010311 e24KC2ThetaAboveNode0010312
      e24KC2ThetaAboveNode0010313

theorem e24KC2ThetaAboveNode001032 :
    adaptiveCoverCheck 13 (childHL (childHH thetaAboveCell0010)) = true :=
  adaptiveCoverCheck_succ_of_children 12 (childHL (childHH thetaAboveCell0010))
    e24KC2ThetaAboveNode0010320 e24KC2ThetaAboveNode0010321 e24KC2ThetaAboveNode0010322
      e24KC2ThetaAboveNode0010323

theorem e24KC2ThetaAboveNode001033 :
    adaptiveCoverCheck 13 (childHH (childHH thetaAboveCell0010)) = true :=
  adaptiveCoverCheck_succ_of_children 12 (childHH (childHH thetaAboveCell0010))
    e24KC2ThetaAboveNode0010330 e24KC2ThetaAboveNode0010331 e24KC2ThetaAboveNode0010332
      e24KC2ThetaAboveNode0010333

theorem e24KC2ThetaAboveNode001120 :
    adaptiveCoverCheck 13 (childLL (childHL thetaAboveCell0011)) = true :=
  adaptiveCoverCheck_succ_of_children 12 (childLL (childHL thetaAboveCell0011))
    e24KC2ThetaAboveLeaf0011200 e24KC2ThetaAboveLeaf0011201 e24KC2ThetaAboveNode0011202
      e24KC2ThetaAboveNode0011203

theorem e24KC2ThetaAboveNode001121 :
    adaptiveCoverCheck 13 (childLH (childHL thetaAboveCell0011)) = true :=
  adaptiveCoverCheck_succ_of_children 12 (childLH (childHL thetaAboveCell0011))
    e24KC2ThetaAboveLeaf0011210 e24KC2ThetaAboveLeaf0011211 e24KC2ThetaAboveNode0011212
      e24KC2ThetaAboveNode0011213

theorem e24KC2ThetaAboveNode001122 :
    adaptiveCoverCheck 13 (childHL (childHL thetaAboveCell0011)) = true :=
  adaptiveCoverCheck_succ_of_children 12 (childHL (childHL thetaAboveCell0011))
    e24KC2ThetaAboveNode0011220 e24KC2ThetaAboveNode0011221 e24KC2ThetaAboveNode0011222
      e24KC2ThetaAboveNode0011223

theorem e24KC2ThetaAboveNode001123 :
    adaptiveCoverCheck 13 (childHH (childHL thetaAboveCell0011)) = true :=
  adaptiveCoverCheck_succ_of_children 12 (childHH (childHL thetaAboveCell0011))
    e24KC2ThetaAboveNode0011230 e24KC2ThetaAboveNode0011231 e24KC2ThetaAboveNode0011232
      e24KC2ThetaAboveNode0011233

theorem e24KC2ThetaAboveNode001130 :
    adaptiveCoverCheck 13 (childLL (childHH thetaAboveCell0011)) = true :=
  adaptiveCoverCheck_succ_of_children 12 (childLL (childHH thetaAboveCell0011))
    e24KC2ThetaAboveLeaf0011300 e24KC2ThetaAboveLeaf0011301 e24KC2ThetaAboveNode0011302
      e24KC2ThetaAboveNode0011303

theorem e24KC2ThetaAboveNode001131 :
    adaptiveCoverCheck 13 (childLH (childHH thetaAboveCell0011)) = true :=
  adaptiveCoverCheck_succ_of_children 12 (childLH (childHH thetaAboveCell0011))
    e24KC2ThetaAboveLeaf0011310 e24KC2ThetaAboveLeaf0011311 e24KC2ThetaAboveNode0011312
      e24KC2ThetaAboveNode0011313

theorem e24KC2ThetaAboveNode001132 :
    adaptiveCoverCheck 13 (childHL (childHH thetaAboveCell0011)) = true :=
  adaptiveCoverCheck_succ_of_children 12 (childHL (childHH thetaAboveCell0011))
    e24KC2ThetaAboveNode0011320 e24KC2ThetaAboveNode0011321 e24KC2ThetaAboveNode0011322
      e24KC2ThetaAboveNode0011323

theorem e24KC2ThetaAboveNode001133 :
    adaptiveCoverCheck 13 (childHH (childHH thetaAboveCell0011)) = true :=
  adaptiveCoverCheck_succ_of_children 12 (childHH (childHH thetaAboveCell0011))
    e24KC2ThetaAboveNode0011330 e24KC2ThetaAboveNode0011331 e24KC2ThetaAboveNode0011332
      e24KC2ThetaAboveNode0011333

theorem e24KC2ThetaAboveNode001200 :
    adaptiveCoverCheck 13 (childLL (childLL thetaAboveCell0012)) = true :=
  adaptiveCoverCheck_succ_of_children 12 (childLL (childLL thetaAboveCell0012))
    e24KC2ThetaAboveLeaf0012000 e24KC2ThetaAboveLeaf0012001 e24KC2ThetaAboveLeaf0012002
      e24KC2ThetaAboveLeaf0012003

theorem e24KC2ThetaAboveNode001201 :
    adaptiveCoverCheck 13 (childLH (childLL thetaAboveCell0012)) = true :=
  adaptiveCoverCheck_succ_of_children 12 (childLH (childLL thetaAboveCell0012))
    e24KC2ThetaAboveLeaf0012010 e24KC2ThetaAboveLeaf0012011 e24KC2ThetaAboveLeaf0012012
      e24KC2ThetaAboveLeaf0012013

theorem e24KC2ThetaAboveNode001210 :
    adaptiveCoverCheck 13 (childLL (childLH thetaAboveCell0012)) = true :=
  adaptiveCoverCheck_succ_of_children 12 (childLL (childLH thetaAboveCell0012))
    e24KC2ThetaAboveLeaf0012100 e24KC2ThetaAboveLeaf0012101 e24KC2ThetaAboveLeaf0012102
      e24KC2ThetaAboveLeaf0012103

theorem e24KC2ThetaAboveNode001211 :
    adaptiveCoverCheck 13 (childLH (childLH thetaAboveCell0012)) = true :=
  adaptiveCoverCheck_succ_of_children 12 (childLH (childLH thetaAboveCell0012))
    e24KC2ThetaAboveLeaf0012110 e24KC2ThetaAboveLeaf0012111 e24KC2ThetaAboveLeaf0012112
      e24KC2ThetaAboveLeaf0012113

theorem e24KC2ThetaAboveNode001300 :
    adaptiveCoverCheck 13 (childLL (childLL thetaAboveCell0013)) = true :=
  adaptiveCoverCheck_succ_of_children 12 (childLL (childLL thetaAboveCell0013))
    e24KC2ThetaAboveLeaf0013000 e24KC2ThetaAboveLeaf0013001 e24KC2ThetaAboveLeaf0013002
      e24KC2ThetaAboveLeaf0013003

theorem e24KC2ThetaAboveNode001301 :
    adaptiveCoverCheck 13 (childLH (childLL thetaAboveCell0013)) = true :=
  adaptiveCoverCheck_succ_of_children 12 (childLH (childLL thetaAboveCell0013))
    e24KC2ThetaAboveLeaf0013010 e24KC2ThetaAboveLeaf0013011 e24KC2ThetaAboveLeaf0013012
      e24KC2ThetaAboveLeaf0013013

theorem e24KC2ThetaAboveNode001310 :
    adaptiveCoverCheck 13 (childLL (childLH thetaAboveCell0013)) = true :=
  adaptiveCoverCheck_succ_of_children 12 (childLL (childLH thetaAboveCell0013))
    e24KC2ThetaAboveLeaf0013100 e24KC2ThetaAboveLeaf0013101 e24KC2ThetaAboveLeaf0013102
      e24KC2ThetaAboveLeaf0013103

theorem e24KC2ThetaAboveNode001311 :
    adaptiveCoverCheck 13 (childLH (childLH thetaAboveCell0013)) = true :=
  adaptiveCoverCheck_succ_of_children 12 (childLH (childLH thetaAboveCell0013))
    e24KC2ThetaAboveLeaf0013110 e24KC2ThetaAboveLeaf0013111 e24KC2ThetaAboveLeaf0013112
      e24KC2ThetaAboveLeaf0013113

theorem e24KC2ThetaAboveNode010020 :
    adaptiveCoverCheck 13 (childLL (childHL thetaAboveCell0100)) = true :=
  adaptiveCoverCheck_succ_of_children 12 (childLL (childHL thetaAboveCell0100))
    e24KC2ThetaAboveLeaf0100200 e24KC2ThetaAboveLeaf0100201 e24KC2ThetaAboveNode0100202
      e24KC2ThetaAboveNode0100203

theorem e24KC2ThetaAboveNode010021 :
    adaptiveCoverCheck 13 (childLH (childHL thetaAboveCell0100)) = true :=
  adaptiveCoverCheck_succ_of_children 12 (childLH (childHL thetaAboveCell0100))
    e24KC2ThetaAboveLeaf0100210 e24KC2ThetaAboveLeaf0100211 e24KC2ThetaAboveNode0100212
      e24KC2ThetaAboveNode0100213

theorem e24KC2ThetaAboveNode010022 :
    adaptiveCoverCheck 13 (childHL (childHL thetaAboveCell0100)) = true :=
  adaptiveCoverCheck_succ_of_children 12 (childHL (childHL thetaAboveCell0100))
    e24KC2ThetaAboveNode0100220 e24KC2ThetaAboveNode0100221 e24KC2ThetaAboveNode0100222
      e24KC2ThetaAboveNode0100223

theorem e24KC2ThetaAboveNode010023 :
    adaptiveCoverCheck 13 (childHH (childHL thetaAboveCell0100)) = true :=
  adaptiveCoverCheck_succ_of_children 12 (childHH (childHL thetaAboveCell0100))
    e24KC2ThetaAboveNode0100230 e24KC2ThetaAboveNode0100231 e24KC2ThetaAboveNode0100232
      e24KC2ThetaAboveNode0100233

theorem e24KC2ThetaAboveNode010030 :
    adaptiveCoverCheck 13 (childLL (childHH thetaAboveCell0100)) = true :=
  adaptiveCoverCheck_succ_of_children 12 (childLL (childHH thetaAboveCell0100))
    e24KC2ThetaAboveLeaf0100300 e24KC2ThetaAboveLeaf0100301 e24KC2ThetaAboveNode0100302
      e24KC2ThetaAboveNode0100303

theorem e24KC2ThetaAboveNode010031 :
    adaptiveCoverCheck 13 (childLH (childHH thetaAboveCell0100)) = true :=
  adaptiveCoverCheck_succ_of_children 12 (childLH (childHH thetaAboveCell0100))
    e24KC2ThetaAboveLeaf0100310 e24KC2ThetaAboveLeaf0100311 e24KC2ThetaAboveNode0100312
      e24KC2ThetaAboveNode0100313

theorem e24KC2ThetaAboveNode010032 :
    adaptiveCoverCheck 13 (childHL (childHH thetaAboveCell0100)) = true :=
  adaptiveCoverCheck_succ_of_children 12 (childHL (childHH thetaAboveCell0100))
    e24KC2ThetaAboveNode0100320 e24KC2ThetaAboveNode0100321 e24KC2ThetaAboveNode0100322
      e24KC2ThetaAboveNode0100323

theorem e24KC2ThetaAboveNode010033 :
    adaptiveCoverCheck 13 (childHH (childHH thetaAboveCell0100)) = true :=
  adaptiveCoverCheck_succ_of_children 12 (childHH (childHH thetaAboveCell0100))
    e24KC2ThetaAboveNode0100330 e24KC2ThetaAboveNode0100331 e24KC2ThetaAboveNode0100332
      e24KC2ThetaAboveNode0100333

theorem e24KC2ThetaAboveNode010120 :
    adaptiveCoverCheck 13 (childLL (childHL thetaAboveCell0101)) = true :=
  adaptiveCoverCheck_succ_of_children 12 (childLL (childHL thetaAboveCell0101))
    e24KC2ThetaAboveLeaf0101200 e24KC2ThetaAboveLeaf0101201 e24KC2ThetaAboveNode0101202
      e24KC2ThetaAboveNode0101203

theorem e24KC2ThetaAboveNode010121 :
    adaptiveCoverCheck 13 (childLH (childHL thetaAboveCell0101)) = true :=
  adaptiveCoverCheck_succ_of_children 12 (childLH (childHL thetaAboveCell0101))
    e24KC2ThetaAboveLeaf0101210 e24KC2ThetaAboveLeaf0101211 e24KC2ThetaAboveNode0101212
      e24KC2ThetaAboveNode0101213

theorem e24KC2ThetaAboveNode010122 :
    adaptiveCoverCheck 13 (childHL (childHL thetaAboveCell0101)) = true :=
  adaptiveCoverCheck_succ_of_children 12 (childHL (childHL thetaAboveCell0101))
    e24KC2ThetaAboveNode0101220 e24KC2ThetaAboveNode0101221 e24KC2ThetaAboveNode0101222
      e24KC2ThetaAboveNode0101223

theorem e24KC2ThetaAboveNode010123 :
    adaptiveCoverCheck 13 (childHH (childHL thetaAboveCell0101)) = true :=
  adaptiveCoverCheck_succ_of_children 12 (childHH (childHL thetaAboveCell0101))
    e24KC2ThetaAboveNode0101230 e24KC2ThetaAboveNode0101231 e24KC2ThetaAboveNode0101232
      e24KC2ThetaAboveNode0101233

theorem e24KC2ThetaAboveNode010130 :
    adaptiveCoverCheck 13 (childLL (childHH thetaAboveCell0101)) = true :=
  adaptiveCoverCheck_succ_of_children 12 (childLL (childHH thetaAboveCell0101))
    e24KC2ThetaAboveLeaf0101300 e24KC2ThetaAboveLeaf0101301 e24KC2ThetaAboveNode0101302
      e24KC2ThetaAboveNode0101303

theorem e24KC2ThetaAboveNode010131 :
    adaptiveCoverCheck 13 (childLH (childHH thetaAboveCell0101)) = true :=
  adaptiveCoverCheck_succ_of_children 12 (childLH (childHH thetaAboveCell0101))
    e24KC2ThetaAboveLeaf0101310 e24KC2ThetaAboveLeaf0101311 e24KC2ThetaAboveNode0101312
      e24KC2ThetaAboveNode0101313

theorem e24KC2ThetaAboveNode010132 :
    adaptiveCoverCheck 13 (childHL (childHH thetaAboveCell0101)) = true :=
  adaptiveCoverCheck_succ_of_children 12 (childHL (childHH thetaAboveCell0101))
    e24KC2ThetaAboveNode0101320 e24KC2ThetaAboveNode0101321 e24KC2ThetaAboveNode0101322
      e24KC2ThetaAboveNode0101323

theorem e24KC2ThetaAboveNode010133 :
    adaptiveCoverCheck 13 (childHH (childHH thetaAboveCell0101)) = true :=
  adaptiveCoverCheck_succ_of_children 12 (childHH (childHH thetaAboveCell0101))
    e24KC2ThetaAboveNode0101330 e24KC2ThetaAboveNode0101331 e24KC2ThetaAboveNode0101332
      e24KC2ThetaAboveNode0101333

theorem e24KC2ThetaAboveNode010200 :
    adaptiveCoverCheck 13 (childLL (childLL thetaAboveCell0102)) = true :=
  adaptiveCoverCheck_succ_of_children 12 (childLL (childLL thetaAboveCell0102))
    e24KC2ThetaAboveLeaf0102000 e24KC2ThetaAboveLeaf0102001 e24KC2ThetaAboveLeaf0102002
      e24KC2ThetaAboveLeaf0102003

theorem e24KC2ThetaAboveNode010201 :
    adaptiveCoverCheck 13 (childLH (childLL thetaAboveCell0102)) = true :=
  adaptiveCoverCheck_succ_of_children 12 (childLH (childLL thetaAboveCell0102))
    e24KC2ThetaAboveLeaf0102010 e24KC2ThetaAboveLeaf0102011 e24KC2ThetaAboveLeaf0102012
      e24KC2ThetaAboveLeaf0102013

theorem e24KC2ThetaAboveNode010210 :
    adaptiveCoverCheck 13 (childLL (childLH thetaAboveCell0102)) = true :=
  adaptiveCoverCheck_succ_of_children 12 (childLL (childLH thetaAboveCell0102))
    e24KC2ThetaAboveLeaf0102100 e24KC2ThetaAboveLeaf0102101 e24KC2ThetaAboveLeaf0102102
      e24KC2ThetaAboveLeaf0102103

theorem e24KC2ThetaAboveNode010211 :
    adaptiveCoverCheck 13 (childLH (childLH thetaAboveCell0102)) = true :=
  adaptiveCoverCheck_succ_of_children 12 (childLH (childLH thetaAboveCell0102))
    e24KC2ThetaAboveLeaf0102110 e24KC2ThetaAboveLeaf0102111 e24KC2ThetaAboveLeaf0102112
      e24KC2ThetaAboveLeaf0102113

theorem e24KC2ThetaAboveNode010300 :
    adaptiveCoverCheck 13 (childLL (childLL thetaAboveCell0103)) = true :=
  adaptiveCoverCheck_succ_of_children 12 (childLL (childLL thetaAboveCell0103))
    e24KC2ThetaAboveLeaf0103000 e24KC2ThetaAboveLeaf0103001 e24KC2ThetaAboveLeaf0103002
      e24KC2ThetaAboveLeaf0103003

theorem e24KC2ThetaAboveNode010301 :
    adaptiveCoverCheck 13 (childLH (childLL thetaAboveCell0103)) = true :=
  adaptiveCoverCheck_succ_of_children 12 (childLH (childLL thetaAboveCell0103))
    e24KC2ThetaAboveLeaf0103010 e24KC2ThetaAboveLeaf0103011 e24KC2ThetaAboveLeaf0103012
      e24KC2ThetaAboveLeaf0103013

theorem e24KC2ThetaAboveNode010310 :
    adaptiveCoverCheck 13 (childLL (childLH thetaAboveCell0103)) = true :=
  adaptiveCoverCheck_succ_of_children 12 (childLL (childLH thetaAboveCell0103))
    e24KC2ThetaAboveLeaf0103100 e24KC2ThetaAboveLeaf0103101 e24KC2ThetaAboveLeaf0103102
      e24KC2ThetaAboveLeaf0103103

theorem e24KC2ThetaAboveNode010311 :
    adaptiveCoverCheck 13 (childLH (childLH thetaAboveCell0103)) = true :=
  adaptiveCoverCheck_succ_of_children 12 (childLH (childLH thetaAboveCell0103))
    e24KC2ThetaAboveLeaf0103110 e24KC2ThetaAboveLeaf0103111 e24KC2ThetaAboveLeaf0103112
      e24KC2ThetaAboveLeaf0103113

theorem e24KC2ThetaAboveNode011020 :
    adaptiveCoverCheck 13 (childLL (childHL thetaAboveCell0110)) = true :=
  adaptiveCoverCheck_succ_of_children 12 (childLL (childHL thetaAboveCell0110))
    e24KC2ThetaAboveLeaf0110200 e24KC2ThetaAboveLeaf0110201 e24KC2ThetaAboveNode0110202
      e24KC2ThetaAboveNode0110203

theorem e24KC2ThetaAboveNode011021 :
    adaptiveCoverCheck 13 (childLH (childHL thetaAboveCell0110)) = true :=
  adaptiveCoverCheck_succ_of_children 12 (childLH (childHL thetaAboveCell0110))
    e24KC2ThetaAboveLeaf0110210 e24KC2ThetaAboveLeaf0110211 e24KC2ThetaAboveNode0110212
      e24KC2ThetaAboveNode0110213

theorem e24KC2ThetaAboveNode011022 :
    adaptiveCoverCheck 13 (childHL (childHL thetaAboveCell0110)) = true :=
  adaptiveCoverCheck_succ_of_children 12 (childHL (childHL thetaAboveCell0110))
    e24KC2ThetaAboveNode0110220 e24KC2ThetaAboveNode0110221 e24KC2ThetaAboveNode0110222
      e24KC2ThetaAboveNode0110223

theorem e24KC2ThetaAboveNode011023 :
    adaptiveCoverCheck 13 (childHH (childHL thetaAboveCell0110)) = true :=
  adaptiveCoverCheck_succ_of_children 12 (childHH (childHL thetaAboveCell0110))
    e24KC2ThetaAboveNode0110230 e24KC2ThetaAboveNode0110231 e24KC2ThetaAboveNode0110232
      e24KC2ThetaAboveNode0110233

theorem e24KC2ThetaAboveNode011030 :
    adaptiveCoverCheck 13 (childLL (childHH thetaAboveCell0110)) = true :=
  adaptiveCoverCheck_succ_of_children 12 (childLL (childHH thetaAboveCell0110))
    e24KC2ThetaAboveLeaf0110300 e24KC2ThetaAboveLeaf0110301 e24KC2ThetaAboveNode0110302
      e24KC2ThetaAboveNode0110303

theorem e24KC2ThetaAboveNode011031 :
    adaptiveCoverCheck 13 (childLH (childHH thetaAboveCell0110)) = true :=
  adaptiveCoverCheck_succ_of_children 12 (childLH (childHH thetaAboveCell0110))
    e24KC2ThetaAboveLeaf0110310 e24KC2ThetaAboveLeaf0110311 e24KC2ThetaAboveNode0110312
      e24KC2ThetaAboveNode0110313

theorem e24KC2ThetaAboveNode011032 :
    adaptiveCoverCheck 13 (childHL (childHH thetaAboveCell0110)) = true :=
  adaptiveCoverCheck_succ_of_children 12 (childHL (childHH thetaAboveCell0110))
    e24KC2ThetaAboveNode0110320 e24KC2ThetaAboveNode0110321 e24KC2ThetaAboveNode0110322
      e24KC2ThetaAboveNode0110323

theorem e24KC2ThetaAboveNode011033 :
    adaptiveCoverCheck 13 (childHH (childHH thetaAboveCell0110)) = true :=
  adaptiveCoverCheck_succ_of_children 12 (childHH (childHH thetaAboveCell0110))
    e24KC2ThetaAboveNode0110330 e24KC2ThetaAboveNode0110331 e24KC2ThetaAboveNode0110332
      e24KC2ThetaAboveNode0110333

theorem e24KC2ThetaAboveNode011120 :
    adaptiveCoverCheck 13 (childLL (childHL thetaAboveCell0111)) = true :=
  adaptiveCoverCheck_succ_of_children 12 (childLL (childHL thetaAboveCell0111))
    e24KC2ThetaAboveLeaf0111200 e24KC2ThetaAboveLeaf0111201 e24KC2ThetaAboveNode0111202
      e24KC2ThetaAboveNode0111203

theorem e24KC2ThetaAboveNode011121 :
    adaptiveCoverCheck 13 (childLH (childHL thetaAboveCell0111)) = true :=
  adaptiveCoverCheck_succ_of_children 12 (childLH (childHL thetaAboveCell0111))
    e24KC2ThetaAboveLeaf0111210 e24KC2ThetaAboveLeaf0111211 e24KC2ThetaAboveNode0111212
      e24KC2ThetaAboveNode0111213

theorem e24KC2ThetaAboveNode011122 :
    adaptiveCoverCheck 13 (childHL (childHL thetaAboveCell0111)) = true :=
  adaptiveCoverCheck_succ_of_children 12 (childHL (childHL thetaAboveCell0111))
    e24KC2ThetaAboveNode0111220 e24KC2ThetaAboveNode0111221 e24KC2ThetaAboveNode0111222
      e24KC2ThetaAboveNode0111223

theorem e24KC2ThetaAboveNode011123 :
    adaptiveCoverCheck 13 (childHH (childHL thetaAboveCell0111)) = true :=
  adaptiveCoverCheck_succ_of_children 12 (childHH (childHL thetaAboveCell0111))
    e24KC2ThetaAboveNode0111230 e24KC2ThetaAboveNode0111231 e24KC2ThetaAboveNode0111232
      e24KC2ThetaAboveNode0111233

theorem e24KC2ThetaAboveNode011130 :
    adaptiveCoverCheck 13 (childLL (childHH thetaAboveCell0111)) = true :=
  adaptiveCoverCheck_succ_of_children 12 (childLL (childHH thetaAboveCell0111))
    e24KC2ThetaAboveLeaf0111300 e24KC2ThetaAboveLeaf0111301 e24KC2ThetaAboveNode0111302
      e24KC2ThetaAboveNode0111303

theorem e24KC2ThetaAboveNode011131 :
    adaptiveCoverCheck 13 (childLH (childHH thetaAboveCell0111)) = true :=
  adaptiveCoverCheck_succ_of_children 12 (childLH (childHH thetaAboveCell0111))
    e24KC2ThetaAboveLeaf0111310 e24KC2ThetaAboveLeaf0111311 e24KC2ThetaAboveNode0111312
      e24KC2ThetaAboveNode0111313

theorem e24KC2ThetaAboveNode011132 :
    adaptiveCoverCheck 13 (childHL (childHH thetaAboveCell0111)) = true :=
  adaptiveCoverCheck_succ_of_children 12 (childHL (childHH thetaAboveCell0111))
    e24KC2ThetaAboveNode0111320 e24KC2ThetaAboveNode0111321 e24KC2ThetaAboveNode0111322
      e24KC2ThetaAboveNode0111323

theorem e24KC2ThetaAboveNode011133 :
    adaptiveCoverCheck 13 (childHH (childHH thetaAboveCell0111)) = true :=
  adaptiveCoverCheck_succ_of_children 12 (childHH (childHH thetaAboveCell0111))
    e24KC2ThetaAboveNode0111330 e24KC2ThetaAboveNode0111331 e24KC2ThetaAboveNode0111332
      e24KC2ThetaAboveNode0111333

theorem e24KC2ThetaAboveNode011200 :
    adaptiveCoverCheck 13 (childLL (childLL thetaAboveCell0112)) = true :=
  adaptiveCoverCheck_succ_of_children 12 (childLL (childLL thetaAboveCell0112))
    e24KC2ThetaAboveLeaf0112000 e24KC2ThetaAboveLeaf0112001 e24KC2ThetaAboveLeaf0112002
      e24KC2ThetaAboveLeaf0112003

theorem e24KC2ThetaAboveNode011201 :
    adaptiveCoverCheck 13 (childLH (childLL thetaAboveCell0112)) = true :=
  adaptiveCoverCheck_succ_of_children 12 (childLH (childLL thetaAboveCell0112))
    e24KC2ThetaAboveLeaf0112010 e24KC2ThetaAboveLeaf0112011 e24KC2ThetaAboveLeaf0112012
      e24KC2ThetaAboveLeaf0112013

theorem e24KC2ThetaAboveNode011210 :
    adaptiveCoverCheck 13 (childLL (childLH thetaAboveCell0112)) = true :=
  adaptiveCoverCheck_succ_of_children 12 (childLL (childLH thetaAboveCell0112))
    e24KC2ThetaAboveLeaf0112100 e24KC2ThetaAboveLeaf0112101 e24KC2ThetaAboveLeaf0112102
      e24KC2ThetaAboveLeaf0112103

theorem e24KC2ThetaAboveNode011211 :
    adaptiveCoverCheck 13 (childLH (childLH thetaAboveCell0112)) = true :=
  adaptiveCoverCheck_succ_of_children 12 (childLH (childLH thetaAboveCell0112))
    e24KC2ThetaAboveLeaf0112110 e24KC2ThetaAboveLeaf0112111 e24KC2ThetaAboveLeaf0112112
      e24KC2ThetaAboveLeaf0112113

theorem e24KC2ThetaAboveNode011300 :
    adaptiveCoverCheck 13 (childLL (childLL thetaAboveCell0113)) = true :=
  adaptiveCoverCheck_succ_of_children 12 (childLL (childLL thetaAboveCell0113))
    e24KC2ThetaAboveLeaf0113000 e24KC2ThetaAboveLeaf0113001 e24KC2ThetaAboveLeaf0113002
      e24KC2ThetaAboveLeaf0113003

theorem e24KC2ThetaAboveNode011301 :
    adaptiveCoverCheck 13 (childLH (childLL thetaAboveCell0113)) = true :=
  adaptiveCoverCheck_succ_of_children 12 (childLH (childLL thetaAboveCell0113))
    e24KC2ThetaAboveLeaf0113010 e24KC2ThetaAboveLeaf0113011 e24KC2ThetaAboveLeaf0113012
      e24KC2ThetaAboveLeaf0113013

theorem e24KC2ThetaAboveNode011310 :
    adaptiveCoverCheck 13 (childLL (childLH thetaAboveCell0113)) = true :=
  adaptiveCoverCheck_succ_of_children 12 (childLL (childLH thetaAboveCell0113))
    e24KC2ThetaAboveLeaf0113100 e24KC2ThetaAboveLeaf0113101 e24KC2ThetaAboveLeaf0113102
      e24KC2ThetaAboveLeaf0113103

theorem e24KC2ThetaAboveNode011311 :
    adaptiveCoverCheck 13 (childLH (childLH thetaAboveCell0113)) = true :=
  adaptiveCoverCheck_succ_of_children 12 (childLH (childLH thetaAboveCell0113))
    e24KC2ThetaAboveLeaf0113110 e24KC2ThetaAboveLeaf0113111 e24KC2ThetaAboveLeaf0113112
      e24KC2ThetaAboveLeaf0113113

theorem e24KC2ThetaAboveNode100020 :
    adaptiveCoverCheck 13 (childLL (childHL thetaAboveCell1000)) = true :=
  adaptiveCoverCheck_succ_of_children 12 (childLL (childHL thetaAboveCell1000))
    e24KC2ThetaAboveLeaf1000200 e24KC2ThetaAboveLeaf1000201 e24KC2ThetaAboveNode1000202
      e24KC2ThetaAboveNode1000203

theorem e24KC2ThetaAboveNode100021 :
    adaptiveCoverCheck 13 (childLH (childHL thetaAboveCell1000)) = true :=
  adaptiveCoverCheck_succ_of_children 12 (childLH (childHL thetaAboveCell1000))
    e24KC2ThetaAboveLeaf1000210 e24KC2ThetaAboveLeaf1000211 e24KC2ThetaAboveNode1000212
      e24KC2ThetaAboveNode1000213

theorem e24KC2ThetaAboveNode100022 :
    adaptiveCoverCheck 13 (childHL (childHL thetaAboveCell1000)) = true :=
  adaptiveCoverCheck_succ_of_children 12 (childHL (childHL thetaAboveCell1000))
    e24KC2ThetaAboveNode1000220 e24KC2ThetaAboveNode1000221 e24KC2ThetaAboveNode1000222
      e24KC2ThetaAboveNode1000223

theorem e24KC2ThetaAboveNode100023 :
    adaptiveCoverCheck 13 (childHH (childHL thetaAboveCell1000)) = true :=
  adaptiveCoverCheck_succ_of_children 12 (childHH (childHL thetaAboveCell1000))
    e24KC2ThetaAboveNode1000230 e24KC2ThetaAboveNode1000231 e24KC2ThetaAboveNode1000232
      e24KC2ThetaAboveNode1000233

theorem e24KC2ThetaAboveNode100030 :
    adaptiveCoverCheck 13 (childLL (childHH thetaAboveCell1000)) = true :=
  adaptiveCoverCheck_succ_of_children 12 (childLL (childHH thetaAboveCell1000))
    e24KC2ThetaAboveLeaf1000300 e24KC2ThetaAboveLeaf1000301 e24KC2ThetaAboveNode1000302
      e24KC2ThetaAboveNode1000303

theorem e24KC2ThetaAboveNode100031 :
    adaptiveCoverCheck 13 (childLH (childHH thetaAboveCell1000)) = true :=
  adaptiveCoverCheck_succ_of_children 12 (childLH (childHH thetaAboveCell1000))
    e24KC2ThetaAboveLeaf1000310 e24KC2ThetaAboveLeaf1000311 e24KC2ThetaAboveNode1000312
      e24KC2ThetaAboveNode1000313

theorem e24KC2ThetaAboveNode100032 :
    adaptiveCoverCheck 13 (childHL (childHH thetaAboveCell1000)) = true :=
  adaptiveCoverCheck_succ_of_children 12 (childHL (childHH thetaAboveCell1000))
    e24KC2ThetaAboveNode1000320 e24KC2ThetaAboveNode1000321 e24KC2ThetaAboveNode1000322
      e24KC2ThetaAboveNode1000323

theorem e24KC2ThetaAboveNode100033 :
    adaptiveCoverCheck 13 (childHH (childHH thetaAboveCell1000)) = true :=
  adaptiveCoverCheck_succ_of_children 12 (childHH (childHH thetaAboveCell1000))
    e24KC2ThetaAboveNode1000330 e24KC2ThetaAboveNode1000331 e24KC2ThetaAboveNode1000332
      e24KC2ThetaAboveNode1000333

theorem e24KC2ThetaAboveNode100120 :
    adaptiveCoverCheck 13 (childLL (childHL thetaAboveCell1001)) = true :=
  adaptiveCoverCheck_succ_of_children 12 (childLL (childHL thetaAboveCell1001))
    e24KC2ThetaAboveLeaf1001200 e24KC2ThetaAboveLeaf1001201 e24KC2ThetaAboveNode1001202
      e24KC2ThetaAboveNode1001203

theorem e24KC2ThetaAboveNode100121 :
    adaptiveCoverCheck 13 (childLH (childHL thetaAboveCell1001)) = true :=
  adaptiveCoverCheck_succ_of_children 12 (childLH (childHL thetaAboveCell1001))
    e24KC2ThetaAboveLeaf1001210 e24KC2ThetaAboveLeaf1001211 e24KC2ThetaAboveNode1001212
      e24KC2ThetaAboveNode1001213

theorem e24KC2ThetaAboveNode100122 :
    adaptiveCoverCheck 13 (childHL (childHL thetaAboveCell1001)) = true :=
  adaptiveCoverCheck_succ_of_children 12 (childHL (childHL thetaAboveCell1001))
    e24KC2ThetaAboveNode1001220 e24KC2ThetaAboveNode1001221 e24KC2ThetaAboveNode1001222
      e24KC2ThetaAboveNode1001223

theorem e24KC2ThetaAboveNode100123 :
    adaptiveCoverCheck 13 (childHH (childHL thetaAboveCell1001)) = true :=
  adaptiveCoverCheck_succ_of_children 12 (childHH (childHL thetaAboveCell1001))
    e24KC2ThetaAboveNode1001230 e24KC2ThetaAboveNode1001231 e24KC2ThetaAboveNode1001232
      e24KC2ThetaAboveNode1001233

theorem e24KC2ThetaAboveNode100130 :
    adaptiveCoverCheck 13 (childLL (childHH thetaAboveCell1001)) = true :=
  adaptiveCoverCheck_succ_of_children 12 (childLL (childHH thetaAboveCell1001))
    e24KC2ThetaAboveLeaf1001300 e24KC2ThetaAboveLeaf1001301 e24KC2ThetaAboveNode1001302
      e24KC2ThetaAboveNode1001303

theorem e24KC2ThetaAboveNode100131 :
    adaptiveCoverCheck 13 (childLH (childHH thetaAboveCell1001)) = true :=
  adaptiveCoverCheck_succ_of_children 12 (childLH (childHH thetaAboveCell1001))
    e24KC2ThetaAboveLeaf1001310 e24KC2ThetaAboveLeaf1001311 e24KC2ThetaAboveNode1001312
      e24KC2ThetaAboveNode1001313

theorem e24KC2ThetaAboveNode100132 :
    adaptiveCoverCheck 13 (childHL (childHH thetaAboveCell1001)) = true :=
  adaptiveCoverCheck_succ_of_children 12 (childHL (childHH thetaAboveCell1001))
    e24KC2ThetaAboveNode1001320 e24KC2ThetaAboveNode1001321 e24KC2ThetaAboveNode1001322
      e24KC2ThetaAboveNode1001323

theorem e24KC2ThetaAboveNode100133 :
    adaptiveCoverCheck 13 (childHH (childHH thetaAboveCell1001)) = true :=
  adaptiveCoverCheck_succ_of_children 12 (childHH (childHH thetaAboveCell1001))
    e24KC2ThetaAboveNode1001330 e24KC2ThetaAboveNode1001331 e24KC2ThetaAboveNode1001332
      e24KC2ThetaAboveNode1001333

theorem e24KC2ThetaAboveNode100200 :
    adaptiveCoverCheck 13 (childLL (childLL thetaAboveCell1002)) = true :=
  adaptiveCoverCheck_succ_of_children 12 (childLL (childLL thetaAboveCell1002))
    e24KC2ThetaAboveLeaf1002000 e24KC2ThetaAboveLeaf1002001 e24KC2ThetaAboveLeaf1002002
      e24KC2ThetaAboveLeaf1002003

theorem e24KC2ThetaAboveNode100201 :
    adaptiveCoverCheck 13 (childLH (childLL thetaAboveCell1002)) = true :=
  adaptiveCoverCheck_succ_of_children 12 (childLH (childLL thetaAboveCell1002))
    e24KC2ThetaAboveLeaf1002010 e24KC2ThetaAboveLeaf1002011 e24KC2ThetaAboveLeaf1002012
      e24KC2ThetaAboveLeaf1002013

theorem e24KC2ThetaAboveNode100210 :
    adaptiveCoverCheck 13 (childLL (childLH thetaAboveCell1002)) = true :=
  adaptiveCoverCheck_succ_of_children 12 (childLL (childLH thetaAboveCell1002))
    e24KC2ThetaAboveLeaf1002100 e24KC2ThetaAboveLeaf1002101 e24KC2ThetaAboveLeaf1002102
      e24KC2ThetaAboveLeaf1002103

theorem e24KC2ThetaAboveNode100211 :
    adaptiveCoverCheck 13 (childLH (childLH thetaAboveCell1002)) = true :=
  adaptiveCoverCheck_succ_of_children 12 (childLH (childLH thetaAboveCell1002))
    e24KC2ThetaAboveLeaf1002110 e24KC2ThetaAboveLeaf1002111 e24KC2ThetaAboveLeaf1002112
      e24KC2ThetaAboveLeaf1002113

theorem e24KC2ThetaAboveNode100300 :
    adaptiveCoverCheck 13 (childLL (childLL thetaAboveCell1003)) = true :=
  adaptiveCoverCheck_succ_of_children 12 (childLL (childLL thetaAboveCell1003))
    e24KC2ThetaAboveLeaf1003000 e24KC2ThetaAboveLeaf1003001 e24KC2ThetaAboveLeaf1003002
      e24KC2ThetaAboveLeaf1003003

theorem e24KC2ThetaAboveNode100301 :
    adaptiveCoverCheck 13 (childLH (childLL thetaAboveCell1003)) = true :=
  adaptiveCoverCheck_succ_of_children 12 (childLH (childLL thetaAboveCell1003))
    e24KC2ThetaAboveLeaf1003010 e24KC2ThetaAboveLeaf1003011 e24KC2ThetaAboveLeaf1003012
      e24KC2ThetaAboveLeaf1003013

theorem e24KC2ThetaAboveNode100310 :
    adaptiveCoverCheck 13 (childLL (childLH thetaAboveCell1003)) = true :=
  adaptiveCoverCheck_succ_of_children 12 (childLL (childLH thetaAboveCell1003))
    e24KC2ThetaAboveLeaf1003100 e24KC2ThetaAboveLeaf1003101 e24KC2ThetaAboveLeaf1003102
      e24KC2ThetaAboveLeaf1003103

theorem e24KC2ThetaAboveNode100311 :
    adaptiveCoverCheck 13 (childLH (childLH thetaAboveCell1003)) = true :=
  adaptiveCoverCheck_succ_of_children 12 (childLH (childLH thetaAboveCell1003))
    e24KC2ThetaAboveLeaf1003110 e24KC2ThetaAboveLeaf1003111 e24KC2ThetaAboveLeaf1003112
      e24KC2ThetaAboveLeaf1003113

theorem e24KC2ThetaAboveNode101020 :
    adaptiveCoverCheck 13 (childLL (childHL thetaAboveCell1010)) = true :=
  adaptiveCoverCheck_succ_of_children 12 (childLL (childHL thetaAboveCell1010))
    e24KC2ThetaAboveLeaf1010200 e24KC2ThetaAboveLeaf1010201 e24KC2ThetaAboveNode1010202
      e24KC2ThetaAboveNode1010203

theorem e24KC2ThetaAboveNode101021 :
    adaptiveCoverCheck 13 (childLH (childHL thetaAboveCell1010)) = true :=
  adaptiveCoverCheck_succ_of_children 12 (childLH (childHL thetaAboveCell1010))
    e24KC2ThetaAboveLeaf1010210 e24KC2ThetaAboveLeaf1010211 e24KC2ThetaAboveLeaf1010212
      e24KC2ThetaAboveLeaf1010213

theorem e24KC2ThetaAboveNode101022 :
    adaptiveCoverCheck 13 (childHL (childHL thetaAboveCell1010)) = true :=
  adaptiveCoverCheck_succ_of_children 12 (childHL (childHL thetaAboveCell1010))
    e24KC2ThetaAboveNode1010220 e24KC2ThetaAboveNode1010221 e24KC2ThetaAboveNode1010222
      e24KC2ThetaAboveNode1010223

theorem e24KC2ThetaAboveNode101023 :
    adaptiveCoverCheck 13 (childHH (childHL thetaAboveCell1010)) = true :=
  adaptiveCoverCheck_succ_of_children 12 (childHH (childHL thetaAboveCell1010))
    e24KC2ThetaAboveNode1010230 e24KC2ThetaAboveNode1010231 e24KC2ThetaAboveNode1010232
      e24KC2ThetaAboveNode1010233

theorem e24KC2ThetaAboveNode101030 :
    adaptiveCoverCheck 13 (childLL (childHH thetaAboveCell1010)) = true :=
  adaptiveCoverCheck_succ_of_children 12 (childLL (childHH thetaAboveCell1010))
    e24KC2ThetaAboveLeaf1010300 e24KC2ThetaAboveLeaf1010301 e24KC2ThetaAboveLeaf1010302
      e24KC2ThetaAboveLeaf1010303

theorem e24KC2ThetaAboveNode101031 :
    adaptiveCoverCheck 13 (childLH (childHH thetaAboveCell1010)) = true :=
  adaptiveCoverCheck_succ_of_children 12 (childLH (childHH thetaAboveCell1010))
    e24KC2ThetaAboveLeaf1010310 e24KC2ThetaAboveLeaf1010311 e24KC2ThetaAboveLeaf1010312
      e24KC2ThetaAboveLeaf1010313

theorem e24KC2ThetaAboveNode101032 :
    adaptiveCoverCheck 13 (childHL (childHH thetaAboveCell1010)) = true :=
  adaptiveCoverCheck_succ_of_children 12 (childHL (childHH thetaAboveCell1010))
    e24KC2ThetaAboveNode1010320 e24KC2ThetaAboveNode1010321 e24KC2ThetaAboveNode1010322
      e24KC2ThetaAboveNode1010323

theorem e24KC2ThetaAboveNode101033 :
    adaptiveCoverCheck 13 (childHH (childHH thetaAboveCell1010)) = true :=
  adaptiveCoverCheck_succ_of_children 12 (childHH (childHH thetaAboveCell1010))
    e24KC2ThetaAboveNode1010330 e24KC2ThetaAboveNode1010331 e24KC2ThetaAboveNode1010332
      e24KC2ThetaAboveNode1010333

theorem e24KC2ThetaAboveNode101120 :
    adaptiveCoverCheck 13 (childLL (childHL thetaAboveCell1011)) = true :=
  adaptiveCoverCheck_succ_of_children 12 (childLL (childHL thetaAboveCell1011))
    e24KC2ThetaAboveLeaf1011200 e24KC2ThetaAboveLeaf1011201 e24KC2ThetaAboveLeaf1011202
      e24KC2ThetaAboveLeaf1011203

theorem e24KC2ThetaAboveNode101121 :
    adaptiveCoverCheck 13 (childLH (childHL thetaAboveCell1011)) = true :=
  adaptiveCoverCheck_succ_of_children 12 (childLH (childHL thetaAboveCell1011))
    e24KC2ThetaAboveLeaf1011210 e24KC2ThetaAboveLeaf1011211 e24KC2ThetaAboveLeaf1011212
      e24KC2ThetaAboveLeaf1011213

theorem e24KC2ThetaAboveNode101122 :
    adaptiveCoverCheck 13 (childHL (childHL thetaAboveCell1011)) = true :=
  adaptiveCoverCheck_succ_of_children 12 (childHL (childHL thetaAboveCell1011))
    e24KC2ThetaAboveNode1011220 e24KC2ThetaAboveNode1011221 e24KC2ThetaAboveNode1011222
      e24KC2ThetaAboveNode1011223

theorem e24KC2ThetaAboveNode101123 :
    adaptiveCoverCheck 13 (childHH (childHL thetaAboveCell1011)) = true :=
  adaptiveCoverCheck_succ_of_children 12 (childHH (childHL thetaAboveCell1011))
    e24KC2ThetaAboveNode1011230 e24KC2ThetaAboveNode1011231 e24KC2ThetaAboveNode1011232
      e24KC2ThetaAboveNode1011233

theorem e24KC2ThetaAboveNode101130 :
    adaptiveCoverCheck 13 (childLL (childHH thetaAboveCell1011)) = true :=
  adaptiveCoverCheck_succ_of_children 12 (childLL (childHH thetaAboveCell1011))
    e24KC2ThetaAboveLeaf1011300 e24KC2ThetaAboveLeaf1011301 e24KC2ThetaAboveLeaf1011302
      e24KC2ThetaAboveLeaf1011303

theorem e24KC2ThetaAboveNode101131 :
    adaptiveCoverCheck 13 (childLH (childHH thetaAboveCell1011)) = true :=
  adaptiveCoverCheck_succ_of_children 12 (childLH (childHH thetaAboveCell1011))
    e24KC2ThetaAboveLeaf1011310 e24KC2ThetaAboveLeaf1011311 e24KC2ThetaAboveLeaf1011312
      e24KC2ThetaAboveLeaf1011313

theorem e24KC2ThetaAboveNode101132 :
    adaptiveCoverCheck 13 (childHL (childHH thetaAboveCell1011)) = true :=
  adaptiveCoverCheck_succ_of_children 12 (childHL (childHH thetaAboveCell1011))
    e24KC2ThetaAboveNode1011320 e24KC2ThetaAboveNode1011321 e24KC2ThetaAboveNode1011322
      e24KC2ThetaAboveNode1011323

theorem e24KC2ThetaAboveNode101133 :
    adaptiveCoverCheck 13 (childHH (childHH thetaAboveCell1011)) = true :=
  adaptiveCoverCheck_succ_of_children 12 (childHH (childHH thetaAboveCell1011))
    e24KC2ThetaAboveNode1011330 e24KC2ThetaAboveNode1011331 e24KC2ThetaAboveNode1011332
      e24KC2ThetaAboveNode1011333

theorem e24KC2ThetaAboveNode101200 :
    adaptiveCoverCheck 13 (childLL (childLL thetaAboveCell1012)) = true :=
  adaptiveCoverCheck_succ_of_children 12 (childLL (childLL thetaAboveCell1012))
    e24KC2ThetaAboveLeaf1012000 e24KC2ThetaAboveLeaf1012001 e24KC2ThetaAboveLeaf1012002
      e24KC2ThetaAboveLeaf1012003

theorem e24KC2ThetaAboveNode101201 :
    adaptiveCoverCheck 13 (childLH (childLL thetaAboveCell1012)) = true :=
  adaptiveCoverCheck_succ_of_children 12 (childLH (childLL thetaAboveCell1012))
    e24KC2ThetaAboveLeaf1012010 e24KC2ThetaAboveLeaf1012011 e24KC2ThetaAboveLeaf1012012
      e24KC2ThetaAboveLeaf1012013

theorem e24KC2ThetaAboveNode101210 :
    adaptiveCoverCheck 13 (childLL (childLH thetaAboveCell1012)) = true :=
  adaptiveCoverCheck_succ_of_children 12 (childLL (childLH thetaAboveCell1012))
    e24KC2ThetaAboveLeaf1012100 e24KC2ThetaAboveLeaf1012101 e24KC2ThetaAboveLeaf1012102
      e24KC2ThetaAboveLeaf1012103

theorem e24KC2ThetaAboveNode101211 :
    adaptiveCoverCheck 13 (childLH (childLH thetaAboveCell1012)) = true :=
  adaptiveCoverCheck_succ_of_children 12 (childLH (childLH thetaAboveCell1012))
    e24KC2ThetaAboveLeaf1012110 e24KC2ThetaAboveLeaf1012111 e24KC2ThetaAboveLeaf1012112
      e24KC2ThetaAboveLeaf1012113

theorem e24KC2ThetaAboveNode101300 :
    adaptiveCoverCheck 13 (childLL (childLL thetaAboveCell1013)) = true :=
  adaptiveCoverCheck_succ_of_children 12 (childLL (childLL thetaAboveCell1013))
    e24KC2ThetaAboveLeaf1013000 e24KC2ThetaAboveLeaf1013001 e24KC2ThetaAboveLeaf1013002
      e24KC2ThetaAboveLeaf1013003

theorem e24KC2ThetaAboveNode101301 :
    adaptiveCoverCheck 13 (childLH (childLL thetaAboveCell1013)) = true :=
  adaptiveCoverCheck_succ_of_children 12 (childLH (childLL thetaAboveCell1013))
    e24KC2ThetaAboveLeaf1013010 e24KC2ThetaAboveLeaf1013011 e24KC2ThetaAboveLeaf1013012
      e24KC2ThetaAboveLeaf1013013

theorem e24KC2ThetaAboveNode101310 :
    adaptiveCoverCheck 13 (childLL (childLH thetaAboveCell1013)) = true :=
  adaptiveCoverCheck_succ_of_children 12 (childLL (childLH thetaAboveCell1013))
    e24KC2ThetaAboveLeaf1013100 e24KC2ThetaAboveLeaf1013101 e24KC2ThetaAboveLeaf1013102
      e24KC2ThetaAboveLeaf1013103

theorem e24KC2ThetaAboveNode101311 :
    adaptiveCoverCheck 13 (childLH (childLH thetaAboveCell1013)) = true :=
  adaptiveCoverCheck_succ_of_children 12 (childLH (childLH thetaAboveCell1013))
    e24KC2ThetaAboveLeaf1013110 e24KC2ThetaAboveLeaf1013111 e24KC2ThetaAboveLeaf1013112
      e24KC2ThetaAboveLeaf1013113

theorem e24KC2ThetaAboveNode110020 :
    adaptiveCoverCheck 13 (childLL (childHL thetaAboveCell1100)) = true :=
  adaptiveCoverCheck_succ_of_children 12 (childLL (childHL thetaAboveCell1100))
    e24KC2ThetaAboveLeaf1100200 e24KC2ThetaAboveLeaf1100201 e24KC2ThetaAboveLeaf1100202
      e24KC2ThetaAboveLeaf1100203

theorem e24KC2ThetaAboveNode110021 :
    adaptiveCoverCheck 13 (childLH (childHL thetaAboveCell1100)) = true :=
  adaptiveCoverCheck_succ_of_children 12 (childLH (childHL thetaAboveCell1100))
    e24KC2ThetaAboveLeaf1100210 e24KC2ThetaAboveLeaf1100211 e24KC2ThetaAboveLeaf1100212
      e24KC2ThetaAboveLeaf1100213

theorem e24KC2ThetaAboveNode110022 :
    adaptiveCoverCheck 13 (childHL (childHL thetaAboveCell1100)) = true :=
  adaptiveCoverCheck_succ_of_children 12 (childHL (childHL thetaAboveCell1100))
    e24KC2ThetaAboveNode1100220 e24KC2ThetaAboveNode1100221 e24KC2ThetaAboveNode1100222
      e24KC2ThetaAboveNode1100223

theorem e24KC2ThetaAboveNode110023 :
    adaptiveCoverCheck 13 (childHH (childHL thetaAboveCell1100)) = true :=
  adaptiveCoverCheck_succ_of_children 12 (childHH (childHL thetaAboveCell1100))
    e24KC2ThetaAboveNode1100230 e24KC2ThetaAboveNode1100231 e24KC2ThetaAboveNode1100232
      e24KC2ThetaAboveNode1100233

theorem e24KC2ThetaAboveNode110030 :
    adaptiveCoverCheck 13 (childLL (childHH thetaAboveCell1100)) = true :=
  adaptiveCoverCheck_succ_of_children 12 (childLL (childHH thetaAboveCell1100))
    e24KC2ThetaAboveLeaf1100300 e24KC2ThetaAboveLeaf1100301 e24KC2ThetaAboveLeaf1100302
      e24KC2ThetaAboveLeaf1100303

theorem e24KC2ThetaAboveNode110031 :
    adaptiveCoverCheck 13 (childLH (childHH thetaAboveCell1100)) = true :=
  adaptiveCoverCheck_succ_of_children 12 (childLH (childHH thetaAboveCell1100))
    e24KC2ThetaAboveLeaf1100310 e24KC2ThetaAboveLeaf1100311 e24KC2ThetaAboveLeaf1100312
      e24KC2ThetaAboveLeaf1100313

theorem e24KC2ThetaAboveNode110032 :
    adaptiveCoverCheck 13 (childHL (childHH thetaAboveCell1100)) = true :=
  adaptiveCoverCheck_succ_of_children 12 (childHL (childHH thetaAboveCell1100))
    e24KC2ThetaAboveNode1100320 e24KC2ThetaAboveNode1100321 e24KC2ThetaAboveNode1100322
      e24KC2ThetaAboveNode1100323

theorem e24KC2ThetaAboveNode110033 :
    adaptiveCoverCheck 13 (childHH (childHH thetaAboveCell1100)) = true :=
  adaptiveCoverCheck_succ_of_children 12 (childHH (childHH thetaAboveCell1100))
    e24KC2ThetaAboveNode1100330 e24KC2ThetaAboveNode1100331 e24KC2ThetaAboveNode1100332
      e24KC2ThetaAboveNode1100333

theorem e24KC2ThetaAboveNode110120 :
    adaptiveCoverCheck 13 (childLL (childHL thetaAboveCell1101)) = true :=
  adaptiveCoverCheck_succ_of_children 12 (childLL (childHL thetaAboveCell1101))
    e24KC2ThetaAboveLeaf1101200 e24KC2ThetaAboveLeaf1101201 e24KC2ThetaAboveLeaf1101202
      e24KC2ThetaAboveLeaf1101203

theorem e24KC2ThetaAboveNode110121 :
    adaptiveCoverCheck 13 (childLH (childHL thetaAboveCell1101)) = true :=
  adaptiveCoverCheck_succ_of_children 12 (childLH (childHL thetaAboveCell1101))
    e24KC2ThetaAboveLeaf1101210 e24KC2ThetaAboveLeaf1101211 e24KC2ThetaAboveLeaf1101212
      e24KC2ThetaAboveLeaf1101213

theorem e24KC2ThetaAboveNode110122 :
    adaptiveCoverCheck 13 (childHL (childHL thetaAboveCell1101)) = true :=
  adaptiveCoverCheck_succ_of_children 12 (childHL (childHL thetaAboveCell1101))
    e24KC2ThetaAboveNode1101220 e24KC2ThetaAboveNode1101221 e24KC2ThetaAboveNode1101222
      e24KC2ThetaAboveNode1101223

theorem e24KC2ThetaAboveNode110123 :
    adaptiveCoverCheck 13 (childHH (childHL thetaAboveCell1101)) = true :=
  adaptiveCoverCheck_succ_of_children 12 (childHH (childHL thetaAboveCell1101))
    e24KC2ThetaAboveNode1101230 e24KC2ThetaAboveNode1101231 e24KC2ThetaAboveNode1101232
      e24KC2ThetaAboveNode1101233

theorem e24KC2ThetaAboveNode110130 :
    adaptiveCoverCheck 13 (childLL (childHH thetaAboveCell1101)) = true :=
  adaptiveCoverCheck_succ_of_children 12 (childLL (childHH thetaAboveCell1101))
    e24KC2ThetaAboveLeaf1101300 e24KC2ThetaAboveLeaf1101301 e24KC2ThetaAboveLeaf1101302
      e24KC2ThetaAboveLeaf1101303

theorem e24KC2ThetaAboveNode110131 :
    adaptiveCoverCheck 13 (childLH (childHH thetaAboveCell1101)) = true :=
  adaptiveCoverCheck_succ_of_children 12 (childLH (childHH thetaAboveCell1101))
    e24KC2ThetaAboveLeaf1101310 e24KC2ThetaAboveLeaf1101311 e24KC2ThetaAboveLeaf1101312
      e24KC2ThetaAboveLeaf1101313

theorem e24KC2ThetaAboveNode110132 :
    adaptiveCoverCheck 13 (childHL (childHH thetaAboveCell1101)) = true :=
  adaptiveCoverCheck_succ_of_children 12 (childHL (childHH thetaAboveCell1101))
    e24KC2ThetaAboveNode1101320 e24KC2ThetaAboveNode1101321 e24KC2ThetaAboveNode1101322
      e24KC2ThetaAboveNode1101323

theorem e24KC2ThetaAboveNode110133 :
    adaptiveCoverCheck 13 (childHH (childHH thetaAboveCell1101)) = true :=
  adaptiveCoverCheck_succ_of_children 12 (childHH (childHH thetaAboveCell1101))
    e24KC2ThetaAboveNode1101330 e24KC2ThetaAboveNode1101331 e24KC2ThetaAboveNode1101332
      e24KC2ThetaAboveNode1101333

theorem e24KC2ThetaAboveNode110200 :
    adaptiveCoverCheck 13 (childLL (childLL thetaAboveCell1102)) = true :=
  adaptiveCoverCheck_succ_of_children 12 (childLL (childLL thetaAboveCell1102))
    e24KC2ThetaAboveLeaf1102000 e24KC2ThetaAboveLeaf1102001 e24KC2ThetaAboveLeaf1102002
      e24KC2ThetaAboveLeaf1102003

theorem e24KC2ThetaAboveNode110201 :
    adaptiveCoverCheck 13 (childLH (childLL thetaAboveCell1102)) = true :=
  adaptiveCoverCheck_succ_of_children 12 (childLH (childLL thetaAboveCell1102))
    e24KC2ThetaAboveLeaf1102010 e24KC2ThetaAboveLeaf1102011 e24KC2ThetaAboveLeaf1102012
      e24KC2ThetaAboveLeaf1102013

theorem e24KC2ThetaAboveNode110210 :
    adaptiveCoverCheck 13 (childLL (childLH thetaAboveCell1102)) = true :=
  adaptiveCoverCheck_succ_of_children 12 (childLL (childLH thetaAboveCell1102))
    e24KC2ThetaAboveLeaf1102100 e24KC2ThetaAboveLeaf1102101 e24KC2ThetaAboveLeaf1102102
      e24KC2ThetaAboveLeaf1102103

theorem e24KC2ThetaAboveNode110211 :
    adaptiveCoverCheck 13 (childLH (childLH thetaAboveCell1102)) = true :=
  adaptiveCoverCheck_succ_of_children 12 (childLH (childLH thetaAboveCell1102))
    e24KC2ThetaAboveLeaf1102110 e24KC2ThetaAboveLeaf1102111 e24KC2ThetaAboveLeaf1102112
      e24KC2ThetaAboveLeaf1102113

theorem e24KC2ThetaAboveNode110300 :
    adaptiveCoverCheck 13 (childLL (childLL thetaAboveCell1103)) = true :=
  adaptiveCoverCheck_succ_of_children 12 (childLL (childLL thetaAboveCell1103))
    e24KC2ThetaAboveLeaf1103000 e24KC2ThetaAboveLeaf1103001 e24KC2ThetaAboveLeaf1103002
      e24KC2ThetaAboveLeaf1103003

theorem e24KC2ThetaAboveNode110301 :
    adaptiveCoverCheck 13 (childLH (childLL thetaAboveCell1103)) = true :=
  adaptiveCoverCheck_succ_of_children 12 (childLH (childLL thetaAboveCell1103))
    e24KC2ThetaAboveLeaf1103010 e24KC2ThetaAboveLeaf1103011 e24KC2ThetaAboveLeaf1103012
      e24KC2ThetaAboveLeaf1103013

theorem e24KC2ThetaAboveNode110310 :
    adaptiveCoverCheck 13 (childLL (childLH thetaAboveCell1103)) = true :=
  adaptiveCoverCheck_succ_of_children 12 (childLL (childLH thetaAboveCell1103))
    e24KC2ThetaAboveLeaf1103100 e24KC2ThetaAboveLeaf1103101 e24KC2ThetaAboveLeaf1103102
      e24KC2ThetaAboveLeaf1103103

theorem e24KC2ThetaAboveNode110311 :
    adaptiveCoverCheck 13 (childLH (childLH thetaAboveCell1103)) = true :=
  adaptiveCoverCheck_succ_of_children 12 (childLH (childLH thetaAboveCell1103))
    e24KC2ThetaAboveLeaf1103110 e24KC2ThetaAboveLeaf1103111 e24KC2ThetaAboveLeaf1103112
      e24KC2ThetaAboveLeaf1103113

theorem e24KC2ThetaAboveNode111020 :
    adaptiveCoverCheck 13 (childLL (childHL thetaAboveCell1110)) = true :=
  adaptiveCoverCheck_succ_of_children 12 (childLL (childHL thetaAboveCell1110))
    e24KC2ThetaAboveLeaf1110200 e24KC2ThetaAboveLeaf1110201 e24KC2ThetaAboveLeaf1110202
      e24KC2ThetaAboveLeaf1110203

theorem e24KC2ThetaAboveNode111021 :
    adaptiveCoverCheck 13 (childLH (childHL thetaAboveCell1110)) = true :=
  adaptiveCoverCheck_succ_of_children 12 (childLH (childHL thetaAboveCell1110))
    e24KC2ThetaAboveLeaf1110210 e24KC2ThetaAboveLeaf1110211 e24KC2ThetaAboveLeaf1110212
      e24KC2ThetaAboveLeaf1110213

theorem e24KC2ThetaAboveNode111022 :
    adaptiveCoverCheck 13 (childHL (childHL thetaAboveCell1110)) = true :=
  adaptiveCoverCheck_succ_of_children 12 (childHL (childHL thetaAboveCell1110))
    e24KC2ThetaAboveNode1110220 e24KC2ThetaAboveNode1110221 e24KC2ThetaAboveNode1110222
      e24KC2ThetaAboveNode1110223

theorem e24KC2ThetaAboveNode111023 :
    adaptiveCoverCheck 13 (childHH (childHL thetaAboveCell1110)) = true :=
  adaptiveCoverCheck_succ_of_children 12 (childHH (childHL thetaAboveCell1110))
    e24KC2ThetaAboveNode1110230 e24KC2ThetaAboveNode1110231 e24KC2ThetaAboveNode1110232
      e24KC2ThetaAboveNode1110233

theorem e24KC2ThetaAboveNode111030 :
    adaptiveCoverCheck 13 (childLL (childHH thetaAboveCell1110)) = true :=
  adaptiveCoverCheck_succ_of_children 12 (childLL (childHH thetaAboveCell1110))
    e24KC2ThetaAboveLeaf1110300 e24KC2ThetaAboveLeaf1110301 e24KC2ThetaAboveLeaf1110302
      e24KC2ThetaAboveLeaf1110303

theorem e24KC2ThetaAboveNode111031 :
    adaptiveCoverCheck 13 (childLH (childHH thetaAboveCell1110)) = true :=
  adaptiveCoverCheck_succ_of_children 12 (childLH (childHH thetaAboveCell1110))
    e24KC2ThetaAboveLeaf1110310 e24KC2ThetaAboveLeaf1110311 e24KC2ThetaAboveLeaf1110312
      e24KC2ThetaAboveLeaf1110313

theorem e24KC2ThetaAboveNode111032 :
    adaptiveCoverCheck 13 (childHL (childHH thetaAboveCell1110)) = true :=
  adaptiveCoverCheck_succ_of_children 12 (childHL (childHH thetaAboveCell1110))
    e24KC2ThetaAboveNode1110320 e24KC2ThetaAboveNode1110321 e24KC2ThetaAboveNode1110322
      e24KC2ThetaAboveNode1110323

theorem e24KC2ThetaAboveNode111033 :
    adaptiveCoverCheck 13 (childHH (childHH thetaAboveCell1110)) = true :=
  adaptiveCoverCheck_succ_of_children 12 (childHH (childHH thetaAboveCell1110))
    e24KC2ThetaAboveNode1110330 e24KC2ThetaAboveNode1110331 e24KC2ThetaAboveNode1110332
      e24KC2ThetaAboveNode1110333

theorem e24KC2ThetaAboveNode111120 :
    adaptiveCoverCheck 13 (childLL (childHL thetaAboveCell1111)) = true :=
  adaptiveCoverCheck_succ_of_children 12 (childLL (childHL thetaAboveCell1111))
    e24KC2ThetaAboveLeaf1111200 e24KC2ThetaAboveLeaf1111201 e24KC2ThetaAboveLeaf1111202
      e24KC2ThetaAboveLeaf1111203

theorem e24KC2ThetaAboveNode111121 :
    adaptiveCoverCheck 13 (childLH (childHL thetaAboveCell1111)) = true :=
  adaptiveCoverCheck_succ_of_children 12 (childLH (childHL thetaAboveCell1111))
    e24KC2ThetaAboveLeaf1111210 e24KC2ThetaAboveLeaf1111211 e24KC2ThetaAboveLeaf1111212
      e24KC2ThetaAboveLeaf1111213

theorem e24KC2ThetaAboveNode111122 :
    adaptiveCoverCheck 13 (childHL (childHL thetaAboveCell1111)) = true :=
  adaptiveCoverCheck_succ_of_children 12 (childHL (childHL thetaAboveCell1111))
    e24KC2ThetaAboveNode1111220 e24KC2ThetaAboveNode1111221 e24KC2ThetaAboveNode1111222
      e24KC2ThetaAboveNode1111223

theorem e24KC2ThetaAboveNode111123 :
    adaptiveCoverCheck 13 (childHH (childHL thetaAboveCell1111)) = true :=
  adaptiveCoverCheck_succ_of_children 12 (childHH (childHL thetaAboveCell1111))
    e24KC2ThetaAboveNode1111230 e24KC2ThetaAboveNode1111231 e24KC2ThetaAboveNode1111232
      e24KC2ThetaAboveNode1111233

theorem e24KC2ThetaAboveNode111130 :
    adaptiveCoverCheck 13 (childLL (childHH thetaAboveCell1111)) = true :=
  adaptiveCoverCheck_succ_of_children 12 (childLL (childHH thetaAboveCell1111))
    e24KC2ThetaAboveLeaf1111300 e24KC2ThetaAboveLeaf1111301 e24KC2ThetaAboveLeaf1111302
      e24KC2ThetaAboveLeaf1111303

theorem e24KC2ThetaAboveNode111131 :
    adaptiveCoverCheck 13 (childLH (childHH thetaAboveCell1111)) = true :=
  adaptiveCoverCheck_succ_of_children 12 (childLH (childHH thetaAboveCell1111))
    e24KC2ThetaAboveLeaf1111310 e24KC2ThetaAboveLeaf1111311 e24KC2ThetaAboveLeaf1111312
      e24KC2ThetaAboveLeaf1111313

theorem e24KC2ThetaAboveNode111132 :
    adaptiveCoverCheck 13 (childHL (childHH thetaAboveCell1111)) = true :=
  adaptiveCoverCheck_succ_of_children 12 (childHL (childHH thetaAboveCell1111))
    e24KC2ThetaAboveNode1111320 e24KC2ThetaAboveNode1111321 e24KC2ThetaAboveNode1111322
      e24KC2ThetaAboveNode1111323

theorem e24KC2ThetaAboveNode111133 :
    adaptiveCoverCheck 13 (childHH (childHH thetaAboveCell1111)) = true :=
  adaptiveCoverCheck_succ_of_children 12 (childHH (childHH thetaAboveCell1111))
    e24KC2ThetaAboveNode1111330 e24KC2ThetaAboveNode1111331 e24KC2ThetaAboveNode1111332
      e24KC2ThetaAboveNode1111333

theorem e24KC2ThetaAboveNode111200 :
    adaptiveCoverCheck 13 (childLL (childLL thetaAboveCell1112)) = true :=
  adaptiveCoverCheck_succ_of_children 12 (childLL (childLL thetaAboveCell1112))
    e24KC2ThetaAboveLeaf1112000 e24KC2ThetaAboveLeaf1112001 e24KC2ThetaAboveLeaf1112002
      e24KC2ThetaAboveLeaf1112003

theorem e24KC2ThetaAboveNode111201 :
    adaptiveCoverCheck 13 (childLH (childLL thetaAboveCell1112)) = true :=
  adaptiveCoverCheck_succ_of_children 12 (childLH (childLL thetaAboveCell1112))
    e24KC2ThetaAboveLeaf1112010 e24KC2ThetaAboveLeaf1112011 e24KC2ThetaAboveLeaf1112012
      e24KC2ThetaAboveLeaf1112013

theorem e24KC2ThetaAboveNode111210 :
    adaptiveCoverCheck 13 (childLL (childLH thetaAboveCell1112)) = true :=
  adaptiveCoverCheck_succ_of_children 12 (childLL (childLH thetaAboveCell1112))
    e24KC2ThetaAboveLeaf1112100 e24KC2ThetaAboveLeaf1112101 e24KC2ThetaAboveLeaf1112102
      e24KC2ThetaAboveLeaf1112103

theorem e24KC2ThetaAboveNode111211 :
    adaptiveCoverCheck 13 (childLH (childLH thetaAboveCell1112)) = true :=
  adaptiveCoverCheck_succ_of_children 12 (childLH (childLH thetaAboveCell1112))
    e24KC2ThetaAboveLeaf1112110 e24KC2ThetaAboveLeaf1112111 e24KC2ThetaAboveLeaf1112112
      e24KC2ThetaAboveLeaf1112113

theorem e24KC2ThetaAboveNode111300 :
    adaptiveCoverCheck 13 (childLL (childLL thetaAboveCell1113)) = true :=
  adaptiveCoverCheck_succ_of_children 12 (childLL (childLL thetaAboveCell1113))
    e24KC2ThetaAboveLeaf1113000 e24KC2ThetaAboveLeaf1113001 e24KC2ThetaAboveLeaf1113002
      e24KC2ThetaAboveLeaf1113003

theorem e24KC2ThetaAboveNode111301 :
    adaptiveCoverCheck 13 (childLH (childLL thetaAboveCell1113)) = true :=
  adaptiveCoverCheck_succ_of_children 12 (childLH (childLL thetaAboveCell1113))
    e24KC2ThetaAboveLeaf1113010 e24KC2ThetaAboveLeaf1113011 e24KC2ThetaAboveLeaf1113012
      e24KC2ThetaAboveLeaf1113013

theorem e24KC2ThetaAboveNode111310 :
    adaptiveCoverCheck 13 (childLL (childLH thetaAboveCell1113)) = true :=
  adaptiveCoverCheck_succ_of_children 12 (childLL (childLH thetaAboveCell1113))
    e24KC2ThetaAboveLeaf1113100 e24KC2ThetaAboveLeaf1113101 e24KC2ThetaAboveLeaf1113102
      e24KC2ThetaAboveLeaf1113103

theorem e24KC2ThetaAboveNode111311 :
    adaptiveCoverCheck 13 (childLH (childLH thetaAboveCell1113)) = true :=
  adaptiveCoverCheck_succ_of_children 12 (childLH (childLH thetaAboveCell1113))
    e24KC2ThetaAboveLeaf1113110 e24KC2ThetaAboveLeaf1113111 e24KC2ThetaAboveLeaf1113112
      e24KC2ThetaAboveLeaf1113113

theorem e24KC2ThetaAboveNode00000 :
    adaptiveCoverCheck 14 (childLL thetaAboveCell0000) = true :=
  adaptiveCoverCheck_succ_of_children 13 (childLL thetaAboveCell0000)
    e24KC2ThetaAboveLeaf000000 e24KC2ThetaAboveLeaf000001 e24KC2ThetaAboveLeaf000002
      e24KC2ThetaAboveLeaf000003

theorem e24KC2ThetaAboveNode00001 :
    adaptiveCoverCheck 14 (childLH thetaAboveCell0000) = true :=
  adaptiveCoverCheck_succ_of_children 13 (childLH thetaAboveCell0000)
    e24KC2ThetaAboveLeaf000010 e24KC2ThetaAboveLeaf000011 e24KC2ThetaAboveLeaf000012
      e24KC2ThetaAboveLeaf000013

theorem e24KC2ThetaAboveNode00002 :
    adaptiveCoverCheck 14 (childHL thetaAboveCell0000) = true :=
  adaptiveCoverCheck_succ_of_children 13 (childHL thetaAboveCell0000)
    e24KC2ThetaAboveNode000020 e24KC2ThetaAboveNode000021 e24KC2ThetaAboveNode000022
      e24KC2ThetaAboveNode000023

theorem e24KC2ThetaAboveNode00003 :
    adaptiveCoverCheck 14 (childHH thetaAboveCell0000) = true :=
  adaptiveCoverCheck_succ_of_children 13 (childHH thetaAboveCell0000)
    e24KC2ThetaAboveNode000030 e24KC2ThetaAboveNode000031 e24KC2ThetaAboveNode000032
      e24KC2ThetaAboveNode000033

theorem e24KC2ThetaAboveNode00010 :
    adaptiveCoverCheck 14 (childLL thetaAboveCell0001) = true :=
  adaptiveCoverCheck_succ_of_children 13 (childLL thetaAboveCell0001)
    e24KC2ThetaAboveLeaf000100 e24KC2ThetaAboveLeaf000101 e24KC2ThetaAboveLeaf000102
      e24KC2ThetaAboveLeaf000103

theorem e24KC2ThetaAboveNode00011 :
    adaptiveCoverCheck 14 (childLH thetaAboveCell0001) = true :=
  adaptiveCoverCheck_succ_of_children 13 (childLH thetaAboveCell0001)
    e24KC2ThetaAboveLeaf000110 e24KC2ThetaAboveLeaf000111 e24KC2ThetaAboveLeaf000112
      e24KC2ThetaAboveLeaf000113

theorem e24KC2ThetaAboveNode00012 :
    adaptiveCoverCheck 14 (childHL thetaAboveCell0001) = true :=
  adaptiveCoverCheck_succ_of_children 13 (childHL thetaAboveCell0001)
    e24KC2ThetaAboveNode000120 e24KC2ThetaAboveNode000121 e24KC2ThetaAboveNode000122
      e24KC2ThetaAboveNode000123

theorem e24KC2ThetaAboveNode00013 :
    adaptiveCoverCheck 14 (childHH thetaAboveCell0001) = true :=
  adaptiveCoverCheck_succ_of_children 13 (childHH thetaAboveCell0001)
    e24KC2ThetaAboveNode000130 e24KC2ThetaAboveNode000131 e24KC2ThetaAboveNode000132
      e24KC2ThetaAboveNode000133

theorem e24KC2ThetaAboveNode00020 :
    adaptiveCoverCheck 14 (childLL thetaAboveCell0002) = true :=
  adaptiveCoverCheck_succ_of_children 13 (childLL thetaAboveCell0002)
    e24KC2ThetaAboveNode000200 e24KC2ThetaAboveNode000201 e24KC2ThetaAboveLeaf000202
      e24KC2ThetaAboveLeaf000203

theorem e24KC2ThetaAboveNode00021 :
    adaptiveCoverCheck 14 (childLH thetaAboveCell0002) = true :=
  adaptiveCoverCheck_succ_of_children 13 (childLH thetaAboveCell0002)
    e24KC2ThetaAboveNode000210 e24KC2ThetaAboveNode000211 e24KC2ThetaAboveLeaf000212
      e24KC2ThetaAboveLeaf000213

theorem e24KC2ThetaAboveNode00030 :
    adaptiveCoverCheck 14 (childLL thetaAboveCell0003) = true :=
  adaptiveCoverCheck_succ_of_children 13 (childLL thetaAboveCell0003)
    e24KC2ThetaAboveNode000300 e24KC2ThetaAboveNode000301 e24KC2ThetaAboveLeaf000302
      e24KC2ThetaAboveLeaf000303

theorem e24KC2ThetaAboveNode00031 :
    adaptiveCoverCheck 14 (childLH thetaAboveCell0003) = true :=
  adaptiveCoverCheck_succ_of_children 13 (childLH thetaAboveCell0003)
    e24KC2ThetaAboveNode000310 e24KC2ThetaAboveNode000311 e24KC2ThetaAboveLeaf000312
      e24KC2ThetaAboveLeaf000313

theorem e24KC2ThetaAboveNode00100 :
    adaptiveCoverCheck 14 (childLL thetaAboveCell0010) = true :=
  adaptiveCoverCheck_succ_of_children 13 (childLL thetaAboveCell0010)
    e24KC2ThetaAboveLeaf001000 e24KC2ThetaAboveLeaf001001 e24KC2ThetaAboveLeaf001002
      e24KC2ThetaAboveLeaf001003

theorem e24KC2ThetaAboveNode00101 :
    adaptiveCoverCheck 14 (childLH thetaAboveCell0010) = true :=
  adaptiveCoverCheck_succ_of_children 13 (childLH thetaAboveCell0010)
    e24KC2ThetaAboveLeaf001010 e24KC2ThetaAboveLeaf001011 e24KC2ThetaAboveLeaf001012
      e24KC2ThetaAboveLeaf001013

theorem e24KC2ThetaAboveNode00102 :
    adaptiveCoverCheck 14 (childHL thetaAboveCell0010) = true :=
  adaptiveCoverCheck_succ_of_children 13 (childHL thetaAboveCell0010)
    e24KC2ThetaAboveNode001020 e24KC2ThetaAboveNode001021 e24KC2ThetaAboveNode001022
      e24KC2ThetaAboveNode001023

theorem e24KC2ThetaAboveNode00103 :
    adaptiveCoverCheck 14 (childHH thetaAboveCell0010) = true :=
  adaptiveCoverCheck_succ_of_children 13 (childHH thetaAboveCell0010)
    e24KC2ThetaAboveNode001030 e24KC2ThetaAboveNode001031 e24KC2ThetaAboveNode001032
      e24KC2ThetaAboveNode001033

theorem e24KC2ThetaAboveNode00110 :
    adaptiveCoverCheck 14 (childLL thetaAboveCell0011) = true :=
  adaptiveCoverCheck_succ_of_children 13 (childLL thetaAboveCell0011)
    e24KC2ThetaAboveLeaf001100 e24KC2ThetaAboveLeaf001101 e24KC2ThetaAboveLeaf001102
      e24KC2ThetaAboveLeaf001103

theorem e24KC2ThetaAboveNode00111 :
    adaptiveCoverCheck 14 (childLH thetaAboveCell0011) = true :=
  adaptiveCoverCheck_succ_of_children 13 (childLH thetaAboveCell0011)
    e24KC2ThetaAboveLeaf001110 e24KC2ThetaAboveLeaf001111 e24KC2ThetaAboveLeaf001112
      e24KC2ThetaAboveLeaf001113

theorem e24KC2ThetaAboveNode00112 :
    adaptiveCoverCheck 14 (childHL thetaAboveCell0011) = true :=
  adaptiveCoverCheck_succ_of_children 13 (childHL thetaAboveCell0011)
    e24KC2ThetaAboveNode001120 e24KC2ThetaAboveNode001121 e24KC2ThetaAboveNode001122
      e24KC2ThetaAboveNode001123

theorem e24KC2ThetaAboveNode00113 :
    adaptiveCoverCheck 14 (childHH thetaAboveCell0011) = true :=
  adaptiveCoverCheck_succ_of_children 13 (childHH thetaAboveCell0011)
    e24KC2ThetaAboveNode001130 e24KC2ThetaAboveNode001131 e24KC2ThetaAboveNode001132
      e24KC2ThetaAboveNode001133

theorem e24KC2ThetaAboveNode00120 :
    adaptiveCoverCheck 14 (childLL thetaAboveCell0012) = true :=
  adaptiveCoverCheck_succ_of_children 13 (childLL thetaAboveCell0012)
    e24KC2ThetaAboveNode001200 e24KC2ThetaAboveNode001201 e24KC2ThetaAboveLeaf001202
      e24KC2ThetaAboveLeaf001203

theorem e24KC2ThetaAboveNode00121 :
    adaptiveCoverCheck 14 (childLH thetaAboveCell0012) = true :=
  adaptiveCoverCheck_succ_of_children 13 (childLH thetaAboveCell0012)
    e24KC2ThetaAboveNode001210 e24KC2ThetaAboveNode001211 e24KC2ThetaAboveLeaf001212
      e24KC2ThetaAboveLeaf001213

theorem e24KC2ThetaAboveNode00130 :
    adaptiveCoverCheck 14 (childLL thetaAboveCell0013) = true :=
  adaptiveCoverCheck_succ_of_children 13 (childLL thetaAboveCell0013)
    e24KC2ThetaAboveNode001300 e24KC2ThetaAboveNode001301 e24KC2ThetaAboveLeaf001302
      e24KC2ThetaAboveLeaf001303

theorem e24KC2ThetaAboveNode00131 :
    adaptiveCoverCheck 14 (childLH thetaAboveCell0013) = true :=
  adaptiveCoverCheck_succ_of_children 13 (childLH thetaAboveCell0013)
    e24KC2ThetaAboveNode001310 e24KC2ThetaAboveNode001311 e24KC2ThetaAboveLeaf001312
      e24KC2ThetaAboveLeaf001313

theorem e24KC2ThetaAboveNode01000 :
    adaptiveCoverCheck 14 (childLL thetaAboveCell0100) = true :=
  adaptiveCoverCheck_succ_of_children 13 (childLL thetaAboveCell0100)
    e24KC2ThetaAboveLeaf010000 e24KC2ThetaAboveLeaf010001 e24KC2ThetaAboveLeaf010002
      e24KC2ThetaAboveLeaf010003

theorem e24KC2ThetaAboveNode01001 :
    adaptiveCoverCheck 14 (childLH thetaAboveCell0100) = true :=
  adaptiveCoverCheck_succ_of_children 13 (childLH thetaAboveCell0100)
    e24KC2ThetaAboveLeaf010010 e24KC2ThetaAboveLeaf010011 e24KC2ThetaAboveLeaf010012
      e24KC2ThetaAboveLeaf010013

theorem e24KC2ThetaAboveNode01002 :
    adaptiveCoverCheck 14 (childHL thetaAboveCell0100) = true :=
  adaptiveCoverCheck_succ_of_children 13 (childHL thetaAboveCell0100)
    e24KC2ThetaAboveNode010020 e24KC2ThetaAboveNode010021 e24KC2ThetaAboveNode010022
      e24KC2ThetaAboveNode010023

theorem e24KC2ThetaAboveNode01003 :
    adaptiveCoverCheck 14 (childHH thetaAboveCell0100) = true :=
  adaptiveCoverCheck_succ_of_children 13 (childHH thetaAboveCell0100)
    e24KC2ThetaAboveNode010030 e24KC2ThetaAboveNode010031 e24KC2ThetaAboveNode010032
      e24KC2ThetaAboveNode010033

theorem e24KC2ThetaAboveNode01010 :
    adaptiveCoverCheck 14 (childLL thetaAboveCell0101) = true :=
  adaptiveCoverCheck_succ_of_children 13 (childLL thetaAboveCell0101)
    e24KC2ThetaAboveLeaf010100 e24KC2ThetaAboveLeaf010101 e24KC2ThetaAboveLeaf010102
      e24KC2ThetaAboveLeaf010103

theorem e24KC2ThetaAboveNode01011 :
    adaptiveCoverCheck 14 (childLH thetaAboveCell0101) = true :=
  adaptiveCoverCheck_succ_of_children 13 (childLH thetaAboveCell0101)
    e24KC2ThetaAboveLeaf010110 e24KC2ThetaAboveLeaf010111 e24KC2ThetaAboveLeaf010112
      e24KC2ThetaAboveLeaf010113

theorem e24KC2ThetaAboveNode01012 :
    adaptiveCoverCheck 14 (childHL thetaAboveCell0101) = true :=
  adaptiveCoverCheck_succ_of_children 13 (childHL thetaAboveCell0101)
    e24KC2ThetaAboveNode010120 e24KC2ThetaAboveNode010121 e24KC2ThetaAboveNode010122
      e24KC2ThetaAboveNode010123

theorem e24KC2ThetaAboveNode01013 :
    adaptiveCoverCheck 14 (childHH thetaAboveCell0101) = true :=
  adaptiveCoverCheck_succ_of_children 13 (childHH thetaAboveCell0101)
    e24KC2ThetaAboveNode010130 e24KC2ThetaAboveNode010131 e24KC2ThetaAboveNode010132
      e24KC2ThetaAboveNode010133

theorem e24KC2ThetaAboveNode01020 :
    adaptiveCoverCheck 14 (childLL thetaAboveCell0102) = true :=
  adaptiveCoverCheck_succ_of_children 13 (childLL thetaAboveCell0102)
    e24KC2ThetaAboveNode010200 e24KC2ThetaAboveNode010201 e24KC2ThetaAboveLeaf010202
      e24KC2ThetaAboveLeaf010203

theorem e24KC2ThetaAboveNode01021 :
    adaptiveCoverCheck 14 (childLH thetaAboveCell0102) = true :=
  adaptiveCoverCheck_succ_of_children 13 (childLH thetaAboveCell0102)
    e24KC2ThetaAboveNode010210 e24KC2ThetaAboveNode010211 e24KC2ThetaAboveLeaf010212
      e24KC2ThetaAboveLeaf010213

theorem e24KC2ThetaAboveNode01030 :
    adaptiveCoverCheck 14 (childLL thetaAboveCell0103) = true :=
  adaptiveCoverCheck_succ_of_children 13 (childLL thetaAboveCell0103)
    e24KC2ThetaAboveNode010300 e24KC2ThetaAboveNode010301 e24KC2ThetaAboveLeaf010302
      e24KC2ThetaAboveLeaf010303

theorem e24KC2ThetaAboveNode01031 :
    adaptiveCoverCheck 14 (childLH thetaAboveCell0103) = true :=
  adaptiveCoverCheck_succ_of_children 13 (childLH thetaAboveCell0103)
    e24KC2ThetaAboveNode010310 e24KC2ThetaAboveNode010311 e24KC2ThetaAboveLeaf010312
      e24KC2ThetaAboveLeaf010313

theorem e24KC2ThetaAboveNode01100 :
    adaptiveCoverCheck 14 (childLL thetaAboveCell0110) = true :=
  adaptiveCoverCheck_succ_of_children 13 (childLL thetaAboveCell0110)
    e24KC2ThetaAboveLeaf011000 e24KC2ThetaAboveLeaf011001 e24KC2ThetaAboveLeaf011002
      e24KC2ThetaAboveLeaf011003

theorem e24KC2ThetaAboveNode01101 :
    adaptiveCoverCheck 14 (childLH thetaAboveCell0110) = true :=
  adaptiveCoverCheck_succ_of_children 13 (childLH thetaAboveCell0110)
    e24KC2ThetaAboveLeaf011010 e24KC2ThetaAboveLeaf011011 e24KC2ThetaAboveLeaf011012
      e24KC2ThetaAboveLeaf011013

theorem e24KC2ThetaAboveNode01102 :
    adaptiveCoverCheck 14 (childHL thetaAboveCell0110) = true :=
  adaptiveCoverCheck_succ_of_children 13 (childHL thetaAboveCell0110)
    e24KC2ThetaAboveNode011020 e24KC2ThetaAboveNode011021 e24KC2ThetaAboveNode011022
      e24KC2ThetaAboveNode011023

theorem e24KC2ThetaAboveNode01103 :
    adaptiveCoverCheck 14 (childHH thetaAboveCell0110) = true :=
  adaptiveCoverCheck_succ_of_children 13 (childHH thetaAboveCell0110)
    e24KC2ThetaAboveNode011030 e24KC2ThetaAboveNode011031 e24KC2ThetaAboveNode011032
      e24KC2ThetaAboveNode011033

theorem e24KC2ThetaAboveNode01110 :
    adaptiveCoverCheck 14 (childLL thetaAboveCell0111) = true :=
  adaptiveCoverCheck_succ_of_children 13 (childLL thetaAboveCell0111)
    e24KC2ThetaAboveLeaf011100 e24KC2ThetaAboveLeaf011101 e24KC2ThetaAboveLeaf011102
      e24KC2ThetaAboveLeaf011103

theorem e24KC2ThetaAboveNode01111 :
    adaptiveCoverCheck 14 (childLH thetaAboveCell0111) = true :=
  adaptiveCoverCheck_succ_of_children 13 (childLH thetaAboveCell0111)
    e24KC2ThetaAboveLeaf011110 e24KC2ThetaAboveLeaf011111 e24KC2ThetaAboveLeaf011112
      e24KC2ThetaAboveLeaf011113

theorem e24KC2ThetaAboveNode01112 :
    adaptiveCoverCheck 14 (childHL thetaAboveCell0111) = true :=
  adaptiveCoverCheck_succ_of_children 13 (childHL thetaAboveCell0111)
    e24KC2ThetaAboveNode011120 e24KC2ThetaAboveNode011121 e24KC2ThetaAboveNode011122
      e24KC2ThetaAboveNode011123

theorem e24KC2ThetaAboveNode01113 :
    adaptiveCoverCheck 14 (childHH thetaAboveCell0111) = true :=
  adaptiveCoverCheck_succ_of_children 13 (childHH thetaAboveCell0111)
    e24KC2ThetaAboveNode011130 e24KC2ThetaAboveNode011131 e24KC2ThetaAboveNode011132
      e24KC2ThetaAboveNode011133

theorem e24KC2ThetaAboveNode01120 :
    adaptiveCoverCheck 14 (childLL thetaAboveCell0112) = true :=
  adaptiveCoverCheck_succ_of_children 13 (childLL thetaAboveCell0112)
    e24KC2ThetaAboveNode011200 e24KC2ThetaAboveNode011201 e24KC2ThetaAboveLeaf011202
      e24KC2ThetaAboveLeaf011203

theorem e24KC2ThetaAboveNode01121 :
    adaptiveCoverCheck 14 (childLH thetaAboveCell0112) = true :=
  adaptiveCoverCheck_succ_of_children 13 (childLH thetaAboveCell0112)
    e24KC2ThetaAboveNode011210 e24KC2ThetaAboveNode011211 e24KC2ThetaAboveLeaf011212
      e24KC2ThetaAboveLeaf011213

theorem e24KC2ThetaAboveNode01130 :
    adaptiveCoverCheck 14 (childLL thetaAboveCell0113) = true :=
  adaptiveCoverCheck_succ_of_children 13 (childLL thetaAboveCell0113)
    e24KC2ThetaAboveNode011300 e24KC2ThetaAboveNode011301 e24KC2ThetaAboveLeaf011302
      e24KC2ThetaAboveLeaf011303

theorem e24KC2ThetaAboveNode01131 :
    adaptiveCoverCheck 14 (childLH thetaAboveCell0113) = true :=
  adaptiveCoverCheck_succ_of_children 13 (childLH thetaAboveCell0113)
    e24KC2ThetaAboveNode011310 e24KC2ThetaAboveNode011311 e24KC2ThetaAboveLeaf011312
      e24KC2ThetaAboveLeaf011313

theorem e24KC2ThetaAboveNode10000 :
    adaptiveCoverCheck 14 (childLL thetaAboveCell1000) = true :=
  adaptiveCoverCheck_succ_of_children 13 (childLL thetaAboveCell1000)
    e24KC2ThetaAboveLeaf100000 e24KC2ThetaAboveLeaf100001 e24KC2ThetaAboveLeaf100002
      e24KC2ThetaAboveLeaf100003

theorem e24KC2ThetaAboveNode10001 :
    adaptiveCoverCheck 14 (childLH thetaAboveCell1000) = true :=
  adaptiveCoverCheck_succ_of_children 13 (childLH thetaAboveCell1000)
    e24KC2ThetaAboveLeaf100010 e24KC2ThetaAboveLeaf100011 e24KC2ThetaAboveLeaf100012
      e24KC2ThetaAboveLeaf100013

theorem e24KC2ThetaAboveNode10002 :
    adaptiveCoverCheck 14 (childHL thetaAboveCell1000) = true :=
  adaptiveCoverCheck_succ_of_children 13 (childHL thetaAboveCell1000)
    e24KC2ThetaAboveNode100020 e24KC2ThetaAboveNode100021 e24KC2ThetaAboveNode100022
      e24KC2ThetaAboveNode100023

theorem e24KC2ThetaAboveNode10003 :
    adaptiveCoverCheck 14 (childHH thetaAboveCell1000) = true :=
  adaptiveCoverCheck_succ_of_children 13 (childHH thetaAboveCell1000)
    e24KC2ThetaAboveNode100030 e24KC2ThetaAboveNode100031 e24KC2ThetaAboveNode100032
      e24KC2ThetaAboveNode100033

theorem e24KC2ThetaAboveNode10010 :
    adaptiveCoverCheck 14 (childLL thetaAboveCell1001) = true :=
  adaptiveCoverCheck_succ_of_children 13 (childLL thetaAboveCell1001)
    e24KC2ThetaAboveLeaf100100 e24KC2ThetaAboveLeaf100101 e24KC2ThetaAboveLeaf100102
      e24KC2ThetaAboveLeaf100103

theorem e24KC2ThetaAboveNode10011 :
    adaptiveCoverCheck 14 (childLH thetaAboveCell1001) = true :=
  adaptiveCoverCheck_succ_of_children 13 (childLH thetaAboveCell1001)
    e24KC2ThetaAboveLeaf100110 e24KC2ThetaAboveLeaf100111 e24KC2ThetaAboveLeaf100112
      e24KC2ThetaAboveLeaf100113

theorem e24KC2ThetaAboveNode10012 :
    adaptiveCoverCheck 14 (childHL thetaAboveCell1001) = true :=
  adaptiveCoverCheck_succ_of_children 13 (childHL thetaAboveCell1001)
    e24KC2ThetaAboveNode100120 e24KC2ThetaAboveNode100121 e24KC2ThetaAboveNode100122
      e24KC2ThetaAboveNode100123

theorem e24KC2ThetaAboveNode10013 :
    adaptiveCoverCheck 14 (childHH thetaAboveCell1001) = true :=
  adaptiveCoverCheck_succ_of_children 13 (childHH thetaAboveCell1001)
    e24KC2ThetaAboveNode100130 e24KC2ThetaAboveNode100131 e24KC2ThetaAboveNode100132
      e24KC2ThetaAboveNode100133

theorem e24KC2ThetaAboveNode10020 :
    adaptiveCoverCheck 14 (childLL thetaAboveCell1002) = true :=
  adaptiveCoverCheck_succ_of_children 13 (childLL thetaAboveCell1002)
    e24KC2ThetaAboveNode100200 e24KC2ThetaAboveNode100201 e24KC2ThetaAboveLeaf100202
      e24KC2ThetaAboveLeaf100203

theorem e24KC2ThetaAboveNode10021 :
    adaptiveCoverCheck 14 (childLH thetaAboveCell1002) = true :=
  adaptiveCoverCheck_succ_of_children 13 (childLH thetaAboveCell1002)
    e24KC2ThetaAboveNode100210 e24KC2ThetaAboveNode100211 e24KC2ThetaAboveLeaf100212
      e24KC2ThetaAboveLeaf100213

theorem e24KC2ThetaAboveNode10030 :
    adaptiveCoverCheck 14 (childLL thetaAboveCell1003) = true :=
  adaptiveCoverCheck_succ_of_children 13 (childLL thetaAboveCell1003)
    e24KC2ThetaAboveNode100300 e24KC2ThetaAboveNode100301 e24KC2ThetaAboveLeaf100302
      e24KC2ThetaAboveLeaf100303

theorem e24KC2ThetaAboveNode10031 :
    adaptiveCoverCheck 14 (childLH thetaAboveCell1003) = true :=
  adaptiveCoverCheck_succ_of_children 13 (childLH thetaAboveCell1003)
    e24KC2ThetaAboveNode100310 e24KC2ThetaAboveNode100311 e24KC2ThetaAboveLeaf100312
      e24KC2ThetaAboveLeaf100313

theorem e24KC2ThetaAboveNode10100 :
    adaptiveCoverCheck 14 (childLL thetaAboveCell1010) = true :=
  adaptiveCoverCheck_succ_of_children 13 (childLL thetaAboveCell1010)
    e24KC2ThetaAboveLeaf101000 e24KC2ThetaAboveLeaf101001 e24KC2ThetaAboveLeaf101002
      e24KC2ThetaAboveLeaf101003

theorem e24KC2ThetaAboveNode10101 :
    adaptiveCoverCheck 14 (childLH thetaAboveCell1010) = true :=
  adaptiveCoverCheck_succ_of_children 13 (childLH thetaAboveCell1010)
    e24KC2ThetaAboveLeaf101010 e24KC2ThetaAboveLeaf101011 e24KC2ThetaAboveLeaf101012
      e24KC2ThetaAboveLeaf101013

theorem e24KC2ThetaAboveNode10102 :
    adaptiveCoverCheck 14 (childHL thetaAboveCell1010) = true :=
  adaptiveCoverCheck_succ_of_children 13 (childHL thetaAboveCell1010)
    e24KC2ThetaAboveNode101020 e24KC2ThetaAboveNode101021 e24KC2ThetaAboveNode101022
      e24KC2ThetaAboveNode101023

theorem e24KC2ThetaAboveNode10103 :
    adaptiveCoverCheck 14 (childHH thetaAboveCell1010) = true :=
  adaptiveCoverCheck_succ_of_children 13 (childHH thetaAboveCell1010)
    e24KC2ThetaAboveNode101030 e24KC2ThetaAboveNode101031 e24KC2ThetaAboveNode101032
      e24KC2ThetaAboveNode101033

theorem e24KC2ThetaAboveNode10110 :
    adaptiveCoverCheck 14 (childLL thetaAboveCell1011) = true :=
  adaptiveCoverCheck_succ_of_children 13 (childLL thetaAboveCell1011)
    e24KC2ThetaAboveLeaf101100 e24KC2ThetaAboveLeaf101101 e24KC2ThetaAboveLeaf101102
      e24KC2ThetaAboveLeaf101103

theorem e24KC2ThetaAboveNode10111 :
    adaptiveCoverCheck 14 (childLH thetaAboveCell1011) = true :=
  adaptiveCoverCheck_succ_of_children 13 (childLH thetaAboveCell1011)
    e24KC2ThetaAboveLeaf101110 e24KC2ThetaAboveLeaf101111 e24KC2ThetaAboveLeaf101112
      e24KC2ThetaAboveLeaf101113

theorem e24KC2ThetaAboveNode10112 :
    adaptiveCoverCheck 14 (childHL thetaAboveCell1011) = true :=
  adaptiveCoverCheck_succ_of_children 13 (childHL thetaAboveCell1011)
    e24KC2ThetaAboveNode101120 e24KC2ThetaAboveNode101121 e24KC2ThetaAboveNode101122
      e24KC2ThetaAboveNode101123

theorem e24KC2ThetaAboveNode10113 :
    adaptiveCoverCheck 14 (childHH thetaAboveCell1011) = true :=
  adaptiveCoverCheck_succ_of_children 13 (childHH thetaAboveCell1011)
    e24KC2ThetaAboveNode101130 e24KC2ThetaAboveNode101131 e24KC2ThetaAboveNode101132
      e24KC2ThetaAboveNode101133

theorem e24KC2ThetaAboveNode10120 :
    adaptiveCoverCheck 14 (childLL thetaAboveCell1012) = true :=
  adaptiveCoverCheck_succ_of_children 13 (childLL thetaAboveCell1012)
    e24KC2ThetaAboveNode101200 e24KC2ThetaAboveNode101201 e24KC2ThetaAboveLeaf101202
      e24KC2ThetaAboveLeaf101203

theorem e24KC2ThetaAboveNode10121 :
    adaptiveCoverCheck 14 (childLH thetaAboveCell1012) = true :=
  adaptiveCoverCheck_succ_of_children 13 (childLH thetaAboveCell1012)
    e24KC2ThetaAboveNode101210 e24KC2ThetaAboveNode101211 e24KC2ThetaAboveLeaf101212
      e24KC2ThetaAboveLeaf101213

theorem e24KC2ThetaAboveNode10130 :
    adaptiveCoverCheck 14 (childLL thetaAboveCell1013) = true :=
  adaptiveCoverCheck_succ_of_children 13 (childLL thetaAboveCell1013)
    e24KC2ThetaAboveNode101300 e24KC2ThetaAboveNode101301 e24KC2ThetaAboveLeaf101302
      e24KC2ThetaAboveLeaf101303

theorem e24KC2ThetaAboveNode10131 :
    adaptiveCoverCheck 14 (childLH thetaAboveCell1013) = true :=
  adaptiveCoverCheck_succ_of_children 13 (childLH thetaAboveCell1013)
    e24KC2ThetaAboveNode101310 e24KC2ThetaAboveNode101311 e24KC2ThetaAboveLeaf101312
      e24KC2ThetaAboveLeaf101313

theorem e24KC2ThetaAboveNode11000 :
    adaptiveCoverCheck 14 (childLL thetaAboveCell1100) = true :=
  adaptiveCoverCheck_succ_of_children 13 (childLL thetaAboveCell1100)
    e24KC2ThetaAboveLeaf110000 e24KC2ThetaAboveLeaf110001 e24KC2ThetaAboveLeaf110002
      e24KC2ThetaAboveLeaf110003

theorem e24KC2ThetaAboveNode11001 :
    adaptiveCoverCheck 14 (childLH thetaAboveCell1100) = true :=
  adaptiveCoverCheck_succ_of_children 13 (childLH thetaAboveCell1100)
    e24KC2ThetaAboveLeaf110010 e24KC2ThetaAboveLeaf110011 e24KC2ThetaAboveLeaf110012
      e24KC2ThetaAboveLeaf110013

theorem e24KC2ThetaAboveNode11002 :
    adaptiveCoverCheck 14 (childHL thetaAboveCell1100) = true :=
  adaptiveCoverCheck_succ_of_children 13 (childHL thetaAboveCell1100)
    e24KC2ThetaAboveNode110020 e24KC2ThetaAboveNode110021 e24KC2ThetaAboveNode110022
      e24KC2ThetaAboveNode110023

theorem e24KC2ThetaAboveNode11003 :
    adaptiveCoverCheck 14 (childHH thetaAboveCell1100) = true :=
  adaptiveCoverCheck_succ_of_children 13 (childHH thetaAboveCell1100)
    e24KC2ThetaAboveNode110030 e24KC2ThetaAboveNode110031 e24KC2ThetaAboveNode110032
      e24KC2ThetaAboveNode110033

theorem e24KC2ThetaAboveNode11010 :
    adaptiveCoverCheck 14 (childLL thetaAboveCell1101) = true :=
  adaptiveCoverCheck_succ_of_children 13 (childLL thetaAboveCell1101)
    e24KC2ThetaAboveLeaf110100 e24KC2ThetaAboveLeaf110101 e24KC2ThetaAboveLeaf110102
      e24KC2ThetaAboveLeaf110103

theorem e24KC2ThetaAboveNode11011 :
    adaptiveCoverCheck 14 (childLH thetaAboveCell1101) = true :=
  adaptiveCoverCheck_succ_of_children 13 (childLH thetaAboveCell1101)
    e24KC2ThetaAboveLeaf110110 e24KC2ThetaAboveLeaf110111 e24KC2ThetaAboveLeaf110112
      e24KC2ThetaAboveLeaf110113

theorem e24KC2ThetaAboveNode11012 :
    adaptiveCoverCheck 14 (childHL thetaAboveCell1101) = true :=
  adaptiveCoverCheck_succ_of_children 13 (childHL thetaAboveCell1101)
    e24KC2ThetaAboveNode110120 e24KC2ThetaAboveNode110121 e24KC2ThetaAboveNode110122
      e24KC2ThetaAboveNode110123

theorem e24KC2ThetaAboveNode11013 :
    adaptiveCoverCheck 14 (childHH thetaAboveCell1101) = true :=
  adaptiveCoverCheck_succ_of_children 13 (childHH thetaAboveCell1101)
    e24KC2ThetaAboveNode110130 e24KC2ThetaAboveNode110131 e24KC2ThetaAboveNode110132
      e24KC2ThetaAboveNode110133

theorem e24KC2ThetaAboveNode11020 :
    adaptiveCoverCheck 14 (childLL thetaAboveCell1102) = true :=
  adaptiveCoverCheck_succ_of_children 13 (childLL thetaAboveCell1102)
    e24KC2ThetaAboveNode110200 e24KC2ThetaAboveNode110201 e24KC2ThetaAboveLeaf110202
      e24KC2ThetaAboveLeaf110203

theorem e24KC2ThetaAboveNode11021 :
    adaptiveCoverCheck 14 (childLH thetaAboveCell1102) = true :=
  adaptiveCoverCheck_succ_of_children 13 (childLH thetaAboveCell1102)
    e24KC2ThetaAboveNode110210 e24KC2ThetaAboveNode110211 e24KC2ThetaAboveLeaf110212
      e24KC2ThetaAboveLeaf110213

theorem e24KC2ThetaAboveNode11030 :
    adaptiveCoverCheck 14 (childLL thetaAboveCell1103) = true :=
  adaptiveCoverCheck_succ_of_children 13 (childLL thetaAboveCell1103)
    e24KC2ThetaAboveNode110300 e24KC2ThetaAboveNode110301 e24KC2ThetaAboveLeaf110302
      e24KC2ThetaAboveLeaf110303

theorem e24KC2ThetaAboveNode11031 :
    adaptiveCoverCheck 14 (childLH thetaAboveCell1103) = true :=
  adaptiveCoverCheck_succ_of_children 13 (childLH thetaAboveCell1103)
    e24KC2ThetaAboveNode110310 e24KC2ThetaAboveNode110311 e24KC2ThetaAboveLeaf110312
      e24KC2ThetaAboveLeaf110313

theorem e24KC2ThetaAboveNode11100 :
    adaptiveCoverCheck 14 (childLL thetaAboveCell1110) = true :=
  adaptiveCoverCheck_succ_of_children 13 (childLL thetaAboveCell1110)
    e24KC2ThetaAboveLeaf111000 e24KC2ThetaAboveLeaf111001 e24KC2ThetaAboveLeaf111002
      e24KC2ThetaAboveLeaf111003

theorem e24KC2ThetaAboveNode11101 :
    adaptiveCoverCheck 14 (childLH thetaAboveCell1110) = true :=
  adaptiveCoverCheck_succ_of_children 13 (childLH thetaAboveCell1110)
    e24KC2ThetaAboveLeaf111010 e24KC2ThetaAboveLeaf111011 e24KC2ThetaAboveLeaf111012
      e24KC2ThetaAboveLeaf111013

theorem e24KC2ThetaAboveNode11102 :
    adaptiveCoverCheck 14 (childHL thetaAboveCell1110) = true :=
  adaptiveCoverCheck_succ_of_children 13 (childHL thetaAboveCell1110)
    e24KC2ThetaAboveNode111020 e24KC2ThetaAboveNode111021 e24KC2ThetaAboveNode111022
      e24KC2ThetaAboveNode111023

theorem e24KC2ThetaAboveNode11103 :
    adaptiveCoverCheck 14 (childHH thetaAboveCell1110) = true :=
  adaptiveCoverCheck_succ_of_children 13 (childHH thetaAboveCell1110)
    e24KC2ThetaAboveNode111030 e24KC2ThetaAboveNode111031 e24KC2ThetaAboveNode111032
      e24KC2ThetaAboveNode111033

theorem e24KC2ThetaAboveNode11110 :
    adaptiveCoverCheck 14 (childLL thetaAboveCell1111) = true :=
  adaptiveCoverCheck_succ_of_children 13 (childLL thetaAboveCell1111)
    e24KC2ThetaAboveLeaf111100 e24KC2ThetaAboveLeaf111101 e24KC2ThetaAboveLeaf111102
      e24KC2ThetaAboveLeaf111103

theorem e24KC2ThetaAboveNode11111 :
    adaptiveCoverCheck 14 (childLH thetaAboveCell1111) = true :=
  adaptiveCoverCheck_succ_of_children 13 (childLH thetaAboveCell1111)
    e24KC2ThetaAboveLeaf111110 e24KC2ThetaAboveLeaf111111 e24KC2ThetaAboveLeaf111112
      e24KC2ThetaAboveLeaf111113

theorem e24KC2ThetaAboveNode11112 :
    adaptiveCoverCheck 14 (childHL thetaAboveCell1111) = true :=
  adaptiveCoverCheck_succ_of_children 13 (childHL thetaAboveCell1111)
    e24KC2ThetaAboveNode111120 e24KC2ThetaAboveNode111121 e24KC2ThetaAboveNode111122
      e24KC2ThetaAboveNode111123

theorem e24KC2ThetaAboveNode11113 :
    adaptiveCoverCheck 14 (childHH thetaAboveCell1111) = true :=
  adaptiveCoverCheck_succ_of_children 13 (childHH thetaAboveCell1111)
    e24KC2ThetaAboveNode111130 e24KC2ThetaAboveNode111131 e24KC2ThetaAboveNode111132
      e24KC2ThetaAboveNode111133

theorem e24KC2ThetaAboveNode11120 :
    adaptiveCoverCheck 14 (childLL thetaAboveCell1112) = true :=
  adaptiveCoverCheck_succ_of_children 13 (childLL thetaAboveCell1112)
    e24KC2ThetaAboveNode111200 e24KC2ThetaAboveNode111201 e24KC2ThetaAboveLeaf111202
      e24KC2ThetaAboveLeaf111203

theorem e24KC2ThetaAboveNode11121 :
    adaptiveCoverCheck 14 (childLH thetaAboveCell1112) = true :=
  adaptiveCoverCheck_succ_of_children 13 (childLH thetaAboveCell1112)
    e24KC2ThetaAboveNode111210 e24KC2ThetaAboveNode111211 e24KC2ThetaAboveLeaf111212
      e24KC2ThetaAboveLeaf111213

theorem e24KC2ThetaAboveNode11130 :
    adaptiveCoverCheck 14 (childLL thetaAboveCell1113) = true :=
  adaptiveCoverCheck_succ_of_children 13 (childLL thetaAboveCell1113)
    e24KC2ThetaAboveNode111300 e24KC2ThetaAboveNode111301 e24KC2ThetaAboveLeaf111302
      e24KC2ThetaAboveLeaf111303

theorem e24KC2ThetaAboveNode11131 :
    adaptiveCoverCheck 14 (childLH thetaAboveCell1113) = true :=
  adaptiveCoverCheck_succ_of_children 13 (childLH thetaAboveCell1113)
    e24KC2ThetaAboveNode111310 e24KC2ThetaAboveNode111311 e24KC2ThetaAboveLeaf111312
      e24KC2ThetaAboveLeaf111313

theorem e24KC2ThetaAboveNode0000 :
    adaptiveCoverCheck 15 thetaAboveCell0000 = true :=
  adaptiveCoverCheck_succ_of_children 14 thetaAboveCell0000
    e24KC2ThetaAboveNode00000 e24KC2ThetaAboveNode00001 e24KC2ThetaAboveNode00002
      e24KC2ThetaAboveNode00003

theorem e24KC2ThetaAboveNode0001 :
    adaptiveCoverCheck 15 thetaAboveCell0001 = true :=
  adaptiveCoverCheck_succ_of_children 14 thetaAboveCell0001
    e24KC2ThetaAboveNode00010 e24KC2ThetaAboveNode00011 e24KC2ThetaAboveNode00012
      e24KC2ThetaAboveNode00013

theorem e24KC2ThetaAboveNode0002 :
    adaptiveCoverCheck 15 thetaAboveCell0002 = true :=
  adaptiveCoverCheck_succ_of_children 14 thetaAboveCell0002
    e24KC2ThetaAboveNode00020 e24KC2ThetaAboveNode00021 e24KC2ThetaAboveLeaf00022
      e24KC2ThetaAboveLeaf00023

theorem e24KC2ThetaAboveNode0003 :
    adaptiveCoverCheck 15 thetaAboveCell0003 = true :=
  adaptiveCoverCheck_succ_of_children 14 thetaAboveCell0003
    e24KC2ThetaAboveNode00030 e24KC2ThetaAboveNode00031 e24KC2ThetaAboveLeaf00032
      e24KC2ThetaAboveLeaf00033

theorem e24KC2ThetaAboveNode0010 :
    adaptiveCoverCheck 15 thetaAboveCell0010 = true :=
  adaptiveCoverCheck_succ_of_children 14 thetaAboveCell0010
    e24KC2ThetaAboveNode00100 e24KC2ThetaAboveNode00101 e24KC2ThetaAboveNode00102
      e24KC2ThetaAboveNode00103

theorem e24KC2ThetaAboveNode0011 :
    adaptiveCoverCheck 15 thetaAboveCell0011 = true :=
  adaptiveCoverCheck_succ_of_children 14 thetaAboveCell0011
    e24KC2ThetaAboveNode00110 e24KC2ThetaAboveNode00111 e24KC2ThetaAboveNode00112
      e24KC2ThetaAboveNode00113

theorem e24KC2ThetaAboveNode0012 :
    adaptiveCoverCheck 15 thetaAboveCell0012 = true :=
  adaptiveCoverCheck_succ_of_children 14 thetaAboveCell0012
    e24KC2ThetaAboveNode00120 e24KC2ThetaAboveNode00121 e24KC2ThetaAboveLeaf00122
      e24KC2ThetaAboveLeaf00123

theorem e24KC2ThetaAboveNode0013 :
    adaptiveCoverCheck 15 thetaAboveCell0013 = true :=
  adaptiveCoverCheck_succ_of_children 14 thetaAboveCell0013
    e24KC2ThetaAboveNode00130 e24KC2ThetaAboveNode00131 e24KC2ThetaAboveLeaf00132
      e24KC2ThetaAboveLeaf00133

theorem e24KC2ThetaAboveNode0100 :
    adaptiveCoverCheck 15 thetaAboveCell0100 = true :=
  adaptiveCoverCheck_succ_of_children 14 thetaAboveCell0100
    e24KC2ThetaAboveNode01000 e24KC2ThetaAboveNode01001 e24KC2ThetaAboveNode01002
      e24KC2ThetaAboveNode01003

theorem e24KC2ThetaAboveNode0101 :
    adaptiveCoverCheck 15 thetaAboveCell0101 = true :=
  adaptiveCoverCheck_succ_of_children 14 thetaAboveCell0101
    e24KC2ThetaAboveNode01010 e24KC2ThetaAboveNode01011 e24KC2ThetaAboveNode01012
      e24KC2ThetaAboveNode01013

theorem e24KC2ThetaAboveNode0102 :
    adaptiveCoverCheck 15 thetaAboveCell0102 = true :=
  adaptiveCoverCheck_succ_of_children 14 thetaAboveCell0102
    e24KC2ThetaAboveNode01020 e24KC2ThetaAboveNode01021 e24KC2ThetaAboveLeaf01022
      e24KC2ThetaAboveLeaf01023

theorem e24KC2ThetaAboveNode0103 :
    adaptiveCoverCheck 15 thetaAboveCell0103 = true :=
  adaptiveCoverCheck_succ_of_children 14 thetaAboveCell0103
    e24KC2ThetaAboveNode01030 e24KC2ThetaAboveNode01031 e24KC2ThetaAboveLeaf01032
      e24KC2ThetaAboveLeaf01033

theorem e24KC2ThetaAboveNode0110 :
    adaptiveCoverCheck 15 thetaAboveCell0110 = true :=
  adaptiveCoverCheck_succ_of_children 14 thetaAboveCell0110
    e24KC2ThetaAboveNode01100 e24KC2ThetaAboveNode01101 e24KC2ThetaAboveNode01102
      e24KC2ThetaAboveNode01103

theorem e24KC2ThetaAboveNode0111 :
    adaptiveCoverCheck 15 thetaAboveCell0111 = true :=
  adaptiveCoverCheck_succ_of_children 14 thetaAboveCell0111
    e24KC2ThetaAboveNode01110 e24KC2ThetaAboveNode01111 e24KC2ThetaAboveNode01112
      e24KC2ThetaAboveNode01113

theorem e24KC2ThetaAboveNode0112 :
    adaptiveCoverCheck 15 thetaAboveCell0112 = true :=
  adaptiveCoverCheck_succ_of_children 14 thetaAboveCell0112
    e24KC2ThetaAboveNode01120 e24KC2ThetaAboveNode01121 e24KC2ThetaAboveLeaf01122
      e24KC2ThetaAboveLeaf01123

theorem e24KC2ThetaAboveNode0113 :
    adaptiveCoverCheck 15 thetaAboveCell0113 = true :=
  adaptiveCoverCheck_succ_of_children 14 thetaAboveCell0113
    e24KC2ThetaAboveNode01130 e24KC2ThetaAboveNode01131 e24KC2ThetaAboveLeaf01132
      e24KC2ThetaAboveLeaf01133

theorem e24KC2ThetaAboveNode1000 :
    adaptiveCoverCheck 15 thetaAboveCell1000 = true :=
  adaptiveCoverCheck_succ_of_children 14 thetaAboveCell1000
    e24KC2ThetaAboveNode10000 e24KC2ThetaAboveNode10001 e24KC2ThetaAboveNode10002
      e24KC2ThetaAboveNode10003

theorem e24KC2ThetaAboveNode1001 :
    adaptiveCoverCheck 15 thetaAboveCell1001 = true :=
  adaptiveCoverCheck_succ_of_children 14 thetaAboveCell1001
    e24KC2ThetaAboveNode10010 e24KC2ThetaAboveNode10011 e24KC2ThetaAboveNode10012
      e24KC2ThetaAboveNode10013

theorem e24KC2ThetaAboveNode1002 :
    adaptiveCoverCheck 15 thetaAboveCell1002 = true :=
  adaptiveCoverCheck_succ_of_children 14 thetaAboveCell1002
    e24KC2ThetaAboveNode10020 e24KC2ThetaAboveNode10021 e24KC2ThetaAboveLeaf10022
      e24KC2ThetaAboveLeaf10023

theorem e24KC2ThetaAboveNode1003 :
    adaptiveCoverCheck 15 thetaAboveCell1003 = true :=
  adaptiveCoverCheck_succ_of_children 14 thetaAboveCell1003
    e24KC2ThetaAboveNode10030 e24KC2ThetaAboveNode10031 e24KC2ThetaAboveLeaf10032
      e24KC2ThetaAboveLeaf10033

theorem e24KC2ThetaAboveNode1010 :
    adaptiveCoverCheck 15 thetaAboveCell1010 = true :=
  adaptiveCoverCheck_succ_of_children 14 thetaAboveCell1010
    e24KC2ThetaAboveNode10100 e24KC2ThetaAboveNode10101 e24KC2ThetaAboveNode10102
      e24KC2ThetaAboveNode10103

theorem e24KC2ThetaAboveNode1011 :
    adaptiveCoverCheck 15 thetaAboveCell1011 = true :=
  adaptiveCoverCheck_succ_of_children 14 thetaAboveCell1011
    e24KC2ThetaAboveNode10110 e24KC2ThetaAboveNode10111 e24KC2ThetaAboveNode10112
      e24KC2ThetaAboveNode10113

theorem e24KC2ThetaAboveNode1012 :
    adaptiveCoverCheck 15 thetaAboveCell1012 = true :=
  adaptiveCoverCheck_succ_of_children 14 thetaAboveCell1012
    e24KC2ThetaAboveNode10120 e24KC2ThetaAboveNode10121 e24KC2ThetaAboveLeaf10122
      e24KC2ThetaAboveLeaf10123

theorem e24KC2ThetaAboveNode1013 :
    adaptiveCoverCheck 15 thetaAboveCell1013 = true :=
  adaptiveCoverCheck_succ_of_children 14 thetaAboveCell1013
    e24KC2ThetaAboveNode10130 e24KC2ThetaAboveNode10131 e24KC2ThetaAboveLeaf10132
      e24KC2ThetaAboveLeaf10133

theorem e24KC2ThetaAboveNode1100 :
    adaptiveCoverCheck 15 thetaAboveCell1100 = true :=
  adaptiveCoverCheck_succ_of_children 14 thetaAboveCell1100
    e24KC2ThetaAboveNode11000 e24KC2ThetaAboveNode11001 e24KC2ThetaAboveNode11002
      e24KC2ThetaAboveNode11003

theorem e24KC2ThetaAboveNode1101 :
    adaptiveCoverCheck 15 thetaAboveCell1101 = true :=
  adaptiveCoverCheck_succ_of_children 14 thetaAboveCell1101
    e24KC2ThetaAboveNode11010 e24KC2ThetaAboveNode11011 e24KC2ThetaAboveNode11012
      e24KC2ThetaAboveNode11013

theorem e24KC2ThetaAboveNode1102 :
    adaptiveCoverCheck 15 thetaAboveCell1102 = true :=
  adaptiveCoverCheck_succ_of_children 14 thetaAboveCell1102
    e24KC2ThetaAboveNode11020 e24KC2ThetaAboveNode11021 e24KC2ThetaAboveLeaf11022
      e24KC2ThetaAboveLeaf11023

theorem e24KC2ThetaAboveNode1103 :
    adaptiveCoverCheck 15 thetaAboveCell1103 = true :=
  adaptiveCoverCheck_succ_of_children 14 thetaAboveCell1103
    e24KC2ThetaAboveNode11030 e24KC2ThetaAboveNode11031 e24KC2ThetaAboveLeaf11032
      e24KC2ThetaAboveLeaf11033

theorem e24KC2ThetaAboveNode1110 :
    adaptiveCoverCheck 15 thetaAboveCell1110 = true :=
  adaptiveCoverCheck_succ_of_children 14 thetaAboveCell1110
    e24KC2ThetaAboveNode11100 e24KC2ThetaAboveNode11101 e24KC2ThetaAboveNode11102
      e24KC2ThetaAboveNode11103

theorem e24KC2ThetaAboveNode1111 :
    adaptiveCoverCheck 15 thetaAboveCell1111 = true :=
  adaptiveCoverCheck_succ_of_children 14 thetaAboveCell1111
    e24KC2ThetaAboveNode11110 e24KC2ThetaAboveNode11111 e24KC2ThetaAboveNode11112
      e24KC2ThetaAboveNode11113

theorem e24KC2ThetaAboveNode1112 :
    adaptiveCoverCheck 15 thetaAboveCell1112 = true :=
  adaptiveCoverCheck_succ_of_children 14 thetaAboveCell1112
    e24KC2ThetaAboveNode11120 e24KC2ThetaAboveNode11121 e24KC2ThetaAboveLeaf11122
      e24KC2ThetaAboveLeaf11123

theorem e24KC2ThetaAboveNode1113 :
    adaptiveCoverCheck 15 thetaAboveCell1113 = true :=
  adaptiveCoverCheck_succ_of_children 14 thetaAboveCell1113
    e24KC2ThetaAboveNode11130 e24KC2ThetaAboveNode11131 e24KC2ThetaAboveLeaf11132
      e24KC2ThetaAboveLeaf11133

theorem e24KC2ThetaAboveNode000 :
    adaptiveCoverCheck 16 (childLL (childLL (childLL e24ThetaAboveRoot))) = true :=
  adaptiveCoverCheck_succ_of_children 15 (childLL (childLL (childLL e24ThetaAboveRoot)))
    e24KC2ThetaAboveNode0000 e24KC2ThetaAboveNode0001 e24KC2ThetaAboveNode0002
      e24KC2ThetaAboveNode0003

theorem e24KC2ThetaAboveNode001 :
    adaptiveCoverCheck 16 (childLH (childLL (childLL e24ThetaAboveRoot))) = true :=
  adaptiveCoverCheck_succ_of_children 15 (childLH (childLL (childLL e24ThetaAboveRoot)))
    e24KC2ThetaAboveNode0010 e24KC2ThetaAboveNode0011 e24KC2ThetaAboveNode0012
      e24KC2ThetaAboveNode0013

theorem e24KC2ThetaAboveNode002 :
    adaptiveCoverCheck 16 (childHL (childLL (childLL e24ThetaAboveRoot))) = true :=
  adaptiveCoverCheck_succ_of_children 15 (childHL (childLL (childLL e24ThetaAboveRoot)))
    e24KC2ThetaAboveLeaf0020 e24KC2ThetaAboveLeaf0021 e24KC2ThetaAboveLeaf0022
      e24KC2ThetaAboveLeaf0023

theorem e24KC2ThetaAboveNode003 :
    adaptiveCoverCheck 16 (childHH (childLL (childLL e24ThetaAboveRoot))) = true :=
  adaptiveCoverCheck_succ_of_children 15 (childHH (childLL (childLL e24ThetaAboveRoot)))
    e24KC2ThetaAboveLeaf0030 e24KC2ThetaAboveLeaf0031 e24KC2ThetaAboveLeaf0032
      e24KC2ThetaAboveLeaf0033

theorem e24KC2ThetaAboveNode010 :
    adaptiveCoverCheck 16 (childLL (childLH (childLL e24ThetaAboveRoot))) = true :=
  adaptiveCoverCheck_succ_of_children 15 (childLL (childLH (childLL e24ThetaAboveRoot)))
    e24KC2ThetaAboveNode0100 e24KC2ThetaAboveNode0101 e24KC2ThetaAboveNode0102
      e24KC2ThetaAboveNode0103

theorem e24KC2ThetaAboveNode011 :
    adaptiveCoverCheck 16 (childLH (childLH (childLL e24ThetaAboveRoot))) = true :=
  adaptiveCoverCheck_succ_of_children 15 (childLH (childLH (childLL e24ThetaAboveRoot)))
    e24KC2ThetaAboveNode0110 e24KC2ThetaAboveNode0111 e24KC2ThetaAboveNode0112
      e24KC2ThetaAboveNode0113

theorem e24KC2ThetaAboveNode012 :
    adaptiveCoverCheck 16 (childHL (childLH (childLL e24ThetaAboveRoot))) = true :=
  adaptiveCoverCheck_succ_of_children 15 (childHL (childLH (childLL e24ThetaAboveRoot)))
    e24KC2ThetaAboveLeaf0120 e24KC2ThetaAboveLeaf0121 e24KC2ThetaAboveLeaf0122
      e24KC2ThetaAboveLeaf0123

theorem e24KC2ThetaAboveNode013 :
    adaptiveCoverCheck 16 (childHH (childLH (childLL e24ThetaAboveRoot))) = true :=
  adaptiveCoverCheck_succ_of_children 15 (childHH (childLH (childLL e24ThetaAboveRoot)))
    e24KC2ThetaAboveLeaf0130 e24KC2ThetaAboveLeaf0131 e24KC2ThetaAboveLeaf0132
      e24KC2ThetaAboveLeaf0133

theorem e24KC2ThetaAboveNode100 :
    adaptiveCoverCheck 16 (childLL (childLL (childLH e24ThetaAboveRoot))) = true :=
  adaptiveCoverCheck_succ_of_children 15 (childLL (childLL (childLH e24ThetaAboveRoot)))
    e24KC2ThetaAboveNode1000 e24KC2ThetaAboveNode1001 e24KC2ThetaAboveNode1002
      e24KC2ThetaAboveNode1003

theorem e24KC2ThetaAboveNode101 :
    adaptiveCoverCheck 16 (childLH (childLL (childLH e24ThetaAboveRoot))) = true :=
  adaptiveCoverCheck_succ_of_children 15 (childLH (childLL (childLH e24ThetaAboveRoot)))
    e24KC2ThetaAboveNode1010 e24KC2ThetaAboveNode1011 e24KC2ThetaAboveNode1012
      e24KC2ThetaAboveNode1013

theorem e24KC2ThetaAboveNode102 :
    adaptiveCoverCheck 16 (childHL (childLL (childLH e24ThetaAboveRoot))) = true :=
  adaptiveCoverCheck_succ_of_children 15 (childHL (childLL (childLH e24ThetaAboveRoot)))
    e24KC2ThetaAboveLeaf1020 e24KC2ThetaAboveLeaf1021 e24KC2ThetaAboveLeaf1022
      e24KC2ThetaAboveLeaf1023

theorem e24KC2ThetaAboveNode103 :
    adaptiveCoverCheck 16 (childHH (childLL (childLH e24ThetaAboveRoot))) = true :=
  adaptiveCoverCheck_succ_of_children 15 (childHH (childLL (childLH e24ThetaAboveRoot)))
    e24KC2ThetaAboveLeaf1030 e24KC2ThetaAboveLeaf1031 e24KC2ThetaAboveLeaf1032
      e24KC2ThetaAboveLeaf1033

theorem e24KC2ThetaAboveNode110 :
    adaptiveCoverCheck 16 (childLL (childLH (childLH e24ThetaAboveRoot))) = true :=
  adaptiveCoverCheck_succ_of_children 15 (childLL (childLH (childLH e24ThetaAboveRoot)))
    e24KC2ThetaAboveNode1100 e24KC2ThetaAboveNode1101 e24KC2ThetaAboveNode1102
      e24KC2ThetaAboveNode1103

theorem e24KC2ThetaAboveNode111 :
    adaptiveCoverCheck 16 (childLH (childLH (childLH e24ThetaAboveRoot))) = true :=
  adaptiveCoverCheck_succ_of_children 15 (childLH (childLH (childLH e24ThetaAboveRoot)))
    e24KC2ThetaAboveNode1110 e24KC2ThetaAboveNode1111 e24KC2ThetaAboveNode1112
      e24KC2ThetaAboveNode1113

theorem e24KC2ThetaAboveNode112 :
    adaptiveCoverCheck 16 (childHL (childLH (childLH e24ThetaAboveRoot))) = true :=
  adaptiveCoverCheck_succ_of_children 15 (childHL (childLH (childLH e24ThetaAboveRoot)))
    e24KC2ThetaAboveLeaf1120 e24KC2ThetaAboveLeaf1121 e24KC2ThetaAboveLeaf1122
      e24KC2ThetaAboveLeaf1123

theorem e24KC2ThetaAboveNode113 :
    adaptiveCoverCheck 16 (childHH (childLH (childLH e24ThetaAboveRoot))) = true :=
  adaptiveCoverCheck_succ_of_children 15 (childHH (childLH (childLH e24ThetaAboveRoot)))
    e24KC2ThetaAboveLeaf1130 e24KC2ThetaAboveLeaf1131 e24KC2ThetaAboveLeaf1132
      e24KC2ThetaAboveLeaf1133

theorem e24KC2ThetaAboveNode00 :
    adaptiveCoverCheck 17 (childLL (childLL e24ThetaAboveRoot)) = true :=
  adaptiveCoverCheck_succ_of_children 16 (childLL (childLL e24ThetaAboveRoot))
    e24KC2ThetaAboveNode000 e24KC2ThetaAboveNode001 e24KC2ThetaAboveNode002 e24KC2ThetaAboveNode003

theorem e24KC2ThetaAboveNode01 :
    adaptiveCoverCheck 17 (childLH (childLL e24ThetaAboveRoot)) = true :=
  adaptiveCoverCheck_succ_of_children 16 (childLH (childLL e24ThetaAboveRoot))
    e24KC2ThetaAboveNode010 e24KC2ThetaAboveNode011 e24KC2ThetaAboveNode012 e24KC2ThetaAboveNode013

theorem e24KC2ThetaAboveNode02 :
    adaptiveCoverCheck 17 (childHL (childLL e24ThetaAboveRoot)) = true :=
  adaptiveCoverCheck_succ_of_children 16 (childHL (childLL e24ThetaAboveRoot))
    e24KC2ThetaAboveLeaf020 e24KC2ThetaAboveLeaf021 e24KC2ThetaAboveLeaf022 e24KC2ThetaAboveLeaf023

theorem e24KC2ThetaAboveNode03 :
    adaptiveCoverCheck 17 (childHH (childLL e24ThetaAboveRoot)) = true :=
  adaptiveCoverCheck_succ_of_children 16 (childHH (childLL e24ThetaAboveRoot))
    e24KC2ThetaAboveLeaf030 e24KC2ThetaAboveLeaf031 e24KC2ThetaAboveLeaf032 e24KC2ThetaAboveLeaf033

theorem e24KC2ThetaAboveNode10 :
    adaptiveCoverCheck 17 (childLL (childLH e24ThetaAboveRoot)) = true :=
  adaptiveCoverCheck_succ_of_children 16 (childLL (childLH e24ThetaAboveRoot))
    e24KC2ThetaAboveNode100 e24KC2ThetaAboveNode101 e24KC2ThetaAboveNode102 e24KC2ThetaAboveNode103

theorem e24KC2ThetaAboveNode11 :
    adaptiveCoverCheck 17 (childLH (childLH e24ThetaAboveRoot)) = true :=
  adaptiveCoverCheck_succ_of_children 16 (childLH (childLH e24ThetaAboveRoot))
    e24KC2ThetaAboveNode110 e24KC2ThetaAboveNode111 e24KC2ThetaAboveNode112 e24KC2ThetaAboveNode113

theorem e24KC2ThetaAboveNode12 :
    adaptiveCoverCheck 17 (childHL (childLH e24ThetaAboveRoot)) = true :=
  adaptiveCoverCheck_succ_of_children 16 (childHL (childLH e24ThetaAboveRoot))
    e24KC2ThetaAboveLeaf120 e24KC2ThetaAboveLeaf121 e24KC2ThetaAboveLeaf122 e24KC2ThetaAboveLeaf123

theorem e24KC2ThetaAboveNode13 :
    adaptiveCoverCheck 17 (childHH (childLH e24ThetaAboveRoot)) = true :=
  adaptiveCoverCheck_succ_of_children 16 (childHH (childLH e24ThetaAboveRoot))
    e24KC2ThetaAboveLeaf130 e24KC2ThetaAboveLeaf131 e24KC2ThetaAboveLeaf132 e24KC2ThetaAboveLeaf133

theorem e24KC2ThetaAboveNode20 :
    adaptiveCoverCheck 17 (childLL (childHL e24ThetaAboveRoot)) = true :=
  adaptiveCoverCheck_succ_of_children 16 (childLL (childHL e24ThetaAboveRoot))
    e24KC2ThetaAboveLeaf200 e24KC2ThetaAboveLeaf201 e24KC2ThetaAboveLeaf202 e24KC2ThetaAboveLeaf203

theorem e24KC2ThetaAboveNode21 :
    adaptiveCoverCheck 17 (childLH (childHL e24ThetaAboveRoot)) = true :=
  adaptiveCoverCheck_succ_of_children 16 (childLH (childHL e24ThetaAboveRoot))
    e24KC2ThetaAboveLeaf210 e24KC2ThetaAboveLeaf211 e24KC2ThetaAboveLeaf212 e24KC2ThetaAboveLeaf213

theorem e24KC2ThetaAboveNode22 :
    adaptiveCoverCheck 17 (childHL (childHL e24ThetaAboveRoot)) = true :=
  adaptiveCoverCheck_succ_of_children 16 (childHL (childHL e24ThetaAboveRoot))
    e24KC2ThetaAboveLeaf220 e24KC2ThetaAboveLeaf221 e24KC2ThetaAboveLeaf222 e24KC2ThetaAboveLeaf223

theorem e24KC2ThetaAboveNode23 :
    adaptiveCoverCheck 17 (childHH (childHL e24ThetaAboveRoot)) = true :=
  adaptiveCoverCheck_succ_of_children 16 (childHH (childHL e24ThetaAboveRoot))
    e24KC2ThetaAboveLeaf230 e24KC2ThetaAboveLeaf231 e24KC2ThetaAboveLeaf232 e24KC2ThetaAboveLeaf233

theorem e24KC2ThetaAboveNode30 :
    adaptiveCoverCheck 17 (childLL (childHH e24ThetaAboveRoot)) = true :=
  adaptiveCoverCheck_succ_of_children 16 (childLL (childHH e24ThetaAboveRoot))
    e24KC2ThetaAboveLeaf300 e24KC2ThetaAboveLeaf301 e24KC2ThetaAboveLeaf302 e24KC2ThetaAboveLeaf303

theorem e24KC2ThetaAboveNode31 :
    adaptiveCoverCheck 17 (childLH (childHH e24ThetaAboveRoot)) = true :=
  adaptiveCoverCheck_succ_of_children 16 (childLH (childHH e24ThetaAboveRoot))
    e24KC2ThetaAboveLeaf310 e24KC2ThetaAboveLeaf311 e24KC2ThetaAboveLeaf312 e24KC2ThetaAboveLeaf313

theorem e24KC2ThetaAboveNode32 :
    adaptiveCoverCheck 17 (childHL (childHH e24ThetaAboveRoot)) = true :=
  adaptiveCoverCheck_succ_of_children 16 (childHL (childHH e24ThetaAboveRoot))
    e24KC2ThetaAboveLeaf320 e24KC2ThetaAboveLeaf321 e24KC2ThetaAboveLeaf322 e24KC2ThetaAboveLeaf323

theorem e24KC2ThetaAboveNode33 :
    adaptiveCoverCheck 17 (childHH (childHH e24ThetaAboveRoot)) = true :=
  adaptiveCoverCheck_succ_of_children 16 (childHH (childHH e24ThetaAboveRoot))
    e24KC2ThetaAboveLeaf330 e24KC2ThetaAboveLeaf331 e24KC2ThetaAboveLeaf332 e24KC2ThetaAboveLeaf333

theorem e24KC2ThetaAboveNode0 :
    adaptiveCoverCheck 18 (childLL e24ThetaAboveRoot) = true :=
  adaptiveCoverCheck_succ_of_children 17 (childLL e24ThetaAboveRoot)
    e24KC2ThetaAboveNode00 e24KC2ThetaAboveNode01 e24KC2ThetaAboveNode02 e24KC2ThetaAboveNode03

theorem e24KC2ThetaAboveNode1 :
    adaptiveCoverCheck 18 (childLH e24ThetaAboveRoot) = true :=
  adaptiveCoverCheck_succ_of_children 17 (childLH e24ThetaAboveRoot)
    e24KC2ThetaAboveNode10 e24KC2ThetaAboveNode11 e24KC2ThetaAboveNode12 e24KC2ThetaAboveNode13

theorem e24KC2ThetaAboveNode2 :
    adaptiveCoverCheck 18 (childHL e24ThetaAboveRoot) = true :=
  adaptiveCoverCheck_succ_of_children 17 (childHL e24ThetaAboveRoot)
    e24KC2ThetaAboveNode20 e24KC2ThetaAboveNode21 e24KC2ThetaAboveNode22 e24KC2ThetaAboveNode23

theorem e24KC2ThetaAboveNode3 :
    adaptiveCoverCheck 18 (childHH e24ThetaAboveRoot) = true :=
  adaptiveCoverCheck_succ_of_children 17 (childHH e24ThetaAboveRoot)
    e24KC2ThetaAboveNode30 e24KC2ThetaAboveNode31 e24KC2ThetaAboveNode32 e24KC2ThetaAboveNode33

theorem e24KC2ThetaAboveNodeROOT :
    adaptiveCoverCheck 19 e24ThetaAboveRoot = true :=
  adaptiveCoverCheck_succ_of_children 18 e24ThetaAboveRoot
    e24KC2ThetaAboveNode0 e24KC2ThetaAboveNode1 e24KC2ThetaAboveNode2 e24KC2ThetaAboveNode3

theorem e24ThetaAboveKernelCheck :
    adaptiveCoverCheck 19 e24ThetaAboveRoot = true :=
  e24KC2ThetaAboveNodeROOT

end PartE
end GerverSofa

end

end

end

section

/-!
# Gerver Sofa / Kernel Only / Part E / E24KC6Kernel Final Closure
-/

public section

noncomputable section

namespace GerverSofa
namespace PartE

theorem deepMindABPhiTheta_existsUnique :
    ∃! ABphiTheta : ℝ × ℝ × ℝ × ℝ,
      DeepMindABPhiThetaSpec
        ABphiTheta.1 ABphiTheta.2.1 ABphiTheta.2.2.1 ABphiTheta.2.2.2 :=
  deepMindABPhiTheta_existsUnique_of_alignedChecks
    e24PhiBelowKernelCheck
    e24PhiAboveKernelCheck
    e24ThetaBelowKernelCheck
    e24ThetaAboveKernelCheck

end PartE
end GerverSofa

end

end

end

end

end

end
