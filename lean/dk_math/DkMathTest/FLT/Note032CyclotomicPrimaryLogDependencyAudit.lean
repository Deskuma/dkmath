/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Lib.NumberTheory.CyclotomicPrimaryLogCriterion

#print "file: DkMathTest.FLT.Note032CyclotomicPrimaryLogDependencyAudit"

namespace Note032CyclotomicPrimaryLogDependencyAudit

open Lean Elab Command

private def forbidden (n : Name) : Bool :=
  let s := (privateToUserName n).toString
  n == ``sorryAx || s.startsWith "P2M." || s.startsWith "P2MW." ||
    s.startsWith "FltRegular." || s.startsWith "FreyPackage." ||
    s.startsWith "DkMath.FLT.Kummer." || s.contains "fermatLastTheorem" ||
    s.contains "fermat_last_theorem" || s.contains "fermatFive_no_positive_solution"

private def checkRoot (root : Name) (required : Array Name) : CommandElabM Unit := do
  let env ← getEnv
  let mut pending := #[root]
  let mut visited : NameSet := {}
  while !pending.isEmpty do
    let n := pending.back!
    pending := pending.pop
    if visited.contains n then continue
    visited := visited.insert n
    if forbidden n then throwError "Forbidden dependency: {n}"
    let some info := env.checked.get.find? n | throwError "Missing constant: {n}"
    pending := pending ++ info.type.getUsedConstants
    if let .inductInfo v := info then pending := pending ++ v.ctors.toArray
    if let .axiomInfo _ := info then
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains n do
        throwError "Unexpected axiom: {n}"
    if let some value := info.value? (allowOpaque := true) then
      pending := pending ++ value.getUsedConstants
  for n in required do
    unless visited.contains n do throwError "Required theorem absent: {n}"
  logInfo m!"PASS: {root}; {visited.size} reachable constants; required actual theorems present."

private def binderNames : Expr → List Name
  | .forallE n _ b _ => n :: binderNames b
  | .letE n _ _ b _ => n :: binderNames b
  | _ => []

private def checkInputs (root : Name) (required banned : Array Name) : CommandElabM Unit := do
  let env ← getEnv
  let some info := env.checked.get.find? root | throwError "Missing constant: {root}"
  let names := binderNames info.type
  for n in required do
    unless names.contains n do throwError "Required input absent in {root}: {n}"
  for n in banned do
    if names.contains n then throwError "Unexpected input in {root}: {n}"
  logInfo m!"PASS inputs: {root}; remaining arithmetic inputs explicit."

set_option maxHeartbeats 0 in
-- Ten finite traversals inspect types, constructors and opaque proof bodies.
run_cmd do
  checkRoot ``DkMath.Lib.NumberTheory.CyclotomicTruncatedLog.tlog_mul #[]
  checkRoot ``DkMath.Lib.NumberTheory.CyclotomicPrimaryLog.parameter_sq_ne_zero #[``IsPrimitiveRoot.zeta_sub_one_prime']
  checkRoot ``DkMath.Lib.NumberTheory.CyclotomicPrimaryLog.residueCharP #[``DkMath.Lib.NumberTheory.CyclotomicPrimaryCongruence.natCast_mem_ramifiedIdeal_pow]
  checkRoot ``DkMath.Lib.NumberTheory.CyclotomicPrimaryLog.unitLog_pow #[``DkMath.Lib.NumberTheory.CyclotomicTruncatedLog.tlog_mul, ``DkMath.Lib.NumberTheory.CyclotomicPrimaryLog.natCast_eq_zero]
  checkRoot ``DkMath.Lib.NumberTheory.CyclotomicPrimaryLog.primaryLog #[``DkMath.Lib.NumberTheory.CyclotomicPrimaryLog.unitLog_pow]
  checkRoot ``DkMath.Lib.NumberTheory.CyclotomicPrimaryLog.primaryLog_mk_eq_zero_of_local_power #[``DkMath.Lib.NumberTheory.CyclotomicPrimaryCongruence.pow_sub_one_mem_ramifiedIdeal_cube_of_local_power, ``DkMath.Lib.NumberTheory.CyclotomicPrimaryLog.primaryLog]
  checkRoot ``DkMath.Lib.NumberTheory.CyclotomicPrimaryLog.primaryLog_eq_zero_of_mem_localPowerSpace #[``DkMath.Lib.NumberTheory.CyclotomicPrimaryLog.primaryLog_mk_eq_zero_of_local_power]
  checkRoot ``DkMath.Lib.NumberTheory.CyclotomicPrimaryLog.primaryLog_smul #[``DkMath.Lib.NumberTheory.CyclotomicPrimaryLog.scalarMap_apply]
  checkRoot ``DkMath.Lib.NumberTheory.CyclotomicPrimaryLogCriterion.eq_zero_of_rank_one_of_log_eq_zero #[``DkMath.Lib.NumberTheory.CyclotomicPrimaryLog.primaryLog_smul]
  checkRoot ``DkMath.Lib.NumberTheory.CyclotomicPrimaryLogCriterion.primaryWeightSquareSpace_eq_bot_of_rank_one_of_detection #[``DkMath.Lib.NumberTheory.CyclotomicPrimaryLogCriterion.primaryWeightSquareSpace_log_eq_zero, ``DkMath.Lib.NumberTheory.CyclotomicPrimaryLogCriterion.eq_zero_of_rank_one_of_log_eq_zero]
  checkInputs ``DkMath.Lib.NumberTheory.CyclotomicPrimaryLog.primaryLog #[`hp5] #[`hloc, `hu, `hunit, `hrank, `hdetect]
  checkInputs ``DkMath.Lib.NumberTheory.CyclotomicPrimaryLog.primaryLog_mk_eq_zero_of_local_power #[`hp5, `hu] #[`hunit, `hrank, `hdetect]
  checkInputs ``DkMath.Lib.NumberTheory.CyclotomicPrimaryLog.primaryLog_eq_zero_of_mem_localPowerSpace #[`hp5, `hx] #[`hu, `hunit, `hrank, `hdetect]
  checkInputs ``DkMath.Lib.NumberTheory.CyclotomicPrimaryLogCriterion.eq_zero_of_rank_one_of_log_eq_zero #[`hp5, `W, `hrank, `g, `hdetect, `x, `hx] #[`hunit]
  checkInputs ``DkMath.Lib.NumberTheory.CyclotomicPrimaryLogCriterion.primaryWeightSquareSpace_eq_bot_of_rank_one_of_detection #[`hp5, `hrank, `g, `hdetect] #[`hunit, `hloc, `hclass, `hbad]

end Note032CyclotomicPrimaryLogDependencyAudit
