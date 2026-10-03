import DkMath.FLT.Three
import DkMath.FLT.Five.Main
import DkMath.FLT.Seven.CurrentCarrierNormalizedPower
import Lean.Util.FoldConsts

/-!
A bounded compiled proof dependency audit. This is not an import-graph check:
starting at each named endpoint, recursively visit constants mentioned by its
kernel type and by every available kernel declaration body (including opaque
bodies). As in Lean.Util.CollectAxioms, an inductive declaration also queues
all of its constructors, so their types are traversed even when no constructor
name occurs directly in the root expression. No full Lake build or production
edit is required.

The forbidden filters are grounded in the pinned Mathlib FLT Three/Four source
families and the DkMath MathlibBridge/FLT34 wrappers. Generic FLT.Basic
definitions and conditional reductions are not classified as completed FLT
proofs. Missing constants and body-bearing declarations without readable
bodies cause the audit to fail, rather than silently establishing independence.
-/

open Lean Elab Command

namespace FLT357SourceDependencyAudit

def forbiddenDependency (n : Name) : Bool :=
  let s := n.toString
  n == ``sorryAx ||
  s.startsWith "fermatLastTheoremThree" ||
  s == "FermatLastTheoremForThree_of_FermatLastTheoremThreeGen" ||
  s == "FermatLastTheoremForThreeGen" ||
  s.startsWith "FermatLastTheoremForThreeGen." ||
  s == "fermatLastTheoremFour" || s == "not_fermat_42" ||
  s == "Fermat42" || s.startsWith "Fermat42." ||
  s == "DkMath.FLT.FLT3_core" || s == "DkMath.FLT.FLT4_core" ||
  s.contains "_private.Mathlib.NumberTheory.FLT.Three." ||
  s.contains "_private.Mathlib.NumberTheory.FLT.Four."

def bodyExpected : ConstantInfo → Bool
  | .defnInfo _ | .thmInfo _ | .opaqueInfo _ => true
  | _ => false

def kindLabel : ConstantInfo → String
  | .axiomInfo _ => "axiom"
  | .defnInfo _ => "definition"
  | .thmInfo _ => "theorem"
  | .opaqueInfo _ => "opaque"
  | .quotInfo _ => "quotient primitive"
  | .inductInfo _ => "inductive"
  | .ctorInfo _ => "constructor"
  | .recInfo _ => "recursor"

def checkRoot (env : Environment) (root : Name) : CommandElabM Unit := do
  let mut pending : Array Name := #[root]
  let mut visited : NameSet := {}
  let mut bodies : Nat := 0
  let mut missing : Array Name := #[]
  let mut unreadable : Array Name := #[]
  let mut forbidden : Array Name := #[]
  let mut axioms : Array Name := #[]
  let mut kinds : Std.HashMap String Nat := {}
  while !pending.isEmpty do
    let n := pending.back!
    pending := pending.pop
    if visited.contains n then
      continue
    visited := visited.insert n
    if forbiddenDependency n then
      forbidden := forbidden.push n
    match env.checked.get.find? n with
    | none => missing := missing.push n
    | some info =>
      let k := kindLabel info
      kinds := kinds.insert k ((kinds[k]?).getD 0 + 1)
      if let .axiomInfo _ := info then
        axioms := axioms.push n
      pending := pending ++ info.type.getUsedConstants
      if let .inductInfo v := info then
        pending := pending ++ v.ctors.toArray
      match info.value? (allowOpaque := true) with
      | some value =>
        bodies := bodies + 1
        pending := pending ++ value.getUsedConstants
      | none =>
        if bodyExpected info then
          unreadable := unreadable.push n
  logInfo m!"DEPENDENCY ROOT: {root}"
  logInfo m!"reachable constants: {visited.size}; readable declaration bodies: {bodies}"
  for k in #["definition", "theorem", "opaque", "axiom", "inductive", "constructor",
      "recursor", "quotient primitive"] do
    logInfo m!"declaration kind {k}: {(kinds[k]?).getD 0}"
  logInfo m!"axiom leaves: {axioms}"
  logInfo m!"forbidden dependencies: {forbidden}"
  logInfo m!"missing constants: {missing}"
  logInfo m!"unreadable expected bodies: {unreadable}"
  unless forbidden.isEmpty && missing.isEmpty && unreadable.isEmpty do
    throwError "compiled dependency audit incomplete or forbidden dependency found for {root}"
  logInfo m!"PASS: recursive kernel types and readable bodies contain no forbidden dependency"

end FLT357SourceDependencyAudit

set_option maxHeartbeats 0 in
run_cmd do
  logInfo "Forbidden completed-external-proof filters: sorryAx; fermatLastTheoremThree*; FermatLastTheoremForThree_of_FermatLastTheoremThreeGen; FermatLastTheoremForThreeGen (whole namespace); fermatLastTheoremFour; not_fermat_42; Fermat42 (whole namespace); DkMath.FLT.FLT3_core; DkMath.FLT.FLT4_core; private Mathlib.NumberTheory.FLT.Three/Four names."
  let env ← getEnv
  FLT357SourceDependencyAudit.checkRoot env
    ``DkMath.FLT.Three.fermatThree_no_positive_solution
  FLT357SourceDependencyAudit.checkRoot env ``DkMath.FLT.Five.flt5Target
  FLT357SourceDependencyAudit.checkRoot env
    ``DkMath.FLT.Seven.SevenRealCubic.CurrentCarrierPower.currentCarrier_ramified_element_receiver
  FLT357SourceDependencyAudit.checkRoot env
    ``DkMath.FLT.Seven.SevenRealCubic.CurrentCarrierPower.currentCarrier_ramifiedIdeal_mul_seventh_power
