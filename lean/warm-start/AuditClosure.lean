import AcceleratedLogConcave.WarmStart
import Lean.Elab.Command
set_option maxHeartbeats 0
set_option maxRecDepth 100000
/-! Direct traversal of checked declaration types and values, not cached axiom lists.
    Only the four public WarmStart endpoints are roots; this is not an all-module audit. -/
open Lean Elab Command in
run_cmd do
  let env := (← getEnv).setExporting false
  let roots : Array Name := #[
    `AcceleratedLogConcave.WarmStart.accelerated_warm_start,
    `AcceleratedLogConcave.WarmStart.original_target_warm_error,
    `AcceleratedLogConcave.WarmStart.implemented_error,
    `AcceleratedLogConcave.WarmStart.public_parameters]
  let mut todo := roots
  let mut seen : NameSet := {}
  let mut rows : Array Json := #[]
  let mut axs : NameSet := {}
  while !todo.isEmpty do
    let name := todo.back!
    todo := todo.pop
    if seen.contains name then continue
    seen := seen.insert name
    let some ci := env.checked.get.find? name | throwError "Missing kernel declaration {name}"
    let mut deps := ci.type.getUsedConstants
    let mut kind := ""
    match ci with
    | .axiomInfo _ =>
      kind := "axiom"
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains name do
        throwError "Unexpected reachable axiom {name}"
      axs := axs.insert name
    | .defnInfo v => kind := "definition"; deps := deps ++ v.value.getUsedConstants
    | .thmInfo v => kind := "theorem"; deps := deps ++ v.value.getUsedConstants
    | .opaqueInfo v => kind := "opaque"; deps := deps ++ v.value.getUsedConstants
    | .quotInfo _ => kind := "quotient"
    | .ctorInfo v => kind := "constructor"; deps := deps.push v.induct
    | .recInfo v =>
      kind := "recursor"
      deps := deps ++ v.all.toArray
      for rule in v.rules do
        deps := (deps.push rule.ctor) ++ rule.rhs.getUsedConstants
    | .inductInfo v => kind := "inductive"; deps := deps ++ v.ctors.toArray ++ v.all.toArray
    todo := todo ++ deps
    rows := rows.push <| Json.mkObj [("name",toJson name.toString),("kind",toJson kind),("dependencies",toJson (deps.map Name.toString))]

  logInfo m!"ACTUAL_ENDPOINT_CLOSURE_PASS roots={roots.size} reachable={rows.size} axioms={axs.toArray}"

