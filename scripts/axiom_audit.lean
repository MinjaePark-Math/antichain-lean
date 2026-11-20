import Antichain
import Lean.Util.CollectAxioms

set_option maxRecDepth 100000
set_option pp.universes true
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.proofs true
set_option pp.maxSteps 1000000

open Lean Elab Command in
run_cmd do
  let countText ← liftIO <| IO.getEnv "ANTICHAIN_AUDIT_SHARD_COUNT"
  let indexText ← liftIO <| IO.getEnv "ANTICHAIN_AUDIT_SHARD_INDEX"
  let (shardCount, shardIndex) ← match countText, indexText with
    | none, none => pure (1, 0)
    | some count, some index => do
      let some count := count.toNat? | throwError "Invalid audit shard count"
      let some index := index.toNat? | throwError "Invalid audit shard index"
      if count == 0 || index ≥ count then
        throwError "Audit shard count must be positive and index must be below count"
      pure (count, index)
    | _, _ => throwError "Audit shard count and index must be supplied together"
  let env ← getEnv
  let mut total := 0
  let mut selected := 0
  for (name, info) in env.constants.toList do
    if let some idx := env.getModuleIdxFor? name then
      let modName := env.header.moduleNames[idx.toNat]!
      if modName.toString == "Antichain" || modName.toString.startsWith "Antichain." then
        total := total + 1
        if (hash name).toNat % shardCount == shardIndex then
          selected := selected + 1
          let axioms ← collectAxioms name
          let prettyType ← liftCoreM (Meta.MetaM.run' (Meta.ppExpr info.type))
          let kind := match info with
            | .thmInfo _ => "theorem"
            | .axiomInfo _ => "axiom"
            | .defnInfo _ => "definition"
            | .opaqueInfo _ => "opaque"
            | .inductInfo _ => "inductive"
            | .ctorInfo _ => "constructor"
            | .recInfo _ => "recursor"
            | .quotInfo _ => "quotient"
          let row := Json.mkObj [
            ("name", toJson name.toString),
            ("module", toJson modName.toString),
            ("kind", toJson kind),
            ("unsafe", toJson info.isUnsafe),
            ("axioms", toJson (axioms.map Name.toString)),
            ("universe_parameters", toJson (info.levelParams.map Name.toString)),
            ("type_expression", toJson (reprStr info.type)),
            ("readable_type", toJson prettyType.pretty)]
          liftIO <| IO.println ("AUDIT_JSON " ++ row.compress)
  let summary := Json.mkObj [
    ("shard_index", toJson shardIndex),
    ("shard_count", toJson shardCount),
    ("total_project_declarations", toJson total),
    ("selected_declarations", toJson selected)]
  liftIO <| IO.println ("AUDIT_SUMMARY " ++ summary.compress)
