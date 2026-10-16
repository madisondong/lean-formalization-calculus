import calculus
import Lean.Util.CollectAxioms
import Lean.Elab.Command

/-!
# Kiểm tra tiên đề

Chỉ các phát biểu gốc trong danh sách cho phép được dùng `sorryAx`.
Mọi hằng công khai khác của dự án, kể cả hằng sinh tự động, chỉ được dùng
`propext`, `Classical.choice`, `Quot.sound`.
-/

open Lean Elab Command

private def allowedAxioms : Array Name :=
  #[``propext, ``Classical.choice, ``Quot.sound]

private def checkDeclaration (name : Name) : CommandElabM Unit := do
  let axioms ← collectAxioms name
  let unexpected := axioms.filter fun axiomName => !allowedAxioms.contains axiomName
  unless unexpected.isEmpty do
    throwError "Axiom audit failed for {name}: unexpected axioms {unexpected}"
  logInfo m!"AXIOMS {name}: {axioms}"

elab "audit_calculus_axioms" : command => do
  let env ← getEnv
  let exportedEnv := env.setExporting true
  let names := env.constants.fold (init := #[]) fun acc name _ =>
    let projectModule := match env.getModuleIdxFor? name with
      | some index => match env.header.moduleNames[index.toNat]? with
        | some moduleName => (`calculus).isPrefixOf moduleName
        | none => false
      | none => false
    if ((`calculus).isPrefixOf name || projectModule) && !name.isInternal &&
        (exportedEnv.find? name).isSome then
      acc.push name
    else acc
  let names := names.qsort Name.lt
  if names.isEmpty then
    throwError "No exported project constants found for axiom audit"
  let sourceExercises ← liftIO <|
    IO.FS.readFile ".lake/audit-source-exercises.txt"
  let mut exerciseNames : Array Name := #[]
  for line in sourceExercises.splitOn "\n" do
    unless line.isEmpty do
      match line.splitOn "\t" with
      | [sourceId, nameText, moduleText] =>
        let name := nameText.toName
        if exerciseNames.contains name then
          throwError "Repeated original-source exercise: {name}"
        unless names.contains name do
          throwError "Original-source exercise is not exported by calculus: {name}"
        let some info := exportedEnv.find? name |
          throwError "Missing original-source exercise: {name}"
        match info with
        | .thmInfo _ => pure ()
        | _ => throwError "Original-source exercise is not a theorem: {name}"
        let some moduleIdx := env.getModuleIdxFor? name |
          throwError "Missing imported module for original-source exercise: {name}"
        let some moduleName := env.header.moduleNames[moduleIdx.toNat]? |
          throwError "Invalid module index for original-source exercise: {name}"
        unless moduleName == moduleText.toName do
          throwError "Original-source exercise module mismatch for {name}: expected {moduleText}, found {moduleName}"
        let axioms ← collectAxioms name
        unless axioms.contains ``sorryAx do
          throwError "Original-source exercise no longer contains sorryAx; update its status: {name}"
        let unexpected := axioms.filter fun axiomName =>
          axiomName != ``sorryAx && !allowedAxioms.contains axiomName
        unless unexpected.isEmpty do
          throwError "Original-source exercise has unexpected axioms {unexpected}: {name}"
        logInfo m!"SOURCE_EXERCISE_AXIOMS {sourceId} {name}: {axioms}"
        logInfo m!"SOURCE_EXERCISE_TYPE {sourceId} {name}: {info.type}"
        exerciseNames := exerciseNames.push name
      | _ => throwError "Malformed generated original-source exercise line: {line}"
  for name in names do
    unless exerciseNames.contains name do
      checkDeclaration name
  logInfo m!"AUDIT_OK: {names.size} exported project constants; {exerciseNames.size} original-source exercises; {names.size - exerciseNames.size} constants passed the strict axiom audit"

audit_calculus_axioms
