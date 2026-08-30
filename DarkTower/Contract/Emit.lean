import Lean.Data.Json

/-! A small, Mathlib-free declaration-registry JSON emitter. -/

namespace DarkTower.Contract.Emit

open Lean

inductive DeclarationKind where
  | closed
  | hole

structure Declaration where
  name : String
  kind : DeclarationKind
  signature : String
  owner : String
  holder : String
  decided : String
  clojureLocus : Option String := none
  fixture : Option String := none
  evidence : Option String := none
  falsifier : Option String := none

structure Registry where
  schemaVersion : Nat
  contractId : String
  moduleName : String
  declarations : List Declaration

private def nullableString : Option String → Json
  | some value => Json.str value
  | none => Json.null

private def kindString : DeclarationKind → String
  | .closed => "closed"
  | .hole => "hole"

def Declaration.toJson (decl : Declaration) : Json :=
  Json.mkObj
    [("name", decl.name), ("kind", kindString decl.kind),
     ("signature", decl.signature), ("owner", decl.owner),
     ("holder", decl.holder), ("decided", decl.decided),
     ("clojure-locus", nullableString decl.clojureLocus),
     ("fixture", nullableString decl.fixture),
     ("evidence", nullableString decl.evidence),
     ("falsifier", nullableString decl.falsifier)]

private def modulePath (moduleName : String) : String :=
  String.intercalate "/" (moduleName.splitOn ".") ++ ".lean"

def sourceGitSha (moduleName : String) : IO String := do
  let path := modulePath moduleName
  let output ← IO.Process.output
    {cmd := "git", args := #["log", "-1", "--format=%H", "--", path]}
  if output.exitCode != 0 then
    throw <| IO.userError s!"git log failed for {path}: {output.stderr}"
  let sha := output.stdout.trimAscii.toString
  if sha.isEmpty then
    throw <| IO.userError s!"git log returned no commit for {path}"
  pure sha

def Registry.toJson (registry : Registry) (gitSha : String) : Json :=
  Json.mkObj
    [("schema-version", registry.schemaVersion),
     ("contract-id", registry.contractId),
     ("source", Json.mkObj [("module", registry.moduleName), ("git-sha", gitSha)]),
     ("declarations", Json.arr <| registry.declarations.map Declaration.toJson |>.toArray)]

def emit (registry : Registry) : IO Unit := do
  let gitSha ← sourceGitSha registry.moduleName
  IO.println (registry.toJson gitSha).compress

end DarkTower.Contract.Emit
