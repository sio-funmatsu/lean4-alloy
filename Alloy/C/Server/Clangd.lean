/-
Copyright (c) 2022 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
import Alloy.Util.Server.Methods

open System Lean Lsp

namespace Alloy.Clangd

/-! ## `clangd` Initialization Options -/

structure CompilationDatabaseEntry where
  workingDirectory : String
  compilationCommand : Array String
  deriving ToJson, FromJson

abbrev CompilationDatabase :=
  Std.TreeMap FilePath CompilationDatabaseEntry (compareOn (·.toString))

instance : ToJson CompilationDatabase where
  toJson v := Json.obj <| v.foldl (init := .empty) fun a k v =>
    a.insert k.toString (toJson v)

instance : FromJson CompilationDatabase where
  fromJson? v := do
    let o ← v.getObj?
    o.foldlM (init := {}) fun a k v => do
      return a.insert (FilePath.mk k) (← fromJson? v)

structure InitializationOptions where
  fallbackFlags? : Option (Array String) := none
  compilationDatabasePath? : Option String := none
  compilationDatabaseChanges? : Option CompilationDatabase := none
  clangdFileStatus? : Option Bool := none
  deriving ToJson, FromJson

structure FileStatus where
  uri : DocumentUri
  state : String
  deriving ToJson, FromJson

instance : LsClientNote "textDocument/clangd.fileStatus" FileStatus := {}
