/-
Copyright (c) 2023 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
import Alloy.Util.Binder
import Lean.Elab.MutualDef

/-! # Opaque Types
Defines an `opaque_type` command which is simplified syntactic sugar for
defining a nonempty type with an opaque representation.
-/

namespace Alloy
open Lean Elab Parser Command Meta

/--
The `Nonempty` instance of a `NonemptyType`.

Defined here to make the implementation of `opaque_type` simpler
than it would be if `Subtype.property` was used directly.
-/
abbrev NonemptyType.nonempty (type : NonemptyType.{u}) : Nonempty type.val :=
  type.property

/-- A type specifier that is restricted to types of the `Type [<lv>]` form. -/
syntax typeLvSpec := " : " "Type " (level)?

/--
An opaque type is a nonempty type with an opaque representation.
It is useful for defining foreign-function interfaces (FFIs) and
forward-declared types.

```
opaque_type T <binders>.. : Type u
```

Is essentially syntactic sugar equivalent to the following:

```
opaque T.nonemptyType <binders>.. : NonemptyType.{u}
def T <binders>.. : Type u := NonemptyType.type (T.nonemptyType  ..)
instance T.nonempty <binders>.. : Nonempty (T ..) :=
  NonemptyType.nonempty (T.nonemptyType ..)
```
-/
syntax (name := opaqueType)
declModifiers "opaque_type " declId binders (typeLvSpec)? : command

elab_rules : command
| `(opaqueType| $mods:declModifiers opaque_type $declId $bs* $[: Type $(lv??)?]?) => do
  let modifiers ← elabModifiers ⟨mods⟩
  let {docString?, visibility, isProtected, attrs, ..} := modifiers
  let safety := if modifiers.isUnsafe then DefinitionSafety.unsafe else .safe
  let {declName, ..} ← liftTermElabM <| expandDeclId (← getCurrNamespace) (← getLevelNames) declId {docString?, visibility, isProtected}
  let sc ← Command.getScope
  runTermElabM fun vars => do
  let stx ← getRef
  let nt ← if let some (some lv) := lv?? then
    `(NonemptyType.{$lv}) else `(NonemptyType.{0})
  let ntName := declName.str "nonemptyType"
  let ntId := mkIdentFrom declId <| `_root_ ++ ntName
  let ntDefn := mkNode ``Parser.Command.declValSimple
    #[mkAtomFrom stx ":=", ← `(default_or_ofNonempty%)]
  Term.elabMutualDef vars sc #[{
    ref := stx, headerRef := stx, kind := .opaque,
    modifiers := {isUnsafe := safety matches .unsafe},
    declId := declId.raw.setArg 0 ntId, binders := mkNullNode bs,
    type? := nt, value := ntDefn, docString? := none
  }] {}
  let .opaqueInfo {type, levelParams, ..} ← getConstInfo ntName
    | throwError "expected opaque info for 'nonemptyType'"
  forallTelescope type fun as r => do
  let .const _ [u] := r | throwError "unexpected type of 'nonemptyType'"
  let levels := levelParams.map mkLevelParam
  let ntValue := mkAppN (mkConst ntName levels) as
  let tyValue ← mkLambdaFVars as <| mkApp (mkConst ``NonemptyType.type [u]) ntValue
  let tyType ← mkForallFVars as <| mkSort <| .succ u
  addDecl <| .defnDecl {
    levelParams
    name := declName
    type := tyType
    value := tyValue
    hints := .regular <| getMaxHeight (← getEnv) tyValue + 1
    safety
  }
  withSaveInfoContext do
    Term.addTermInfo' declId (mkConst declName levels) (isBinder := true)
  Term.applyAttributes declName attrs
  let instName := declName.str "nonempty"
  let neValue ← mkLambdaFVars as <|
    mkApp (mkConst ``NonemptyType.nonempty [u]) ntValue
  let neType ← mkForallFVars as <|
    mkApp (mkConst ``Nonempty [.succ u]) <| mkAppN (mkConst declName levels) as
  addDecl <| .defnDecl {
    levelParams
    name := instName
    type := neType
    value := neValue
    hints := .abbrev
    safety
  }
  addInstance instName .global (eval_prio default)
