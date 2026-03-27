/-
Copyright (c) 2026 Jovan Gerbscheid. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jovan Gerbscheid
-/

module
public import Mathlib.Tactic.ApplyFun

set_option linter.style.header false
set_option linter.directoryDependency false

/-! # Leaky instances

This linter reports leaky instances
-/

public meta section

open Lean Meta
namespace Batteries.Tactic.Lint

def getLambdaBody : Expr → Expr
  | .lam _ _ b .. => getLambdaBody b
  | e                => e

def checkInstance (cinfo : ConstantInfo) : MetaM (Option MessageData) := do
  let type := cinfo.type
  let some cls ← Meta.isClass? type | return none
  if cls matches
    ``Decidable | ``DecidableEq | ``DecidableLT | ``DecidableLE |
    ``Inhabited | ``Unique then
    return none
  if ← isProp type then return none
  let some value := cinfo.value? | return none
  if (getLambdaBody value).isBVar then return none
  withReducibleAndInstances do
  let type' ← inferType value
  if ← isDefEq type' type then return none
  forallTelescope type fun _ type =>
  forallTelescope type' fun _ type' =>
  return some <| ← addMessageContext m!"{indentExpr type'}{indentExpr type}\n"

@[env_linter] public def myLinter : Linter where
  noErrorsFound := "all good."
  errorsFound := "PROBLEM"
  test declName := do
    checkInstance (← getConstInfo declName)

end Batteries.Tactic.Lint
