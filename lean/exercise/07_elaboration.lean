import Lean
open Lean Elab Command Term Meta

/- ### 1. Consider the following code. Rewrite `syntax` + `@[term_elab hi]... : TermElab` combination using just `elab`. -/

elab l:term "♥" a:"♥"? b:"♥"? : term => do
  let nExpr ← elabTermEnsuringType l (mkConst `Nat)
  if let some a := a then
    if let some b := b then
      return Expr.app (Expr.app (Expr.const `Nat.add []) nExpr) (mkNatLit 3)
    else
      return Expr.app (Expr.app (Expr.const `Nat.add []) nExpr) (mkNatLit 2)
  else
    return Expr.app (Expr.app (Expr.const `Nat.add []) nExpr) (mkNatLit 1)

#eval 7 ♥ -- 8
#eval 7 ♥♥ -- 9
#eval 7 ♥♥♥ -- 10

/- ### 2. Here is some syntax taken from a real mathlib command `alias`. -/

-- syntax (name := our_alias) (docComment)? "our_alias " ident " ← " ident* : command
-- We want `alias hi ← hello yes` to print out the identifiers after `←` - that is, "hello" and "yes".
-- Please add these semantics:

-- **a)** using `syntax` + `@[command_elab alias] def elabOurAlias : CommandElab`.
syntax (name := aliasA) (docComment)? "aliasA " ident " ← " ident* : command

@[command_elab «aliasA»]
def elabAlias : CommandElab := λ stx =>
  match stx with
  | `(aliasA $x:ident ← $ys:ident*) =>
    for y in ys do
      Lean.logInfo y
  | _ =>
    throwUnsupportedSyntax

aliasA hi ← hello yes

-- **b)** using `syntax` + `elab_rules`.

syntax (name := aliasB) (docComment)? "aliasB " ident " ← " ident* : command

elab_rules : command
  | `(aliasB $x:ident ← $ys:ident*) => do
    for y in ys do
      Lean.logInfo y

aliasB hi ← hello yes

-- **c)** using `elab`.

elab "aliasC " x:ident " ← " ys:ident* : command => do
  for y in ys do
    Lean.logInfo y

aliasC hi ← hello yes

/- 3. Here is some syntax taken from a real mathlib tactic `nth_rewrite`. -/

open Parser.Tactic

-- We want `nth_rewrite 5 [←add_zero a] at h` to print out `"rewrite location!"` if the user provided location, and `"rewrite target!"` if the user didn't provide location.

-- Please add these semantics:
-- **a)** using `syntax` + `@[tactic nthRewrite] def elabNthRewrite : Lean.Elab.Tactic.Tactic`.

syntax (name := nthRewriteA) "nth_rewriteA " (config)? num rwRuleSeq (ppSpace location)? : tactic

@[tactic nthRewriteA] def elabNthRewrite : Lean.Elab.Tactic.Tactic := fun stx => do
  match stx with
  | `(tactic| nth_rewriteA $[$cfg]? $n $rules $_loc) =>
    Lean.logInfo "rewrite location!"
  | `(tactic| nth_rewriteA $[$cfg]? $n $rules) =>
    Lean.logInfo "rewrite target!"
  | _ =>
    throwUnsupportedSyntax

-- **b)** using `syntax` + `elab_rules`.
syntax (name := nthRewriteB) "nth_rewriteB " (config)? num rwRuleSeq (ppSpace location)? : tactic

elab_rules (kind := nthRewriteB) : tactic
  | `(tactic| nth_rewriteB $[$cfg]? $n $rules $_loc) =>
    Lean.logInfo "rewrite location!"
  | `(tactic| nth_rewriteB $[$cfg]? $n $rules) =>
    Lean.logInfo "rewrite target!"

-- **c)** using `elab`.
elab "nth_rewriteC " (config)? num rwRuleSeq loc:(ppSpace location)? : tactic =>
  if let some loc := loc then
    Lean.logInfo "rewrite location!"
  else
    Lean.logInfo "rewrite target!"

example : 2 + 2 = 4 := by
  nth_rewriteC 2 [← add_zero] at h
  nth_rewriteC 2 [← add_zero]
  sorry
