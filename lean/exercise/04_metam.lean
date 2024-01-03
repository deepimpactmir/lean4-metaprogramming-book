import Lean
open Lean Meta

/- 1. [**Metavariables**] Create a metavariable with type `Nat`, and assign to it value `3`.
Notice that changing the type of the metavarible from `Nat` to, for example, `String`,
doesn't raise any errors - that's why, as was mentioned, we must make sure
*"(a) that `val` must have the target type of `mvarId` and
(b) that `val` must only contain `fvars` from the local context of `mvarId`".* -/

#eval show MetaM Unit from do
  let hi ← Lean.Meta.mkFreshExprMVar (Expr.const ``Nat []) (userName := `hi)
  IO.println s!"value in hi: {← instantiateMVars hi}" -- ?_uniq.1

  hi.mvarId!.assign (Expr.lit (Literal.natVal 3))
  IO.println s!"value in hi: {← instantiateMVars hi}"

  let hii ← Lean.Meta.mkFreshExprMVar (Expr.const ``String []) (userName := `hii)
  IO.println s!"value in hii: {← instantiateMVars hii}" -- ?_uniq.2

  hii.mvarId!.assign (Expr.lit (Literal.natVal 3))
  IO.println s!"value in hii: {← instantiateMVars hii}"

/- 2. [**Metavariables**] What would `instantiateMVars (Lean.mkAppN (Expr.const 'Nat.add []) #[mkNatLit 1, mkNatLit 2])` output? -/

#eval show MetaM Unit from do
  let instantiatedExpr ← instantiateMVars (Lean.mkAppN (Expr.const `Nat.add []) #[mkNatLit 1, mkNatLit 2])
  IO.println instantiatedExpr

/- ### 3. -/

#eval show MetaM Unit from do
  let oneExpr := Expr.app (Expr.const `Nat.succ []) (Expr.const ``Nat.zero [])
  let twoExpr := Expr.app (Expr.const `Nat.succ []) oneExpr
  -- IO.println s!"value in oneExpr: {← instantiateMVars oneExpr}"

  -- Create `mvar1` with type `Nat`
  let mvar1 ← Lean.Meta.mkFreshExprMVar (Expr.const `Nat []) (userName := `mvar1)
  -- Create `mvar2` with type `Nat`
  let mvar2 ← Lean.Meta.mkFreshExprMVar (Expr.const `Nat []) (userName := `mvar2)
  -- Create `mvar3` with type `Nat`
  let mvar3 ← Lean.Meta.mkFreshExprMVar (Expr.const `Nat []) (userName := `mvar3)

  -- Assign `mvar1` to `2 + ?mvar2 + ?mvar3`
  mvar1.mvarId!.assign (Lean.mkAppN (Expr.const `Nat.add []) #[(Lean.mkAppN (Expr.const `Nat.add []) #[twoExpr, mvar2]), mvar3])

  -- Assign `mvar3` to `1`
  mvar3.mvarId!.assign oneExpr

  -- Instantiate `mvar1`, which should result in expression `2 + ?mvar2 + 1`
  let instantiatedMvar1 ← instantiateMVars mvar1
  IO.println instantiatedMvar1 -- Nat.add (Nat.add 2 ?_uniq.2) 1

/- ### 4. -/
elab "explore" : tactic => do
  let mvarId : MVarId ← Lean.Elab.Tactic.getMainGoal
  let metavarDecl : MetavarDecl ← mvarId.getDecl

  IO.println "Our metavariable"
  IO.println s!"{metavarDecl.userName} : {metavarDecl.type}"

  IO.println "All of its local declarations"
  let localContext : LocalContext := metavarDecl.lctx
  for (localDecl : LocalDecl) in localContext do
    if localDecl.isImplementationDetail then
      IO.println s!"(impl detail) {localDecl.userName} : {localDecl.type}"
    else
      IO.println s!"{localDecl.userName} : {localDecl.type}"

theorem red (hA : 1 = 1) (hB : 2 = 2) : 2 = 2 := by
  explore
  sorry

/- ### 5. [Metavariables] Write a tactic solve that proves the theorem red. -/

elab "solve" : tactic => do
  let mvarId : MVarId ← Lean.Elab.Tactic.getMainGoal
  let metavarDecl : MetavarDecl ← mvarId.getDecl

  let localContext : LocalContext := metavarDecl.lctx
  for (localDecl : LocalDecl) in localContext do
    if ← Lean.Meta.isDefEq localDecl.type metavarDecl.type then
      mvarId.assign localDecl.toExpr

theorem red' (hA : 1 = 1) (hB : 2 = 2) : 2 = 2 := by
  solve

/- ### 6. [Computation] What is the normal form of the following expressions:
  a) fun x => x of type Bool → Bool
  b) (fun x => x) ((true && false) || true) of type Bool
  c) 800 + 2 of type Nat
-/

def sixA : Bool -> Bool := fun x => x
-- Lean.Expr.lam `x (Lean.Expr.const `Bool []) (Lean.Expr.bvar 0) (Lean.BinderInfo.default)
#eval Lean.Meta.reduce (Expr.const ``sixA [])

def sixB : Bool := (fun x => x) ((true && false) || true)
-- Lean.Expr.const `Bool.true []
#eval Lean.Meta.reduce (Expr.const ``sixB [])

def sixC : Nat := 800 + 2
-- Lean.Expr.lit (Lean.Literal.natVal 802)
#eval Lean.Meta.reduce (Expr.const ``sixC [])

/- ### 7. -/
#eval show MetaM Unit from do
  let oneExpr := Expr.lit (Lean.Literal.natVal 1)
  let oneExpr' := Expr.app (Expr.const `Nat.succ []) (Expr.const ``Nat.zero [])

  let isEqual ← Lean.Meta.isDefEq oneExpr oneExpr'
  IO.println isEqual -- true

/- ### 8. -/

-- a) `5 =?= (fun x => 5) ((fun y : Nat → Nat => y) (fun z : Nat => z))`
def expr := (fun x => 5) ((fun y : Nat → Nat => y) (fun z : Nat => z))
#eval show MetaM Unit from do
  let expr := Expr.const `expr []
  let expr' := Lean.mkNatLit 5
  let isEqual ← Lean.Meta.isDefEq expr expr'
  IO.println isEqual -- true

-- b) 2 + 1 =?= 1 + 2
#eval show MetaM Unit from do
  let expr := Lean.mkAppN (Expr.const `Nat.add []) #[mkNatLit 2, mkNatLit 1]
  let expr' := Lean.mkAppN (Expr.const `Nat.add []) #[mkNatLit 1, mkNatLit 2]
  let isEqual ← Lean.Meta.isDefEq expr expr'
  IO.println isEqual -- true

-- c) ?a =?= 2, where ?a has a type String
#eval show MetaM Unit from do
  let expr ← Lean.Meta.mkFreshExprMVar (Expr.const `String []) (userName := `expr)
  let expr' := Lean.mkNatLit 2
  let isEqual ← Lean.Meta.isDefEq expr expr'
  IO.println isEqual -- false

-- d) ?a + Int =?= "hi" + ?b, where ?a and ?b don't have a type
#eval show MetaM Unit from do
  let a ← Lean.Meta.mkFreshExprMVar Option.none (userName := `a)
  let b ← Lean.Meta.mkFreshExprMVar Option.none (userName := `b)
  let expr := Lean.mkAppN (Expr.const `Nat.add []) #[a, Expr.const `Int []]
  let expr' := Lean.mkAppN (Expr.const `Nat.add []) #[Lean.mkStrLit "hi", b]
  let isEqual ← Lean.Meta.isDefEq expr expr'
  IO.println isEqual -- true

  IO.println s!"a: {← instantiateMVars a}"
  IO.println s!"b: {← instantiateMVars b}"

-- e) 2 + ?a =?= 3
#eval show MetaM Unit from do
  let a ← Lean.Meta.mkFreshExprMVar (Expr.const `Nat []) (userName := `a)
  let expr := Lean.mkAppN (Expr.const `Nat.add []) #[Lean.mkNatLit 2, a]
  let isEqual ← Lean.Meta.isDefEq expr (Lean.mkNatLit 3)
  IO.println isEqual -- false

-- f) 2 + ?a =?= 2 + 1
#eval show MetaM Unit from do
  let a ← Lean.Meta.mkFreshExprMVar (Expr.const `Nat []) (userName := `a)
  let expr := Lean.mkAppN (Expr.const `Nat.add []) #[Lean.mkNatLit 2, a]
  let expr' := Lean.mkAppN (Expr.const `Nat.add []) #[Lean.mkNatLit 2, Lean.mkNatLit 1]
  let isEqual ← Lean.Meta.isDefEq expr expr'
  IO.println isEqual -- true

  IO.println s!"a: {← instantiateMVars a}"

/- ### 9. [Computation] Write down what you expect the following code to output. -/

@[reducible] def reducibleDef     : Nat := 1 -- same as `abbrev`
@[instance] def instanceDef       : Nat := 2 -- same as `instance`
def defaultDef                    : Nat := 3
@[irreducible] def irreducibleDef : Nat := 4

@[reducible] def sum := [reducibleDef, instanceDef, defaultDef, irreducibleDef]

#eval show MetaM Unit from do
  let constantExpr := Expr.const `sum []

  Meta.withTransparency Meta.TransparencyMode.reducible do
    let reducedExpr ← Meta.reduce constantExpr
    dbg_trace (← ppExpr reducedExpr) -- [1, instanceDef, defaultDef, irreducibleDef]

  Meta.withTransparency Meta.TransparencyMode.instances do
    let reducedExpr ← Meta.reduce constantExpr
    dbg_trace (← ppExpr reducedExpr) -- [1, 2, defaultDef, irreducibleDef]

  Meta.withTransparency Meta.TransparencyMode.default do
    let reducedExpr ← Meta.reduce constantExpr
    dbg_trace (← ppExpr reducedExpr) -- [1, 2, 3, irreducibleDef]

  Meta.withTransparency Meta.TransparencyMode.all do
    let reducedExpr ← Meta.reduce constantExpr
    dbg_trace (← ppExpr reducedExpr) -- [1, 2, 3, 4]

  let reducedExpr ← Meta.reduce constantExpr
  dbg_trace (← ppExpr reducedExpr) -- [1, 2, 3, irreducibleDef]

/- ### 10. [Constructing Expressions] Create expression fun x, 1 + x in two ways: -/

-- a) not idiomatically, with loose bound variables
def tenA : MetaM Expr := do
  let body := Lean.mkAppN (Expr.const ``Nat.add []) #[mkNatLit 1, Expr.bvar 0]
  return Lean.Expr.lam `x (Lean.Expr.const ``Nat []) body BinderInfo.default

-- b) idiomatically.
def tenB : MetaM Expr := do
  withLocalDecl `x BinderInfo.default (.const ``Nat []) λ x => do
    -- let body := Lean.mkAppN (Expr.const `Nat.add []) #[Lean.mkNatLit 1, x]
    let body ← mkAppM ``Nat.add #[mkNatLit 1, x]
    mkLambdaFVars #[x] body

#eval show MetaM _ from do
  ppExpr (← tenA) -- fun x => Nat.add 1 x

#eval show MetaM _ from do
  ppExpr (← tenB) -- fun x => Nat.add 1 x

/- In what version can you use Lean.mkAppN? In what version can you use Lean.Meta.mkAppM? -/
-- We can use Lean.mkAppN in both versions, but Lean.Meta.mkAppM is only in tenB.

/- ### 11. [**Constructing Expressions**] Create expression `∀ (yellow: Nat), yellow`. -/

def eleven : MetaM Expr :=
  return Expr.forallE `yellow (Expr.const `Nat []) (Expr.bvar 0) BinderInfo.default

#eval show MetaM _ from do
  dbg_trace (← eleven) -- forall (yellow : Nat), yellow

/- ### 12. [**Constructing Expressions**] Create expression `∀ (n : Nat), n = n + 1` in two ways: -/

-- a) not idiomatically, with loose bound variables: we can only use `Lean.mkApp3`.
def twelveA : MetaM Expr := do
  let rhs := Expr.app (Expr.app (Expr.const `Nat.add []) (Expr.bvar 0)) (mkNatLit 1)
  let eqn := mkApp3 (Expr.const ``Eq []) (Expr.const `Nat []) (Expr.bvar 0) rhs
  return Expr.forallE `n (Expr.const `Nat []) eqn BinderInfo.default

#eval show MetaM _ from do
  ppExpr (← twelveA)

-- b) idiomatically. We can use both `Lean.mkApp3` and `Lean.Meta.mkEq`.
def twelveB : MetaM Expr := do
  withLocalDecl `n BinderInfo.default (.const ``Nat []) λ n => do
    let rhs ← mkAppM ``Nat.add #[n, mkNatLit 1]
    let eqn ← mkEq n rhs
    mkForallFVars #[n] eqn

#eval show MetaM _ from do
  ppExpr (← twelveB)

-- In what version can you use `Lean.mkApp3`? In what version can you use `Lean.Meta.mkEq`?

/- ### 13. -/
-- Create expression fun (f : Nat → Nat), ∀ (n : Nat), f n = f (n + 1) idiomatically.

def thirteen : MetaM Expr := do
  withLocalDecl `f BinderInfo.default (Expr.forallE `a (Expr.const `Nat []) (Expr.const `Nat []) .default) fun y => do
    let lamBody ← withLocalDecl `n BinderInfo.default (Expr.const `Nat []) fun x => do
      let fn := Expr.app y x
      let fnPlusOne := Expr.app y (Expr.app (Expr.app (Expr.const `Nat.add []) (x)) (Lean.mkNatLit 1))
      let forAllBody := mkApp3 (mkConst ``Eq []) (Expr.const `Nat []) fn fnPlusOne
      mkForallFVars #[x] forAllBody
    mkLambdaFVars #[y] lamBody

#eval show MetaM _ from do
  ppExpr (← thirteen) -- fun f => (n : Nat) → Eq Nat (f n) (f (Nat.add n 1))

/- ### 14. [**Constructing Expressions**] What would you expect the output of the following code to be? -/

#eval show Lean.Elab.Term.TermElabM _ from do
  let stx : Syntax ← `(∀ (a : Prop) (b : Prop), a ∨ b → b → a ∧ a)
  let expr ← Elab.Term.elabTermAndSynthesize stx none

  let (_, _, conclusion) ← forallMetaTelescope expr
  dbg_trace conclusion -- And ?_uniq.10 ?_uniq.10

  let (_, _, conclusion) ← forallMetaBoundedTelescope expr 2
  dbg_trace conclusion -- (Or ?_uniq.14 ?_uniq.15) -> ?_uniq.15 -> (And ?_uniq.14 ?_uniq.14)

  let (_, _, conclusion) ← lambdaMetaTelescope expr
  dbg_trace conclusion -- forall (a.1 : Prop) (b.1 : Prop), (Or a.1 b.1) -> b.1 -> (And a.1 a.1)

/- ### 15. -/

#eval show MetaM Unit from do
  let a ← Lean.Meta.mkFreshExprMVar (Expr.const `String []) (userName := `a)
  let b ← Lean.Meta.mkFreshExprMVar (Expr.sort (Nat.toLevel 1)) (userName := `b)
  -- ?a + Int
  let c := Lean.mkAppN (Expr.const `Nat.add []) #[a, Expr.const `Int []]
  -- "hi" + ?b
  let d := Lean.mkAppN (Expr.const `Nat.add []) #[Lean.mkStrLit "hi", b]

  IO.println s!"value in c: {← instantiateMVars c}" -- Nat.add ?_uniq.1 Int
  IO.println s!"value in d: {← instantiateMVars d}" -- Nat.add String ?_uniq.2

  let state : SavedState ← saveState
  IO.println "\nSaved state\n"

  if ← Lean.Meta.isDefEq c d then
    IO.println true
    IO.println s!"value in c: {← instantiateMVars c}"
    IO.println s!"value in d: {← instantiateMVars d}"

  restoreState state
  IO.println "\nRestored state\n"

  IO.println s!"value in c: {← instantiateMVars c}"
  IO.println s!"value in d: {← instantiateMVars d}"
