import Lean.Elab.Tactic
open Lean Elab Tactic Meta

/- ### 1. -/
-- Consider the theorem `p ∧ q ↔ q ∧ p`. We could either write its proof as a proof term, or construct it using the tactics.
-- When we are writing the proof of this theorem *as a proof term*, we're gradually filling up `_`s with certain expressions, step by step. Each such step corresponds to a tactic.

-- There are many combinations of steps in which we could write this proof term - but consider the sequence of steps we wrote below. Please write each step as a tactic.
-- The tactic `step_1` is filled in, please do the same for the remaining tactics (for the sake of the exercise, try to use lower-level apis, such as `mkFreshExprMVar`, `mvarId.assign` and `modify fun _ => { goals := ~)`.

elab "step_1" : tactic => do
  let mvarId ← getMainGoal
  let goalType ← getMainTarget

  let Expr.app (Expr.app (Expr.const `Iff _) a) b := goalType | throwError "Goal type is not of the form `a ↔ b`"

  -- 1. Create new `_`s with appropriate types.
  let mvarId1 ← mkFreshExprMVar (Expr.forallE `xxx a b .default) (userName := "red")
  let mvarId2 ← mkFreshExprMVar (Expr.forallE `yyy b a .default) (userName := "blue")

  -- 2. Assign the main goal to the expression `Iff.intro _ _`.
  mvarId.assign (mkAppN (Expr.const `Iff.intro []) #[a, b, mvarId1, mvarId2])

  -- 3. Report the new `_`s to Lean as the new goals.
  modify fun _ => { goals := [mvarId1.mvarId!, mvarId2.mvarId!] }

elab "step_2" : tactic => do
  let some redMvarId ← (← get).goals.findM? (fun mvarId => do
    return (← mvarId.getDecl).userName == `red
  ) | throwError "No mvar with username `red`"
  let some blueMvarId ← (← get).goals.findM? (fun mvarId => do
    return (← mvarId.getDecl).userName == `blue
  ) | throwError "No mvar with username `blue`"

  -- `red`
  let Expr.forallE _ redFrom redTo _ := (← redMvarId.getDecl).type | throwError "Goal type is not of the form `a → b`"
  let handyRedMvarId ← withLocalDecl `hA BinderInfo.default redFrom (fun fvar => do
    -- syntheticOpaque to prevent isDefEq from assigning
    let mvarId1 ← mkFreshExprMVar redTo MetavarKind.syntheticOpaque `red
    redMvarId.assign (← mkLambdaFVars #[fvar] mvarId1)
    return mvarId1.mvarId!
  )

  modify fun _ => { goals := [handyRedMvarId, blueMvarId] }

  -- `blue`
  let Expr.forallE _ blueFrom _ _ := (← blueMvarId.getDecl).type | throwError "Goal type is not of the form `a → b`"
  -- `fun hB : q ∧ p => (And.intro hB.right hB.left)`.
  Lean.Meta.withLocalDecl `hB .default blueFrom (fun hB => do
    let body ← Lean.Meta.mkAppM `And.intro #[← Lean.Meta.mkAppM `And.right #[hB], ← Lean.Meta.mkAppM `And.left #[hB]]
    blueMvarId.assign (← Lean.Meta.mkLambdaFVars #[hB] body)
  )
  modify fun _ => { goals := [handyRedMvarId] }

elab "step_3" : tactic => do
  let mvarId ← getMainGoal
  let goalType ← getMainTarget
  let mainDecl ← mvarId.getDecl

  let Expr.app (Expr.app (Expr.const `And _) q) p := goalType | throwError "Goal type is not of the form `And q p`"

  let mvarId1 ← mkFreshExprMVarAt mainDecl.lctx mainDecl.localInstances q (userName := "red1")
  let mvarId2 ← mkFreshExprMVarAt mainDecl.lctx mainDecl.localInstances p (userName := "red2")

  -- `And.intro _ _`.
  mvarId.assign (← mkAppM `And.intro #[mvarId1, mvarId2])

  modify fun _ => { goals := [mvarId1.mvarId!, mvarId2.mvarId!] }

elab "step_4" : tactic => do
  let some red1MvarId ← (← get).goals.findM? (fun mvarId => do
    return (← mvarId.getDecl).userName == `red1
  ) | throwError "No mvar with username `red1`"
  let some red2MvarId ← (← get).goals.findM? (fun mvarId => do
    return (← mvarId.getDecl).userName == `red2
  ) | throwError "No mvar with username `red2`"

  let some hA := (← red1MvarId.getDecl).lctx.findFromUserName? `hA | throwError "No hypthesis with name `hA` (in goal `red1`)"
  red1MvarId.withContext do
    red1MvarId.assign (← mkAppM `And.right #[hA.toExpr])
  modify fun _ => { goals := [red2MvarId] }

  let some hA := (← red2MvarId.getDecl).lctx.findFromUserName? `hA | throwError "No hypthesis with name `hA` (in goal `red2`)"
  red2MvarId.withContext do
    red2MvarId.assign (← mkAppM `And.left #[hA.toExpr])
  modify fun _ => { goals := [] }

theorem gradual (p q : Prop) : p ∧ q ↔ q ∧ p := by
  step_1
  step_2
  step_3
  step_4

/- ### 2. -/
-- In the first exercise, we used lower-level `modify` api to update our goals.
-- `liftMetaTactic`, `setGoals`, `appendGoals`, `replaceMainGoal`, `closeMainGoal`, etc. are all syntax sugars on top of `modify fun s : State => { s with goals := myMvarIds }`.
-- Please rewrite the `forker` tactic with:

-- **a)** `liftMetaTactic`
-- **b)** `setGoals`
-- **c)** `replaceMainGoal`

elab "forker" : tactic => do
  let mvarId ← getMainGoal
  let goalType ← getMainTarget

  let (Expr.app (Expr.app (Expr.const `And _) p) q) := goalType | Lean.Meta.throwTacticEx `forker mvarId (m!"Goal is not of the form P ∧ Q")

  mvarId.withContext do
    let mvarIdP ← mkFreshExprMVar p (userName := "red")
    let mvarIdQ ← mkFreshExprMVar q (userName := "blue")

    let proofTerm := mkAppN (Expr.const `And.intro []) #[p, q, mvarIdP, mvarIdQ]
    mvarId.assign proofTerm

    modify fun state => { goals := [mvarIdP.mvarId!, mvarIdQ.mvarId!] ++ state.goals.drop 1 }

-- **a)** `liftMetaTactic`
elab "forkerA" : tactic => do
  liftMetaTactic fun mvarId => do
    let (Expr.app (Expr.app (Expr.const `And _) p) q) ← mvarId.getType | Lean.Meta.throwTacticEx `forker mvarId (m!"Goal is not of the form P ∧ Q")

    let mvarIdP ← mkFreshExprMVar p (userName := "red")
    let mvarIdQ ← mkFreshExprMVar q (userName := "blue")

    let proofTerm := mkAppN (Expr.const `And.intro []) #[p, q, mvarIdP, mvarIdQ]
    mvarId.assign proofTerm

    return [mvarIdP.mvarId!, mvarIdQ.mvarId!]

-- **b)** `setGoals`
elab "forkerB" : tactic => do
  let mvarId ← getMainGoal
  let goalType ← getMainTarget

  let (Expr.app (Expr.app (Expr.const `And _) p) q) := goalType | Lean.Meta.throwTacticEx `forker mvarId (m!"Goal is not of the form P ∧ Q")

  mvarId.withContext do
    let mvarIdP ← mkFreshExprMVar p (userName := "red")
    let mvarIdQ ← mkFreshExprMVar q (userName := "blue")

    let proofTerm := mkAppN (Expr.const `And.intro []) #[p, q, mvarIdP, mvarIdQ]
    mvarId.assign proofTerm

    setGoals [mvarIdP.mvarId!, mvarIdQ.mvarId!]

-- **c)** `replaceMainGoal`
elab "forkerC" : tactic => do
  let mvarId ← getMainGoal
  let goalType ← getMainTarget

  let (Expr.app (Expr.app (Expr.const `And _) p) q) := goalType | Lean.Meta.throwTacticEx `forker mvarId (m!"Goal is not of the form P ∧ Q")

  mvarId.withContext do
    let mvarIdP ← mkFreshExprMVar p (userName := "red")
    let mvarIdQ ← mkFreshExprMVar q (userName := "blue")

    let proofTerm := mkAppN (Expr.const `And.intro []) #[p, q, mvarIdP, mvarIdQ]
    mvarId.assign proofTerm

    replaceMainGoal [mvarIdP.mvarId!, mvarIdQ.mvarId!]

example (A B C : Prop) : A → B → C → (A ∧ B) ∧ C := by
  intro hA hB hC
  forkerA
  forkerA
  all_goals assumption

/- ### 3. -/
-- In the first exercise, you created your own `intro` in `step_2` (with a hardcoded hypothesis name, but the basics are the same). When writing tactics, we usually want to use functions such as `intro`, `intro1`, `intro1P`, `introN` or `introNP`.

-- For each of the points below, create a tactic `introductor` (one per each point), that turns the goal `(ab: a = b) → (bc: b = c) → (a = c)`:

-- **a)** into the goal `(a = c)` with hypotheses `(ab✝: a = b)` and `(bc✝: b = c)`.
-- **b)** into the goal `(bc: b = c) → (a = c)` with hypothesis `(ab: a = b)`.
-- **c)** into the goal `(bc: b = c) → (a = c)` with hypothesis `(hello: a = b)`.

-- Hint: **"P"** in `intro1P` and `introNP` stands for **"Preserve"**.

elab "introductorA" : tactic => do
  withMainContext do
    liftMetaTactic fun mvarId => do
      let (_, mvarIdNew) ← mvarId.introN 2
      return [mvarIdNew]

elab "introductorB" : tactic => do
  withMainContext do
    liftMetaTactic fun mvarId => do
      let (_, mvarIdNew) ← mvarId.intro1P
      return [mvarIdNew]

elab "introductorC" : tactic => do
  withMainContext do
    liftMetaTactic fun mvarId => do
      let (_, mvarIdNew) ← mvarId.intro `hello
      return [mvarIdNew]

example (a b c : Nat) : (ab: a = b) → (bc: b = c) → (a = c) := by
  introductorC
  sorry
