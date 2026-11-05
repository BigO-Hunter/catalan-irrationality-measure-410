module
public import Submission.CatalanMeasure.Cert.ExplicitIntegerGap
public meta import Lean.Meta.Eval
public meta import Lean.Elab.Tactic
@[expose] public section
namespace CatalanMeasure.Cert

theorem ipHom_step_explicit (a b d c : ℤ) (p D N : List ℤ)
    (h : ipHom a b d p=(D,N)) :
    ipHom a b d (c::p)=
      (ipLinear d d D,ipAdd (ipSmul c D) (ipLinear b a N)) := by
  rw [ipHom,h]

theorem noRootCheck_of_explicitHom (p : List ℤ) (a b d : ℤ) (D N : List ℤ)
    (h : ipHom a b d p=(D,N)) (hd : 0<d) (hab : a<b)
    (hs : ipSignCheck N=true) : ipNoRootCheck p a b d=true := by
  simp only [ipNoRootCheck,h,hd,hab,decide_true,Bool.true_and,hs]

end CatalanMeasure.Cert

public meta section
namespace CatalanMeasure.Cert
open Lean Meta Elab Tactic

def witnessAdd (p q : List Int) : List Int :=
  match p,q with
  | [],q => q
  | p,[] => p
  | a::p,b::q => (a+b)::witnessAdd p q

def witnessSmul (a : Int) (p : List Int) : List Int := p.map (a*·)
def witnessLinear (a b : Int) (p : List Int) : List Int :=
  witnessAdd (witnessSmul a p) (0::witnessSmul b p)

def proveWitnessArithmetic (ty : Expr) : TacticM Expr := do
  let saved ← getGoals
  let h ← mkFreshExprMVar ty
  setGoals [h.mvarId!]
  -- Only one linear/list update is reduced here. No recursive homogeneous
  -- substitution is unfolded, and the equality is checked by the kernel.
  evalTactic (← `(tactic| decide +kernel))
  unless (← getGoals).isEmpty do
    throwError "unclosed integer-list witness step"
  let proof ← instantiateMVars h
  setGoals saved
  return proof

partial def buildHomWitness (aE bE dE : Expr) (a b d : Int)
    (remaining suffix den num : List Int) (hp : Expr) : TacticM Expr := do
  match remaining with
  | [] => return hp
  | c::rest =>
    let step ← mkAppM ``ipHom_step_explicit
      #[aE,bE,dE,toExpr c,toExpr suffix,toExpr den,toExpr num,hp]
    let some (_,_,rhs) := (← inferType step).eq? |
      throwError "unexpected homogeneous step type"
    let nextDen := witnessLinear d d den
    let nextNum := witnessAdd (witnessSmul c den) (witnessLinear b a num)
    let pair ← mkAppM ``Prod.mk #[toExpr nextDen,toExpr nextNum]
    let ha ← proveWitnessArithmetic (← mkEq rhs pair)
    let hn ← mkEqTrans step ha
    if suffix.length % 20 == 0 then
      IO.println s!"hom witness step {suffix.length+1}"
    -- Keep every checked prefix as a local proof. Reusing a free variable
    -- prevents repeated elaboration of the entire growing equality proof.
    withLetDecl (Name.mkSimple s!"homWitness{suffix.length}") (← inferType hn) hn fun hlocal => do
      let result ← buildHomWitness aE bE dE a b d rest (c::suffix) nextDen nextNum hlocal
      mkLetFVars #[hlocal] result

/-- Construct ordinary equality proofs for each short integer-list recurrence.
Compiled evaluation chooses integer witnesses only. Every recurrence and final
sign comparison is proved separately and checked by the Lean kernel. -/
elab "certify_hom_gap" : tactic => withMainContext do
  let goal ← getMainGoal
  let some (_,lhs,_) := (← goal.getType).eq? |
    throwError "expected an equality with ipNoRootCheck"
  unless lhs.getAppFn.isConstOf ``ipNoRootCheck do
    throwError "expected ipNoRootCheck on the left"
  let args := lhs.getAppArgs
  unless args.size=4 do throwError "unexpected no-root checker arity"
  let pE := args[0]!
  let aE := args[1]!
  let bE := args[2]!
  let dE := args[3]!
  let p ← unsafe evalExpr (List Int) (mkApp (mkConst ``List [Level.zero]) (mkConst ``Int)) pE
  let a ← unsafe evalExpr Int (mkConst ``Int) aE
  let b ← unsafe evalExpr Int (mkConst ``Int) bE
  let d ← unsafe evalExpr Int (mkConst ``Int) dE
  let base ← mkAppM ``ipHom #[aE,bE,dE,toExpr ([]:List Int)]
  let hp ← buildHomWitness aE bE dE a b d p.reverse [] [1] [] (← mkEqRefl base)
  let some (_,_,pair) := (← inferType hp).eq? | throwError "unexpected final witness type"
  let den := pair.getAppArgs[2]!
  let num := pair.getAppArgs[3]!
  let finish ← mkAppM ``noRootCheck_of_explicitHom
    #[pE,aE,bE,dE,den,num,hp]
  let goals ← goal.apply finish
  setGoals goals
  evalTactic (← `(tactic| all_goals decide +kernel))

end CatalanMeasure.Cert
