module
public meta import Lean.Elab.Term
/-!
# Raw integer-list literals

`raw_ints% [3, -5, 7]` elaborates directly to `List.cons (Int.ofNat 3) (List.cons (Int.negSucc 4) …)`
with raw `Nat` literals: no `OfNat`/`Neg` instance synthesis per element. Elaborating the megabyte
literal states of the split certificates the usual way spent minutes in `synthesize pending MVars`.
The resulting term is also smaller for the kernel to type-check. It is definitionally the same list.
-/

declare_syntax_cat rawint
syntax num : rawint
syntax "-" num : rawint
syntax (name := rawIntsStx) "raw_ints% " "[" rawint,* "]" : term

public meta section
namespace CatalanMeasure.CellCert
open Lean Elab Term

def rawIntExpr : Int → Expr
  | .ofNat n => mkApp (Lean.mkConst ``Int.ofNat) (mkRawNatLit n)
  | .negSucc n => mkApp (Lean.mkConst ``Int.negSucc) (mkRawNatLit n)

@[term_elab rawIntsStx] def elabRawInts : TermElab := fun stx _ => do
  let int := Lean.mkConst ``Int
  let mut acc := mkApp (Lean.mkConst ``List.nil [Level.zero]) int
  for a in stx[2].getSepArgs.reverse do
    let z : Int ← match a with
      | `(rawint| $n:num) => pure (n.getNat : Int)
      | `(rawint| - $n:num) => pure (-(n.getNat : Int))
      | _ => throwUnsupportedSyntax
    acc := mkApp3 (Lean.mkConst ``List.cons [Level.zero]) int (rawIntExpr z) acc
  return acc

end CatalanMeasure.CellCert
end
