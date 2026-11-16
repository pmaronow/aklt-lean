import Lean

/-! Untrusted elaboration of integer literals. The elaborator only constructs
ordinary kernel terms; it neither proves facts nor reads external files. -/
namespace AKLT.Cert.H1
open Lean Elab Term Meta

private def rowExpr (s : String) : MetaM Expr := do
  let cells ← (s.splitOn ",").mapM fun cell => do
    let some n := cell.toInt? | throwError "expected an integer literal"
    pure (mkIntLit n)
  mkListLit (mkConst ``Int) cells

syntax (name := intRow) "h1_row% " str : term
@[term_elab intRow] def elabIntRow : TermElab := fun stx _ => do
  let some s := stx[1].isStrLit? | throwError "expected a string literal"
  if s.isEmpty then
    return ← liftMetaM <| mkListLit (mkConst ``Int) []
  liftMetaM <| rowExpr s

end AKLT.Cert.H1
