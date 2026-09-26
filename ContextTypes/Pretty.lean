import ContextTypes.Interp
import Lean.PrettyPrinter.Delaborator

set_option autoImplicit false

namespace ContextTypes

open Lean PrettyPrinter Delaborator SubExpr

open scoped ContextTypes

private def withExpression {α : Type}
    (e : Lean.Expr) (action : DelabM α) : DelabM α :=
  withTheReader Lean.SubExpr (fun s => { s with expr := e }) action

private def guardNotation : DelabM Unit := do
  guard !(← getPPOption getPPAll)
  guard (← getPPOption getPPNotation)

@[app_delab ContextTypes.ContextType.over,
  app_delab ContextTypes.ContextType.under,
  app_delab ContextTypes.ContextType.inter,
  app_delab ContextTypes.ContextType.union,
  app_delab ContextTypes.ContextType.sum,
  app_delab ContextTypes.ContextType.arrow,
  app_delab ContextTypes.ContextType.wand,
  app_delab ContextTypes.ContextType.persist]
private def delabContextType : Delab := do
  guardNotation
  let e ← getExpr
  let args := e.getAppArgs
  match e.getAppFn.constName? with
  | some ``ContextType.over =>
      guard (args.size >= 2)
      let b ← withNaryArg (args.size - 2) delab
      let q ← withNaryArg (args.size - 1) delab
      return ⟨← `(term| {ν : $b | $q})⟩
  | some ``ContextType.under =>
      guard (args.size >= 2)
      let b ← withNaryArg (args.size - 2) delab
      let q ← withNaryArg (args.size - 1) delab
      return ⟨← `(term| [ν : $b | $q])⟩
  | some ``ContextType.inter =>
      guard (args.size >= 2)
      let τ₁ ← withNaryArg (args.size - 2) delab
      let τ₂ ← withNaryArg (args.size - 1) delab
      return ⟨← `(term| $τ₁ ⊓ $τ₂)⟩
  | some ``ContextType.union =>
      guard (args.size >= 2)
      let τ₁ ← withNaryArg (args.size - 2) delab
      let τ₂ ← withNaryArg (args.size - 1) delab
      return ⟨← `(term| $τ₁ ⊔ $τ₂)⟩
  | some ``ContextType.sum =>
      guard (args.size >= 2)
      let τ₁ ← withNaryArg (args.size - 2) delab
      let τ₂ ← withNaryArg (args.size - 1) delab
      return ⟨← `(term| $τ₁ ⊕ $τ₂)⟩
  | some ``ContextType.arrow =>
      guard (args.size >= 2)
      let τ₁ ← withNaryArg (args.size - 2) delab
      let τ₂ ← withNaryArg (args.size - 1) delab
      return ⟨← `(term| $τ₁ → $τ₂)⟩
  | some ``ContextType.wand =>
      guard (args.size >= 2)
      let τ₁ ← withNaryArg (args.size - 2) delab
      let τ₂ ← withNaryArg (args.size - 1) delab
      return ⟨← `(term| $τ₁ -∗ $τ₂)⟩
  | some ``ContextType.persist =>
      let some τ := args.back? | failure
      let τ ← withExpression τ delab
      return ⟨← `(term| □ $τ)⟩
  | _ => failure

@[app_delab ContextTypes.Context.bind,
  app_delab ContextTypes.Context.comma,
  app_delab ContextTypes.Context.star,
  app_delab ContextTypes.Context.sum]
private def delabContext : Delab := do
  guardNotation
  let e ← getExpr
  let args := e.getAppArgs
  match e.getAppFn.constName? with
  | some ``Context.bind =>
      guard (args.size >= 2)
      let x ← withNaryArg (args.size - 2) delab
      let τ ← withNaryArg (args.size - 1) delab
      return ⟨← `(term| $x ∷ $τ)⟩
  | some ``Context.comma =>
      guard (args.size >= 2)
      let Γ₁ ← withNaryArg (args.size - 2) delab
      let Γ₂ ← withNaryArg (args.size - 1) delab
      return ⟨← `(term| $Γ₁ ,, $Γ₂)⟩
  | some ``Context.star =>
      guard (args.size >= 2)
      let Γ₁ ← withNaryArg (args.size - 2) delab
      let Γ₂ ← withNaryArg (args.size - 1) delab
      return ⟨← `(term| $Γ₁ ∗ $Γ₂)⟩
  | some ``Context.sum =>
      guard (args.size >= 2)
      let Γ₁ ← withNaryArg (args.size - 2) delab
      let Γ₂ ← withNaryArg (args.size - 1) delab
      return ⟨← `(term| $Γ₁ ⊕ $Γ₂)⟩
  | _ => failure

@[app_delab ContextTypes.Formula.top,
  app_delab ContextTypes.Formula.bot,
  app_delab ContextTypes.Formula.atom,
  app_delab ContextTypes.Formula.and,
  app_delab ContextTypes.Formula.or,
  app_delab ContextTypes.Formula.impl,
  app_delab ContextTypes.Formula.star,
  app_delab ContextTypes.Formula.wand,
  app_delab ContextTypes.Formula.sum,
  app_delab ContextTypes.Formula.all,
  app_delab ContextTypes.Formula.over,
  app_delab ContextTypes.Formula.under,
  app_delab ContextTypes.Formula.persist]
private def delabFormula : Delab := do
  guardNotation
  let e ← getExpr
  let args := e.getAppArgs
  match e.getAppFn.constName? with
  | some ``Formula.top => return ⟨← `(term| ⊤ᶜ)⟩
  | some ``Formula.bot => return ⟨← `(term| ⊥ᶜ)⟩
  | some ``Formula.atom =>
      let some q := args.back? | failure
      let q ← withExpression q delab
      return ⟨← `(term| Atom($q))⟩
  | some ``Formula.and =>
      guard (args.size >= 2)
      let P ← withNaryArg (args.size - 2) delab
      let Q ← withNaryArg (args.size - 1) delab
      return ⟨← `(term| $P ∧ᶜ $Q)⟩
  | some ``Formula.or =>
      guard (args.size >= 2)
      let P ← withNaryArg (args.size - 2) delab
      let Q ← withNaryArg (args.size - 1) delab
      return ⟨← `(term| $P ∨ᶜ $Q)⟩
  | some ``Formula.impl =>
      guard (args.size >= 2)
      let P ← withNaryArg (args.size - 2) delab
      let Q ← withNaryArg (args.size - 1) delab
      return ⟨← `(term| $P ⇒ᶜ $Q)⟩
  | some ``Formula.star =>
      guard (args.size >= 2)
      let P ← withNaryArg (args.size - 2) delab
      let Q ← withNaryArg (args.size - 1) delab
      return ⟨← `(term| $P ∗ $Q)⟩
  | some ``Formula.wand =>
      guard (args.size >= 3)
      let dExpr := args[args.size - 3]!
      let P ← withNaryArg (args.size - 2) delab
      let Q ← withNaryArg (args.size - 1) delab
      match ← Lean.Meta.getNatValue? dExpr with
      | some 1 => return ⟨← `(term| $P -∗ $Q)⟩
      | _ =>
          let d ← withNaryArg (args.size - 3) delab
          return ⟨← `(term| $P -∗[$d] $Q)⟩
  | some ``Formula.sum =>
      guard (args.size >= 2)
      let P ← withNaryArg (args.size - 2) delab
      let Q ← withNaryArg (args.size - 1) delab
      return ⟨← `(term| $P ⊕ $Q)⟩
  | some ``Formula.all =>
      let some P := args.back? | failure
      let P ← withExpression P delab
      let x := Lean.mkIdent `x
      return ⟨← `(term| ∀ᶜ $x:ident, $P)⟩
  | some ``Formula.over =>
      let some P := args.back? | failure
      let P ← withExpression P delab
      return ⟨← `(term| 🄾 $P)⟩
  | some ``Formula.under =>
      let some P := args.back? | failure
      let P ← withExpression P delab
      return ⟨← `(term| 🅄 $P)⟩
  | some ``Formula.persist =>
      let some P := args.back? | failure
      let P ← withExpression P delab
      return ⟨← `(term| □ $P)⟩
  | _ => failure

@[app_delab ContextTypes.Formula.bind]
private def delabFormulaBind : Delab := do
  guardNotation
  let args := (← getExpr).getAppArgs
  guard (args.size >= 2)
  let x ← withNaryArg (args.size - 2) delab
  let P ← withNaryArg (args.size - 1) delab
  return ⟨← `(term| $x ▷ $P)⟩

@[app_delab ContextTypes.Formula.bindSet]
private def delabFormulaBindSet : Delab := do
  guardNotation
  let args := (← getExpr).getAppArgs
  guard (args.size >= 2)
  let X ← withNaryArg (args.size - 2) delab
  let P ← withNaryArg (args.size - 1) delab
  return ⟨← `(term| $X ▷ $P)⟩

@[app_delab ContextTypes.ContextType.interp]
private def delabTypeInterp : Delab := do
  guardNotation
  let args := (← getExpr).getAppArgs
  guard (args.size >= 3)
  let Δ ← withNaryArg (args.size - 3) delab
  let τ ← withNaryArg (args.size - 2) delab
  let e ← withNaryArg (args.size - 1) delab
  return ⟨← `(term| ⟦$τ⟧[$Δ] $e)⟩

@[app_delab ContextTypes.Context.interpUnder]
private def delabContextInterp : Delab := do
  guardNotation
  let args := (← getExpr).getAppArgs
  guard (args.size >= 2)
  let «Σ» ← withNaryArg (args.size - 2) delab
  let Γ ← withNaryArg (args.size - 1) delab
  return ⟨← `(term| ⟦$Γ⟧[$«Σ»])⟩

end ContextTypes
