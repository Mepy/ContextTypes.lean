import ContextTypes.SemTyp

set_option autoImplicit false

namespace ContextTypes.Fundamental

open scoped ContextTypes

/-- Syntactic context typing entails semantic context typing for every
well-formed primitive-operation context. -/
theorem sound {Φ : PrimitiveContext} {«Σ» : BasicEnv} {Γ : Context}
    {e : Term} {τ : ContextType} (wfΦ : Φ.WellFormed)
    (typed : Φ ; «Σ» ; Γ ⊢ e ⋮ τ) : Φ ; «Σ» ; Γ ⊨ e ⋮ τ := by
  induction typed with
  | var x τ wf => exact SemTyp.var x τ wf
  | const c wf => exact SemTyp.const c wf
  | sub wf typed subtype ih => exact SemTyp.sub wf ih subtype
  | ctxSub wf typed subcontext ih => exact SemTyp.ctxSub wf ih subcontext
  | persist wf persistent typed ih => exact SemTyp.persist wf persistent ih
  | letE L wf left right ih₁ ih₂ =>
    exact SemTyp.letE L wf left.wellFormed (fun x hx => (right x hx).wellFormed) ih₁ ih₂
  | letSep L wf left right ih₁ ih₂ =>
    exact SemTyp.letSep L wf left.wellFormed (fun x hx => (right x hx).wellFormed) ih₁ ih₂
  | lam L wf body ih =>
    exact SemTyp.lam L wf (fun y hy => (body y hy).wellFormed) ih
  | lamSep L wf body ih =>
    exact SemTyp.lamSep L wf (fun y hy => (body y hy).wellFormed) ih
  | app wf fresh fn arg ih₁ ih₂ =>
    exact SemTyp.app wf fn.wellFormed arg.wellFormed fresh ih₁ ih₂
  | appSep wf fresh fn arg ih₁ ih₂ =>
    exact SemTyp.appSep wf fn.wellFormed arg.wellFormed fresh ih₁ ih₂
  | fixpoint L erasure wf body ih =>
    exact SemTyp.fixpoint L erasure wf (fun y hy => (body y hy).wellFormed) ih
  | primitive wf arg ih => exact SemTyp.primitive wfΦ wf ih
  | matchBoth wf trueValue falseValue trueBranch falseBranch ih₁ ih₂ ih₃ ih₄ =>
    exact SemTyp.matchBoth wf ih₁ ih₂ ih₃ ih₄
  | matchTrue wf value branch ih₁ ih₂ => exact SemTyp.matchTrue wf ih₁ ih₂
  | matchFalse wf value branch ih₁ ih₂ => exact SemTyp.matchFalse wf ih₁ ih₂

/-- Fundamental theorem for the core language's concrete primitive signatures. -/
theorem concrete {«Σ» : BasicEnv} {Γ : Context} {e : Term} {τ : ContextType}
    (typed : PrimitiveContext.concrete ; «Σ» ; Γ ⊢ e ⋮ τ) :
    PrimitiveContext.concrete ; «Σ» ; Γ ⊨ e ⋮ τ :=
  sound PrimitiveContext.concrete_wellFormed typed

end ContextTypes.Fundamental
