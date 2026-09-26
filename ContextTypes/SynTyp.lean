import ContextTypes.Interp
import Mathlib.Tactic

set_option autoImplicit false

namespace ContextTypes

/-!
# Syntactic context typing

This module contains the declarative context-typing judgment, its primitive
operation interface, and the static side conditions shared by all typing
rules.
-/

open scoped ContextTypes

/-! ## Primitive-operation contexts -/

/-- A refined signature for one unary primitive operation. -/
structure PrimitiveSignature where
  argBase : BaseType
  argQualifier : Qualifier
  resultBase : BaseType
  resultQualifier : Qualifier

namespace PrimitiveSignature

/-- Overapproximate argument type of a primitive signature. -/
def argType (s : PrimitiveSignature) : ContextType :=
  .over s.argBase s.argQualifier

/-- Precise result type of a primitive signature. -/
def resultType (s : PrimitiveSignature) : ContextType :=
  .precise s.resultBase s.resultQualifier

@[simp] theorem erase_argType (s : PrimitiveSignature) :
    s.argType.erase = .base s.argBase :=
  rfl

@[simp] theorem erase_resultType (s : PrimitiveSignature) :
    s.resultType.erase = .base s.resultBase :=
  rfl

end PrimitiveSignature

/-- Refined signatures for all core primitive operations. -/
def PrimitiveContext := Primitive → PrimitiveSignature

namespace PrimitiveSignature

/-- A refined signature agrees with the erased core signature. -/
def ErasureOk (op : Primitive) (s : PrimitiveSignature) : Prop :=
  op.signature = Prod.mk s.argBase s.resultBase

/-- The primitive denotation is exact at its refined signature. -/
def SemanticOk (op : Primitive) (s : PrimitiveSignature) : Prop :=
  ∀ x,
    let Γ := Context.bind x s.argType
    let τ := s.resultType.openAt 0 x
    let e := Term.primitive op (.free x)
    (Context.interp Γ ⊫ ContextType.interp Γ.erase τ e) ∧
      (ContextType.interp Γ.erase τ e ⊫ Context.interp Γ)

/-- Static and semantic well-formedness of one primitive signature. -/
structure WellFormed (op : Primitive) (s : PrimitiveSignature) : Prop where
  erasure : s.ErasureOk op
  arg : s.argType.WellFormed ∅
  result : s.resultType.WellFormedAt 1 ∅
  semantic : s.SemanticOk op

end PrimitiveSignature

namespace PrimitiveContext

/-- Every signature in a primitive context is well formed. -/
def WellFormed (Φ : PrimitiveContext) : Prop :=
  ∀ op, (Φ op).WellFormed op

end PrimitiveContext

/-! ## Shared side conditions -/

namespace SynTyp

/-- Formation and erased typing required by every context-typing conclusion. -/
def WellFormed («Σ» : BasicEnv) (Γ : Context) (e : Term)
    (τ : ContextType) : Prop :=
  Γ.WellFormedUnder «Σ».domain ∧
  τ.WellFormed Γ.erase.domain ∧
  Γ.erase ⊢ₑ e ⋮ τ.erase

/-- A Boolean branch is semantically unreachable under a context. -/
def BranchUnreachable («Σ» : BasicEnv) (Γ : Context)
    (v : Value) (b : Bool) : Prop :=
  Context.interpUnder «Σ» Γ ⊫
    (ContextType.interp Γ.erase (ContextType.boolPrecise b) (.ret v) ⇒ᶜ ⊥ᶜ)

end SynTyp

/-! ## Declarative typing -/

/-- Syntactic context typing for the nondeterministic core language. -/
inductive SynTyp (Φ : PrimitiveContext) («Σ» : BasicEnv) :
    Context → Term → ContextType → Prop where
  | var (x : Atom) (τ : ContextType)
      (wf : SynTyp.WellFormed «Σ» (.bind x τ) (.ret (.free x)) τ) :
      SynTyp Φ «Σ» (.bind x τ) (.ret (.free x)) τ
  | const (c : Constant)
      (wf : SynTyp.WellFormed «Σ» .empty (.ret (.const c))
        (ContextType.constantPrecise c)) :
      SynTyp Φ «Σ» .empty (.ret (.const c))
        (ContextType.constantPrecise c)
  | sub {Γ : Context} {e : Term} {τ₁ τ₂ : ContextType}
      (wf : SynTyp.WellFormed «Σ» Γ e τ₂)
      (typed : SynTyp Φ «Σ» Γ e τ₁)
      (subtype : «Σ» ; Γ ⊢ τ₁ <: τ₂) :
      SynTyp Φ «Σ» Γ e τ₂
  | ctxSub {Γ₁ Γ₂ : Context} {e : Term} {τ : ContextType}
      (wf : SynTyp.WellFormed «Σ» Γ₁ e τ)
      (typed : SynTyp Φ «Σ» Γ₂ e τ)
      (subcontext : «Σ» ⊢ Γ₁ ≤[e.support ∪ τ.freeAtoms] Γ₂) :
      SynTyp Φ «Σ» Γ₁ e τ
  | persist {Γ : Context} {v : Value} {τ : ContextType}
      (wf : SynTyp.WellFormed «Σ» Γ (.ret v) (.persist τ))
      (persistent : Formula.Persistent (Context.interpUnder «Σ» Γ))
      (typed : SynTyp Φ «Σ» Γ (.ret v) τ) :
      SynTyp Φ «Σ» Γ (.ret v) (.persist τ)
  | letE {Γ : Context} {τ₁ τ₂ : ContextType} {e₁ e₂ : Term}
      (L : Finset Atom)
      (wf : SynTyp.WellFormed «Σ» Γ (.letE e₁ e₂) τ₂)
      (left : SynTyp Φ «Σ» Γ e₁ τ₁)
      (right : ∀ x, x ∉ L →
        SynTyp Φ «Σ» (.comma Γ (.bind x τ₁))
          (e₂.openAt 0 (.free x)) τ₂) :
      SynTyp Φ «Σ» Γ (.letE e₁ e₂) τ₂
  | letSep {Γ₁ Γ₂ : Context} {τ₁ τ₂ : ContextType} {e₁ e₂ : Term}
      (L : Finset Atom)
      (wf : SynTyp.WellFormed «Σ» (.star Γ₁ Γ₂) (.letE e₁ e₂) τ₂)
      (left : SynTyp Φ «Σ» Γ₁ e₁ τ₁)
      (right : ∀ x, x ∉ L →
        SynTyp Φ «Σ» (.star Γ₂ (.bind x τ₁))
          (e₂.openAt 0 (.free x)) τ₂) :
      SynTyp Φ «Σ» (.star Γ₁ Γ₂) (.letE e₁ e₂) τ₂
  | lam {Γ : Context} {τₓ τ : ContextType} {e : Term}
      (L : Finset Atom)
      (wf : SynTyp.WellFormed «Σ» Γ (.ret (.lam τₓ.erase e)) (.arrow τₓ τ))
      (body : ∀ y, y ∉ L →
        SynTyp Φ «Σ» (.comma Γ (.bind y τₓ))
          (e.openAt 0 (.free y)) (τ.openAt 0 y)) :
      SynTyp Φ «Σ» Γ (.ret (.lam τₓ.erase e)) (.arrow τₓ τ)
  | lamSep {Γ : Context} {τₓ τ : ContextType} {e : Term}
      (L : Finset Atom)
      (wf : SynTyp.WellFormed «Σ» Γ (.ret (.lam τₓ.erase e)) (.wand τₓ τ))
      (body : ∀ y, y ∉ L →
        SynTyp Φ «Σ» (.star Γ (.bind y τₓ))
          (e.openAt 0 (.free y)) (τ.openAt 0 y)) :
      SynTyp Φ «Σ» Γ (.ret (.lam τₓ.erase e)) (.wand τₓ τ)
  | app {Γ : Context} {τₓ τ : ContextType} {v : Value} {x : Atom}
      (wf : SynTyp.WellFormed «Σ» Γ (.app v (.free x)) (τ.openAt 0 x))
      (fresh : x ∉ v.support ∪ τₓ.freeAtoms ∪ τ.freeAtoms)
      (fn : SynTyp Φ «Σ» Γ (.ret v) (.arrow τₓ τ))
      (arg : SynTyp Φ «Σ» Γ (.ret (.free x)) τₓ) :
      SynTyp Φ «Σ» Γ (.app v (.free x)) (τ.openAt 0 x)
  | appSep {Γ₁ Γ₂ : Context} {τₓ τ : ContextType} {v : Value} {x : Atom}
      (wf : SynTyp.WellFormed «Σ» (.star Γ₁ Γ₂) (.app v (.free x))
        (τ.openAt 0 x))
      (fresh : x ∉ v.support ∪ τₓ.freeAtoms ∪ τ.freeAtoms)
      (fn : SynTyp Φ «Σ» Γ₁ (.ret v) (.wand τₓ τ))
      (arg : SynTyp Φ «Σ» Γ₂ (.ret (.free x)) τₓ) :
      SynTyp Φ «Σ» (.star Γ₁ Γ₂) (.app v (.free x)) (τ.openAt 0 x)
  | fixpoint {Γ : Context} {q : Qualifier} {τ : ContextType}
      {v : Value} {b : BaseType} {T : SimpleType} (L : Finset Atom)
      (erasure : τ.erase = T)
      (wf : SynTyp.WellFormed «Σ» Γ
        (.ret (.fix (.arrow (.base b) T) v)) (.arrow (.over b q) τ))
      (body : ∀ y, y ∉ L →
        SynTyp Φ «Σ» (.comma Γ (.bind y (.over b q)))
          (.ret (v.openAt 0 (.free y)))
          (.arrow (ContextType.recursiveCall b y (.over b q) τ)
            (τ.openAt 0 y))) :
      SynTyp Φ «Σ» Γ (.ret (.fix (.arrow (.base b) T) v))
        (.arrow (.over b q) τ)
  | primitive {Γ : Context} {op : Primitive} {x : Atom}
      (wf : SynTyp.WellFormed «Σ» Γ (.primitive op (.free x))
        ((Φ op).resultType.openAt 0 x))
      (arg : SynTyp Φ «Σ» Γ (.ret (.free x)) (Φ op).argType) :
      SynTyp Φ «Σ» Γ (.primitive op (.free x))
        ((Φ op).resultType.openAt 0 x)
  | matchBoth {Γ₁ Γ₂ : Context} {x : Atom} {τ₁ τ₂ : ContextType}
      {e₁ e₂ : Term}
      (wf : SynTyp.WellFormed «Σ» (.sum Γ₁ Γ₂) (.matchBool (.free x) e₁ e₂)
        (.sum τ₁ τ₂))
      (trueValue : SynTyp Φ «Σ» Γ₁ (.ret (.free x))
        (ContextType.boolPrecise true))
      (falseValue : SynTyp Φ «Σ» Γ₂ (.ret (.free x))
        (ContextType.boolPrecise false))
      (trueBranch : SynTyp Φ «Σ» Γ₁ e₁ τ₁)
      (falseBranch : SynTyp Φ «Σ» Γ₂ e₂ τ₂) :
      SynTyp Φ «Σ» (.sum Γ₁ Γ₂) (.matchBool (.free x) e₁ e₂)
        (.sum τ₁ τ₂)
  | matchTrue {Γ : Context} {x : Atom} {τ : ContextType} {e₁ e₂ : Term}
      (wf : SynTyp.WellFormed «Σ» Γ (.matchBool (.free x) e₁ e₂) τ)
      (value : SynTyp Φ «Σ» Γ (.ret (.free x))
        (ContextType.boolPrecise true))
      (branch : SynTyp Φ «Σ» Γ e₁ τ) :
      SynTyp Φ «Σ» Γ (.matchBool (.free x) e₁ e₂) τ
  | matchFalse {Γ : Context} {x : Atom} {τ : ContextType} {e₁ e₂ : Term}
      (wf : SynTyp.WellFormed «Σ» Γ (.matchBool (.free x) e₁ e₂) τ)
      (value : SynTyp Φ «Σ» Γ (.ret (.free x))
        (ContextType.boolPrecise false))
      (branch : SynTyp Φ «Σ» Γ e₂ τ) :
      SynTyp Φ «Σ» Γ (.matchBool (.free x) e₁ e₂) τ

set_option hygiene false in
scoped[ContextTypes] notation:40 (name := syntacticContextTyping)
    Φ:41 " ; " «Σ»:41 " ; " Γ:41 " ⊢ " e:41 " ⋮ " τ:41 =>
  ContextTypes.SynTyp Φ «Σ» Γ e τ

namespace SynTyp

theorem wellFormed {Φ : PrimitiveContext} {«Σ» : BasicEnv}
    {Γ : Context} {e : Term} {τ : ContextType}
    (h : SynTyp Φ «Σ» Γ e τ) : WellFormed «Σ» Γ e τ := by
  cases h <;> assumption

theorem contextWellFormed {Φ : PrimitiveContext} {«Σ» : BasicEnv}
    {Γ : Context} {e : Term} {τ : ContextType}
    (h : SynTyp Φ «Σ» Γ e τ) : Γ.WellFormedUnder «Σ».domain :=
  h.wellFormed.1

theorem typeWellFormed {Φ : PrimitiveContext} {«Σ» : BasicEnv}
    {Γ : Context} {e : Term} {τ : ContextType}
    (h : SynTyp Φ «Σ» Γ e τ) : τ.WellFormed Γ.erase.domain :=
  h.wellFormed.2.1

theorem basicTyping {Φ : PrimitiveContext} {«Σ» : BasicEnv}
    {Γ : Context} {e : Term} {τ : ContextType}
    (h : SynTyp Φ «Σ» Γ e τ) : Γ.erase ⊢ₑ e ⋮ τ.erase :=
  h.wellFormed.2.2

theorem termLocallyClosed {Φ : PrimitiveContext} {«Σ» : BasicEnv}
    {Γ : Context} {e : Term} {τ : ContextType}
    (h : SynTyp Φ «Σ» Γ e τ) : e.locallyClosed :=
  h.basicTyping.locallyClosed

theorem contextEraseDomain {Φ : PrimitiveContext} {«Σ» : BasicEnv}
    {Γ : Context} {e : Term} {τ : ContextType}
    (h : SynTyp Φ «Σ» Γ e τ) : Γ.erase.domain = Γ.domain :=
  Context.WellFormedUnder.erase_domain h.contextWellFormed

end SynTyp

end ContextTypes
