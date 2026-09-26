import ContextTypes.SynTyp

set_option autoImplicit false

namespace ContextTypes

/-!
# Semantic context typing

Semantic context typing interprets a bunched context as the assumptions of an
entailment and a context type at a term as its conclusion.
-/

open scoped ContextTypes

/-- Semantic context typing as entailment between the context and type
interpretations.  The primitive context is retained in the judgment so that
the syntactic and semantic judgments have the same public parameters; its
well-formedness is an external premise of the primitive compatibility case and
the Fundamental theorem. -/
def SemTyp (_Φ : PrimitiveContext) («Σ» : BasicEnv) (Γ : Context)
    (e : Term) (τ : ContextType) : Prop :=
  Context.interpUnder «Σ» Γ ⊫ ContextType.interp Γ.erase τ e

set_option hygiene false in
scoped[ContextTypes] notation:40 (name := semanticContextTyping)
    Φ:41 " ; " «Σ»:41 " ; " Γ:51 " ⊨ " e:41 " ⋮ " τ:41 =>
  ContextTypes.SemTyp Φ «Σ» Γ e τ

end ContextTypes
