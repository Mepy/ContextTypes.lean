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

namespace SemTyp

/-- The atoms observed by a well-formed typing conclusion are observed by its
context interpretation. -/
theorem observed_subset_context {«Σ» : BasicEnv} {Γ : Context}
    {e : Term} {τ : ContextType}
    (wf : SynTyp.WellFormed «Σ» Γ e τ) :
    τ.freeAtoms ∪ e.support ⊆
      (Context.interpUnder «Σ» Γ).freeAtoms := by
  have hΓdom : Γ.erase.domain ⊆ (Context.erasureUnder «Σ» Γ).domain := by
    simp only [Context.erasureUnder]
    simp only [BasicEnv.domain_merge]
    simp only [BasicEnv.domain_restrict]
    exact Finset.subset_union_right
  have hinterp :=
    Context.erasureUnder_domain_subset_freeAtoms_interpUnder «Σ» Γ
  exact Finset.union_subset
    (Finset.Subset.trans wf.2.1.freeAtoms_subset
      (Finset.Subset.trans hΓdom hinterp))
    (Finset.Subset.trans wf.2.2.support_subset
      (Finset.Subset.trans hΓdom hinterp))

/-- A model of a well-formed typing context contains every atom observed by
the conclusion. -/
theorem observed_subset {«Σ» : BasicEnv} {Γ : Context}
    {e : Term} {τ : ContextType} {m : Capability}
    (wf : SynTyp.WellFormed «Σ» Γ e τ)
    (hΓ : m ⊨ Context.interpUnder «Σ» Γ) :
    τ.freeAtoms ∪ e.support ⊆ m.domain :=
  Finset.Subset.trans (observed_subset_context wf) (Formula.models_scope hΓ)

end SemTyp

end ContextTypes
