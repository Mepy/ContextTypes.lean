import ContextTypes.SemTyp.Core
import Mathlib.Tactic

set_option autoImplicit false

namespace ContextTypes

/-! # Boolean matching semantic-typing compatibility -/

open scoped ContextTypes

namespace SemTyp

private theorem matchBool
    {Φ : PrimitiveContext} {«Σ» : BasicEnv} {Γ : Context}
    {x : Atom} {b : Bool} {τ : ContextType} {e₁ e₂ : Term}
    (wf : SynTyp.WellFormed «Σ» Γ (.matchBool (.free x) e₁ e₂) τ)
    (value : Φ ; «Σ» ; Γ ⊨ (.ret (.free x)) ⋮ ContextType.boolPrecise b)
    (branch : Φ ; «Σ» ; Γ ⊨ (if b then e₁ else e₂) ⋮ τ) :
    Φ ; «Σ» ; Γ ⊨ (.matchBool (.free x) e₁ e₂) ⋮ τ := by
  intro m hΓ
  have hworld := Context.models_interpUnder_erase_basicWorld wf.1 hΓ
  have hbasic := wf.2.2
  have hval : Γ.erase ⊢ᵥ (.free x) ⋮ (.base .bool) := by
    cases hbasic with
    | matchBool hv _ _ => exact hv
  have hselected : Γ.erase ⊢ₑ (if b then e₁ else e₂) ⋮ τ.erase := by
    cases hbasic with
    | matchBool _ ht hf =>
        cases b with
        | false => exact hf
        | true => exact ht
  have hvalue := value m hΓ
  have hlookup := ContextType.models_constantPrecise_ret_free_lookup
    (c := .bool b) hval hvalue
  have hbranch := branch m hΓ
  have hclosed : ∀ σ, σ ∈ m →
      (Interp.instantiateTerm (.matchBool (.free x) e₁ e₂) σ.toAssignment).locallyClosed := by
    intro σ hσ
    exact (Interp.instantiateTerm_typed hbasic
      ((Interp.models_basicWorld_iff m Γ.erase).1 hworld |>.2 σ hσ)).locallyClosed
  have htotal : m ⊨ Interp.total (.matchBool (.free x) e₁ e₂) := by
    apply (Interp.models_total_iff hbasic.locallyClosed).2
    refine ⟨Finset.Subset.trans hbasic.support_subset
      ((Interp.models_basicWorld_iff m Γ.erase).1 hworld).1, ?_⟩
    intro σ hσ
    apply (Interp.instantiateTerm_matchBool_mustTerminate_iff
      (hlookup σ hσ) (hclosed σ hσ)).2
    exact Interp.models_total_term hselected.locallyClosed
      (ContextType.models_interp_total hbranch) hσ
  apply ContextType.models_interp_of_reaches_iff wf.2.1 hselected hbasic hworld htotal
    _ _ hbranch
  · cases b with
    | false =>
        simp only [Bool.false_eq_true, ↓reduceIte, Term.support]
        exact Finset.subset_union_right
    | true =>
        simp only [↓reduceIte, Term.support]
        exact Finset.Subset.trans Finset.subset_union_right Finset.subset_union_left
  · intro σ hσ v
    exact (Interp.instantiateTerm_matchBool_reaches_iff
      (hlookup σ hσ) (hclosed σ hσ)).symm

/-- A precise true scrutinee selects the true branch semantically. -/
theorem matchTrue
    {Φ : PrimitiveContext} {«Σ» : BasicEnv} {Γ : Context}
    {x : Atom} {τ : ContextType} {e₁ e₂ : Term}
    (wf : SynTyp.WellFormed «Σ» Γ (.matchBool (.free x) e₁ e₂) τ)
    (value : Φ ; «Σ» ; Γ ⊨ (.ret (.free x)) ⋮ ContextType.boolPrecise true)
    (branch : Φ ; «Σ» ; Γ ⊨ e₁ ⋮ τ) :
    Φ ; «Σ» ; Γ ⊨ (.matchBool (.free x) e₁ e₂) ⋮ τ :=
  matchBool (b := true) wf value branch

/-- A precise false scrutinee selects the false branch semantically. -/
theorem matchFalse
    {Φ : PrimitiveContext} {«Σ» : BasicEnv} {Γ : Context}
    {x : Atom} {τ : ContextType} {e₁ e₂ : Term}
    (wf : SynTyp.WellFormed «Σ» Γ (.matchBool (.free x) e₁ e₂) τ)
    (value : Φ ; «Σ» ; Γ ⊨ (.ret (.free x)) ⋮ ContextType.boolPrecise false)
    (branch : Φ ; «Σ» ; Γ ⊨ e₂ ⋮ τ) :
    Φ ; «Σ» ; Γ ⊨ (.matchBool (.free x) e₁ e₂) ⋮ τ :=
  matchBool (b := false) wf value branch

/-- Precise Boolean branches of an additive context combine their complete
result capabilities into the corresponding additive result type. -/
theorem matchBoth
    {Φ : PrimitiveContext} {«Σ» : BasicEnv} {Γ₁ Γ₂ : Context}
    {x : Atom} {τ₁ τ₂ : ContextType} {e₁ e₂ : Term}
    (wf : SynTyp.WellFormed «Σ» (.sum Γ₁ Γ₂) (.matchBool (.free x) e₁ e₂) (.sum τ₁ τ₂))
    (trueValue : Φ ; «Σ» ; Γ₁ ⊨ (.ret (.free x)) ⋮ ContextType.boolPrecise true)
    (falseValue : Φ ; «Σ» ; Γ₂ ⊨ (.ret (.free x)) ⋮ ContextType.boolPrecise false)
    (trueBranch : Φ ; «Σ» ; Γ₁ ⊨ e₁ ⋮ τ₁)
    (falseBranch : Φ ; «Σ» ; Γ₂ ⊨ e₂ ⋮ τ₂) :
    Φ ; «Σ» ; (.sum Γ₁ Γ₂) ⊨ (.matchBool (.free x) e₁ e₂) ⋮ (.sum τ₁ τ₂) := by
  have eraseΓ : Γ₁.erase = Γ₂.erase := wf.1.2.2.2
  have eraseτ : τ₁.erase = τ₂.erase := wf.2.1.2.2
  have wf₁ : SynTyp.WellFormed «Σ» Γ₁ (.matchBool (.free x) e₁ e₂) τ₁ :=
    ⟨wf.1.1, wf.2.1.1, wf.2.2⟩
  have wf₂ : SynTyp.WellFormed «Σ» Γ₂ (.matchBool (.free x) e₁ e₂) τ₂ := by
    refine ⟨wf.1.2.1, ?_, ?_⟩
    · rw [← eraseΓ]
      exact wf.2.1.2.1
    · rw [← eraseΓ, ← eraseτ]
      exact wf.2.2
  intro m hΓ
  obtain ⟨m₁, m₂, defined, same, hΓ₁, hΓ₂⟩ := Context.models_interpUnder_sum_elim hΓ
  have h₁ := matchTrue wf₁ trueValue trueBranch m₁ hΓ₁
  have h₂ := matchFalse wf₂ falseValue falseBranch m₂ hΓ₂
  rw [← eraseΓ] at h₂
  exact ContextType.models_interp_sum_intro defined same wf.2.1 wf.2.2
    (Context.models_interpUnder_erase_basicWorld wf.1 hΓ) h₁ h₂

end SemTyp

end ContextTypes
