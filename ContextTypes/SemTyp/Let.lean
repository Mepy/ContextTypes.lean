import ContextTypes.SemTyp.Core
import Mathlib.Tactic

set_option autoImplicit false

namespace ContextTypes

open scoped ContextTypes

namespace SemTyp

/-- Ordinary let compatibility retains every intermediate result and its
correlation with the original input capability. -/
theorem letE
    {Φ : PrimitiveContext} {«Σ» : BasicEnv} {Γ : Context}
    {τ₁ τ₂ : ContextType} {e₁ e₂ : Term} (L : Finset Atom)
    (wf : SynTyp.WellFormed «Σ» Γ (.letE e₁ e₂) τ₂)
    (wf₁ : SynTyp.WellFormed «Σ» Γ e₁ τ₁)
    (wf₂ : ∀ x, x ∉ L → SynTyp.WellFormed «Σ» (Γ ,, (x ∷ τ₁))
      (e₂.openAt 0 (.free x)) τ₂)
    (left : Φ ; «Σ» ; Γ ⊨ e₁ ⋮ τ₁)
    (right : ∀ x, x ∉ L → Φ ; «Σ» ; (Γ ,, (x ∷ τ₁)) ⊨
      (e₂.openAt 0 (.free x)) ⋮ τ₂) :
    Φ ; «Σ» ; Γ ⊨ (.letE e₁ e₂) ⋮ τ₂ := by
  intro m hΓ
  let A := L ∪ m.domain ∪ (Context.erasureUnder «Σ» Γ).domain
  obtain ⟨x, hA⟩ := Finset.exists_nat_subset_range A
  have freshA : x ∉ A := by
    intro hx
    have := hA hx
    simp at this
  have freshL : x ∉ L := fun hx => freshA
    (Finset.mem_union_left _ (Finset.mem_union_left _ hx))
  have freshM : x ∉ m.domain := fun hx => freshA
    (Finset.mem_union_left _ (Finset.mem_union_right _ hx))
  have freshΔ : x ∉ (Context.erasureUnder «Σ» Γ).domain := fun hx => freshA
    (Finset.mem_union_right _ hx)
  have freshΓ : x ∉ Γ.erase.domain := by
    intro hx
    apply freshΔ
    rw [Context.erasureUnder, BasicEnv.domain_merge]
    exact Finset.mem_union_right _ hx
  have world := Context.models_interpUnder_erase_basicWorld wf.1 hΓ
  have hleft := left m hΓ
  have total₁ := ContextType.models_interp_total hleft
  have returns : ∀ σ, σ ∈ m → ∃ v, (Interp.instantiateTerm e₁ σ.toAssignment).reaches v :=
    fun σ hσ => (Interp.models_total_term wf₁.2.2.locallyClosed total₁ hσ).reaches_result
  let g := Interp.resultCapability m m.domain e₁ x (Finset.Subset.refl _) returns
  have base : g.restrict m.domain = m := by
    rw [Interp.resultCapability_restrict, Capability.restrict_domain_self]
  have href : m ⊑ g := base.symm
  have hΓg := Formula.models_kripke href hΓ
  have worldg := Formula.models_kripke href world
  have hleftg := Formula.models_kripke href hleft
  have support₁ : e₁.support ⊆ m.domain :=
    Finset.Subset.trans wf₁.2.2.support_subset ((Interp.models_basicWorld_iff m Γ.erase).1 world).1
  have typeSupport₁ : τ₁.freeAtoms ⊆ m.domain :=
    Finset.Subset.trans wf₁.2.1.freeAtoms_subset ((Interp.models_basicWorld_iff m Γ.erase).1 world).1
  have closedX : LogicVar.LocallyClosed (m.domain.image LogicVar.free) := by
    intro k hk
    simp at hk
  have logicSupport : e₁.logicSupport ⊆ m.domain.image LogicVar.free := by
    rw [LogicVar.eq_image_free_of_locallyClosed
      (Interp.termLogicSupport_locallyClosed e₁ wf₁.2.2.locallyClosed),
      Interp.freeAtomSet_term_logicSupport]
    exact Finset.image_subset_image support₁
  have hres := Interp.models_resultCapability m m.domain e₁ x
    (Finset.Subset.refl _) returns wf₁.2.2.locallyClosed support₁ freshM
  have hnamed := ContextType.models_interp_named_result wf₁.2.1 wf₁.2.2 worldg
    closedX logicSupport (Finset.image_subset_image typeSupport₁)
    (by simpa using freshM) freshΓ hres hleftg
  have hcom := Context.models_interpUnder_comma_bind wf.1 wf₁.2.1 freshΔ hΓg hnamed
  have hbody := right x freshL g hcom
  have wfbody := wf₂ x freshL
  have eraseBody : (Γ ,, (x ∷ τ₁) : Context).erase = Γ.erase.insert x τ₁.erase := by
    simp only [Context.erase]
    exact BasicEnv.merge_singleton_eq_insert freshΓ
  rw [eraseBody] at hbody
  have typedBody : Γ.erase.insert x τ₁.erase ⊢ₑ (e₂.openAt 0 (.free x)) ⋮ τ₂.erase := by
    simpa only [eraseBody] using wfbody.2.2
  have wfτBody : τ₂.WellFormed (Γ.erase.insert x τ₁.erase).domain := by
    simpa only [eraseBody] using wfbody.2.1
  have support₂ : e₂.support ⊆ m.domain := by
    apply Finset.Subset.trans _ ((Interp.models_basicWorld_iff m Γ.erase).1 world).1
    exact Finset.Subset.trans Finset.subset_union_right wf.2.2.support_subset
  have closedInputs : ∀ σ, σ ∈ m → ∀ y, y ∈ e₂.support →
      ∀ w, σ.lookup y = some w → w.locallyClosed := by
    intro σ hσ y hy w hw
    have hyΓ : y ∈ Γ.erase.domain :=
      wf.2.2.support_subset (Finset.mem_union_right _ hy)
    obtain ⟨T, hT⟩ := (BasicEnv.mem_domain_iff Γ.erase y).1 hyΓ
    obtain ⟨u, hu, htyped⟩ := (Interp.models_basicWorld_iff m Γ.erase).1 world |>.2 σ hσ y T hT
    have : u = w := Option.some.inj (hu.symm.trans hw)
    exact this ▸ htyped.locallyClosed
  have closedLet : ∀ σ, σ ∈ m →
      (Interp.instantiateTerm (.letE e₁ e₂) σ.toAssignment).locallyClosed := by
    intro σ hσ
    exact (Interp.instantiateTerm_typed wf.2.2
      ((Interp.models_basicWorld_iff m Γ.erase).1 world |>.2 σ hσ)).locallyClosed
  have total := Interp.models_total_let_of_resultCapability returns freshM
    wf.2.2.locallyClosed support₂ closedInputs closedLet total₁
    (ContextType.models_interp_total hbody)
  apply ContextType.models_interp_of_resultsEquivOn wfτBody wf.2.1
    typedBody wf.2.2 world total ?_ ?_ hbody
  · intro y hy
    rw [BasicEnv.lookup_insert_of_ne _ _]
    intro hyx
    subst y
    exact freshΓ (wf.2.1.freeAtoms_subset hy)
  · exact (Interp.resultsEquivOn_let_resultCapability returns freshM support₂
      closedInputs closedLet
      (Finset.Subset.trans wf.2.1.freeAtoms_subset ((Interp.models_basicWorld_iff m Γ.erase).1 world).1)).symm

end SemTyp

end ContextTypes

