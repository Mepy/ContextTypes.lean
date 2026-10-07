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

/-- Separating let evaluates the left factor and frames every intermediate
result with the independent context before interpreting the body. -/
theorem letSep
    {Φ : PrimitiveContext} {«Σ» : BasicEnv} {Γ₁ Γ₂ : Context}
    {τ₁ τ₂ : ContextType} {e₁ e₂ : Term} (L : Finset Atom)
    (wf : SynTyp.WellFormed «Σ» (Γ₁ ∗ Γ₂) (.letE e₁ e₂) τ₂)
    (wf₁ : SynTyp.WellFormed «Σ» Γ₁ e₁ τ₁)
    (wf₂ : ∀ x, x ∉ L → SynTyp.WellFormed «Σ» (Γ₂ ∗ (x ∷ τ₁))
      (e₂.openAt 0 (.free x)) τ₂)
    (left : Φ ; «Σ» ; Γ₁ ⊨ e₁ ⋮ τ₁)
    (right : ∀ x, x ∉ L → Φ ; «Σ» ; (Γ₂ ∗ (x ∷ τ₁)) ⊨
      (e₂.openAt 0 (.free x)) ⋮ τ₂) :
    Φ ; «Σ» ; (Γ₁ ∗ Γ₂) ⊨ (.letE e₁ e₂) ⋮ τ₂ := by
  intro m hΓ
  obtain ⟨m₁, m₂, compat, href, h₁, h₂⟩ := Context.models_interpUnder_star_elim hΓ
  let p := Capability.product m₁ m₂ compat
  have href₁ := Capability.refines_trans (Capability.product_refines_left compat) href
  have href₂ := Capability.refines_trans (Capability.product_refines_right compat) href
  have world := Context.models_interpUnder_erase_basicWorld wf.1 hΓ
  have world₁ := Context.models_interpUnder_erase_basicWorld wf₁.1 h₁
  have hleft := left m₁ h₁
  have hleftM := Formula.models_kripke href₁ hleft
  have total₁ := ContextType.models_interp_total hleft
  have returns₁ : ∀ σ, σ ∈ m₁ → ∃ v, (Interp.instantiateTerm e₁ σ.toAssignment).reaches v :=
    fun σ hσ => (Interp.models_total_term wf₁.2.2.locallyClosed total₁ hσ).reaches_result
  have returnsP : ∀ σ, σ ∈ p → ∃ v, (Interp.instantiateTerm e₁ σ.toAssignment).reaches v :=
    fun σ hσ => (Interp.models_total_term wf₁.2.2.locallyClosed
      (Formula.models_kripke (Capability.product_refines_left compat) total₁) hσ).reaches_result
  have totalM := ContextType.models_interp_total hleftM
  have returnsM : ∀ σ, σ ∈ m → ∃ v, (Interp.instantiateTerm e₁ σ.toAssignment).reaches v :=
    fun σ hσ => (Interp.models_total_term wf₁.2.2.locallyClosed totalM hσ).reaches_result
  obtain ⟨x, hx⟩ := Finset.exists_nat_subset_range (L ∪ m.domain)
  have fresh : x ∉ L ∪ m.domain := by
    intro h
    have := hx h
    simp at this
  have freshL : x ∉ L := fun h => fresh (Finset.mem_union_left _ h)
  have freshM : x ∉ m.domain := fun h => fresh (Finset.mem_union_right _ h)
  have fresh₁ : x ∉ m₁.domain := fun h => freshM (Capability.refines_domain_subset href₁ h)
  have fresh₂ : x ∉ m₂.domain := fun h => freshM (Capability.refines_domain_subset href₂ h)
  have freshΓ₁ : x ∉ Γ₁.erase.domain := fun h => fresh₁
    ((Interp.models_basicWorld_iff m₁ Γ₁.erase).1 world₁ |>.1 h)
  have wfbody := wf₂ x freshL
  have closedτ : τ₁.freeAtoms = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.2
    intro y hy
    have hyΓ : y ∈ Γ₁.domain := by
      rw [← wf₁.1.erase_domain]
      exact wf₁.2.1.freeAtoms_subset hy
    have hambient : y ∈ «Σ».domain := wfbody.1.2.1.2.freeAtoms_subset hy
    exact Finset.disjoint_left.1 wf₁.1.domain_disjoint hyΓ hambient
  have support₁ : e₁.support ⊆ m₁.domain :=
    Finset.Subset.trans wf₁.2.2.support_subset ((Interp.models_basicWorld_iff m₁ Γ₁.erase).1 world₁).1
  let g₁ := Interp.resultCapability m₁ m₁.domain e₁ x (Finset.Subset.refl _) returns₁
  let g := Interp.resultCapability m m.domain e₁ x (Finset.Subset.refl _) returnsM
  have base₁ : g₁.restrict m₁.domain = m₁ := by
    rw [Interp.resultCapability_restrict, Capability.restrict_domain_self]
  have hrefg₁ : m₁ ⊑ g₁ := base₁.symm
  have logicX : e₁.logicSupport ⊆ m₁.domain.image LogicVar.free := by
    rw [LogicVar.eq_image_free_of_locallyClosed
      (Interp.termLogicSupport_locallyClosed e₁ wf₁.2.2.locallyClosed),
      Interp.freeAtomSet_term_logicSupport]
    exact Finset.image_subset_image support₁
  have named := ContextType.models_interp_named_result wf₁.2.1 wf₁.2.2
    (Formula.models_kripke hrefg₁ world₁) (by intro k hk; simp at hk) logicX
    (by simp [closedτ]) (by simpa using fresh₁) freshΓ₁
    (Interp.models_resultCapability m₁ m₁.domain e₁ x (Finset.Subset.refl _) returns₁
      wf₁.2.2.locallyClosed support₁ fresh₁)
    (Formula.models_kripke hrefg₁ hleft)
  have named' : g₁ ⊨ ContextType.interp (BasicEnv.singleton x τ₁.erase) τ₁ (.ret (.free x)) := by
    have agree : BasicEnv.AgreeOn (τ₁.freeAtoms ∪ (.ret (.free x) : Term).support)
        (Γ₁.erase.insert x τ₁.erase) (BasicEnv.singleton x τ₁.erase) := by
      intro y hy
      have hyx : y = x := by simpa [closedτ, Term.support, Value.support] using hy
      subst y
      simp
    rw [← ContextType.interp_eq_of_agreeOn agree]
    exact named
  have compatg : Capability.Compatible g₁ m₂ :=
    Interp.compatible_resultCapability compat fresh₂ returns₁
  have freshΔ₂ : x ∉ (Context.erasureUnder «Σ» Γ₂).domain := fun h => fresh₂
    ((Interp.models_basicWorld_iff m₂ _).1 (Context.models_interpUnder_basicWorld h₂) |>.1 h)
  have ctxBody := Context.models_interpUnder_star_bind_closed
    (Capability.Compatible.symm compatg) closedτ freshΔ₂ h₂ named'
  have hframe := Interp.resultCapability_product compat support₁ fresh₂ returns₁ returnsP
  have hrefg := Interp.resultCapability_refines href
    (Finset.Subset.trans support₁ Finset.subset_union_left) freshM returnsP returnsM
  have framed : Capability.product m₂ g₁ (Capability.Compatible.symm compatg) ⊑ g := by
    rw [← Capability.product_comm compatg, ← hframe]
    exact hrefg
  have hbody := right x freshL g (Formula.models_kripke framed ctxBody)
  have freshΓ₂ : x ∉ Γ₂.erase.domain := by
    intro h
    apply freshΔ₂
    rw [Context.erasureUnder, BasicEnv.domain_merge]
    exact Finset.mem_union_right _ h
  have eraseBody : (Γ₂ ∗ (x ∷ τ₁) : Context).erase = Γ₂.erase.insert x τ₁.erase := by
    simp only [Context.erase]
    exact BasicEnv.merge_singleton_eq_insert freshΓ₂
  rw [eraseBody] at hbody
  have typedBody : Γ₂.erase.insert x τ₁.erase ⊢ₑ (e₂.openAt 0 (.free x)) ⋮ τ₂.erase := by
    simpa only [eraseBody] using wfbody.2.2
  have wfτBody : τ₂.WellFormed (Γ₂.erase.insert x τ₁.erase).domain := by
    simpa only [eraseBody] using wfbody.2.1
  let Δ := (Γ₁ ∗ Γ₂ : Context).erase
  have scopeΔ := (Interp.models_basicWorld_iff m Δ).1 world |>.1
  have support₂ : e₂.support ⊆ m.domain :=
    Finset.Subset.trans (Finset.Subset.trans Finset.subset_union_right wf.2.2.support_subset) scopeΔ
  have closedInputs : ∀ σ, σ ∈ m → ∀ y, y ∈ e₂.support →
      ∀ w, σ.lookup y = some w → w.locallyClosed := by
    intro σ hσ y hy w hw
    have hyΔ := wf.2.2.support_subset (Finset.mem_union_right _ hy)
    obtain ⟨T, hT⟩ := (BasicEnv.mem_domain_iff Δ y).1 hyΔ
    obtain ⟨u, hu, htyped⟩ := (Interp.models_basicWorld_iff m Δ).1 world |>.2 σ hσ y T hT
    have : u = w := Option.some.inj (hu.symm.trans hw)
    exact this ▸ htyped.locallyClosed
  have closedLet : ∀ σ, σ ∈ m →
      (Interp.instantiateTerm (.letE e₁ e₂) σ.toAssignment).locallyClosed := by
    intro σ hσ
    exact (Interp.instantiateTerm_typed wf.2.2
      ((Interp.models_basicWorld_iff m Δ).1 world |>.2 σ hσ)).locallyClosed
  have total := Interp.models_total_let_of_resultCapability returnsM freshM
    wf.2.2.locallyClosed support₂ closedInputs closedLet totalM
    (ContextType.models_interp_total hbody)
  apply ContextType.models_interp_of_resultsEquivOn wfτBody wf.2.1
    typedBody wf.2.2 world total ?_ ?_ hbody
  · intro y hy
    have hyx : y ≠ x := by
      intro h
      subst y
      exact freshM (scopeΔ (wf.2.1.freeAtoms_subset hy))
    have hyΓ₂ : y ∈ Γ₂.erase.domain := by
      have h := wfτBody.freeAtoms_subset hy
      simpa [BasicEnv.domain_insert, hyx] using h
    have hyΓ₁ : y ∉ Γ₁.erase.domain := by
      intro h
      exact Finset.disjoint_left.1 wf.1.2.2
        (Context.erase_domain_subset_domain Γ₁ h) (Context.erase_domain_subset_domain Γ₂ hyΓ₂)
    rw [BasicEnv.lookup_insert_of_ne _ _ hyx]
    exact (BasicEnv.lookup_merge_right _ _ hyΓ₁).symm
  · exact (Interp.resultsEquivOn_let_resultCapability returnsM freshM support₂
      closedInputs closedLet (Finset.Subset.trans wf.2.1.freeAtoms_subset scopeΔ)).symm

end SemTyp

end ContextTypes
