import ContextTypes.Fundamental

set_option autoImplicit false

namespace ContextTypes.Soundness

open scoped ContextTypes

/-- Closed syntactically typed programs have a model containing exactly all
their results, with the result named by any chosen atom. -/
theorem denotational {Φ : PrimitiveContext} {e : Term} {τ : ContextType}
    (wfΦ : Φ.WellFormed) (typed : Φ ; ∅ ; Context.empty ⊢ e ⋮ τ) (x : Atom) :
    ∃ m : Capability,
      (∀ σ, σ ∈ m ↔ ∃ v, e.reaches v ∧ σ = Store.singleton x v) ∧
      m ⊨ (⟦τ⟧[BasicEnv.singleton x τ.erase] (.ret (.free x))) := by
  have wf := typed.wellFormed
  have wfτ : τ.WellFormed ∅ := wf.2.1
  have typedE : (∅ : BasicEnv) ⊢ₑ e ⋮ τ.erase := wf.2.2
  have supp : e.support ⊆ ∅ := typedE.support_subset
  have suppτ : τ.freeAtoms ⊆ ∅ := wfτ.freeAtoms_subset
  have world (m : Capability) : m ⊨ Interp.basicWorld ∅ := Interp.models_basicWorld_empty m
  have ctx : Capability.unit ⊨ Context.interpUnder ∅ Context.empty := by
    simpa only [Context.interpUnder, BasicEnv.restrict_empty] using
      Formula.models_and_intro (world Capability.unit) (Formula.models_top Capability.unit)
  have source : Capability.unit ⊨ (⟦τ⟧[∅] e) := Fundamental.sound wfΦ typed _ ctx
  have total := ContextType.models_interp_total source
  have returns : ∀ σ, σ ∈ Capability.unit →
      ∃ v, (Interp.instantiateTerm e σ.toAssignment).reaches v :=
    fun σ hσ => (Interp.models_total_term typedE.locallyClosed total hσ).reaches_result
  let m := Interp.resultCapability Capability.unit ∅ e x (by simp) returns
  have href : Capability.unit ⊑ m := by
    simp [Capability.Refines, Capability.unit_domain]
  have graph := Interp.models_resultCapability Capability.unit ∅ e x (by simp) returns
    typedE.locallyClosed supp (by simp)
  refine ⟨m, ?_, ?_⟩
  · intro σ
    change (∃ ρ, ρ ∈ Capability.unit ∧ ∃ v,
      (Interp.instantiateTerm e ρ.toAssignment).reaches v ∧
        σ = (ρ.restrict ∅).merge (Store.singleton x v)) ↔ _
    simp only [Capability.mem_unit_iff, exists_eq_left, Store.empty_toAssignment,
      Interp.instantiateTerm_empty, Store.restrict_empty, Store.empty_merge]
  · have h := ContextType.models_interp_named_result wfτ typedE (world m)
      (X := ∅) (by intro k hk; simp at hk)
      (by
        intro ξ hξ
        cases ξ with
        | bound k => exact (Interp.termLogicSupport_locallyClosed e typedE.locallyClosed k hξ).elim
        | free y =>
          have hy := (LogicVar.mem_freeAtomSet_iff _ _).2 hξ
          rw [Interp.freeAtomSet_term_logicSupport e] at hy
          exact (Finset.notMem_empty y (supp hy)).elim)
      (by
        intro ξ hξ
        obtain ⟨y, hy, rfl⟩ := Finset.mem_image.1 hξ
        exact (Finset.notMem_empty y (suppτ hy)).elim)
      (by simp) (by simp) (by simpa using graph)
      (Formula.models_kripke href source)
    simpa only [BasicEnv.insert_empty] using h

end ContextTypes.Soundness
