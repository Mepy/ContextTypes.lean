import ContextTypes.SemTyp.Core
import Mathlib.Tactic

set_option autoImplicit false

namespace ContextTypes

open scoped ContextTypes

namespace SemTyp

private theorem persist_body_freeAtoms (gas : Nat) (Δ : BasicEnv)
    (τ : ContextType) (v : Value)
    (wfτ : τ.WellFormed Δ.domain)
    (typed : BasicTermTyp Δ (.ret v) τ.erase) :
    let Δ' := Interp.relevantEnv Δ τ (.ret v)
    let P :=
      Interp.resultFirst Δ' (.persist τ) (.ret v) ⇒ᶜ
        □ ContextType.interpFuel gas 1 Δ' (τ.shiftFrom 0)
          (.ret (.bound 0))
    P.freeAtoms = τ.freeAtoms ∪ v.support := by
  let A := τ.freeAtoms ∪ v.support
  let Δ' := Interp.relevantEnv Δ τ (.ret v)
  let Q := ContextType.interpFuel gas 1 Δ' (τ.shiftFrom 0)
    (.ret (.bound 0))
  let P := Interp.resultFirst Δ' (.persist τ) (.ret v) ⇒ᶜ □ Q
  have hAΔ : A ⊆ Δ.domain :=
    Finset.union_subset wfτ.freeAtoms_subset typed.support_subset
  have hΔ' : Δ'.domain = A := by
    simp only [Δ', Interp.relevantEnv_domain, Interp.relevantAtoms,
      Term.support, A]
    exact Finset.inter_eq_right.2 hAΔ
  have hres :
      (Interp.resultFirst Δ' (.persist τ) (.ret v)).freeAtoms = A := by
    rw [Interp.freeAtoms_resultFirst]
    simp only [Interp.relevantEnv_persist, Term.support]
    have hidem : Interp.relevantEnv Δ' τ (.ret v) = Δ' := by
      simp [Δ']
    rw [hidem]
    rw [hΔ']
    exact Finset.union_eq_left.2 Finset.subset_union_right
  have hQ : Q.freeAtoms ⊆ A := by
    intro x hx
    have h := ContextType.freeAtoms_interpFuel_subset gas 1 Δ'
      (τ.shiftFrom 0) (.ret (.bound 0)) hx
    simp only [ContextType.freeAtoms_shiftFrom, Term.support,
      Value.support, Finset.union_empty] at h
    exact Finset.mem_union_left _ h
  apply Finset.Subset.antisymm
  · simp only [Formula.freeAtoms_impl, Formula.freeAtoms_persist]
    change
      (Interp.resultFirst Δ' (.persist τ) (.ret v)).freeAtoms ∪
        Q.freeAtoms ⊆ A
    rw [hres]
    exact Finset.union_subset (Finset.Subset.rfl) hQ
  · simp only [Formula.freeAtoms_impl, Formula.freeAtoms_persist]
    change A ⊆
      (Interp.resultFirst Δ' (.persist τ) (.ret v)).freeAtoms ∪
        Q.freeAtoms
    rw [hres]
    exact Finset.subset_union_left

private theorem persist_body_open_freeAtoms (gas : Nat) (Δ : BasicEnv)
    (τ : ContextType) (v : Value) (y : Atom)
    (wfτ : τ.WellFormed Δ.domain)
    (typed : BasicTermTyp Δ (.ret v) τ.erase)
    (fresh : y ∉ τ.freeAtoms ∪ v.support) :
    let Δ' := Interp.relevantEnv Δ τ (.ret v)
    let P :=
      Interp.resultFirst Δ' (.persist τ) (.ret v) ⇒ᶜ
        □ ContextType.interpFuel gas 1 Δ' (τ.shiftFrom 0)
          (.ret (.bound 0))
    (P.openAt 0 y).freeAtoms = (τ.freeAtoms ∪ v.support) ∪ {y} := by
  let A := τ.freeAtoms ∪ v.support
  let Δ' := Interp.relevantEnv Δ τ (.ret v)
  let X := Interp.relevantSupport Δ' (.persist τ) (.ret v)
  let Q := ContextType.interpFuel gas 1 Δ' (τ.shiftFrom 0)
    (.ret (.bound 0))
  let P := Interp.resultFirst Δ' (.persist τ) (.ret v) ⇒ᶜ □ Q
  have hAΔ : A ⊆ Δ.domain :=
    Finset.union_subset wfτ.freeAtoms_subset typed.support_subset
  have hΔ' : Δ'.domain = A := by
    simp only [Δ', Interp.relevantEnv_domain, Interp.relevantAtoms,
      Term.support, A]
    exact Finset.inter_eq_right.2 hAΔ
  have hXfree : LogicVar.freeAtomSet X = A := by
    simp only [X, Interp.freeAtomSet_relevantSupport]
    have hidem : Interp.relevantEnv Δ' (.persist τ) (.ret v) = Δ' := by
      simp [Δ']
    rw [hidem, hΔ']
  have hclosedV : v.locallyClosed := typed.locallyClosed
  have hclosedX : LogicVar.LocallyClosed X := by
    exact Interp.relevantSupport_locallyClosed Δ' (.persist τ) (.ret v)
      wfτ.locallyClosedAt hclosedV
  have hsupport : (.ret v : Term).logicSupport ⊆ X := by
    apply Interp.logicSupport_subset_relevantSupport
    intro x hx
    rw [hΔ']
    exact Finset.mem_union_right _ hx
  have hfreshX : LogicVar.free y ∉ X := by
    intro hy
    apply fresh
    have : y ∈ LogicVar.freeAtomSet X :=
      (LogicVar.mem_freeAtomSet_iff X y).2 hy
    rwa [hXfree] at this
  have hresOpen :
      (Interp.resultFirst Δ' (.persist τ) (.ret v)).openAt 0 y =
        Interp.resultAt X (.ret v) (.free y) := by
    exact Interp.resultFirst_openAt Δ' (.persist τ) (.ret v) y
      hclosedX hclosedV hsupport hfreshX
  have hresFree :
      ((Interp.resultFirst Δ' (.persist τ) (.ret v)).openAt 0 y).freeAtoms =
        A ∪ {y} := by
    rw [hresOpen, Interp.freeAtoms_resultAt, hXfree]
    simp only [Term.support]
    rw [Finset.union_eq_left.2 Finset.subset_union_right]
    simp [LogicVar.freeAtoms, A]
  have hQ : Q.freeAtoms ⊆ A := by
    intro x hx
    have h := ContextType.freeAtoms_interpFuel_subset gas 1 Δ'
      (τ.shiftFrom 0) (.ret (.bound 0)) hx
    simp only [ContextType.freeAtoms_shiftFrom, Term.support,
      Value.support, Finset.union_empty] at h
    exact Finset.mem_union_left _ h
  have hQopen : (Q.openAt 0 y).freeAtoms ⊆ A ∪ {y} := by
    intro x hx
    have hx' := Formula.freeAtoms_openAt_subset Q 0 y hx
    rcases Finset.mem_union.1 hx' with hx' | hx'
    · exact Finset.mem_union_right _ hx'
    · exact Finset.mem_union_left _ (hQ hx')
  apply Finset.Subset.antisymm
  · simp only [Formula.openAt, Formula.freeAtoms_impl,
      Formula.freeAtoms_persist]
    rw [hresFree]
    exact Finset.union_subset Finset.Subset.rfl hQopen
  · simp only [Formula.openAt, Formula.freeAtoms_impl,
      Formula.freeAtoms_persist]
    rw [hresFree]
    exact Finset.subset_union_left

private theorem persist_result_open_freeAtoms (Δ : BasicEnv)
    (τ : ContextType) (v : Value) (y : Atom)
    (wfτ : τ.WellFormed Δ.domain)
    (typed : BasicTermTyp Δ (.ret v) τ.erase)
    (fresh : y ∉ τ.freeAtoms ∪ v.support) :
    let Δ' := Interp.relevantEnv Δ τ (.ret v)
    ((Interp.resultFirst Δ' (.persist τ) (.ret v)).openAt 0 y).freeAtoms =
      (τ.freeAtoms ∪ v.support) ∪ {y} := by
  let A := τ.freeAtoms ∪ v.support
  let Δ' := Interp.relevantEnv Δ τ (.ret v)
  let X := Interp.relevantSupport Δ' (.persist τ) (.ret v)
  have hAΔ : A ⊆ Δ.domain :=
    Finset.union_subset wfτ.freeAtoms_subset typed.support_subset
  have hΔ' : Δ'.domain = A := by
    simp only [Δ', Interp.relevantEnv_domain, Interp.relevantAtoms,
      Term.support, A]
    exact Finset.inter_eq_right.2 hAΔ
  have hXfree : LogicVar.freeAtomSet X = A := by
    simp only [X, Interp.freeAtomSet_relevantSupport]
    have hidem : Interp.relevantEnv Δ' (.persist τ) (.ret v) = Δ' := by
      simp [Δ']
    rw [hidem, hΔ']
  have hclosedV : v.locallyClosed := typed.locallyClosed
  have hclosedX : LogicVar.LocallyClosed X :=
    Interp.relevantSupport_locallyClosed Δ' (.persist τ) (.ret v)
      wfτ.locallyClosedAt hclosedV
  have hsupport : (.ret v : Term).logicSupport ⊆ X := by
    apply Interp.logicSupport_subset_relevantSupport
    intro x hx
    rw [hΔ']
    exact Finset.mem_union_right _ hx
  have hfreshX : LogicVar.free y ∉ X := by
    intro hy
    apply fresh
    have : y ∈ LogicVar.freeAtomSet X :=
      (LogicVar.mem_freeAtomSet_iff X y).2 hy
    rwa [hXfree] at this
  change
    ((Interp.resultFirst Δ' (.persist τ) (.ret v)).openAt 0 y).freeAtoms =
      A ∪ {y}
  rw [Interp.resultFirst_openAt Δ' (.persist τ) (.ret v) y
    hclosedX hclosedV hsupport hfreshX,
    Interp.freeAtoms_resultAt, hXfree]
  simp [A, LogicVar.freeAtoms, Term.support, Finset.union_assoc]

/-- A persistent context semantically types persistent returned values. -/
theorem persist
    {Φ : PrimitiveContext} {«Σ» : BasicEnv} {Γ : Context}
    {v : Value} {τ : ContextType}
    (wf : SynTyp.WellFormed «Σ» Γ (.ret v) (.persist τ))
    (persistent : Formula.Persistent (Context.interpUnder «Σ» Γ))
    (typed : Φ ; «Σ» ; Γ ⊨ (.ret v) ⋮ τ) :
    Φ ; «Σ» ; Γ ⊨ (.ret v) ⋮ (.persist τ) := by
  intro m hΓ
  let Δ := Γ.erase
  let A := τ.freeAtoms ∪ v.support
  let Δ' := Interp.relevantEnv Δ τ (.ret v)
  let X := Interp.relevantSupport Δ' (.persist τ) (.ret v)
  let Q := ContextType.interpFuel τ.measure 1 Δ' (τ.shiftFrom 0)
    (.ret (.bound 0))
  let P := Interp.resultFirst Δ' (.persist τ) (.ret v) ⇒ᶜ □ Q
  have wfτ : τ.WellFormed Δ.domain := wf.2.1
  have htyped : BasicTermTyp Δ (.ret v) τ.erase := wf.2.2
  have hAΓ : A ⊆ (Context.interpUnder «Σ» Γ).freeAtoms := by
    simpa [A, ContextType.freeAtoms, Term.support] using
      observed_subset_context wf
  obtain ⟨σ, hσdom, hsingle⟩ :=
    persistent.singleton_restrict hΓ hAΓ
  have hτ := typed m hΓ
  rw [ContextType.interp_persist]
  apply Formula.models_and_intro
  · simpa [Δ, Δ', Interp.relevantEnv_persist] using
      ContextType.models_interpFuel_guard hτ
  · have hPfree : P.freeAtoms = A := by
      simpa [P, Q, A, Δ'] using
        persist_body_freeAtoms τ.measure Δ τ v wfτ htyped
    apply Formula.models_all_intro
    · rw [hPfree]
      exact Finset.Subset.trans hAΓ (Formula.models_scope hΓ)
    · refine ⟨m.domain ∪ A, ?_⟩
      intro y hy F hFin hFout n hExt
      have hyM : y ∉ m.domain := fun hym => hy (Finset.mem_union_left _ hym)
      have hyA : y ∉ A := fun hya => hy (Finset.mem_union_right _ hya)
      have hbase : m.restrict P.freeAtoms = Capability.singleton σ := by
        rw [hPfree]
        exact hsingle
      have hExt' : F.Extends (Capability.singleton σ) n := by
        rwa [hbase] at hExt
      have hn : n.domain = A ∪ {y} := by
        rw [hExt'.domain_eq, Capability.singleton_domain, hσdom, hFout]
      have hopen : (P.openAt 0 y).freeAtoms = A ∪ {y} := by
        simpa [P, Q, A, Δ'] using
          persist_body_open_freeAtoms τ.measure Δ τ v y wfτ htyped hyA
      apply Formula.models_impl_intro
      · change (P.openAt 0 y).freeAtoms ⊆ n.domain
        rw [hopen, hn]
      · intro k href hres
        have hnk : n ⊑ k := by
          change n.restrict (P.openAt 0 y).freeAtoms ⊑ k at href
          rw [hopen, ← hn, Capability.restrict_domain_self] at href
          exact href
        let R := (Interp.resultFirst Δ' (.persist τ) (.ret v)).openAt 0 y
        have hRfree : R.freeAtoms = A ∪ {y} := by
          simpa [R, A, Δ'] using
            persist_result_open_freeAtoms Δ τ v y wfτ htyped hyA
        have hresN : n ⊨ R := by
          apply (Formula.models_projection n.domain ?_ ?_).2 hres
          · rw [hRfree, hn]
          · calc
              n.restrict n.domain = n := Capability.restrict_domain_self n
              _ = k.restrict n.domain := hnk
        have hΔ' : Δ'.domain = A := by
          simp only [Δ', Interp.relevantEnv_domain, Interp.relevantAtoms,
            Term.support, A]
          exact Finset.inter_eq_right.2
            (Finset.union_subset wfτ.freeAtoms_subset htyped.support_subset)
        have hXfree : LogicVar.freeAtomSet X = A := by
          simp only [X, Interp.freeAtomSet_relevantSupport]
          have hidem : Interp.relevantEnv Δ' (.persist τ) (.ret v) = Δ' := by
            simp [Δ']
          rw [hidem, hΔ']
        have hclosedV : v.locallyClosed := htyped.locallyClosed
        have hclosedX : LogicVar.LocallyClosed X :=
          Interp.relevantSupport_locallyClosed Δ' (.persist τ) (.ret v)
            wfτ.locallyClosedAt hclosedV
        have hsupp : (.ret v : Term).logicSupport ⊆ X := by
          apply Interp.logicSupport_subset_relevantSupport
          intro x hx
          rw [hΔ']
          exact Finset.mem_union_right _ hx
        have hfreshX : LogicVar.free y ∉ X := by
          intro hxy
          apply hyA
          have : y ∈ LogicVar.freeAtomSet X :=
            (LogicVar.mem_freeAtomSet_iff X y).2 hxy
          rwa [hXfree] at this
        obtain ⟨ρ, hρ, hnsingle⟩ :=
          Interp.models_resultFirst_ret_openAt_singleton hExt' hFout
            (by rw [hXfree, hσdom]) hclosedX hclosedV hsupp hfreshX hresN
        have hsource : n ⊨ ContextType.interp Δ' τ (.ret v) := by
          have hmA : m.restrict A ⊨ ContextType.interp Δ τ (.ret v) :=
            (ContextType.models_interp_restrict
              (m := m) (Δ := Δ) (τ := τ) (e := .ret v)
              (X := A) (by simp [A, Term.support])).1 hτ
          have hσ : Capability.singleton σ ⊨
              ContextType.interp Δ τ (.ret v) := by
            rwa [hsingle] at hmA
          have hnΔ : n ⊨ ContextType.interp Δ τ (.ret v) :=
            Formula.models_kripke hExt'.refines hσ
          have hagree : BasicEnv.AgreeOn A Δ Δ' := by
            intro x hx
            change Δ.lookup x =
              (Δ.restrict (τ.freeAtoms ∪ (.ret v : Term).support)).lookup x
            rw [BasicEnv.lookup_restrict, if_pos (by simpa [A] using hx)]
          rw [ContextType.interp_eq_of_agreeOn hagree] at hnΔ
          exact hnΔ
        have hyΔ' : y ∉ Δ'.domain := by rw [hΔ']; exact hyA
        have hresAt : n ⊨ Interp.resultAt X (.ret v) (.free y) := by
          rwa [← Interp.resultFirst_openAt Δ' (.persist τ) (.ret v) y
            hclosedX hclosedV hsupp hfreshX]
        have hinner : n ⊨ Q.openAt 0 y := by
          exact ContextType.models_interpFuel_ret_alias_singleton hclosedX
            htyped.locallyClosed hsupp hfreshX hyΔ'
            (wfτ.regularize (by rw [hΔ']; exact Finset.subset_union_left))
            (by rw [hΔ']; exact Finset.subset_union_right)
            hnsingle hresAt hsource
        have hpersist : n ⊨ (□ (Q.openAt 0 y)) := by
          apply (Formula.models_persist_iff n (Q.openAt 0 y)).2
          let θ := ρ.restrict (Q.openAt 0 y).freeAtoms
          refine ⟨θ, ?_, ?_, ?_⟩
          · rw [Store.domain_restrict, ← Capability.singleton_domain ρ,
              ← hnsingle, Finset.inter_eq_right.2 (Formula.models_scope hinner)]
          · rw [hnsingle, Capability.restrict_singleton]
          · have := (Formula.models_restrict_iff n (Q.openAt 0 y)).1 hinner
            rw [hnsingle] at this
            simpa [θ] using this
        simpa [Q, Formula.openAt] using Formula.models_kripke hnk hpersist

end SemTyp

end ContextTypes
