import ContextTypes.SemTyp.Core
import Mathlib.Tactic

set_option autoImplicit false

namespace ContextTypes
open scoped ContextTypes

/-- Ordinary application names the function result, applies it to the existing
argument binding, and projects away the temporary result alias. -/
theorem SemTyp.app
    {Φ : PrimitiveContext} {«Σ» : BasicEnv} {Γ : Context}
    {τₓ τ : ContextType} {v : Value} {x : Atom}
    (wf : SynTyp.WellFormed «Σ» Γ (.app v (.free x)) (τ.openAt 0 x))
    (wf₁ : SynTyp.WellFormed «Σ» Γ (.ret v) (.arrow τₓ τ))
    (wf₂ : SynTyp.WellFormed «Σ» Γ (.ret (.free x)) τₓ)
    (fresh : x ∉ v.support ∪ τₓ.freeAtoms ∪ τ.freeAtoms)
    (fn : Φ ; «Σ» ; Γ ⊨ (.ret v) ⋮ (.arrow τₓ τ))
    (arg : Φ ; «Σ» ; Γ ⊨ (.ret (.free x)) ⋮ τₓ) :
    Φ ; «Σ» ; Γ ⊨ (.app v (.free x)) ⋮ (τ.openAt 0 x) := by
  intro m hΓ
  let Δ := Γ.erase
  let Δ₀ := Δ.erase x
  let gas := max τₓ.measure τ.measure
  let Δr := Interp.relevantEnv Δ₀ (.arrow τₓ τ) (.ret v)
  let A := Interp.resultFirst Δ₀ (.arrow τₓ τ) (.ret v)
  let B := ContextType.interpFuel gas 2 Δ₀ ((τₓ.shiftFrom 0).shiftFrom 0) (.ret (.bound 0))
  let C := ContextType.interpFuel gas 2 Δ₀ (τ.shiftFrom 1) (.app (.bound 1) (.bound 0))
  have fresh' : (x ∉ v.support ∧ x ∉ τₓ.freeAtoms) ∧ x ∉ τ.freeAtoms := by
    simpa only [Finset.mem_union, not_or] using fresh
  have world := Context.models_interpUnder_erase_basicWorld wf.1 hΓ
  have scopeΔ : Δ.domain ⊆ m.domain := (Interp.models_basicWorld_iff m Δ).1 world |>.1
  have fnM := fn m hΓ
  have argM := arg m hΓ
  have lookupX : Δ.lookup x = some τₓ.erase := by
    cases wf₂.2.2 with
    | ret h => cases h with | free h => exact h
  have presentX : x ∈ m.domain := scopeΔ ((BasicEnv.mem_domain_iff Δ x).2 ⟨_, lookupX⟩)
  have envX : Δ₀.insert x τₓ.erase = Δ := BasicEnv.insert_erase_of_lookup lookupX
  have freshX : x ∉ Δ₀.domain := by simp [Δ₀, BasicEnv.domain_erase]
  have typed₀ : Δ₀ ⊢ₑ (.ret v) ⋮ (.arrow τₓ τ : ContextType).erase := by
    apply wf₁.2.2.of_agreeOn
    intro y hy
    apply (BasicEnv.lookup_erase_of_ne Δ _).symm
    intro h
    subst y
    exact fresh'.1.1 hy
  have wf₀ : (.arrow τₓ τ : ContextType).WellFormed Δ₀.domain := by
    apply wf₁.2.1.regularize
    intro y hy
    rw [BasicEnv.domain_erase, Finset.mem_erase]
    refine ⟨?_, wf₁.2.1.freeAtoms_subset hy⟩
    intro h
    subst y
    have hy' : x ∈ τₓ.freeAtoms ∨ x ∈ τ.freeAtoms := by
      simpa only [ContextType.freeAtoms, Finset.mem_union] using hy
    exact hy'.elim fresh'.1.2 fresh'.2
  have embed₀ : Δ₀.Subset Δ := by
    intro y T hy
    by_cases h : y = x
    · subst y; simp [Δ₀] at hy
    · rwa [BasicEnv.lookup_erase_of_ne Δ h] at hy
  have world₀ := Interp.models_basicWorld_of_subset embed₀ world
  have same₀ : BasicEnv.AgreeOn ((.arrow τₓ τ : ContextType).freeAtoms ∪ (.ret v : Term).support) Δ₀ Δ := by
    intro y hy
    rw [BasicEnv.lookup_erase_of_ne Δ]
    intro h
    subst y
    have hy' : (x ∈ τₓ.freeAtoms ∨ x ∈ τ.freeAtoms) ∨ x ∈ v.support := by
      simpa only [ContextType.freeAtoms, Term.support, Finset.mem_union] using hy
    exact hy'.elim (fun h => h.elim fresh'.1.2 fresh'.2) fresh'.1.1
  have fn₀ : m ⊨ ContextType.interp Δ₀ (.arrow τₓ τ) (.ret v) := by
    rw [ContextType.interp_eq_of_agreeOn same₀]
    exact fnM
  have agree (υ : ContextType) (e : Term)
      (hs : υ.freeAtoms ∪ e.support ⊆ (.arrow τₓ τ : ContextType).freeAtoms ∪ (.ret v : Term).support) :
      BasicEnv.AgreeOn (υ.freeAtoms ∪ e.support) Δr Δ₀ := by
    intro y hy
    simp only [Δr, Interp.relevantEnv, BasicEnv.lookup_restrict, Interp.relevantAtoms, if_pos (hs hy)]
  have envB : ContextType.interpFuel gas 2 Δr ((τₓ.shiftFrom 0).shiftFrom 0) (.ret (.bound 0)) = B := by
    apply ContextType.interpFuel_eq_of_agreeOn
    apply agree
    simp [ContextType.freeAtoms, Term.support, Value.support]
  have envC : ContextType.interpFuel gas 2 Δr (τ.shiftFrom 1) (.app (.bound 1) (.bound 0)) = C := by
    apply ContextType.interpFuel_eq_of_agreeOn
    apply agree
    simp only [ContextType.freeAtoms_shiftFrom, Term.support, Value.support, Finset.union_empty, ContextType.freeAtoms]
    exact Finset.Subset.trans Finset.subset_union_right Finset.subset_union_left
  have universal : m ⊨ Formula.all (A ⇒ᶜ Formula.all (B ⇒ᶜ C)) := by
    simp only [ContextType.interp, ContextType.measure, Nat.add_comm 1] at fn₀
    change m ⊨ ContextType.interpFuel (gas + 1) 0 Δ₀ (.arrow τₓ τ) (.ret v) at fn₀
    simp only [ContextType.interpFuel, Nat.zero_add, Interp.resultFirst_relevantEnv] at fn₀
    rw [envB, envC] at fn₀
    exact Formula.models_and_elim_right fn₀
  obtain ⟨z, hz⟩ := Finset.exists_nat_subset_range m.domain
  have freshZ : z ∉ m.domain := by
    intro h
    have := hz h
    simp at this
  have freshZΔ : z ∉ Δ.domain := fun h => freshZ (scopeΔ h)
  have freshZ₀ : z ∉ Δ₀.domain := by
    intro h
    apply freshZΔ
    rw [BasicEnv.domain_erase] at h
    exact (Finset.mem_erase.1 h).2
  have apart : x ≠ z := fun h => freshZ (h ▸ presentX)
  have total := ContextType.models_interp_total fnM
  have returns : ∀ σ, σ ∈ m → ∃ u, (Interp.instantiateTerm (.ret v) σ.toAssignment).reaches u :=
    fun σ hσ => (Interp.models_total_term wf₁.2.2.locallyClosed total hσ).reaches_result
  let g := Interp.resultCapability m m.domain (.ret v) z (Finset.Subset.refl _) returns
  have base : g.restrict m.domain = m := by
    rw [Interp.resultCapability_restrict, Capability.restrict_domain_self]
  have href : m ⊑ g := base.symm
  have graphFull := Interp.models_resultCapability m m.domain (.ret v) z
    (Finset.Subset.refl _) returns wf₁.2.2.locallyClosed
    (Finset.Subset.trans wf₁.2.2.support_subset scopeΔ) freshZ
  let X := Interp.relevantSupport Δ₀ (.arrow τₓ τ) (.ret v)
  have closedX : LogicVar.LocallyClosed X :=
    Interp.relevantSupport_locallyClosed _ _ _ wf₀.locallyClosedAt typed₀.locallyClosed
  have logicX : (.ret v : Term).logicSupport ⊆ X :=
    Interp.logicSupport_subset_relevantSupport _ _ _ typed₀.support_subset
  have scopeX : X ⊆ m.domain.image LogicVar.free := by
    rw [LogicVar.eq_image_free_of_locallyClosed closedX, Interp.freeAtomSet_relevantSupport]
    apply Finset.image_subset_image
    intro y hy
    apply scopeΔ
    have h := Finset.mem_inter.1 (by simpa only [Interp.relevantEnv_domain] using hy)
    rw [BasicEnv.domain_erase] at h
    exact (Finset.mem_erase.1 h.1).2
  have freshXZ : LogicVar.free z ∉ X := fun h => freshZ (by simpa using scopeX h)
  have graph : g ⊨ A.openAt 0 z := by
    rw [Interp.resultFirst_openAt _ _ _ z closedX typed₀.locallyClosed logicX freshXZ]
    exact Formula.models_kripke (Capability.restrict_refines g _)
      (Interp.models_resultAt_restrict_support (by intro k hk; simp at hk) scopeX logicX
        (by simpa using freshZ) graphFull)
  have outer := Formula.models_all_openAt_of_refines universal freshZ href (by rfl)
  have inner := Formula.models_impl_elim outer graph
  change g ⊨ Formula.all ((B ⇒ᶜ C).openAt 1 z) at inner
  have freshInner : x ∉ ((B ⇒ᶜ C).openAt 1 z).freeAtoms := by
    intro hx
    rcases Finset.mem_union.1 (Formula.freeAtoms_openAt_subset _ _ _ hx) with hx | hx
    · exact apart (Finset.mem_singleton.1 hx)
    · rw [Formula.freeAtoms_impl] at hx
      rcases Finset.mem_union.1 hx with hx | hx
      · have h := ContextType.freeAtoms_interpFuel_subset gas 2 Δ₀ _ _ hx
        exact fresh'.1.2 (by simpa [Term.support, Value.support] using h)
      · have h := ContextType.freeAtoms_interpFuel_subset gas 2 Δ₀ _ _ hx
        exact fresh'.2 (by simpa [Term.support, Value.support] using h)
  have opened := Formula.models_all_elim_named inner freshInner (Capability.refines_domain_subset href presentX)
  have argG : g ⊨ ContextType.interp (Δ₀.insert x τₓ.erase) τₓ (.ret (.free x)) := by
    rw [envX]
    exact Formula.models_kripke href argM
  have argBound := (ContextType.models_interp_arg_bound_openAt_iff
    (gas := gas) (z := z)
    (Nat.le_max_left τₓ.measure τ.measure) wf₀.1 freshX freshZ₀).2 argG
  have result := Formula.models_impl_elim opened argBound
  have worldZ := Interp.models_basicWorld_resultFirst_openAt wf₀ typed₀
    (Formula.models_kripke href world₀) freshZ₀ graph
  let Δ' := (Δ₀.insert z (.arrow τₓ.erase τ.erase)).insert x τₓ.erase
  have fullEq : Δ' = Δ.insert z (.arrow τₓ.erase τ.erase) := by
    dsimp only [Δ']
    rw [BasicEnv.insert_comm Δ₀ _ _ apart.symm, envX]
  have worldG := Formula.models_kripke href world
  have worldFull : g ⊨ Interp.basicWorld Δ' := by
    apply Interp.models_basicWorld_insert worldZ (Capability.refines_domain_subset href presentX)
    exact fun σ hσ => ((Interp.models_basicWorld_iff g Δ).1 worldG).2 σ hσ x τₓ.erase lookupX
  have namedFuel := (ContextType.models_interpFuel_app_bound_openAt_iff
    (gas := gas)
    (Nat.le_max_right τₓ.measure τ.measure) wf₀.2 freshX freshZ₀ apart worldFull).1 result
  have named : g ⊨ ContextType.interp Δ' (τ.openAt 0 x) (.app (.free z) (.free x)) := by
    rw [ContextType.interp]
    rw [← ContextType.interpFuel_eq_of_measure_le gas (τ.openAt 0 x).measure 0 Δ' _ _
      (by simpa only [ContextType.measure_openAt] using Nat.le_max_right τₓ.measure τ.measure) (Nat.le_refl _)]
    exact namedFuel
  have embed : Δ.Subset Δ' := by
    rw [fullEq]
    exact BasicEnv.subset_insert_of_fresh Δ z _ freshZΔ
  have typedActual : Δ' ⊢ₑ (.app v (.free x)) ⋮ (τ.openAt 0 x).erase := wf.2.2.weaken embed
  have typedNamed : Δ' ⊢ₑ (.app (.free z) (.free x)) ⋮ (τ.openAt 0 x).erase := by
    rw [ContextType.erase_openAt]
    exact BasicTermTyp.app
      (BasicValTyp.free (by rw [BasicEnv.lookup_insert_of_ne _ _ apart.symm, BasicEnv.lookup_insert]))
      (BasicValTyp.free (BasicEnv.lookup_insert _ _ _))
  have formed : (τ.openAt 0 x).WellFormed Δ'.domain := wf.2.1.mono (by
    rw [fullEq, BasicEnv.domain_insert]
    exact Finset.subset_union_right)
  have actual := (ContextType.models_interp_of_instantiate_eq_iff formed typedActual typedNamed worldFull
    (by
      intro σ hσ
      obtain ⟨u, hu, heval⟩ := Interp.models_resultAt_lookup
        (by intro k hk; simp at hk)
        (by
          rw [LogicVar.eq_image_free_of_locallyClosed (Interp.termLogicSupport_locallyClosed _ wf₁.2.2.locallyClosed),
            Interp.freeAtomSet_term_logicSupport]
          exact Finset.image_subset_image (Finset.Subset.trans wf₁.2.2.support_subset scopeΔ))
        (by simpa using freshZ) graphFull σ hσ
      have hv : u = Interp.instantiateValueAt v 0 σ.toAssignment := Term.ret.inj heval.ret_eq
      simp only [Interp.instantiateTerm, Interp.instantiateTermAt, Interp.instantiateValueAt,
        Store.toAssignment_lookup_free, hu, Option.getD_some]
      rw [hv])).2 named
  have sameEnv : BasicEnv.AgreeOn ((τ.openAt 0 x).freeAtoms ∪ (.app v (.free x) : Term).support) Δ' Δ := by
    intro y hy
    rw [fullEq, BasicEnv.lookup_insert_of_ne _ _]
    intro h
    subst y
    exact freshZΔ (Finset.union_subset wf.2.1.freeAtoms_subset wf.2.2.support_subset hy)
  rw [ContextType.interp_eq_of_agreeOn sameEnv] at actual
  apply (Formula.models_projection (m := m) (n := g) m.domain
    (Finset.Subset.trans (ContextType.freeAtoms_interp_subset _ _ _) (SemTyp.observed_subset wf hΓ))
    (by rw [Capability.restrict_domain_self, base])).2
  exact actual
/-- Separating application combines the singleton argument capability with
the function's result graph, then removes the fresh result alias. -/
theorem SemTyp.appSep
    {Φ : PrimitiveContext} {«Σ» : BasicEnv} {Γ₁ Γ₂ : Context}
    {τₓ τ : ContextType} {v : Value} {x : Atom}
    (wf : SynTyp.WellFormed «Σ» (Γ₁ ∗ Γ₂) (.app v (.free x)) (τ.openAt 0 x))
    (wf₁ : SynTyp.WellFormed «Σ» Γ₁ (.ret v) (.wand τₓ τ))
    (wf₂ : SynTyp.WellFormed «Σ» Γ₂ (.ret (.free x)) τₓ)
    (fresh : x ∉ v.support ∪ τₓ.freeAtoms ∪ τ.freeAtoms)
    (fn : Φ ; «Σ» ; Γ₁ ⊨ (.ret v) ⋮ (.wand τₓ τ))
    (arg : Φ ; «Σ» ; Γ₂ ⊨ (.ret (.free x)) ⋮ τₓ) :
    Φ ; «Σ» ; (Γ₁ ∗ Γ₂) ⊨ (.app v (.free x)) ⋮ (τ.openAt 0 x) := by
  intro m hΓ
  obtain ⟨m₁, m₂, compat, href, h₁, h₂⟩ := Context.models_interpUnder_star_elim hΓ
  let Δ₁ := Γ₁.erase
  let Δ₂ := Γ₂.erase
  let Δ := (Γ₁ ∗ Γ₂ : Context).erase
  let Δ₀ := Δ₁.erase x
  let a := m₁.restrict (m₁.domain.erase x)
  let n := m₂.restrict {x}
  let gas := max τₓ.measure τ.measure
  let Δr := Interp.relevantEnv Δ₀ (.wand τₓ τ) (.ret v)
  let A := Interp.resultFirst Δ₀ (.wand τₓ τ) (.ret v)
  let B := ContextType.interpFuel gas 2 Δ₀ ((τₓ.shiftFrom 0).shiftFrom 0) (.ret (.bound 0))
  let C := ContextType.interpFuel gas 2 Δ₀ (τ.shiftFrom 1) (.app (.bound 1) (.bound 0))
  have fresh' : (x ∉ v.support ∧ x ∉ τₓ.freeAtoms) ∧ x ∉ τ.freeAtoms := by
    simpa only [Finset.mem_union, not_or] using fresh
  have closedτ : τₓ.freeAtoms = ∅ := Finset.eq_empty_iff_forall_notMem.2
    (fun y hy => Finset.notMem_empty y (wf₁.2.1.1.freeAtoms_subset hy))
  have wfₓ : τₓ.WellFormed Δ₀.domain := wf₁.2.1.1.mono (Finset.empty_subset _)
  have world₁ := Context.models_interpUnder_erase_basicWorld wf₁.1 h₁
  have scope₁ : Δ₁.domain ⊆ m₁.domain := (Interp.models_basicWorld_iff m₁ Δ₁).1 world₁ |>.1
  have world₂ := Context.models_interpUnder_erase_basicWorld wf₂.1 h₂
  have scope₂ : Δ₂.domain ⊆ m₂.domain := (Interp.models_basicWorld_iff m₂ Δ₂).1 world₂ |>.1
  have lookupX : Δ₂.lookup x = some τₓ.erase := by
    cases wf₂.2.2 with
    | ret h => cases h with | free h => exact h
  have presentX : x ∈ m₂.domain := scope₂ ((BasicEnv.mem_domain_iff Δ₂ x).2 ⟨_, lookupX⟩)
  have ndom : n.domain = {x} := by simp [n, Capability.restrict_domain, presentX]
  have adom : a.domain = m₁.domain.erase x := by
    rw [Capability.restrict_domain, Finset.inter_eq_right.2 (Finset.erase_subset _ _)]
  have freshXA : x ∉ a.domain := by simp [adom]
  have freshX : x ∉ Δ₀.domain := by simp [Δ₀]
  have scope₀ : Δ₀.domain ⊆ a.domain := by
    rw [adom, BasicEnv.domain_erase]
    exact Finset.erase_subset_erase x scope₁
  have typed₀ : Δ₀ ⊢ₑ (.ret v) ⋮ (.wand τₓ τ : ContextType).erase := by
    apply wf₁.2.2.of_agreeOn
    intro y hy
    apply (BasicEnv.lookup_erase_of_ne Δ₁ _).symm
    intro h
    subst y
    exact fresh'.1.1 hy
  have wf₀ : (.wand τₓ τ : ContextType).WellFormed Δ₀.domain := by
    apply wf₁.2.1.regularize
    intro y hy
    rw [BasicEnv.domain_erase, Finset.mem_erase]
    refine ⟨?_, wf₁.2.1.freeAtoms_subset hy⟩
    intro h
    subst y
    have hy' : x ∈ τₓ.freeAtoms ∨ x ∈ τ.freeAtoms := by
      simpa only [ContextType.freeAtoms, Finset.mem_union] using hy
    exact hy'.elim fresh'.1.2 fresh'.2
  have fn₀ : a ⊨ ContextType.interp Δ₀ (.wand τₓ τ) (.ret v) := by
    rw [ContextType.interp_eq_of_agreeOn (Δ₂ := Δ₁) (by
      intro y hy
      rw [BasicEnv.lookup_erase_of_ne Δ₁]
      intro h
      subst y
      have hy' : (x ∈ τₓ.freeAtoms ∨ x ∈ τ.freeAtoms) ∨ x ∈ v.support := by
        simpa only [ContextType.freeAtoms, Term.support, Finset.mem_union] using hy
      exact hy'.elim (fun h => h.elim fresh'.1.2 fresh'.2) fresh'.1.1)]
    apply (Formula.models_restrict_superset m₁ _ ?_).1 (fn m₁ h₁)
    apply Finset.Subset.trans (ContextType.freeAtoms_interp_subset _ _ _)
    intro y hy
    rw [Finset.mem_erase]
    refine ⟨?_, scope₁ (Finset.union_subset wf₁.2.1.freeAtoms_subset wf₁.2.2.support_subset hy)⟩
    intro h
    subst y
    have hy' : (x ∈ τₓ.freeAtoms ∨ x ∈ τ.freeAtoms) ∨ x ∈ v.support := by
      simpa only [ContextType.freeAtoms, Term.support, Finset.mem_union] using hy
    exact hy'.elim (fun h => h.elim fresh'.1.2 fresh'.2) fresh'.1.1
  have argN : n ⊨ ContextType.interp (Δ₀.insert x τₓ.erase) τₓ (.ret (.free x)) := by
    rw [ContextType.interp_eq_of_agreeOn (Δ₂ := Δ₂) (by
      intro y hy
      have hxy : y = x := by simpa [closedτ, Term.support, Value.support] using hy
      subst y
      simp [lookupX])]
    apply (Formula.models_restrict_superset m₂ _ ?_).1 (arg m₂ h₂)
    simpa [closedτ, Term.support, Value.support] using
      ContextType.freeAtoms_interp_subset Δ₂ τₓ (.ret (.free x))
  have agree (υ : ContextType) (e : Term)
      (hs : υ.freeAtoms ∪ e.support ⊆ (.wand τₓ τ : ContextType).freeAtoms ∪ (.ret v : Term).support) :
      BasicEnv.AgreeOn (υ.freeAtoms ∪ e.support) Δr Δ₀ := by
    intro y hy
    simp only [Δr, Interp.relevantEnv, BasicEnv.lookup_restrict, Interp.relevantAtoms, if_pos (hs hy)]
  have envB : ContextType.interpFuel gas 2 Δr ((τₓ.shiftFrom 0).shiftFrom 0) (.ret (.bound 0)) = B := by
    apply ContextType.interpFuel_eq_of_agreeOn
    apply agree
    simp [ContextType.freeAtoms, Term.support, Value.support]
  have envC : ContextType.interpFuel gas 2 Δr (τ.shiftFrom 1) (.app (.bound 1) (.bound 0)) = C := by
    apply ContextType.interpFuel_eq_of_agreeOn
    apply agree
    simp only [ContextType.freeAtoms_shiftFrom, Term.support, Value.support, Finset.union_empty, ContextType.freeAtoms]
    exact Finset.Subset.trans Finset.subset_union_right Finset.subset_union_left
  have universal : a ⊨ Formula.all (A ⇒ᶜ (B -∗[1] C)) := by
    simp only [ContextType.interp, ContextType.measure, Nat.add_comm 1] at fn₀
    change a ⊨ ContextType.interpFuel (gas + 1) 0 Δ₀ (.wand τₓ τ) (.ret v) at fn₀
    simp only [ContextType.interpFuel, Nat.zero_add, Interp.resultFirst_relevantEnv] at fn₀
    rw [envB, envC] at fn₀
    exact Formula.models_and_elim_right fn₀
  have href₁ : m₁ ⊑ m := Capability.refines_trans (Capability.product_refines_left compat) href
  have href₂ : m₂ ⊑ m := Capability.refines_trans (Capability.product_refines_right compat) href
  have hrefA : a ⊑ m := Capability.refines_trans (Capability.restrict_refines m₁ _) href₁
  obtain ⟨z, hz⟩ := Finset.exists_nat_subset_range m.domain
  have freshZ : z ∉ m.domain := by
    intro h
    have := hz h
    simp at this
  have freshZA : z ∉ a.domain := fun h => freshZ (Capability.refines_domain_subset hrefA h)
  have freshZN : z ∉ n.domain := fun h => freshZ
    (Capability.refines_domain_subset href₂ (Capability.refines_domain_subset (Capability.restrict_refines m₂ _) h))
  have freshZ₀ : z ∉ Δ₀.domain := fun h => freshZA (scope₀ h)
  have apart : x ≠ z := fun h => freshZN (h ▸ (by rw [ndom]; simp))
  have total := ContextType.models_interp_total fn₀
  have returns : ∀ σ, σ ∈ a → ∃ u, (Interp.instantiateTerm (.ret v) σ.toAssignment).reaches u :=
    fun σ hσ => (Interp.models_total_term typed₀.locallyClosed total hσ).reaches_result
  let g := Interp.resultCapability a a.domain (.ret v) z (Finset.Subset.refl _) returns
  have base : g.restrict a.domain = a := by
    rw [Interp.resultCapability_restrict, Capability.restrict_domain_self]
  have hrefG : a ⊑ g := base.symm
  have graphFull := Interp.models_resultCapability a a.domain (.ret v) z
    (Finset.Subset.refl _) returns typed₀.locallyClosed
    (Finset.Subset.trans typed₀.support_subset scope₀) freshZA
  let X := Interp.relevantSupport Δ₀ (.wand τₓ τ) (.ret v)
  have closedX : LogicVar.LocallyClosed X :=
    Interp.relevantSupport_locallyClosed _ _ _ wf₀.locallyClosedAt typed₀.locallyClosed
  have logicX : (.ret v : Term).logicSupport ⊆ X :=
    Interp.logicSupport_subset_relevantSupport _ _ _ typed₀.support_subset
  have scopeX : X ⊆ a.domain.image LogicVar.free := by
    rw [LogicVar.eq_image_free_of_locallyClosed closedX, Interp.freeAtomSet_relevantSupport]
    exact Finset.image_subset_image (Finset.Subset.trans
      (by rw [Interp.relevantEnv_domain]; exact Finset.inter_subset_left) scope₀)
  have graph : g ⊨ A.openAt 0 z := by
    rw [Interp.resultFirst_openAt _ _ _ z closedX typed₀.locallyClosed logicX
      (fun h => freshZA (by simpa using scopeX h))]
    exact Formula.models_kripke (Capability.restrict_refines g _)
      (Interp.models_resultAt_restrict_support (by intro k hk; simp at hk) scopeX logicX
        (by simpa using freshZA) graphFull)
  have outer := Formula.models_all_openAt_of_refines universal freshZA hrefG (by rfl)
  have wand := Formula.models_impl_elim outer graph
  change g ⊨ ((B.openAt 1 z) -∗[1] (C.openAt 1 z)) at wand
  have openedB : B.openAt 1 z = B := by
    simp only [B, ContextType.shiftFrom_eq_of_locallyClosedAt τₓ 0 wfₓ.locallyClosedAt]
    exact ContextType.interpFuel_openAt_fresh gas 2 Δ₀ τₓ (.ret (.bound 0)) 1 z
      (wfₓ.locallyClosedAt.mono (by omega)) (by simp [Term.locallyClosedAt, Value.locallyClosedAt])
      freshZ₀ (by simp [closedτ]) (by simp [Term.support, Value.support])
  have closedB : (B.openAt 1 z).freeAtoms = ∅ := by
    rw [openedB]
    apply Finset.eq_empty_iff_forall_notMem.2
    intro y hy
    have hs := ContextType.freeAtoms_interpFuel_subset gas 2 Δ₀ _ _ hy
    simp [closedτ, Term.support, Value.support] at hs
  have compatNA : Capability.Compatible n a :=
    Capability.Compatible.restrict_right
      (Capability.Compatible.restrict_left (Capability.Compatible.symm compat) {x}) (m₁.domain.erase x)
  have compatNG : Capability.Compatible n g :=
    Capability.Compatible.symm (Interp.compatible_resultCapability
      (Capability.Compatible.symm compatNA) freshZN returns)
  let s := Capability.product n a compatNA
  let p := Capability.product n g compatNG
  have freshXG : x ∉ g.domain := by simp [g, freshXA, apart]
  have argBound := (ContextType.models_interp_arg_bound_openAt_iff
    (gas := gas) (z := z) (Nat.le_max_left τₓ.measure τ.measure) wfₓ freshX freshZ₀).2 argN
  have result := Formula.models_wand_elim_named wand closedB freshXG compatNG ndom argBound
  have worldA : a ⊨ Interp.basicWorld Δ₀ := by
    have embed₀ : Δ₀.Subset Δ₁ := by
      intro y T hy
      by_cases h : y = x
      · subst y; simp [Δ₀] at hy
      · rwa [BasicEnv.lookup_erase_of_ne Δ₁ h] at hy
    exact (Formula.models_restrict_superset m₁ _
      (by rw [Interp.freeAtoms_basicWorld, ← adom]; exact scope₀)).1
      (Interp.models_basicWorld_of_subset embed₀ world₁)
  have worldZ := Interp.models_basicWorld_resultFirst_openAt wf₀ typed₀
    (Formula.models_kripke hrefG worldA) freshZ₀ graph
  let Δ' := (Δ₀.insert z (.arrow τₓ.erase τ.erase)).insert x τₓ.erase
  have worldP := Formula.models_kripke (Capability.product_refines_right compatNG) worldZ
  have argP := Formula.models_kripke (Capability.product_refines_left compatNG) argN
  have worldFull : p ⊨ Interp.basicWorld Δ' := by
    apply Interp.models_basicWorld_insert worldP (by simp [Capability.product_domain, ndom])
    intro σ hσ
    apply ((Interp.models_basicWorld_iff p _).1 (ContextType.models_interp_basicWorld argP)).2 σ hσ x τₓ.erase
    simp [Interp.relevantEnv, Interp.relevantAtoms, Term.support, Value.support]
  have namedFuel := (ContextType.models_interpFuel_app_bound_openAt_iff
    (gas := gas) (Nat.le_max_right τₓ.measure τ.measure) wf₀.2 freshX freshZ₀ apart worldFull).1 result
  have named : p ⊨ ContextType.interp Δ' (τ.openAt 0 x) (.app (.free z) (.free x)) := by
    rw [ContextType.interp]
    rw [← ContextType.interpFuel_eq_of_measure_le gas (τ.openAt 0 x).measure 0 Δ' _ _
      (by simpa only [ContextType.measure_openAt] using Nat.le_max_right τₓ.measure τ.measure) (Nat.le_refl _)]
    exact namedFuel
  have embed : Δ₀.Subset Δ' :=
    (BasicEnv.subset_insert_of_fresh Δ₀ z _ freshZ₀).trans
      (BasicEnv.subset_insert_of_fresh _ x _ (by simp [BasicEnv.domain_insert, freshX, apart]))
  have typedActual : Δ' ⊢ₑ (.app v (.free x)) ⋮ (τ.openAt 0 x).erase := by
    cases typed₀ with
    | ret typedV =>
      rw [ContextType.erase_openAt]
      exact BasicTermTyp.app (typedV.weaken embed) (BasicValTyp.free (BasicEnv.lookup_insert _ _ _))
  have typedNamed : Δ' ⊢ₑ (.app (.free z) (.free x)) ⋮ (τ.openAt 0 x).erase := by
    rw [ContextType.erase_openAt]
    exact BasicTermTyp.app
      (BasicValTyp.free (by rw [BasicEnv.lookup_insert_of_ne _ _ apart.symm, BasicEnv.lookup_insert]))
      (BasicValTyp.free (BasicEnv.lookup_insert _ _ _))
  have formed : (τ.openAt 0 x).WellFormed Δ'.domain := (wf₀.2.openAt fresh'.2).mono (by
    intro y hy
    simp only [Δ', BasicEnv.domain_insert, Finset.mem_union, Finset.mem_singleton] at hy ⊢
    exact hy.elim (fun h => Or.inr (Or.inr h)) Or.inl)
  have graphP := Formula.models_kripke (Capability.product_refines_right compatNG) graphFull
  have actual := (ContextType.models_interp_of_instantiate_eq_iff formed typedActual typedNamed worldFull
    (by
      intro σ hσ
      obtain ⟨u, hu, heval⟩ := Interp.models_resultAt_lookup
        (by intro k hk; simp at hk)
        (by
          rw [LogicVar.eq_image_free_of_locallyClosed (Interp.termLogicSupport_locallyClosed _ typed₀.locallyClosed),
            Interp.freeAtomSet_term_logicSupport]
          exact Finset.image_subset_image (Finset.Subset.trans typed₀.support_subset scope₀))
        (by simpa using freshZA) graphP σ hσ
      have hv : u = Interp.instantiateValueAt v 0 σ.toAssignment := Term.ret.inj heval.ret_eq
      simp only [Interp.instantiateTerm, Interp.instantiateTermAt, Interp.instantiateValueAt,
        Store.toAssignment_lookup_free, hu, Option.getD_some]
      rw [hv])).2 named
  have sameEnv : BasicEnv.AgreeOn ((τ.openAt 0 x).freeAtoms ∪ (.app v (.free x) : Term).support) Δ' Δ := by
    intro y hy
    by_cases hxy : y = x
    · subst y
      rw [BasicEnv.lookup_insert]
      exact (show Δ.lookup x = some τₓ.erase from by
        have disj := wf.1.2.2
        have freshX₁ : x ∉ Δ₁.domain := by
          rw [wf₁.1.erase_domain]
          exact fun hx => (Finset.disjoint_left.1 disj hx)
            (by rw [← wf₂.1.erase_domain]; exact (BasicEnv.mem_domain_iff Δ₂ x).2 ⟨_, lookupX⟩)
        exact (BasicEnv.lookup_merge_right Δ₁ Δ₂ freshX₁).trans lookupX).symm
    · have used : y ∈ τ.freeAtoms ∪ v.support := by
        rcases Finset.mem_union.1 hy with hy | hy
        · rcases Finset.mem_union.1 (ContextType.freeAtoms_openAt_subset τ 0 x hy) with hy | hy
          · exact False.elim (hxy (Finset.mem_singleton.1 hy))
          · exact Finset.mem_union_left _ hy
        · have hy' : y ∈ v.support ∨ y = x := by simpa [Term.support, Value.support, or_comm] using hy
          exact hy'.elim (Finset.mem_union_right _) (fun h => False.elim (hxy h))
      have in₀ : y ∈ Δ₀.domain := Finset.union_subset wf₀.2.freeAtoms_subset typed₀.support_subset used
      have in₁ : y ∈ Δ₁.domain := by rw [BasicEnv.domain_erase] at in₀; exact (Finset.mem_erase.1 in₀).2
      have hyz : y ≠ z := fun h => freshZ₀ (h ▸ in₀)
      simp only [Δ', BasicEnv.lookup_insert_of_ne _ _ hxy, BasicEnv.lookup_insert_of_ne _ _ hyz]
      rw [BasicEnv.lookup_erase_of_ne Δ₁ hxy]
      exact (BasicEnv.lookup_merge_left Δ₁ Δ₂ in₁).symm
  rw [ContextType.interp_eq_of_agreeOn sameEnv] at actual
  have totalS := Formula.models_kripke (Capability.product_refines_right compatNA) total
  have returnsS : ∀ σ, σ ∈ s → ∃ u, (Interp.instantiateTerm (.ret v) σ.toAssignment).reaches u :=
    fun σ hσ => (Interp.models_total_term typed₀.locallyClosed totalS hσ).reaches_result
  have baseP : p.restrict s.domain = s := by
    have eq := Interp.resultCapability_product compatNA.symm
      (Finset.Subset.trans typed₀.support_subset scope₀) freshZN returns (by
        rw [← Capability.product_comm compatNA]
        exact returnsS)
    have peq : p = Interp.resultCapability s s.domain (.ret v) z (Finset.Subset.refl _) returnsS := by
      simpa only [p, s, g, Capability.product_domain, Capability.product_comm compatNA.symm,
        Capability.product_comm compatNG.symm, Finset.union_comm] using eq.symm
    rw [peq, Interp.resultCapability_restrict, Capability.restrict_domain_self]
  have scopeResult : (ContextType.interp Δ (τ.openAt 0 x) (.app v (.free x))).freeAtoms ⊆ s.domain := by
    apply Finset.Subset.trans (ContextType.freeAtoms_interp_subset _ _ _)
    rw [Capability.product_domain, ndom]
    intro y hy
    rcases Finset.mem_union.1 hy with hy | hy
    · rcases Finset.mem_union.1 (ContextType.freeAtoms_openAt_subset τ 0 x hy) with hy | hy
      · exact Finset.mem_union_left _ hy
      · exact Finset.mem_union_right _ (scope₀ (wf₀.2.freeAtoms_subset hy))
    · have hy' : y ∈ v.support ∨ y = x := by simpa [Term.support, Value.support, or_comm] using hy
      exact hy'.elim (fun h => Finset.mem_union_right _ (scope₀ (typed₀.support_subset h)))
        (fun h => Finset.mem_union_left _ (by simp [h]))
  have target : s ⊨ ContextType.interp Δ (τ.openAt 0 x) (.app v (.free x)) :=
    (Formula.models_projection (m := s) (n := p) s.domain scopeResult
      (by rw [Capability.restrict_domain_self, baseP])).2 actual
  apply Formula.models_kripke (Capability.refines_trans
    (Capability.product_refines compatNA compat.symm
      (Capability.restrict_refines m₂ _) (Capability.restrict_refines m₁ _)) ?_) target
  rwa [Capability.product_comm compat.symm]


end ContextTypes
