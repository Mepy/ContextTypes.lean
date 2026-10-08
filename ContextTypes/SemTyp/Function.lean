import ContextTypes.SemTyp.Core
import Mathlib.Tactic

set_option autoImplicit false

namespace ContextTypes
open scoped ContextTypes

namespace SemTyp

/-- Ordinary lambda compatibility retains the full input capability while
naming each function result and dependent argument. -/
theorem lam
    {Φ : PrimitiveContext} {«Σ» : BasicEnv} {Γ : Context}
    {τₓ τ : ContextType} {e : Term} (L : Finset Atom)
    (wf : SynTyp.WellFormed «Σ» Γ (.ret (.lam τₓ.erase e)) (.arrow τₓ τ))
    (wf₂ : ∀ y, y ∉ L → SynTyp.WellFormed «Σ» (Γ ,, (y ∷ τₓ))
      (e.openAt 0 (.free y)) (τ.openAt 0 y))
    (body : ∀ y, y ∉ L → Φ ; «Σ» ; (Γ ,, (y ∷ τₓ)) ⊨
      (e.openAt 0 (.free y)) ⋮ (τ.openAt 0 y)) :
    Φ ; «Σ» ; Γ ⊨ (.ret (.lam τₓ.erase e)) ⋮ (.arrow τₓ τ) := by
  intro m hΓ
  let Δ := Γ.erase
  let gas := max τₓ.measure τ.measure
  let v := Value.lam τₓ.erase e
  let Δr := Interp.relevantEnv Δ (.arrow τₓ τ) (.ret v)
  let A := Interp.resultFirst Δ (.arrow τₓ τ) (.ret v)
  let B := ContextType.interpFuel gas 2 Δ ((τₓ.shiftFrom 0).shiftFrom 0) (.ret (.bound 0))
  let C := ContextType.interpFuel gas 2 Δ (τ.shiftFrom 1) (.app (.bound 1) (.bound 0))
  have world := Context.models_interpUnder_erase_basicWorld wf.1 hΓ
  have scopeΔ : Δ.domain ⊆ m.domain := (Interp.models_basicWorld_iff m Δ).1 world |>.1
  have typedV : Δ ⊢ᵥ v ⋮ (.arrow τₓ.erase τ.erase) := by
    cases wf.2.2 with
    | ret h => exact h
  have total : m ⊨ Interp.total (.ret v) := by
    apply (Interp.models_total_iff wf.2.2.locallyClosed).2
    refine ⟨Finset.Subset.trans wf.2.2.support_subset scopeΔ, ?_⟩
    intro σ hσ
    exact Term.MustTerminate.ret _
      (Interp.instantiateTerm_typed wf.2.2 ((Interp.models_basicWorld_iff m Δ).1 world |>.2 σ hσ)).locallyClosed
  have guard := Interp.models_guard_relevant_of_world wf.2.1 wf.2.2 world total
  have agree (υ : ContextType) (u : Term)
      (hs : υ.freeAtoms ∪ u.support ⊆ (.arrow τₓ τ : ContextType).freeAtoms ∪ (.ret v : Term).support) :
      BasicEnv.AgreeOn (υ.freeAtoms ∪ u.support) Δr Δ := by
    intro x hx
    simp only [Δr, Interp.relevantEnv, BasicEnv.lookup_restrict,
      Interp.relevantAtoms, if_pos (hs hx)]
  have envB : ContextType.interpFuel gas 2 Δr ((τₓ.shiftFrom 0).shiftFrom 0)
      (.ret (.bound 0)) = B := by
    apply ContextType.interpFuel_eq_of_agreeOn
    apply agree
    simp [ContextType.freeAtoms, Term.support, Value.support]
  have envC : ContextType.interpFuel gas 2 Δr (τ.shiftFrom 1)
      (.app (.bound 1) (.bound 0)) = C := by
    apply ContextType.interpFuel_eq_of_agreeOn
    apply agree
    simp only [ContextType.freeAtoms_shiftFrom, Term.support, Value.support,
      Finset.union_empty, ContextType.freeAtoms]
    exact Finset.Subset.trans Finset.subset_union_right Finset.subset_union_left
  change m ⊨ ContextType.interp Δ (.arrow τₓ τ) (.ret v)
  simp only [ContextType.interp, ContextType.measure, Nat.add_comm 1]
  change m ⊨ ContextType.interpFuel (gas + 1) 0 Δ (.arrow τₓ τ) (.ret v)
  simp only [ContextType.interpFuel, Nat.zero_add, Interp.resultFirst_relevantEnv]
  rw [envB, envC, Formula.models_and_iff]
  refine ⟨guard, ?_⟩
  have scopeA : A.freeAtoms ⊆ Δ.domain := by
    simp only [A, Interp.freeAtoms_resultFirst]
    exact Finset.union_subset
      (by rw [Interp.relevantEnv_domain]; exact Finset.inter_subset_left)
      wf.2.2.support_subset
  have scopeB : B.freeAtoms ⊆ Δ.domain := by
    apply Finset.Subset.trans (ContextType.freeAtoms_interpFuel_subset _ _ _ _ _)
    simpa [ContextType.freeAtoms_shiftFrom, Term.support, Value.support] using wf.2.1.1.freeAtoms_subset
  have scopeC : C.freeAtoms ⊆ Δ.domain := by
    apply Finset.Subset.trans (ContextType.freeAtoms_interpFuel_subset _ _ _ _ _)
    simpa [ContextType.freeAtoms_shiftFrom, Term.support, Value.support] using wf.2.1.2.freeAtoms_subset
  have scopeP : (A ⇒ᶜ Formula.all (B ⇒ᶜ C)).freeAtoms ⊆ m.domain := by
    simp only [Formula.freeAtoms_impl, Formula.freeAtoms_all]
    exact Finset.Subset.trans (Finset.union_subset scopeA (Finset.union_subset scopeB scopeC)) scopeΔ
  apply (Formula.models_all_iff_full m _).2
  refine ⟨scopeP, ∅, ?_⟩
  intro z _ freshZ n href hdom
  have scopeN : ((A ⇒ᶜ Formula.all (B ⇒ᶜ C)).openAt 0 z).freeAtoms ⊆ n.domain := by
    apply Finset.Subset.trans (Formula.freeAtoms_openAt_subset _ _ _)
    rw [hdom]
    exact Finset.union_subset (by simp) (Finset.Subset.trans scopeP Finset.subset_union_left)
  simp only [Formula.openAt]
  apply (Formula.models_impl_iff_of_scope n _ _ scopeN).2
  intro graph
  have freshZΔ : z ∉ Δ.domain := fun hz => freshZ (scopeΔ hz)
  have worldN := Interp.models_basicWorld_resultFirst_openAt wf.2.1 wf.2.2
    (Formula.models_kripke href world) freshZΔ graph
  have scopeInner : ((B ⇒ᶜ C).openAt 1 z).freeAtoms ⊆ n.domain := by
    apply Finset.Subset.trans (Formula.freeAtoms_openAt_subset _ _ _)
    rw [hdom]
    exact Finset.union_subset (by simp)
      (Finset.Subset.trans (by simpa only [Formula.freeAtoms_impl] using Finset.union_subset scopeB scopeC)
        (Finset.Subset.trans scopeΔ Finset.subset_union_left))
  apply (Formula.models_all_iff_full n _).2
  refine ⟨scopeInner, L, ?_⟩
  intro y freshL freshY p hrefP hdomP
  have scopeP' : (((B ⇒ᶜ C).openAt 1 z).openAt 0 y).freeAtoms ⊆ p.domain := by
    apply Finset.Subset.trans (Formula.freeAtoms_openAt_subset _ _ _)
    rw [hdomP]
    exact Finset.union_subset (by simp) (Finset.Subset.trans scopeInner Finset.subset_union_left)
  simp only [Formula.openAt]
  apply (Formula.models_impl_iff_of_scope p _ _ scopeP').2
  intro arg
  have hrefMP := Capability.refines_trans href hrefP
  have freshYΔ : y ∉ Δ.domain := fun hy => freshY
    (Capability.refines_domain_subset href (scopeΔ hy))
  have apart : y ≠ z := by
    intro h
    subst y
    exact freshY (by rw [hdom]; simp)
  have named := (ContextType.models_interp_arg_bound_openAt_iff
    (Nat.le_max_left _ _) wf.2.1.1 freshYΔ freshZΔ).1 arg
  have freshYCtx : y ∉ (Context.erasureUnder «Σ» Γ).domain := by
    intro hy
    exact freshY (Capability.refines_domain_subset href
      (((Interp.models_basicWorld_iff m _).1 (Context.models_interpUnder_basicWorld hΓ)).1 hy))
  have ctx := Context.models_interpUnder_comma_bind wf.1 wf.2.1.1 freshYCtx
    (Formula.models_kripke hrefMP hΓ) named
  have hbody := body y freshL p ctx
  have wfbody := wf₂ y freshL
  have envBody : (Γ ,, (y ∷ τₓ) : Context).erase = Δ.insert y τₓ.erase := by
    simp only [Context.erase]
    exact BasicEnv.merge_singleton_eq_insert freshYΔ
  rw [envBody] at hbody
  have typedBody : Δ.insert y τₓ.erase ⊢ₑ e.openAt 0 (.free y) ⋮ (τ.openAt 0 y).erase := by
    simpa only [envBody] using wfbody.2.2
  have formedBody : (τ.openAt 0 y).WellFormed (Δ.insert y τₓ.erase).domain := by
    simpa only [envBody] using wfbody.2.1
  let Δ' := (Δ.insert z (.arrow τₓ.erase τ.erase)).insert y τₓ.erase
  have embed : (Δ.insert y τₓ.erase).Subset Δ' :=
    (BasicEnv.subset_insert_of_fresh Δ z _ freshZΔ).insert y τₓ.erase
  have typedApp : Δ' ⊢ₑ (.app v (.free y)) ⋮ (τ.openAt 0 y).erase := by
    rw [ContextType.erase_openAt]
    exact BasicTermTyp.app (typedV.weaken
      ((BasicEnv.subset_insert_of_fresh Δ z _ freshZΔ).trans
        (BasicEnv.subset_insert_of_fresh _ y _ (by simp [BasicEnv.domain_insert, freshYΔ, apart]))))
      (BasicValTyp.free (BasicEnv.lookup_insert _ _ _))
  have formed : (τ.openAt 0 y).WellFormed Δ'.domain :=
    formedBody.mono (by
      intro x hx
      obtain ⟨T, hT⟩ := (BasicEnv.mem_domain_iff _ x).1 hx
      exact (BasicEnv.mem_domain_iff _ x).2 ⟨T, embed x T hT⟩)
  have worldP := Formula.models_kripke hrefP worldN
  have worldArg := ContextType.models_interp_basicWorld named
  have worldFull : p ⊨ Interp.basicWorld Δ' := by
    apply Interp.models_basicWorld_insert worldP
      (by rw [hdomP]; simp)
    intro σ hσ
    apply ((Interp.models_basicWorld_iff p _).1 worldArg).2 σ hσ y τₓ.erase
    simp [Interp.relevantEnv, Interp.relevantAtoms, Term.support, Value.support]
  have sameEnv : BasicEnv.AgreeOn
      ((τ.openAt 0 y).freeAtoms ∪ (e.openAt 0 (.free y)).support) (Δ.insert y τₓ.erase) Δ' := by
    intro x hx
    by_cases hxy : x = y
    · subst x; simp [Δ']
    · simp only [Δ', BasicEnv.lookup_insert_of_ne _ _ hxy]
      rw [BasicEnv.lookup_insert_of_ne _ _]
      intro hxz
      subst x
      have hs := Finset.union_subset formedBody.freeAtoms_subset typedBody.support_subset hx
      simp only [BasicEnv.domain_insert, Finset.mem_union, Finset.mem_singleton] at hs
      exact hs.elim (fun h => apart h.symm) freshZΔ
  have bodyFull : p ⊨ ContextType.interp Δ' (τ.openAt 0 y) (e.openAt 0 (.free y)) := by
    rw [← ContextType.interp_eq_of_agreeOn sameEnv]
    exact hbody
  have beta := (ContextType.models_interp_beta_iff formed typedApp worldFull).2 bodyFull
  have graphP := Formula.models_kripke hrefP graph
  have lookup := Interp.models_resultFirst_openAt_lookup
    (Interp.relevantSupport_locallyClosed Δ (.arrow τₓ τ) (.ret v) wf.2.1.locallyClosedAt wf.2.2.locallyClosed)
    wf.2.2.locallyClosed (Interp.logicSupport_subset_relevantSupport Δ _ _ wf.2.2.support_subset)
    (by rw [Interp.free_mem_relevantSupport_iff]; exact fun hz => freshZΔ hz.1) graphP
  have typedNamed : Δ' ⊢ₑ (.app (.free z) (.free y)) ⋮ (τ.openAt 0 y).erase := by
    rw [ContextType.erase_openAt]
    exact BasicTermTyp.app
      (BasicValTyp.free (by rw [BasicEnv.lookup_insert_of_ne _ _ apart.symm, BasicEnv.lookup_insert]))
      (BasicValTyp.free (BasicEnv.lookup_insert _ _ _))
  have namedApp := (ContextType.models_interp_of_instantiate_eq_iff formed typedApp typedNamed worldFull
    (by
      intro σ hσ
      obtain ⟨u, hu, heval⟩ := lookup σ hσ
      have hv : u = Interp.instantiateValueAt v 0 σ.toAssignment := Term.ret.inj heval.ret_eq
      simp only [Interp.instantiateTerm, Interp.instantiateTermAt, Interp.instantiateValueAt,
        Store.toAssignment_lookup_free, hu, Option.getD_some]
      rw [hv])).1 beta
  have opened := (ContextType.models_interpFuel_app_bound_openAt_iff
    (Nat.le_max_right _ _) wf.2.1.2 freshYΔ freshZΔ apart worldFull).2
    (by
      rw [ContextType.interpFuel_eq_of_measure_le gas (τ.openAt 0 y).measure 0 Δ'
        (τ.openAt 0 y) (.app (.free z) (.free y))
        (by simpa only [ContextType.measure_openAt] using Nat.le_max_right τₓ.measure τ.measure) (Nat.le_refl _)]
      exact namedApp)
  exact opened

end SemTyp

end ContextTypes
