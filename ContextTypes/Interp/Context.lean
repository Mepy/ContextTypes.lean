import ContextTypes.Interp.Type

set_option autoImplicit false

namespace ContextTypes

/-!
# Bunched-context interpretation and semantic subtyping
-/

open scoped ContextTypes

namespace Context

/-! ## Bunched-context interpretation -/

def erasureUnder («Σ» : BasicEnv) (Γ : Context) : BasicEnv :=
  ((«Σ»).restrict Γ.freeAtoms).merge Γ.erase

def interpUnder («Σ» : BasicEnv) : Context → Formula
  | .empty =>
      Interp.basicWorld ((«Σ»).restrict ∅) ∧ᶜ ⊤ᶜ
  | .bind x τ =>
      let «Σ'» := («Σ»).restrict τ.freeAtoms
      Interp.basicWorld ((«Σ'»).merge (BasicEnv.singleton x τ.erase)) ∧ᶜ
        ContextType.interp ((«Σ'»).insert x τ.erase) τ (.ret (.free x))
  | .comma Γ₁ Γ₂ =>
      let Γ := Context.comma Γ₁ Γ₂
      let «Σ'» := («Σ»).restrict Γ.freeAtoms
      Interp.basicWorld ((«Σ'»).merge Γ.erase) ∧ᶜ
        (interpUnder «Σ'» Γ₁ ∧ᶜ
          interpUnder ((«Σ'»).merge Γ₁.erase) Γ₂)
  | .star Γ₁ Γ₂ =>
      let Γ := Context.star Γ₁ Γ₂
      let «Σ'» := («Σ»).restrict Γ.freeAtoms
      Interp.basicWorld ((«Σ'»).merge Γ.erase) ∧ᶜ
        (interpUnder «Σ'» Γ₁ ∗ interpUnder «Σ'» Γ₂)
  | .sum Γ₁ Γ₂ =>
      let Γ := Context.sum Γ₁ Γ₂
      let «Σ'» := («Σ»).restrict Γ.freeAtoms
      Interp.basicWorld ((«Σ'»).merge Γ.erase) ∧ᶜ
        (interpUnder «Σ'» Γ₁ ⊕ interpUnder «Σ'» Γ₂)

def interp (Γ : Context) : Formula :=
  interpUnder ∅ Γ

theorem erasureUnder_domain_subset_support («Σ» : BasicEnv) (Γ : Context) :
    (erasureUnder «Σ» Γ).domain ⊆ Γ.support := by
  rw [Context.support_eq_freeAtoms_union_domain]
  simp only [erasureUnder, BasicEnv.domain_merge, BasicEnv.domain_restrict]
  exact Finset.union_subset
    (Finset.Subset.trans Finset.inter_subset_right Finset.subset_union_left)
    (Finset.Subset.trans (Context.erase_domain_subset_domain Γ)
      Finset.subset_union_right)

theorem erasureUnder_minimal («Σ» : BasicEnv) (Γ : Context) :
    erasureUnder «Σ» Γ = erasureUnder ((«Σ»).restrict Γ.freeAtoms) Γ := by
  simp [erasureUnder, BasicEnv.restrict_restrict]

theorem interpUnder_minimal («Σ» : BasicEnv) (Γ : Context) :
    interpUnder «Σ» Γ = interpUnder ((«Σ»).restrict Γ.freeAtoms) Γ := by
  cases Γ <;>
    simp [interpUnder, Context.freeAtoms, BasicEnv.restrict_restrict]

theorem interpUnder_restrict («Σ» : BasicEnv) (Γ : Context) {X : Finset Atom}
    (support : Γ.freeAtoms ⊆ X) :
    interpUnder («Σ».restrict X) Γ = interpUnder «Σ» Γ := by
  calc
    interpUnder («Σ».restrict X) Γ =
        interpUnder ((«Σ».restrict X).restrict Γ.freeAtoms) Γ :=
      interpUnder_minimal _ Γ
    _ = interpUnder («Σ».restrict Γ.freeAtoms) Γ := by
      rw [BasicEnv.restrict_restrict, Finset.inter_eq_right.2 support]
    _ = interpUnder «Σ» Γ := (interpUnder_minimal «Σ» Γ).symm

/-- An additive context splits the whole capability into models of its
two branches, even when the capability contains additional observations. -/
theorem models_interpUnder_sum_elim {m : Capability} {«Σ» : BasicEnv}
    {Γ₁ Γ₂ : Context} (h : m ⊨ interpUnder «Σ» (.sum Γ₁ Γ₂)) :
    ∃ (m₁ m₂ : Capability) (defined : Capability.SumDefined m₁ m₂),
      Capability.sum m₁ m₂ defined = m ∧
        m₁ ⊨ interpUnder «Σ» Γ₁ ∧ m₂ ⊨ interpUnder «Σ» Γ₂ := by
  have hbody := Formula.models_and_elim_right h
  change m ⊨
    (interpUnder («Σ».restrict (Γ₁.freeAtoms ∪ Γ₂.freeAtoms)) Γ₁ ⊕
     interpUnder («Σ».restrict (Γ₁.freeAtoms ∪ Γ₂.freeAtoms)) Γ₂) at hbody
  rw [interpUnder_restrict «Σ» Γ₁ Finset.subset_union_left,
    interpUnder_restrict «Σ» Γ₂ Finset.subset_union_right] at hbody
  exact (Formula.models_sum_iff_eq _ _ _).1 hbody

/-- The ambient erased world is observed by the context interpretation. -/
theorem erasureUnder_domain_subset_freeAtoms_interpUnder
    («Σ» : BasicEnv) (Γ : Context) :
    (erasureUnder «Σ» Γ).domain ⊆ (interpUnder «Σ» Γ).freeAtoms := by
  cases Γ <;>
    simp [erasureUnder, interpUnder, Context.freeAtoms, Context.erase] <;>
    intro x hx <;>
    simp only [Finset.mem_union, Finset.mem_inter, Finset.mem_sdiff] at hx ⊢ <;>
    tauto

theorem models_interpUnder_basicWorld {m : Capability} {«Σ» : BasicEnv}
    {Γ : Context} (h : m ⊨ interpUnder «Σ» Γ) :
    m ⊨ Interp.basicWorld (erasureUnder «Σ» Γ) := by
  cases Γ <;>
    simpa [interpUnder, erasureUnder, Context.freeAtoms, Context.erase] using
      (Formula.models_and_elim_left h)

/-- A well-formed context interpretation provides a typed world for its
erased bindings independently of the ambient environment. -/
theorem models_interpUnder_erase_basicWorld {m : Capability} {«Σ» : BasicEnv}
    {Γ : Context} (wf : Γ.WellFormedUnder «Σ».domain)
    (h : m ⊨ interpUnder «Σ» Γ) : m ⊨ Interp.basicWorld Γ.erase := by
  obtain ⟨scope, typed⟩ := (Interp.models_basicWorld_iff m (erasureUnder «Σ» Γ)).1
    (models_interpUnder_basicWorld h)
  apply (Interp.models_basicWorld_iff m Γ.erase).2
  refine ⟨?_, ?_⟩
  · apply Finset.Subset.trans _ scope
    simp only [erasureUnder, BasicEnv.domain_merge]
    exact Finset.subset_union_right
  · intro σ hσ x T hx
    have hxΓ : x ∈ Γ.erase.domain := (BasicEnv.mem_domain_iff Γ.erase x).2 ⟨T, hx⟩
    have fresh : x ∉ «Σ».domain := by
      intro hmem
      exact Finset.disjoint_left.1 wf.domain_disjoint
        (by rwa [wf.erase_domain] at hxΓ) hmem
    have hfresh : x ∉ («Σ».restrict Γ.freeAtoms).domain := by
      simp only [BasicEnv.domain_restrict, Finset.mem_inter]
      exact fun h => fresh h.1
    apply typed σ hσ x T
    change ((«Σ».restrict Γ.freeAtoms).merge Γ.erase).lookup x = some T
    rwa [BasicEnv.lookup_merge_right _ _ hfresh]

set_option hygiene false in
scoped[ContextTypes] notation:20 (name := contextInterpUnder)
    "⟦" Γ "⟧[" «Σ» "]" => ContextTypes.Context.interpUnder «Σ» Γ

end Context


def SubTypeUnder («Σ» : BasicEnv) (Γ : Context)
    (τ₁ τ₂ : ContextType) : Prop :=
  Γ.WellFormedUnder («Σ»).domain ∧
  τ₁.WellFormed Γ.erase.domain ∧
  τ₂.WellFormed Γ.erase.domain ∧
  τ₁.erase = τ₂.erase ∧
  ∀ e, BasicTermTyp Γ.erase e τ₁.erase →
    Formula.Entails (Context.interpUnder «Σ» Γ)
      (Formula.impl
        (ContextType.interp Γ.erase τ₁ e)
        (ContextType.interp Γ.erase τ₂ e))

set_option hygiene false in
scoped[ContextTypes] notation:40 (name := semanticSubtype)
    «Σ»:41 " ; " Γ:41 " ⊢ " τ₁:41 " <: " τ₂:41 =>
  ContextTypes.SubTypeUnder «Σ» Γ τ₁ τ₂


namespace Context

/-- Separating contexts expose compatible factors whose product projects
to the original capability, retaining any additional observations. -/
theorem models_interpUnder_star_elim
    {m : Capability} {«Σ» : BasicEnv} {Γ₁ Γ₂ : Context}
    (h : m ⊨ interpUnder «Σ» (Γ₁ ∗ Γ₂)) :
    ∃ (m₁ m₂ : Capability) (compat : Capability.Compatible m₁ m₂),
      Capability.product m₁ m₂ compat ⊑ m ∧
        m₁ ⊨ interpUnder «Σ» Γ₁ ∧ m₂ ⊨ interpUnder «Σ» Γ₂ := by
  have hbody := Formula.models_and_elim_right h
  change m ⊨
    (interpUnder («Σ».restrict (Γ₁.freeAtoms ∪ Γ₂.freeAtoms)) Γ₁ ∗
      interpUnder («Σ».restrict (Γ₁.freeAtoms ∪ Γ₂.freeAtoms)) Γ₂) at hbody
  rw [interpUnder_restrict «Σ» Γ₁ Finset.subset_union_left,
    interpUnder_restrict «Σ» Γ₂ Finset.subset_union_right] at hbody
  obtain ⟨_, m₁, m₂, compat, href, h₁, h₂⟩ := (Formula.models_star_iff m _ _).1 hbody
  exact ⟨m₁, m₂, compat,
    Capability.refines_trans href (Capability.restrict_refines m _), h₁, h₂⟩

/-- A closed result type can be bound independently of a compatible context. -/
theorem models_interpUnder_star_bind_closed
    {m n : Capability} {«Σ» : BasicEnv} {Γ : Context} {τ : ContextType} {x : Atom}
    (compat : Capability.Compatible m n) (closed : τ.freeAtoms = ∅)
    (fresh : x ∉ (erasureUnder «Σ» Γ).domain)
    (hΓ : m ⊨ interpUnder «Σ» Γ)
    (hτ : n ⊨ ContextType.interp (BasicEnv.singleton x τ.erase) τ (.ret (.free x))) :
    Capability.product m n compat ⊨ interpUnder «Σ» (Γ ∗ (x ∷ τ)) := by
  let p := Capability.product m n compat
  have hworldτ := ContextType.models_interp_basicWorld hτ
  have relevant : Interp.relevantEnv (BasicEnv.singleton x τ.erase) τ (.ret (.free x)) =
      BasicEnv.singleton x τ.erase := by
    simp only [Interp.relevantEnv, Interp.relevantAtoms, closed, Term.support,
      Value.support, Finset.empty_union]
    exact BasicEnv.restrict_domain_self _
  rw [relevant] at hworldτ
  have hworldΓ := Formula.models_kripke (Capability.product_refines_left compat)
    (models_interpUnder_basicWorld hΓ)
  have hworldX := Formula.models_kripke (Capability.product_refines_right compat) hworldτ
  have hX := (Interp.models_basicWorld_iff p (BasicEnv.singleton x τ.erase)).1 hworldX
  have hxP : x ∈ p.domain := by
    simpa only [BasicEnv.domain_singleton, Finset.singleton_subset_iff] using hX.1
  have hworld := Interp.models_basicWorld_insert hworldΓ hxP
    (fun σ hσ => hX.2 σ hσ x τ.erase (BasicEnv.lookup_singleton _ _))
  have hbind : n ⊨ interpUnder «Σ» (x ∷ τ) := by
    have := Formula.models_and_intro hworldτ hτ
    simpa [interpUnder, closed, BasicEnv.merge, BasicEnv.insert, BasicEnv.singleton] using this
  have hfree : (Γ ∗ (x ∷ τ) : Context).freeAtoms = Γ.freeAtoms := by
    simp only [Context.freeAtoms, closed, Finset.union_empty]
  have henv : («Σ».restrict Γ.freeAtoms).merge
      (Γ.erase.merge (BasicEnv.singleton x τ.erase)) =
      (erasureUnder «Σ» Γ).insert x τ.erase := by
    rw [← BasicEnv.merge_assoc]
    exact BasicEnv.merge_singleton_eq_insert fresh
  simp only [interpUnder, hfree, Context.erase]
  rw [henv, interpUnder_restrict «Σ» Γ (Finset.Subset.refl _)]
  apply Formula.models_and_intro hworld
  have h := Formula.models_star_product compat hΓ hbind
  simpa [interpUnder, closed, BasicEnv.merge, BasicEnv.insert, BasicEnv.singleton] using h

/-- A named result and a context model establish their entangled extension. -/
theorem models_interpUnder_comma_bind
    {m : Capability} {«Σ» : BasicEnv} {Γ : Context} {τ : ContextType} {x : Atom}
    (wfΓ : Γ.WellFormedUnder «Σ».domain)
    (wfτ : τ.WellFormed Γ.erase.domain)
    (fresh : x ∉ (erasureUnder «Σ» Γ).domain)
    (hΓ : m ⊨ interpUnder «Σ» Γ)
    (hτ : m ⊨ ContextType.interp (Γ.erase.insert x τ.erase) τ (.ret (.free x))) :
    m ⊨ interpUnder «Σ» (Γ ,, (x ∷ τ)) := by
  let Δ := erasureUnder «Σ» Γ
  have hτΓ : τ.freeAtoms ⊆ Γ.domain := by
    rw [← wfΓ.erase_domain]
    exact wfτ.freeAtoms_subset
  have hfree : (Γ ,, (x ∷ τ) : Context).freeAtoms = Γ.freeAtoms := by
    simp only [Context.freeAtoms]
    rw [Finset.sdiff_eq_empty_iff_subset.2 hτΓ, Finset.union_empty]
  have hworld := models_interpUnder_basicWorld hΓ
  have hworldτ := ContextType.models_interp_basicWorld hτ
  have lookup := BasicEnv.lookup_insert Γ.erase x τ.erase
  have hxtyped : ∀ σ, σ ∈ m → ∃ v, σ.lookup x = some v ∧ BasicValTyp ∅ v τ.erase := by
    intro σ hσ
    apply ((Interp.models_basicWorld_iff m _).1 hworldτ).2 σ hσ x τ.erase
    simp [Interp.relevantEnv, Interp.relevantAtoms, Term.support, Value.support, lookup]
  have hxM : x ∈ m.domain := by
    obtain ⟨σ, hσ⟩ := m.nonempty
    obtain ⟨v, hv, _⟩ := hxtyped σ hσ
    rw [← m.mem_domain hσ]
    exact (Store.mem_domain_iff σ x).2 ⟨v, hv⟩
  have hworld' := Interp.models_basicWorld_insert hworld hxM hxtyped
  have henv :
      («Σ».restrict Γ.freeAtoms).merge (Γ.erase.merge (BasicEnv.singleton x τ.erase)) =
        Δ.insert x τ.erase := by
    rw [← BasicEnv.merge_assoc]
    exact BasicEnv.merge_singleton_eq_insert fresh
  have hbind : m ⊨ interpUnder Δ (x ∷ τ) := by
    have hxτ : x ∉ τ.freeAtoms := by
      intro hx
      apply fresh
      rw [erasureUnder, BasicEnv.domain_merge]
      exact Finset.mem_union_right _ (wfτ.freeAtoms_subset hx)
    have hΔτ : x ∉ (Δ.restrict τ.freeAtoms).domain := by simp [hxτ]
    have agree : BasicEnv.AgreeOn
        (τ.freeAtoms ∪ (.ret (.free x) : Term).support)
        (Γ.erase.insert x τ.erase) ((Δ.restrict τ.freeAtoms).insert x τ.erase) := by
      intro y hy
      by_cases hxy : y = x
      · subst y
        simp
      · rw [BasicEnv.lookup_insert_of_ne _ _ hxy, BasicEnv.lookup_insert_of_ne _ _ hxy]
        have hyτ : y ∈ τ.freeAtoms := by
          rcases Finset.mem_union.1 hy with hy | hy
          · exact hy
          · exact (hxy (by simpa [Term.support, Value.support] using hy)).elim
        rw [BasicEnv.lookup_restrict, if_pos hyτ]
        have hyΓ := wfτ.freeAtoms_subset hyτ
        have hambient : y ∉ («Σ».restrict Γ.freeAtoms).domain := by
          intro h
          rw [BasicEnv.domain_restrict] at h
          exact Finset.disjoint_left.1 wfΓ.domain_disjoint
            (by rwa [wfΓ.erase_domain] at hyΓ) (Finset.mem_inter.1 h).1
        exact (BasicEnv.lookup_merge_right _ _ hambient).symm
    have hτ' : m ⊨ ContextType.interp ((Δ.restrict τ.freeAtoms).insert x τ.erase)
        τ (.ret (.free x)) := by
      rw [← ContextType.interp_eq_of_agreeOn agree]
      exact hτ
    apply Formula.models_and_intro ?_ hτ'
    rw [BasicEnv.merge_singleton_eq_insert hΔτ]
    apply (Interp.models_basicWorld_iff m _).2
    refine ⟨?_, ?_⟩
    · simp only [BasicEnv.domain_insert, BasicEnv.domain_restrict]
      exact Finset.union_subset (by simpa using hxM)
        (Finset.Subset.trans Finset.inter_subset_left ((Interp.models_basicWorld_iff m Δ).1 hworld).1)
    · intro σ hσ y T hy
      by_cases hxy : y = x
      · subst y
        rw [BasicEnv.lookup_insert] at hy
        cases Option.some.inj hy
        exact hxtyped σ hσ
      · rw [BasicEnv.lookup_insert_of_ne _ _ hxy, BasicEnv.lookup_restrict] at hy
        split_ifs at hy with hyτ
        exact ((Interp.models_basicWorld_iff m Δ).1 hworld).2 σ hσ y T hy
  simp only [interpUnder, hfree, Context.erase]
  rw [henv, interpUnder_restrict «Σ» Γ (Finset.Subset.refl _)]
  exact Formula.models_and_intro hworld' (Formula.models_and_intro hΓ hbind)

end Context

def SubCtxUnder («Σ» : BasicEnv) (X : Finset Atom) (Γ₁ Γ₂ : Context) : Prop :=
  Γ₁.WellFormedUnder («Σ»).domain ∧
  Γ₂.WellFormedUnder («Σ»).domain ∧
  BasicEnv.AgreeOn X Γ₁.erase Γ₂.erase ∧
  ∀ m, Formula.Models m (Context.interpUnder «Σ» Γ₁) →
    ∃ n, Capability.Refines (m.restrict X) n ∧
      Formula.Models n (Context.interpUnder «Σ» Γ₂)

set_option hygiene false in
scoped[ContextTypes] notation:40 (name := semanticContextSubtype)
    «Σ» " ⊢ " Γ₁ " ≤[" X "] " Γ₂ =>
  ContextTypes.SubCtxUnder «Σ» X Γ₁ Γ₂

end ContextTypes
