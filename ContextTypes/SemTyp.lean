import ContextTypes.SynTyp
import Mathlib.Tactic

set_option autoImplicit false

namespace ContextTypes

/-!
# Semantic context typing

Semantic context typing interprets a bunched context as the assumptions of an
entailment and a context type at a term as its conclusion.  This module proves
one compatibility theorem for each constructor of `SynTyp`.
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

private theorem observed_subset_context {«Σ» : BasicEnv} {Γ : Context}
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

private theorem observed_subset {«Σ» : BasicEnv} {Γ : Context}
    {e : Term} {τ : ContextType} {m : Capability}
    (wf : SynTyp.WellFormed «Σ» Γ e τ)
    (hΓ : m ⊨ Context.interpUnder «Σ» Γ) :
    τ.freeAtoms ∪ e.support ⊆ m.domain :=
  Finset.Subset.trans (observed_subset_context wf) (Formula.models_scope hΓ)

private theorem models_constOver (m : Capability) (c : Constant)
    (hτ : (ContextType.over c.baseType
      (Qualifier.equal (.bound 0) (.const c))).WellFormed ∅) :
    m ⊨ ContextType.interp ∅
      (.over c.baseType (Qualifier.equal (.bound 0) (.const c)))
      (.ret (.const c)) := by
  unfold ContextType.interp
  simp only [ContextType.measure]
  apply Formula.models_and_intro
  · apply Interp.models_guard_ret_const
    · exact hτ
    · rfl
  · apply Formula.models_all_intro
    · simp only [Formula.freeAtoms_impl, Interp.freeAtoms_resultFirst,
        Interp.freeAtoms_overResultFiber, Interp.relevantEnv_idem]
      simp [Interp.relevantEnv_domain, Interp.relevantAtoms,
        ContextType.freeAtoms, Qualifier.freeAtoms, Qualifier.equal,
        Value.logicalSupport, Term.support, Value.support,
        LogicVar.freeAtoms]
    · refine ⟨∅, ?_⟩
      intro y _ F _ hFout n hExt
      let P :=
        Interp.resultFirst
            (Interp.relevantEnv ∅
              (.over c.baseType (Qualifier.equal (.bound 0) (.const c)))
              (.ret (.const c)))
            (.over c.baseType (Qualifier.equal (.bound 0) (.const c)))
            (.ret (.const c)) ⇒ᶜ
          Formula.fiber
            ((Qualifier.equal (.bound 0) (.const c)).support \ {.bound 0})
            (Interp.overResult c.baseType
              (Qualifier.equal (.bound 0) (.const c)))
      have hP : P.freeAtoms = ∅ := by
        simp only [P, Formula.freeAtoms_impl, Interp.freeAtoms_resultFirst,
          Interp.freeAtoms_overResultFiber, Interp.relevantEnv_idem]
        simp [Interp.relevantEnv_domain, Interp.relevantAtoms,
          ContextType.freeAtoms, Qualifier.freeAtoms, Qualifier.equal,
          Value.logicalSupport, Term.support, Value.support,
          LogicVar.freeAtoms]
      have hn : n.domain = {y} := by
        rw [hExt.domain_eq, hFout, Capability.restrict_domain, hP]
        simp
      change n ⊨ P.openAt 0 y
      simp only [P, Formula.openAt]
      apply Formula.models_impl_intro
      · intro x hx
        have hx' := Formula.freeAtoms_openAt_subset P 0 y hx
        rw [hP] at hx'
        rw [hn]
        simpa using hx'
      · intro p _ hres
        exact Interp.models_overResult_ret_const_openAt p c y hres

private theorem models_constUnder (m : Capability) (c : Constant)
    (hτ : (ContextType.under c.baseType
      (Qualifier.equal (.bound 0) (.const c))).WellFormed ∅) :
    m ⊨ ContextType.interp ∅
      (.under c.baseType (Qualifier.equal (.bound 0) (.const c)))
      (.ret (.const c)) := by
  unfold ContextType.interp
  simp only [ContextType.measure, ContextType.interpFuel]
  apply Formula.models_and_intro
  · apply Interp.models_guard_ret_const
    · exact hτ
    · rfl
  · apply Formula.models_all_intro
    · simp only [Formula.freeAtoms_impl, Interp.freeAtoms_resultFirst,
        Interp.freeAtoms_underResultFiber, Interp.relevantEnv_idem]
      simp [Interp.relevantEnv_domain, Interp.relevantAtoms,
        ContextType.freeAtoms, Qualifier.freeAtoms, Qualifier.equal,
        Value.logicalSupport, Term.support, Value.support,
        LogicVar.freeAtoms]
    · refine ⟨∅, ?_⟩
      intro y _ F _ hFout n hExt
      let P :=
        Interp.resultFirst
            (Interp.relevantEnv ∅
              (.under c.baseType (Qualifier.equal (.bound 0) (.const c)))
              (.ret (.const c)))
            (.under c.baseType (Qualifier.equal (.bound 0) (.const c)))
            (.ret (.const c)) ⇒ᶜ
          Formula.fiber
            ((Qualifier.equal (.bound 0) (.const c)).support \ {.bound 0})
            (Interp.underResult c.baseType
              (Qualifier.equal (.bound 0) (.const c)))
      have hP : P.freeAtoms = ∅ := by
        simp only [P, Formula.freeAtoms_impl, Interp.freeAtoms_resultFirst,
          Interp.freeAtoms_underResultFiber, Interp.relevantEnv_idem]
        simp [Interp.relevantEnv_domain, Interp.relevantAtoms,
          ContextType.freeAtoms, Qualifier.freeAtoms, Qualifier.equal,
          Value.logicalSupport, Term.support, Value.support,
          LogicVar.freeAtoms]
      have hn : n.domain = {y} := by
        rw [hExt.domain_eq, hFout, Capability.restrict_domain, hP]
        simp
      change n ⊨ P.openAt 0 y
      simp only [P, Formula.openAt]
      apply Formula.models_impl_intro
      · intro x hx
        have hx' := Formula.freeAtoms_openAt_subset P 0 y hx
        rw [hP] at hx'
        rw [hn]
        simpa using hx'
      · intro p _ hres
        exact Interp.models_underResult_ret_const_openAt p c y hres

private theorem models_constantPrecise (m : Capability) (c : Constant)
    (hτ : (ContextType.constantPrecise c).WellFormed ∅) :
    m ⊨ ContextType.interp ∅ (ContextType.constantPrecise c)
      (.ret (.const c)) := by
  unfold ContextType.interp ContextType.constantPrecise ContextType.precise
  simp only [ContextType.measure]
  apply Formula.models_and_intro
  · apply Interp.models_guard_ret_const
    · exact hτ
    · rfl
  · apply Formula.models_and_intro
    · exact models_constOver m c hτ.1
    · exact models_constUnder m c hτ.2.1

/-- A singleton binding semantically types its variable. -/
theorem var {Φ : PrimitiveContext} {«Σ» : BasicEnv}
    (x : Atom) (τ : ContextType)
    (wf : SynTyp.WellFormed «Σ» (.bind x τ) (.ret (.free x)) τ) :
    Φ ; «Σ» ; (.bind x τ) ⊨ (.ret (.free x)) ⋮ τ := by
  intro m hΓ
  have hden := Formula.models_and_elim_right hΓ
  change m ⊨ ContextType.interp
    ((«Σ».restrict τ.freeAtoms).insert x τ.erase) τ (.ret (.free x)) at hden
  have hagree : BasicEnv.AgreeOn
      (τ.freeAtoms ∪ (.ret (.free x) : Term).support)
      ((«Σ».restrict τ.freeAtoms).insert x τ.erase)
      (BasicEnv.singleton x τ.erase) := by
    intro y hy
    have hyx : y = x := by
      rcases Finset.mem_union.1 hy with hy | hy
      · exact Finset.mem_singleton.1
          (wf.2.1.freeAtoms_subset (by simpa [Context.erase] using hy))
      · change y ∈ ({x} : Finset Atom) at hy
        exact Finset.mem_singleton.1 hy
    subst y
    rw [BasicEnv.lookup_insert]
    exact (BasicEnv.lookup_singleton x τ.erase).symm
  change m ⊨ ContextType.interp (BasicEnv.singleton x τ.erase)
    τ (.ret (.free x))
  rw [← ContextType.interp_eq_of_agreeOn hagree]
  exact hden

/-- Every constant has its precise singleton context type. -/
theorem const {Φ : PrimitiveContext} {«Σ» : BasicEnv} (c : Constant)
    (wf : SynTyp.WellFormed «Σ» .empty (.ret (.const c))
      (ContextType.constantPrecise c)) :
    Φ ; «Σ» ; .empty ⊨ (.ret (.const c)) ⋮ ContextType.constantPrecise c := by
  intro m _
  change m ⊨ ContextType.interp ∅ (ContextType.constantPrecise c)
    (.ret (.const c))
  exact models_constantPrecise m c wf.2.1

/-- Semantic type subsumption is compatible with semantic typing. -/
theorem sub {Φ : PrimitiveContext} {«Σ» : BasicEnv} {Γ : Context}
    {e : Term} {τ₁ τ₂ : ContextType}
    (wf : SynTyp.WellFormed «Σ» Γ e τ₂)
    (typed : Φ ; «Σ» ; Γ ⊨ e ⋮ τ₁)
    (subtype : «Σ» ; Γ ⊢ τ₁ <: τ₂) :
    Φ ; «Σ» ; Γ ⊨ e ⋮ τ₂ := by
  intro m hΓ
  have he : Γ.erase ⊢ₑ e ⋮ τ₁.erase := by
    rw [subtype.2.2.2.1]
    exact wf.2.2
  have himpl := subtype.2.2.2.2 e he m hΓ
  exact Formula.models_impl_elim himpl (typed m hΓ)

/-- Semantic context subsumption is compatible with semantic typing. -/
theorem ctxSub {Φ : PrimitiveContext} {«Σ» : BasicEnv} {Γ₁ Γ₂ : Context}
    {e : Term} {τ : ContextType}
    (wf : SynTyp.WellFormed «Σ» Γ₁ e τ)
    (typed : Φ ; «Σ» ; Γ₂ ⊨ e ⋮ τ)
    (subcontext : «Σ» ⊢ Γ₁ ≤[e.support ∪ τ.freeAtoms] Γ₂) :
    Φ ; «Σ» ; Γ₁ ⊨ e ⋮ τ := by
  intro m hΓ₁
  let X := e.support ∪ τ.freeAtoms
  obtain ⟨n, hrefines, hΓ₂⟩ := subcontext.2.2.2 m hΓ₁
  have hn := typed n hΓ₂
  have hagree : BasicEnv.AgreeOn (τ.freeAtoms ∪ e.support)
      Γ₁.erase Γ₂.erase := by
    intro x hx
    apply subcontext.2.2.1 x
    simpa only [Finset.union_comm] using hx
  rw [ContextType.interp_eq_of_agreeOn hagree]
  have hsupport : (ContextType.interp Γ₂.erase τ e).freeAtoms ⊆ X := by
    change (ContextType.interp Γ₂.erase τ e).freeAtoms ⊆
      e.support ∪ τ.freeAtoms
    exact Finset.Subset.trans
      (ContextType.freeAtoms_interp_subset Γ₂.erase τ e)
      (by
        intro x hx
        rcases Finset.mem_union.1 hx with hx | hx
        · exact Finset.mem_union_right _ hx
        · exact Finset.mem_union_left _ hx)
  apply (Formula.models_projection X hsupport ?_).2 hn
  have hX : X ⊆ m.domain := by
    change e.support ∪ τ.freeAtoms ⊆ m.domain
    simpa only [Finset.union_comm] using observed_subset wf hΓ₁
  calc
    m.restrict X = n.restrict (m.restrict X).domain := hrefines
    _ = n.restrict X := by
      rw [Capability.restrict_domain]
      rw [Finset.inter_eq_right.2 hX]

end SemTyp

end ContextTypes
