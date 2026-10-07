import ContextTypes.BasicTyp
import ContextTypes.CtxLogic
import ContextTypes.Notation
import Mathlib.Tactic

set_option autoImplicit false

namespace ContextTypes

/-!
# Interpretation of context types

The basic operational predicates below are packaged as supported qualifiers;
they are implementation support for the type and context interpretations, not
a separate public denotational layer.
-/

section

open scoped ContextTypes

namespace Interp

/-! ## Logical instantiation used by atomic formulas -/

mutual

  /-- Instantiate logical variables visible outside `d` core binders. -/
  def instantiateValueAt (v : Value) (d : Nat) (ρ : Assignment) : Value :=
    match v with
    | .const c => .const c
    | .free x => (ρ.lookup (.free x)).getD (.free x)
    | .bound k =>
        if k < d then .bound k
        else (ρ.lookup (.bound (k - d))).getD (.bound k)
    | .lam T e => .lam T (instantiateTermAt e (d + 1) ρ)
    | .fix T v => .fix T (instantiateValueAt v (d + 1) ρ)

  /-- Instantiate logical variables visible outside `d` core binders. -/
  def instantiateTermAt (e : Term) (d : Nat) (ρ : Assignment) : Term :=
    match e with
    | .ret v => .ret (instantiateValueAt v d ρ)
    | .letE e₁ e₂ =>
        .letE (instantiateTermAt e₁ d ρ) (instantiateTermAt e₂ (d + 1) ρ)
    | .primitive op v => .primitive op (instantiateValueAt v d ρ)
    | .app v₁ v₂ => .app (instantiateValueAt v₁ d ρ) (instantiateValueAt v₂ d ρ)
    | .matchBool v e₁ e₂ =>
        .matchBool (instantiateValueAt v d ρ) (instantiateTermAt e₁ d ρ)
          (instantiateTermAt e₂ d ρ)

end

abbrev instantiateTerm (e : Term) (ρ : Assignment) : Term :=
  instantiateTermAt e 0 ρ

mutual

  @[simp] theorem instantiateValueAt_empty (v : Value) (d : Nat) :
      instantiateValueAt v d ∅ = v := by
    cases v with
    | const c => rfl
    | free x => simp [instantiateValueAt]
    | bound k => simp [instantiateValueAt]
    | lam T e => simp [instantiateValueAt, instantiateTermAt_empty]
    | fix T v => simp [instantiateValueAt, instantiateValueAt_empty]

  @[simp] theorem instantiateTermAt_empty (e : Term) (d : Nat) :
      instantiateTermAt e d ∅ = e := by
    cases e with
    | ret v => simp [instantiateTermAt, instantiateValueAt_empty]
    | letE e₁ e₂ => simp [instantiateTermAt, instantiateTermAt_empty]
    | primitive op v => simp [instantiateTermAt, instantiateValueAt_empty]
    | app v₁ v₂ => simp [instantiateTermAt, instantiateValueAt_empty]
    | matchBool v e₁ e₂ =>
        simp [instantiateTermAt, instantiateValueAt_empty,
          instantiateTermAt_empty]

end

@[simp] theorem instantiateTerm_empty (e : Term) :
    instantiateTerm e ∅ = e :=
  instantiateTermAt_empty e 0

mutual

  theorem instantiateValueAt_eq_of_agreeOn (v : Value) (d : Nat)
      {ρ σ : Assignment}
      (h : ∀ ξ, ξ ∈ v.logicSupportAt d → ρ.lookup ξ = σ.lookup ξ) :
      instantiateValueAt v d ρ = instantiateValueAt v d σ := by
    cases v with
    | const c => rfl
    | free x =>
        simp only [instantiateValueAt]
        rw [h (.free x) (by simp [Value.logicSupportAt])]
    | bound k =>
        simp only [instantiateValueAt]
        by_cases hkd : k < d
        · simp [hkd]
        · have hdk : d ≤ k := Nat.le_of_not_gt hkd
          simp only [hkd, if_false]
          rw [h (.bound (k - d)) (by
            simp [Value.logicSupportAt, boundLogicSupportAt, hdk])]
    | lam T e =>
        simp only [instantiateValueAt]
        rw [instantiateTermAt_eq_of_agreeOn e (d + 1) h]
    | fix T v =>
        simp only [instantiateValueAt]
        rw [instantiateValueAt_eq_of_agreeOn v (d + 1) h]

  theorem instantiateTermAt_eq_of_agreeOn (e : Term) (d : Nat)
      {ρ σ : Assignment}
      (h : ∀ ξ, ξ ∈ e.logicSupportAt d → ρ.lookup ξ = σ.lookup ξ) :
      instantiateTermAt e d ρ = instantiateTermAt e d σ := by
    cases e with
    | ret v =>
        simp only [instantiateTermAt]
        rw [instantiateValueAt_eq_of_agreeOn v d h]
    | letE e₁ e₂ =>
        simp only [instantiateTermAt]
        rw [instantiateTermAt_eq_of_agreeOn e₁ d (by
          intro ξ hξ
          exact h ξ (Finset.mem_union_left _ hξ))]
        rw [instantiateTermAt_eq_of_agreeOn e₂ (d + 1) (by
          intro ξ hξ
          exact h ξ (Finset.mem_union_right _ hξ))]
    | primitive op v =>
        simp only [instantiateTermAt]
        rw [instantiateValueAt_eq_of_agreeOn v d h]
    | app v₁ v₂ =>
        simp only [instantiateTermAt]
        rw [instantiateValueAt_eq_of_agreeOn v₁ d (by
          intro ξ hξ
          exact h ξ (Finset.mem_union_left _ hξ))]
        rw [instantiateValueAt_eq_of_agreeOn v₂ d (by
          intro ξ hξ
          exact h ξ (Finset.mem_union_right _ hξ))]
    | matchBool v e₁ e₂ =>
        simp only [instantiateTermAt]
        rw [instantiateValueAt_eq_of_agreeOn v d (by
          intro ξ hξ
          exact h ξ (Finset.mem_union_left _
            (Finset.mem_union_left _ hξ)))]
        rw [instantiateTermAt_eq_of_agreeOn e₁ d (by
          intro ξ hξ
          exact h ξ (Finset.mem_union_left _
            (Finset.mem_union_right _ hξ)))]
        rw [instantiateTermAt_eq_of_agreeOn e₂ d (by
          intro ξ hξ
          exact h ξ (Finset.mem_union_right _ hξ))]

end

theorem instantiateTerm_eq_of_agreeOn (e : Term) {ρ σ : Assignment}
    (h : ∀ ξ, ξ ∈ e.logicSupport → ρ.lookup ξ = σ.lookup ξ) :
    instantiateTerm e ρ = instantiateTerm e σ :=
  instantiateTermAt_eq_of_agreeOn e 0 h

theorem instantiateTerm_eq_of_restrict_eq (e : Term) (X : Finset LogicVar)
    (σ ρ : Store) (closedX : LogicVar.LocallyClosed X)
    (support : e.logicSupport ⊆ X)
    (same : σ.restrict (LogicVar.freeAtomSet X) =
      ρ.restrict (LogicVar.freeAtomSet X)) :
    instantiateTerm e σ.toAssignment = instantiateTerm e ρ.toAssignment := by
  apply instantiateTerm_eq_of_agreeOn
  intro ξ hξ
  have hξX := support hξ
  cases ξ with
  | bound k => exact (closedX k hξX).elim
  | free x =>
      simp only [Store.toAssignment_lookup_free]
      have hs := congrArg (fun s => s.lookup x) same
      have hx : x ∈ LogicVar.freeAtomSet X :=
        (LogicVar.mem_freeAtomSet_iff X x).2 hξX
      simpa [Store.lookup_restrict, hx] using hs

mutual
  theorem instantiateValueAt_eq_of_closed_support_empty (v : Value) (d : Nat)
      (ρ : Assignment) (closed : v.locallyClosedAt d) (support : v.support = ∅) :
      instantiateValueAt v d ρ = v := by
    cases v with
    | const c => rfl
    | free x => simp [Value.support] at support
    | bound k => simp only [Value.locallyClosedAt] at closed; simp [instantiateValueAt, closed]
    | lam T e =>
        simp only [instantiateValueAt]
        rw [instantiateTermAt_eq_of_closed_support_empty e (d + 1) ρ closed support]
    | fix T v =>
        simp only [instantiateValueAt]
        rw [instantiateValueAt_eq_of_closed_support_empty v (d + 1) ρ closed support]

  theorem instantiateTermAt_eq_of_closed_support_empty (e : Term) (d : Nat)
      (ρ : Assignment) (closed : e.locallyClosedAt d) (support : e.support = ∅) :
      instantiateTermAt e d ρ = e := by
    cases e with
    | ret v =>
        simp only [instantiateTermAt]
        rw [instantiateValueAt_eq_of_closed_support_empty v d ρ closed support]
    | letE e₁ e₂ =>
        have hs : e₁.support = ∅ ∧ e₂.support = ∅ := by simpa [Term.support] using support
        simp only [instantiateTermAt]
        rw [instantiateTermAt_eq_of_closed_support_empty e₁ d ρ closed.1 hs.1,
          instantiateTermAt_eq_of_closed_support_empty e₂ (d + 1) ρ closed.2 hs.2]
    | primitive op v =>
        simp only [instantiateTermAt]
        rw [instantiateValueAt_eq_of_closed_support_empty v d ρ closed support]
    | app v₁ v₂ =>
        have hs : v₁.support = ∅ ∧ v₂.support = ∅ := by simpa [Term.support] using support
        simp only [instantiateTermAt]
        rw [instantiateValueAt_eq_of_closed_support_empty v₁ d ρ closed.1 hs.1,
          instantiateValueAt_eq_of_closed_support_empty v₂ d ρ closed.2 hs.2]
    | matchBool v e₁ e₂ =>
        have hs : v.support = ∅ ∧ e₁.support = ∅ ∧ e₂.support = ∅ := by
          simpa [Term.support] using support
        simp only [instantiateTermAt]
        rw [instantiateValueAt_eq_of_closed_support_empty v d ρ closed.1 hs.1,
          instantiateTermAt_eq_of_closed_support_empty e₁ d ρ closed.2.1 hs.2.1,
          instantiateTermAt_eq_of_closed_support_empty e₂ d ρ closed.2.2 hs.2.2]
end

mutual
  theorem instantiateValueAt_substitute_of_lookup (v : Value) (d : Nat)
      {ρ : Assignment} {x : Atom} {u : Value}
      (lookup : ρ.lookup (.free x) = some u)
      (closed : u.locallyClosed) (support : u.support = ∅) :
      instantiateValueAt (v.substitute x u) d ρ = instantiateValueAt v d ρ := by
    cases v with
    | const c => rfl
    | free y =>
        by_cases h : y = x
        · subst y
          simp only [Value.substitute, instantiateValueAt, lookup, Option.getD_some]
          exact instantiateValueAt_eq_of_closed_support_empty u d ρ
            (u.locallyClosedAt_mono closed (Nat.zero_le d)) support
        · simp [Value.substitute, instantiateValueAt, h]
    | bound k => rfl
    | lam T e =>
        simp only [Value.substitute, instantiateValueAt]
        rw [instantiateTermAt_substitute_of_lookup e (d + 1) lookup closed support]
    | fix T v =>
        simp only [Value.substitute, instantiateValueAt]
        rw [instantiateValueAt_substitute_of_lookup v (d + 1) lookup closed support]

  theorem instantiateTermAt_substitute_of_lookup (e : Term) (d : Nat)
      {ρ : Assignment} {x : Atom} {u : Value}
      (lookup : ρ.lookup (.free x) = some u)
      (closed : u.locallyClosed) (support : u.support = ∅) :
      instantiateTermAt (e.substitute x u) d ρ = instantiateTermAt e d ρ := by
    cases e with
    | ret v =>
        simp only [Term.substitute, instantiateTermAt]
        rw [instantiateValueAt_substitute_of_lookup v d lookup closed support]
    | letE e₁ e₂ =>
        simp only [Term.substitute, instantiateTermAt]
        rw [instantiateTermAt_substitute_of_lookup e₁ d lookup closed support,
          instantiateTermAt_substitute_of_lookup e₂ (d + 1) lookup closed support]
    | primitive op v =>
        simp only [Term.substitute, instantiateTermAt]
        rw [instantiateValueAt_substitute_of_lookup v d lookup closed support]
    | app v₁ v₂ =>
        simp only [Term.substitute, instantiateTermAt]
        rw [instantiateValueAt_substitute_of_lookup v₁ d lookup closed support,
          instantiateValueAt_substitute_of_lookup v₂ d lookup closed support]
    | matchBool v e₁ e₂ =>
        simp only [Term.substitute, instantiateTermAt]
        rw [instantiateValueAt_substitute_of_lookup v d lookup closed support,
          instantiateTermAt_substitute_of_lookup e₁ d lookup closed support,
          instantiateTermAt_substitute_of_lookup e₂ d lookup closed support]
end

/-- Substituting a well-typed store preserves erased term typing. -/
theorem instantiateTerm_typed {Δ : BasicEnv} {e : Term} {T : SimpleType} {σ : Store}
    (typed : Δ ⊢ₑ e ⋮ T)
    (world : ∀ x U, Δ.lookup x = some U →
      ∃ u, σ.lookup x = some u ∧ BasicValTyp ∅ u U) :
    ∅ ⊢ₑ instantiateTerm e σ.toAssignment ⋮ T := by
  have aux : ∀ n (Δ : BasicEnv) (e : Term), Δ.domain.card = n →
      BasicTermTyp Δ e T →
      (∀ x U, Δ.lookup x = some U →
        ∃ u, σ.lookup x = some u ∧ BasicValTyp ∅ u U) →
      BasicTermTyp ∅ (instantiateTerm e σ.toAssignment) T := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
        intro Δ e hcard typed world
        by_cases hΔ : Δ.domain = ∅
        · have he : Δ = ∅ := by
            calc
              Δ = Δ.restrict Δ.domain := (BasicEnv.restrict_domain_self Δ).symm
              _ = ∅ := by rw [hΔ, BasicEnv.restrict_empty]
          subst Δ
          have hs : e.support = ∅ :=
            Finset.Subset.antisymm (by simpa using typed.support_subset) (Finset.empty_subset _)
          change BasicTermTyp ∅ (instantiateTermAt e 0 σ.toAssignment) T
          rw [instantiateTermAt_eq_of_closed_support_empty e 0 σ.toAssignment typed.locallyClosed hs]
          exact typed
        · obtain ⟨x, hx⟩ := Finset.nonempty_iff_ne_empty.2 hΔ
          obtain ⟨U, hU⟩ := (BasicEnv.mem_domain_iff Δ x).1 hx
          obtain ⟨u, hu, huT⟩ := world x U hU
          have husupp : u.support = ∅ :=
            Finset.Subset.antisymm (by simpa using huT.support_subset) (Finset.empty_subset _)
          have harg : BasicValTyp (Δ.erase x) u U := huT.weaken (by
            intro y V hy
            simp at hy)
          have he : (Δ.erase x).insert x U = Δ := BasicEnv.insert_erase_of_lookup hU
          have htyped : BasicTermTyp (Δ.erase x) (e.substitute x u) T := by
            rw [← he] at typed
            exact typed.substitute harg (by simp)
          have hworld : ∀ y V, (Δ.erase x).lookup y = some V →
              ∃ u, σ.lookup y = some u ∧ BasicValTyp ∅ u V := by
            intro y V hy
            by_cases hxy : y = x
            · subst y
              simp at hy
            · rw [BasicEnv.lookup_erase_of_ne Δ hxy] at hy
              exact world y V hy
          have hlt : (Δ.erase x).domain.card < n := by
            rw [BasicEnv.domain_erase, ← hcard]
            exact Finset.card_erase_lt_of_mem hx
          have hout := ih (Δ.erase x).domain.card hlt (Δ.erase x) (e.substitute x u)
            rfl htyped hworld
          change BasicTermTyp ∅ (instantiateTermAt (e.substitute x u) 0 σ.toAssignment) T at hout
          rw [instantiateTermAt_substitute_of_lookup e 0
            (ρ := σ.toAssignment) (x := x)
            (by simpa using hu) huT.locallyClosed husupp] at hout
          exact hout
  exact aux Δ.domain.card Δ e rfl typed world

/-! ## Binder insertion for result-first formulas -/

mutual

  /-- Insert one external logical binder at cutoff `d` in a value. -/
  def shiftValueAt (v : Value) (d : Nat) : Value :=
    match v with
    | .const c => .const c
    | .free x => .free x
    | .bound k => if d ≤ k then .bound (k + 1) else .bound k
    | .lam T e => .lam T (shiftTermAt e (d + 1))
    | .fix T v => .fix T (shiftValueAt v (d + 1))

  /-- Insert one external logical binder at cutoff `d` in a term. -/
  def shiftTermAt (e : Term) (d : Nat) : Term :=
    match e with
    | .ret v => .ret (shiftValueAt v d)
    | .letE e₁ e₂ => .letE (shiftTermAt e₁ d) (shiftTermAt e₂ (d + 1))
    | .primitive op v => .primitive op (shiftValueAt v d)
    | .app v₁ v₂ => .app (shiftValueAt v₁ d) (shiftValueAt v₂ d)
    | .matchBool v e₁ e₂ =>
        .matchBool (shiftValueAt v d) (shiftTermAt e₁ d) (shiftTermAt e₂ d)

end

abbrev shiftTerm (e : Term) : Term :=
  shiftTermAt e 0

mutual

  theorem shiftValueAt_eq_of_locallyClosedAt (v : Value) (d : Nat)
      (closed : v.locallyClosedAt d) : shiftValueAt v d = v := by
    cases v with
    | const c => rfl
    | free x => rfl
    | bound k =>
        simp only [Value.locallyClosedAt] at closed
        simp [shiftValueAt, Nat.not_le_of_lt closed]
    | lam T e =>
        simp only [Value.locallyClosedAt] at closed
        simp [shiftValueAt,
          shiftTermAt_eq_of_locallyClosedAt e (d + 1) closed]
    | fix T v =>
        simp only [Value.locallyClosedAt] at closed
        simp [shiftValueAt,
          shiftValueAt_eq_of_locallyClosedAt v (d + 1) closed]

  theorem shiftTermAt_eq_of_locallyClosedAt (e : Term) (d : Nat)
      (closed : e.locallyClosedAt d) : shiftTermAt e d = e := by
    cases e with
    | ret v =>
        simp only [Term.locallyClosedAt] at closed
        simp [shiftTermAt, shiftValueAt_eq_of_locallyClosedAt v d closed]
    | letE e₁ e₂ =>
        simp only [Term.locallyClosedAt] at closed
        simp [shiftTermAt,
          shiftTermAt_eq_of_locallyClosedAt e₁ d closed.1,
          shiftTermAt_eq_of_locallyClosedAt e₂ (d + 1) closed.2]
    | primitive op v =>
        simp only [Term.locallyClosedAt] at closed
        simp [shiftTermAt, shiftValueAt_eq_of_locallyClosedAt v d closed]
    | app v₁ v₂ =>
        simp only [Term.locallyClosedAt] at closed
        simp [shiftTermAt,
          shiftValueAt_eq_of_locallyClosedAt v₁ d closed.1,
          shiftValueAt_eq_of_locallyClosedAt v₂ d closed.2]
    | matchBool v e₁ e₂ =>
        simp only [Term.locallyClosedAt] at closed
        simp [shiftTermAt,
          shiftValueAt_eq_of_locallyClosedAt v d closed.1,
          shiftTermAt_eq_of_locallyClosedAt e₁ d closed.2.1,
          shiftTermAt_eq_of_locallyClosedAt e₂ d closed.2.2]

end

theorem shiftTerm_eq_of_locallyClosed (e : Term) (closed : e.locallyClosed) :
    shiftTerm e = e :=
  shiftTermAt_eq_of_locallyClosedAt e 0 closed

mutual

  @[simp] theorem shiftValueAt_support (v : Value) (d : Nat) :
      (shiftValueAt v d).support = v.support := by
    cases v with
    | const c => rfl
    | free x => rfl
    | bound k =>
        by_cases h : d ≤ k <;> simp [shiftValueAt, Value.support, h]
    | lam T e => simp [shiftValueAt, Value.support, shiftTermAt_support]
    | fix T v => simp [shiftValueAt, Value.support, shiftValueAt_support]

  @[simp] theorem shiftTermAt_support (e : Term) (d : Nat) :
      (shiftTermAt e d).support = e.support := by
    cases e with
    | ret v => simp [shiftTermAt, Term.support, shiftValueAt_support]
    | letE e₁ e₂ => simp [shiftTermAt, Term.support, shiftTermAt_support]
    | primitive op v => simp [shiftTermAt, Term.support, shiftValueAt_support]
    | app v₁ v₂ => simp [shiftTermAt, Term.support, shiftValueAt_support]
    | matchBool v e₁ e₂ =>
        simp [shiftTermAt, Term.support, shiftValueAt_support,
          shiftTermAt_support]

end


@[simp] theorem shiftTerm_support (e : Term) :
    (shiftTerm e).support = e.support :=
  shiftTermAt_support e 0

mutual

  @[simp] theorem freeAtomSet_value_logicSupportAt (v : Value) (d : Nat) :
      LogicVar.freeAtomSet (v.logicSupportAt d) = v.support := by
    cases v with
    | const c => rfl
    | free x => simp [Value.logicSupportAt, Value.support]
    | bound k =>
        by_cases h : d ≤ k <;>
          simp [Value.logicSupportAt, Value.support, boundLogicSupportAt,
            LogicVar.freeAtomSet, LogicVar.freeAtoms, h]
    | lam T e =>
        simpa [Value.logicSupportAt, Value.support] using
          freeAtomSet_term_logicSupportAt e (d + 1)
    | fix T v =>
        simpa [Value.logicSupportAt, Value.support] using
          freeAtomSet_value_logicSupportAt v (d + 1)

  @[simp] theorem freeAtomSet_term_logicSupportAt (e : Term) (d : Nat) :
      LogicVar.freeAtomSet (e.logicSupportAt d) = e.support := by
    cases e with
    | ret v =>
        simpa [Term.logicSupportAt, Term.support] using
          freeAtomSet_value_logicSupportAt v d
    | letE e₁ e₂ =>
        simp [Term.logicSupportAt, Term.support,
          freeAtomSet_term_logicSupportAt]
    | primitive op v =>
        simpa [Term.logicSupportAt, Term.support] using
          freeAtomSet_value_logicSupportAt v d
    | app v₁ v₂ =>
        simp [Term.logicSupportAt, Term.support,
          freeAtomSet_value_logicSupportAt]
    | matchBool v e₁ e₂ =>
        simp [Term.logicSupportAt, Term.support,
          freeAtomSet_value_logicSupportAt, freeAtomSet_term_logicSupportAt]

end

@[simp] theorem freeAtomSet_term_logicSupport (e : Term) :
    LogicVar.freeAtomSet e.logicSupport = e.support :=
  freeAtomSet_term_logicSupportAt e 0

mutual

theorem instantiateValueAt_store_depth (v : Value) (σ : Store) (d d' : Nat) :
    instantiateValueAt v d σ.toAssignment = instantiateValueAt v d' σ.toAssignment := by
  cases v with
  | const c => rfl
  | free x => rfl
  | bound k => simp [instantiateValueAt]
  | lam T e =>
      simp only [instantiateValueAt]
      rw [instantiateTermAt_store_depth e σ (d + 1) (d' + 1)]
  | fix T v =>
      simp only [instantiateValueAt]
      rw [instantiateValueAt_store_depth v σ (d + 1) (d' + 1)]

theorem instantiateTermAt_store_depth (e : Term) (σ : Store) (d d' : Nat) :
    instantiateTermAt e d σ.toAssignment = instantiateTermAt e d' σ.toAssignment := by
  cases e with
  | ret v =>
      simp only [instantiateTermAt]
      rw [instantiateValueAt_store_depth v σ d d']
  | letE e₁ e₂ =>
      simp only [instantiateTermAt]
      rw [instantiateTermAt_store_depth e₁ σ d d',
        instantiateTermAt_store_depth e₂ σ (d + 1) (d' + 1)]
  | primitive op v =>
      simp only [instantiateTermAt]
      rw [instantiateValueAt_store_depth v σ d d']
  | app v₁ v₂ =>
      simp only [instantiateTermAt]
      rw [instantiateValueAt_store_depth v₁ σ d d', instantiateValueAt_store_depth v₂ σ d d']
  | matchBool v e₁ e₂ =>
      simp only [instantiateTermAt]
      rw [instantiateValueAt_store_depth v σ d d',
        instantiateTermAt_store_depth e₁ σ d d', instantiateTermAt_store_depth e₂ σ d d']

end

mutual

theorem instantiateValueAt_store_openAt (v u : Value) (σ : Store) (d k : Nat)
    (closed : ∀ x, x ∈ v.support → ∀ w, σ.lookup x = some w → w.locallyClosed) :
    instantiateValueAt (v.openAt k u) d σ.toAssignment =
      (instantiateValueAt v d σ.toAssignment).openAt k (instantiateValueAt u d σ.toAssignment) := by
  cases v with
  | const c => rfl
  | free x =>
      simp only [Value.openAt, instantiateValueAt, Store.toAssignment_lookup_free]
      cases h : σ.lookup x with
      | none => rfl
      | some w =>
          simp only [Option.getD_some]
          exact (Value.openAt_eq_self_of_locallyClosed w _ k
            (closed x (by simp [Value.support]) w h)).symm
  | bound j =>
      by_cases same : j = k
      · subst j
        simp [Value.openAt, instantiateValueAt]
      · simp [Value.openAt, instantiateValueAt, same]
  | lam T e =>
      simp only [Value.openAt, instantiateValueAt]
      rw [instantiateTermAt_store_openAt e u σ (d + 1) (k + 1) closed,
        instantiateValueAt_store_depth u σ (d + 1) d]
  | fix T v =>
      simp only [Value.openAt, instantiateValueAt]
      rw [instantiateValueAt_store_openAt v u σ (d + 1) (k + 1) closed,
        instantiateValueAt_store_depth u σ (d + 1) d]

theorem instantiateTermAt_store_openAt (e : Term) (u : Value) (σ : Store) (d k : Nat)
    (closed : ∀ x, x ∈ e.support → ∀ w, σ.lookup x = some w → w.locallyClosed) :
    instantiateTermAt (e.openAt k u) d σ.toAssignment =
      (instantiateTermAt e d σ.toAssignment).openAt k (instantiateValueAt u d σ.toAssignment) := by
  cases e with
  | ret v =>
      simp only [Term.openAt, instantiateTermAt]
      rw [instantiateValueAt_store_openAt v u σ d k closed]
  | letE e₁ e₂ =>
      simp only [Term.openAt, instantiateTermAt]
      rw [instantiateTermAt_store_openAt e₁ u σ d k
        (fun x hx => closed x (Finset.mem_union_left _ hx)),
        instantiateTermAt_store_openAt e₂ u σ (d + 1) (k + 1)
          (fun x hx => closed x (Finset.mem_union_right _ hx)),
        instantiateValueAt_store_depth u σ (d + 1) d]
  | primitive op v =>
      simp only [Term.openAt, instantiateTermAt]
      rw [instantiateValueAt_store_openAt v u σ d k closed]
  | app v₁ v₂ =>
      simp only [Term.openAt, instantiateTermAt]
      rw [instantiateValueAt_store_openAt v₁ u σ d k
        (fun x hx => closed x (Finset.mem_union_left _ hx)),
        instantiateValueAt_store_openAt v₂ u σ d k
          (fun x hx => closed x (Finset.mem_union_right _ hx))]
  | matchBool v e₁ e₂ =>
      simp only [Term.openAt, instantiateTermAt]
      rw [instantiateValueAt_store_openAt v u σ d k
        (fun x hx => closed x (Finset.mem_union_left _ (Finset.mem_union_left _ hx))),
        instantiateTermAt_store_openAt e₁ u σ d k
          (fun x hx => closed x (Finset.mem_union_left _ (Finset.mem_union_right _ hx))),
        instantiateTermAt_store_openAt e₂ u σ d k
          (fun x hx => closed x (Finset.mem_union_right _ hx))]

end

/-- Store instantiation only depends on free program atoms, independently
of the logical binder depth or any unused bindings. -/
theorem instantiateTermAt_store_eq_of_restrict_eq (e : Term) (d : Nat) (σ ρ : Store)
    (same : σ.restrict e.support = ρ.restrict e.support) :
    instantiateTermAt e d σ.toAssignment = instantiateTermAt e d ρ.toAssignment := by
  apply instantiateTermAt_eq_of_agreeOn
  intro ξ hξ
  cases ξ with
  | bound j => simp
  | free x =>
      have hx := (LogicVar.mem_freeAtomSet_iff (e.logicSupportAt d) x).2 hξ
      rw [freeAtomSet_term_logicSupportAt] at hx
      have h := congrArg (fun s : Store => s.lookup x) same
      simpa only [Store.toAssignment_lookup_free, Store.lookup_restrict, if_pos hx] using h

/-- Opening a let body with the name of an intermediate result agrees with
opening its store-instantiated body with the actual value. -/
theorem instantiateTerm_openAt_of_lookup {e : Term} {σ : Store} {x : Atom} {v : Value}
    (closed : ∀ y, y ∈ e.support → ∀ w, σ.lookup y = some w → w.locallyClosed)
    (lookup : σ.lookup x = some v) :
    instantiateTerm (e.openAt 0 (.free x)) σ.toAssignment =
      (instantiateTermAt e 1 σ.toAssignment).openAt 0 v := by
  change instantiateTermAt (e.openAt 0 (.free x)) 0 σ.toAssignment = _
  rw [instantiateTermAt_store_openAt e (.free x) σ 0 0 closed]
  simp only [instantiateValueAt, Store.toAssignment_lookup_free, lookup, Option.getD_some]
  rw [instantiateTermAt_store_depth e σ 0 1]

/-- A named result added to a store instantiates an opened body exactly as
the corresponding operational let reduction does. -/
theorem instantiateTerm_openAt_merge_result (e : Term) (σ : Store) (X : Finset Atom)
    (x : Atom) (v : Value) (scope : X ⊆ σ.domain) (support : e.support ⊆ X)
    (fresh : x ∉ X)
    (closed : ∀ y, y ∈ e.support → ∀ w, σ.lookup y = some w → w.locallyClosed) :
    instantiateTerm (e.openAt 0 (.free x))
      ((σ.restrict X).merge (Store.singleton x v)).toAssignment =
        (instantiateTermAt e 1 σ.toAssignment).openAt 0 v := by
  let ρ := (σ.restrict X).merge (Store.singleton x v)
  have hdom : (σ.restrict X).domain = X := by
    rw [Store.domain_restrict, Finset.inter_eq_right.2 scope]
  have same : ρ.restrict e.support = σ.restrict e.support := by
    have hbase : ρ.restrict X = σ.restrict X := Store.restrict_merge_left_full hdom
    have h := congrArg (fun s : Store => s.restrict e.support) hbase
    simpa only [Store.restrict_restrict, Finset.inter_eq_right.2 support] using h
  have hclosed : ∀ y, y ∈ e.support → ∀ w, ρ.lookup y = some w → w.locallyClosed := by
    intro y hy w hw
    have h := congrArg (fun s : Store => s.lookup y) same
    have look : ρ.lookup y = σ.lookup y := by
      simpa only [Store.lookup_restrict, if_pos hy] using h
    exact closed y hy w (look ▸ hw)
  have lookup : ρ.lookup x = some v := by
    rw [Store.lookup_merge_right _ _ (by rw [hdom]; exact fresh), Store.lookup_singleton]
  rw [instantiateTerm_openAt_of_lookup hclosed lookup,
    instantiateTermAt_store_eq_of_restrict_eq e 1 ρ σ same]

mutual

  theorem valueLogicSupportAt_locallyClosed (v : Value) (d : Nat)
      (closed : v.locallyClosedAt d) :
      LogicVar.LocallyClosed (v.logicSupportAt d) := by
    intro k hk
    cases v with
    | const c => simp [Value.logicSupportAt] at hk
    | free x => simp [Value.logicSupportAt] at hk
    | bound j =>
        simp only [Value.locallyClosedAt] at closed
        simp [Value.logicSupportAt, boundLogicSupportAt,
          Nat.not_le_of_lt closed] at hk
    | lam T e =>
        exact termLogicSupportAt_locallyClosed e (d + 1) closed k hk
    | fix T v =>
        exact valueLogicSupportAt_locallyClosed v (d + 1) closed k hk

  theorem termLogicSupportAt_locallyClosed (e : Term) (d : Nat)
      (closed : e.locallyClosedAt d) :
      LogicVar.LocallyClosed (e.logicSupportAt d) := by
    intro k hk
    cases e with
    | ret v => exact valueLogicSupportAt_locallyClosed v d closed k hk
    | letE e₁ e₂ =>
        rcases Finset.mem_union.1 hk with hk | hk
        · exact termLogicSupportAt_locallyClosed e₁ d closed.1 k hk
        · exact termLogicSupportAt_locallyClosed e₂ (d + 1) closed.2 k hk
    | primitive op v =>
        exact valueLogicSupportAt_locallyClosed v d closed k hk
    | app v₁ v₂ =>
        rcases Finset.mem_union.1 hk with hk | hk
        · exact valueLogicSupportAt_locallyClosed v₁ d closed.1 k hk
        · exact valueLogicSupportAt_locallyClosed v₂ d closed.2 k hk
    | matchBool v e₁ e₂ =>
        rcases Finset.mem_union.1 hk with hk | hk
        · rcases Finset.mem_union.1 hk with hk | hk
          · exact valueLogicSupportAt_locallyClosed v d closed.1 k hk
          · exact termLogicSupportAt_locallyClosed e₁ d closed.2.1 k hk
        · exact termLogicSupportAt_locallyClosed e₂ d closed.2.2 k hk

end

theorem termLogicSupport_locallyClosed (e : Term) (closed : e.locallyClosed) :
    LogicVar.LocallyClosed e.logicSupport :=
  termLogicSupportAt_locallyClosed e 0 closed

theorem contextTypeSupportAt_locallyClosed {τ : ContextType} {d : Nat}
    (closed : τ.LocallyClosedAt d) :
    LogicVar.LocallyClosed (τ.supportAt d) := by
  intro k hk
  induction τ generalizing d with
  | «over» b q =>
      simp only [ContextType.supportAt] at hk
      obtain ⟨ξ, hξ, hξk⟩ := Finset.mem_biUnion.1 hk
      cases ξ with
      | free x => simp [LogicVar.atDepth] at hξk
      | bound n =>
          by_cases hdn : d + 1 ≤ n
          · have hn := closed n hξ
            omega
          · simp [LogicVar.atDepth, hdn] at hξk
  | under b q =>
      simp only [ContextType.supportAt] at hk
      obtain ⟨ξ, hξ, hξk⟩ := Finset.mem_biUnion.1 hk
      cases ξ with
      | free x => simp [LogicVar.atDepth] at hξk
      | bound n =>
          by_cases hdn : d + 1 ≤ n
          · have hn := closed n hξ
            omega
          · simp [LogicVar.atDepth, hdn] at hξk
  | inter τ₁ τ₂ ih₁ ih₂ =>
      rcases Finset.mem_union.1 hk with hk | hk
      · exact ih₁ closed.1 hk
      · exact ih₂ closed.2 hk
  | union τ₁ τ₂ ih₁ ih₂ =>
      rcases Finset.mem_union.1 hk with hk | hk
      · exact ih₁ closed.1 hk
      · exact ih₂ closed.2 hk
  | sum τ₁ τ₂ ih₁ ih₂ =>
      rcases Finset.mem_union.1 hk with hk | hk
      · exact ih₁ closed.1 hk
      · exact ih₂ closed.2 hk
  | arrow τ₁ τ₂ ih₁ ih₂ =>
      rcases Finset.mem_union.1 hk with hk | hk
      · exact ih₁ closed.1 hk
      · exact ih₂ closed.2 hk
  | wand τ₁ τ₂ ih₁ ih₂ =>
      rcases Finset.mem_union.1 hk with hk | hk
      · exact ih₁ closed.1 hk
      · exact ih₂ closed.2 hk
  | persist τ ih => exact ih closed hk

mutual

  theorem shiftValueAt_logicSupportAt (v : Value) (d : Nat) :
      (shiftValueAt v d).logicSupportAt d =
        (v.logicSupportAt d).image (LogicVar.shiftFrom 0) := by
    cases v with
    | const c => rfl
    | free x => simp [shiftValueAt, Value.logicSupportAt, LogicVar.shiftFrom]
    | bound k =>
        by_cases h : d ≤ k
        · have h' : d ≤ k + 1 := Nat.le_trans h (Nat.le_succ k)
          simp [shiftValueAt, Value.logicSupportAt, boundLogicSupportAt,
            LogicVar.shiftFrom, h, h']
          all_goals omega
        · simp [shiftValueAt, Value.logicSupportAt, boundLogicSupportAt,
            h]
    | lam T e =>
        simpa [shiftValueAt, Value.logicSupportAt] using
          shiftTermAt_logicSupportAt e (d + 1)
    | fix T v =>
        simpa [shiftValueAt, Value.logicSupportAt] using
          shiftValueAt_logicSupportAt v (d + 1)

  theorem shiftTermAt_logicSupportAt (e : Term) (d : Nat) :
      (shiftTermAt e d).logicSupportAt d =
        (e.logicSupportAt d).image (LogicVar.shiftFrom 0) := by
    cases e with
    | ret v =>
        simpa [shiftTermAt, Term.logicSupportAt] using
          shiftValueAt_logicSupportAt v d
    | letE e₁ e₂ =>
        simp [shiftTermAt, Term.logicSupportAt, shiftTermAt_logicSupportAt,
          Finset.image_union]
    | primitive op v =>
        simpa [shiftTermAt, Term.logicSupportAt] using
          shiftValueAt_logicSupportAt v d
    | app v₁ v₂ =>
        simp [shiftTermAt, Term.logicSupportAt, shiftValueAt_logicSupportAt,
          Finset.image_union]
    | matchBool v e₁ e₂ =>
        simp [shiftTermAt, Term.logicSupportAt, shiftValueAt_logicSupportAt,
          shiftTermAt_logicSupportAt, Finset.image_union]

end

@[simp] theorem shiftTerm_logicSupport (e : Term) :
    (shiftTerm e).logicSupport =
      e.logicSupport.image (LogicVar.shiftFrom 0) :=
  shiftTermAt_logicSupportAt e 0

/-! ## Supported atomic predicates -/

def storeTyped («Σ» : LogicVar → Option SimpleType) (ρ : Assignment) : Prop :=
  ∀ ξ T, «Σ» ξ = some T →
    ∃ v, ρ.lookup ξ = some v ∧ BasicValTyp ∅ v T

def basicWorldQualifier (Δ : BasicEnv) : Qualifier where
  support := Δ.domain.image LogicVar.free
  holds := fun ρ =>
    storeTyped
      (fun ξ => match ξ with
        | .bound _ => none
        | .free x => Δ.lookup x)
      ρ.assignment

def basicWorld (Δ : BasicEnv) : Formula :=
  Formula.fiberAtom (basicWorldQualifier Δ)

def wellFormedQualifier (d : Nat) (Δ : BasicEnv)
    (τ : ContextType) : Qualifier where
  support := Δ.domain.image LogicVar.free
  holds := fun _ => τ.WellFormedAt d Δ.domain

def wellFormed (d : Nat) (Δ : BasicEnv) (τ : ContextType) : Formula :=
  Formula.fiberAtom (wellFormedQualifier d Δ τ)

def basicTypingQualifier (Δ : BasicEnv) (e : Term)
    (T : SimpleType) : Qualifier where
  support := Δ.domain.image LogicVar.free ∪ e.logicSupport
  holds := fun ρ =>
    e.support ⊆ Δ.domain ∧
    storeTyped
      (fun ξ => match ξ with
        | .bound _ => none
        | .free x => Δ.lookup x)
      ρ.assignment ∧
    BasicTermTyp ∅ (instantiateTerm e ρ.assignment) T

def basicTyping (Δ : BasicEnv) (e : Term) (T : SimpleType) : Formula :=
  Formula.fiberAtom (basicTypingQualifier Δ e T)

def totalQualifier (e : Term) : Qualifier where
  support := e.logicSupport
  holds := fun ρ => (instantiateTerm e ρ.assignment).MustTerminate

def total (e : Term) : Formula :=
  Formula.fiberAtom (totalQualifier e)

def resultQualifier (e : Term) (ξ : LogicVar) : Qualifier where
  support := e.logicSupport ∪ {ξ}
  holds := fun ρ =>
    ξ ∉ e.logicSupport ∧
    ∃ v, ρ.assignment.lookup ξ = some v ∧
      (instantiateTerm e ρ.assignment).reaches v

def resultAt (X : Finset LogicVar) (e : Term) (ξ : LogicVar) : Formula :=
  .fiber X (.atom (resultQualifier e ξ))

def result (e : Term) (ξ : LogicVar) : Formula :=
  resultAt e.logicSupport e ξ

def resultBasicTyping (b : BaseType) : Formula :=
  basicTyping ∅ (.ret (.bound 0)) (.base b)

def overResult (b : BaseType) (q : Qualifier) : Formula :=
  🄾 (Atom(q) ∧ᶜ resultBasicTyping b)

def underResult (b : BaseType) (q : Qualifier) : Formula :=
  🅄 (Atom(q) ∧ᶜ resultBasicTyping b)

/-! ## Relevant environments and guards -/

def relevantAtoms (τ : ContextType) (e : Term) : Finset Atom :=
  τ.freeAtoms ∪ e.support

def relevantEnv (Δ : BasicEnv) (τ : ContextType) (e : Term) : BasicEnv :=
  Δ.restrict (relevantAtoms τ e)

@[simp] theorem relevantEnv_domain (Δ : BasicEnv) (τ : ContextType)
    (e : Term) :
    (relevantEnv Δ τ e).domain = Δ.domain ∩ relevantAtoms τ e := by
  simp [relevantEnv]

@[simp] theorem relevantEnv_idem (Δ : BasicEnv) (τ : ContextType)
    (e : Term) :
    relevantEnv (relevantEnv Δ τ e) τ e = relevantEnv Δ τ e := by
  simp [relevantEnv, BasicEnv.restrict_restrict]

@[simp] theorem relevantEnv_persist (Δ : BasicEnv) (τ : ContextType)
    (e : Term) :
    relevantEnv Δ (.persist τ) e = relevantEnv Δ τ e :=
  rfl

theorem relevantEnv_minimal (Δ : BasicEnv) (τ : ContextType) (e : Term) :
    relevantEnv Δ τ e = relevantEnv (Δ.restrict (relevantAtoms τ e)) τ e := by
  simpa [relevantEnv] using (relevantEnv_idem Δ τ e).symm

/-- Logical variables retained by the relevant environment.  Free variables
come from the restricted basic environment; ambient bound variables are
tracked directly because `BasicEnv` is atom-keyed. -/
def relevantSupport (Δ : BasicEnv) (τ : ContextType)
    (e : Term) : Finset LogicVar :=
  (relevantEnv Δ τ e).domain.image LogicVar.free ∪
    (τ.support ∪ e.logicSupport).biUnion fun ξ =>
      match ξ with
      | .bound k => {.bound k}
      | .free _ => ∅

theorem relevantSupport_locallyClosed (Δ : BasicEnv) (τ : ContextType)
    (e : Term) (closedτ : τ.LocallyClosed) (closedE : e.locallyClosed) :
    LogicVar.LocallyClosed (relevantSupport Δ τ e) := by
  intro k hk
  simp only [relevantSupport, Finset.mem_union, Finset.mem_image,
    Finset.mem_biUnion] at hk
  rcases hk with ⟨x, _, same⟩ | ⟨ξ, hξ, hξk⟩
  · cases same
  · cases ξ with
    | free x => simp at hξk
    | bound n =>
        simp only [Finset.mem_singleton] at hξk
        cases hξk
        rcases hξ with hξ | hξ
        · exact contextTypeSupportAt_locallyClosed closedτ k hξ
        · exact termLogicSupport_locallyClosed e closedE k hξ

theorem logicSupport_subset_relevantSupport (Δ : BasicEnv) (τ : ContextType)
    (e : Term) (support : e.support ⊆ Δ.domain) :
    e.logicSupport ⊆ relevantSupport Δ τ e := by
  intro ξ hξ
  cases ξ with
  | bound k =>
      apply Finset.mem_union_right
      apply Finset.mem_biUnion.2
      exact ⟨.bound k, Finset.mem_union_right _ hξ, by simp⟩
  | free x =>
      apply Finset.mem_union_left
      apply Finset.mem_image.2
      refine ⟨x, ?_, rfl⟩
      rw [relevantEnv_domain]
      apply Finset.mem_inter.2
      have hx : x ∈ e.support := by
        rw [← freeAtomSet_term_logicSupport e,
          LogicVar.mem_freeAtomSet_iff]
        exact hξ
      exact ⟨support hx, Finset.mem_union_right _ hx⟩

/-- Result formula under a fresh outer logical binder. -/
def resultFirst (Δ : BasicEnv) (τ : ContextType) (e : Term) : Formula :=
  resultAt ((relevantSupport Δ τ e).image (LogicVar.shiftFrom 0))
    (shiftTerm e) (.bound 0)

def guard (d : Nat) (Δ : BasicEnv) (τ : ContextType) (e : Term) : Formula :=
  wellFormed d Δ τ ∧ᶜ
    (basicWorld Δ ∧ᶜ (basicTyping Δ e τ.erase ∧ᶜ total e))

@[simp] theorem guard_persist (d : Nat) (Δ : BasicEnv) (τ : ContextType)
    (e : Term) : guard d Δ (.persist τ) e = guard d Δ τ e :=
  rfl

@[simp] theorem freeAtoms_basicWorld (Δ : BasicEnv) :
    (basicWorld Δ).freeAtoms = Δ.domain := by
  rw [basicWorld, Formula.freeAtoms_fiberAtom]
  change LogicVar.freeAtomSet (Δ.domain.image LogicVar.free) = Δ.domain
  exact Formula.LogicVar.freeAtomSet_image_free Δ.domain

theorem models_wellFormed_iff (m : Capability) (d : Nat)
    (Δ : BasicEnv) (τ : ContextType) :
    m ⊨ wellFormed d Δ τ ↔
      Δ.domain ⊆ m.domain ∧ τ.WellFormedAt d Δ.domain := by
  rw [wellFormed]
  constructor
  · intro h
    obtain ⟨_, scope, holds⟩ :=
      (Formula.models_fiberAtom_iff m (wellFormedQualifier d Δ τ)).1 h
    refine ⟨?_, ?_⟩
    · simpa [wellFormedQualifier, Qualifier.freeAtoms,
        LogicVar.freeAtoms] using scope
    · obtain ⟨σ, hσ⟩ := m.nonempty
      obtain ⟨_, ρ, hρ, _⟩ := holds σ hσ
      exact hρ
  · rintro ⟨scope, wf⟩
    apply (Formula.models_fiberAtom_iff m
      (wellFormedQualifier d Δ τ)).2
    refine ⟨?_, ?_, ?_⟩
    · intro k hk
      simp [wellFormedQualifier] at hk
    · simpa [wellFormedQualifier, Qualifier.freeAtoms,
        LogicVar.freeAtoms] using scope
    · intro σ hσ
      have hdom :
          (σ.restrict (wellFormedQualifier d Δ τ).freeAtoms).domain =
            (wellFormedQualifier d Δ τ).freeAtoms := by
        rw [Store.domain_restrict, m.mem_domain hσ,
          Finset.inter_eq_right.2]
        simpa [wellFormedQualifier, Qualifier.freeAtoms,
          LogicVar.freeAtoms] using scope
      let ρ : AssignmentOn (wellFormedQualifier d Δ τ).support :=
        { assignment := (σ.restrict Δ.domain).toAssignment
          domain_eq := by
            rw [Store.toAssignment_domain, Store.domain_restrict,
              m.mem_domain hσ, Finset.inter_eq_right.2 scope]
            rfl }
      refine ⟨hdom, ρ, wf, ?_⟩
      intro x
      simp [ρ, wellFormedQualifier, Qualifier.freeAtoms,
        LogicVar.freeAtoms]

theorem wellFormed_openAt_eq (d : Nat) (Δ : BasicEnv)
    (τ : ContextType) (k : Nat) (y : Atom) (fresh : y ∉ Δ.domain) :
    (wellFormed d Δ τ).openAt k y = wellFormed d Δ τ := by
  let q := wellFormedQualifier d Δ τ
  have hbound : LogicVar.bound k ∉ q.support := by
    simp [q, wellFormedQualifier]
  have hfree : LogicVar.free y ∉ q.support := by
    simpa [q, wellFormedQualifier] using fresh
  have hq : q.openAt k y = q := q.openAt_fresh k y hbound hfree
  have hsupp : LogicVar.openSupport k y q.support = q.support := by
    apply LogicVar.openSupport_eq_self_of_fresh
    · exact hbound
    · exact hfree
  simp only [wellFormed, Formula.fiberAtom, Formula.openAt]
  change Formula.fiber (LogicVar.openSupport k y q.support)
      (Formula.atom (q.openAt k y)) = Formula.fiber q.support (Formula.atom q)
  rw [hsupp, hq]

theorem models_wellFormed_shift_openAt {m : Capability} {d : Nat}
    {Δ : BasicEnv} {τ : ContextType} {k : Nat} {y : Atom}
    (fresh : y ∉ Δ.domain) (h : m ⊨ wellFormed d Δ τ) :
    m ⊨ (wellFormed (d + 1) Δ (τ.shiftFrom k)).openAt 0 y := by
  rw [wellFormed_openAt_eq (d + 1) Δ (τ.shiftFrom k) 0 y fresh]
  apply (models_wellFormed_iff m (d + 1) Δ (τ.shiftFrom k)).2
  exact ⟨(models_wellFormed_iff m d Δ τ).1 h |>.1,
    ((models_wellFormed_iff m d Δ τ).1 h |>.2).shiftFrom k⟩

theorem basicWorld_openAt_eq (Δ : BasicEnv) (k : Nat) (y : Atom)
    (fresh : y ∉ Δ.domain) :
    (basicWorld Δ).openAt k y = basicWorld Δ := by
  let q := basicWorldQualifier Δ
  have hbound : LogicVar.bound k ∉ q.support := by
    simp [q, basicWorldQualifier]
  have hfree : LogicVar.free y ∉ q.support := by
    simpa [q, basicWorldQualifier] using fresh
  have hq : q.openAt k y = q := q.openAt_fresh k y hbound hfree
  have hsupp : LogicVar.openSupport k y q.support = q.support := by
    apply LogicVar.openSupport_eq_self_of_fresh
    · exact hbound
    · exact hfree
  simp only [basicWorld, Formula.fiberAtom, Formula.openAt]
  change Formula.fiber (LogicVar.openSupport k y q.support)
      (Formula.atom (q.openAt k y)) = Formula.fiber q.support (Formula.atom q)
  rw [hsupp, hq]

theorem models_basicWorld_iff (m : Capability) (Δ : BasicEnv) :
    m ⊨ basicWorld Δ ↔
      Δ.domain ⊆ m.domain ∧
        ∀ σ, σ ∈ m → ∀ x T, Δ.lookup x = some T →
          ∃ v, σ.lookup x = some v ∧ BasicValTyp ∅ v T := by
  rw [basicWorld]
  constructor
  · intro h
    obtain ⟨_, scope, holds⟩ :=
      (Formula.models_fiberAtom_iff m (basicWorldQualifier Δ)).1 h
    refine ⟨?_, ?_⟩
    · simpa [basicWorldQualifier, Qualifier.freeAtoms,
        LogicVar.freeAtoms] using scope
    · intro σ hσ x T hx
      have hs := holds σ hσ
      obtain ⟨_, ρ, hρ, look⟩ := hs
      obtain ⟨v, hv, typed⟩ := hρ (.free x) T (by simpa using hx)
      refine ⟨v, ?_, typed⟩
      rw [← hv, look x]
      rw [show (basicWorldQualifier Δ).freeAtoms = Δ.domain by
        change LogicVar.freeAtomSet (Δ.domain.image LogicVar.free) = Δ.domain
        exact Formula.LogicVar.freeAtomSet_image_free Δ.domain]
      rw [Store.lookup_restrict, if_pos]
      change x ∈ Δ.domain
      exact Finmap.mem_iff.mpr ⟨T, hx⟩
  · rintro ⟨scope, typed⟩
    apply (Formula.models_fiberAtom_iff m (basicWorldQualifier Δ)).2
    refine ⟨?_, ?_, ?_⟩
    · intro k hk
      simp [basicWorldQualifier] at hk
    · simpa [basicWorldQualifier, Qualifier.freeAtoms,
        LogicVar.freeAtoms] using scope
    · intro σ hσ
      have hdom : (σ.restrict (basicWorldQualifier Δ).freeAtoms).domain =
          (basicWorldQualifier Δ).freeAtoms := by
        rw [Store.domain_restrict, m.mem_domain hσ,
          Finset.inter_eq_right.2]
        simpa [basicWorldQualifier, Qualifier.freeAtoms,
          LogicVar.freeAtoms] using scope
      let ρ : AssignmentOn (basicWorldQualifier Δ).support :=
        { assignment := (σ.restrict Δ.domain).toAssignment
          domain_eq := by
            rw [Store.toAssignment_domain, Store.domain_restrict,
              m.mem_domain hσ, Finset.inter_eq_right.2 scope]
            rfl }
      refine ⟨hdom, ρ, ?_, ?_⟩
      · intro ξ T hT
        cases ξ with
        | bound k => simp at hT
        | free x =>
            obtain ⟨v, hv, hvT⟩ := typed σ hσ x T hT
            refine ⟨v, ?_, hvT⟩
            have hx : x ∈ Δ.domain := Finmap.mem_iff.mpr ⟨T, hT⟩
            simp [ρ, Store.lookup_restrict, hx, hv]
      · intro x
        simp [ρ, basicWorldQualifier, Qualifier.freeAtoms,
          LogicVar.freeAtoms]

/-- Removing basic-environment bindings preserves the remaining world facts. -/
theorem models_basicWorld_restrict {m : Capability} {Δ : BasicEnv}
    (X : Finset Atom) (h : m ⊨ basicWorld Δ) :
    m ⊨ basicWorld (Δ.restrict X) := by
  obtain ⟨scope, typed⟩ := (models_basicWorld_iff m Δ).1 h
  apply (models_basicWorld_iff m (Δ.restrict X)).2
  refine ⟨?_, ?_⟩
  · rw [BasicEnv.domain_restrict]
    exact Finset.Subset.trans Finset.inter_subset_left scope
  intro σ hσ x T hx
  rw [BasicEnv.lookup_restrict] at hx
  split_ifs at hx with hxX
  exact typed σ hσ x T hx

theorem models_basicTyping_ret_free {m : Capability} {Δ : BasicEnv}
    {y : Atom} {T : SimpleType} (hworld : m ⊨ basicWorld Δ)
    (hlookup : Δ.lookup y = some T) :
    m ⊨ basicTyping Δ (.ret (.free y)) T := by
  unfold basicTyping Formula.fiberAtom
  let q := basicTypingQualifier Δ (.ret (.free y)) T
  change m ⊨ Formula.fiberAtom q
  have hyΔ : y ∈ Δ.domain := Finmap.mem_iff.mpr ⟨T, hlookup⟩
  have hqsupp : q.support = Δ.domain.image LogicVar.free := by
    simp only [q, basicTypingQualifier, Term.logicSupportAt,
      Value.logicSupportAt, Finset.union_eq_left]
    intro ξ hξ
    have hξy : ξ = .free y := by simpa using hξ
    subst ξ
    exact Finset.mem_image.2 ⟨y, hyΔ, rfl⟩
  have hqfree : q.freeAtoms = Δ.domain := by
    change LogicVar.freeAtomSet q.support = Δ.domain
    rw [hqsupp]
    exact Formula.LogicVar.freeAtomSet_image_free Δ.domain
  obtain ⟨scope, typed⟩ := (models_basicWorld_iff m Δ).1 hworld
  apply (Formula.models_fiberAtom_iff m q).2
  refine ⟨?_, ?_, ?_⟩
  · intro k hk
    rw [hqsupp] at hk
    simp at hk
  · simpa [hqfree] using scope
  · intro σ hσ
    let s := σ.restrict q.freeAtoms
    have hsdom : s.domain = q.freeAtoms := by
      simp only [s]
      rw [Store.domain_restrict, m.mem_domain hσ,
        Finset.inter_eq_right.2]
      simpa [hqfree] using scope
    let ρ : AssignmentOn q.support :=
      { assignment := s.toAssignment
        domain_eq := by
          rw [Store.toAssignment_domain, hsdom, hqfree, hqsupp] }
    refine ⟨hsdom, ρ, ?_, ?_⟩
    · change ((.ret (.free y) : Term).support ⊆ Δ.domain) ∧
        storeTyped
          (fun ξ => match ξ with
            | .bound _ => none
            | .free x => Δ.lookup x)
          ρ.assignment ∧
        BasicTermTyp ∅
          (instantiateTerm (.ret (.free y)) ρ.assignment) T
      refine ⟨by simpa [Term.support, Value.support], ?_, ?_⟩
      · intro ξ U hU
        cases ξ with
        | bound k => simp at hU
        | free x =>
            obtain ⟨v, hv, hvU⟩ := typed σ hσ x U hU
            refine ⟨v, ?_, hvU⟩
            have hx : x ∈ Δ.domain := Finmap.mem_iff.mpr ⟨U, hU⟩
            simp [ρ, s, hqfree, Store.lookup_restrict, hx, hv]
      · obtain ⟨v, hv, hvT⟩ := typed σ hσ y T hlookup
        simpa [ρ, s, hqfree, Store.lookup_restrict, hyΔ, hv,
          instantiateTerm, instantiateTermAt, instantiateValueAt] using
          BasicTermTyp.ret hvT
    · intro x
      simp [ρ, s]

theorem models_total_ret_free {m : Capability} {Δ : BasicEnv}
    {y : Atom} {T : SimpleType} (hworld : m ⊨ basicWorld Δ)
    (hlookup : Δ.lookup y = some T) :
    m ⊨ total (.ret (.free y)) := by
  have hbasic := models_basicTyping_ret_free hworld hlookup
  unfold total Formula.fiberAtom
  let q := totalQualifier (.ret (.free y))
  change m ⊨ Formula.fiberAtom q
  have hqsupp : q.support = {.free y} := by
    simp [q, totalQualifier, Term.logicSupportAt, Value.logicSupportAt]
  have hqfree : q.freeAtoms = {y} := by
    change LogicVar.freeAtomSet q.support = {y}
    rw [hqsupp]
    simp
  have hy : y ∈ m.domain := by
    apply (models_basicWorld_iff m Δ).1 hworld |>.1
    exact Finmap.mem_iff.mpr ⟨T, hlookup⟩
  apply (Formula.models_fiberAtom_iff m q).2
  refine ⟨?_, ?_, ?_⟩
  · intro k hk
    rw [hqsupp] at hk
    simp at hk
  · simpa [hqfree] using hy
  · intro σ hσ
    obtain ⟨v, hv, hvT⟩ :=
      (models_basicWorld_iff m Δ).1 hworld |>.2 σ hσ y T hlookup
    let s := σ.restrict q.freeAtoms
    have hsdom : s.domain = q.freeAtoms := by
      simp only [s]
      rw [Store.domain_restrict, m.mem_domain hσ,
        Finset.inter_eq_right.2]
      simpa [hqfree] using hy
    let ρ : AssignmentOn q.support :=
      { assignment := s.toAssignment
        domain_eq := by
          rw [Store.toAssignment_domain, hsdom, hqfree, hqsupp]
          simp }
    refine ⟨hsdom, ρ, ?_, ?_⟩
    · change (instantiateTerm (.ret (.free y)) ρ.assignment).MustTerminate
      simpa [ρ, s, hqfree, Store.lookup_restrict, hv,
        instantiateTerm, instantiateTermAt, instantiateValueAt] using
        Term.MustTerminate.ret v hvT.locallyClosed
    · intro x
      simp [ρ, s]

theorem models_basicTyping_term {m : Capability} {Δ : BasicEnv}
    {e : Term} {T : SimpleType} (closed : e.locallyClosed)
    (h : m ⊨ basicTyping Δ e T) {σ : Store} (hσ : σ ∈ m) :
    BasicTermTyp ∅ (instantiateTerm e σ.toAssignment) T := by
  have hf := (Formula.models_fiberAtom_iff m
    (basicTypingQualifier Δ e T)).1 h
  have hs := hf.2.2 σ hσ
  obtain ⟨_, a, ha, hlook⟩ := hs
  have hagree : ∀ ξ, ξ ∈ e.logicSupport →
      a.assignment.lookup ξ = σ.toAssignment.lookup ξ := by
    intro ξ hξ
    cases ξ with
    | bound k => exact (termLogicSupport_locallyClosed e closed k hξ).elim
    | free x =>
        rw [hlook x, Store.lookup_restrict,
          if_pos (by
            rw [Qualifier.mem_freeAtoms_iff]
            exact Finset.mem_union_right _ hξ),
          Store.toAssignment_lookup_free]
  rw [← instantiateTerm_eq_of_agreeOn e hagree]
  exact ha.2.2

theorem models_total_term {m : Capability} {e : Term}
    (closed : e.locallyClosed) (h : m ⊨ total e)
    {σ : Store} (hσ : σ ∈ m) :
    (instantiateTerm e σ.toAssignment).MustTerminate := by
  have hf := (Formula.models_fiberAtom_iff m (totalQualifier e)).1 h
  have hs := hf.2.2 σ hσ
  obtain ⟨_, a, ha, hlook⟩ := hs
  have hagree : ∀ ξ, ξ ∈ e.logicSupport →
      a.assignment.lookup ξ = σ.toAssignment.lookup ξ := by
    intro ξ hξ
    cases ξ with
    | bound k => exact (termLogicSupport_locallyClosed e closed k hξ).elim
    | free x =>
        rw [hlook x, Store.lookup_restrict,
          if_pos (by
            rw [Qualifier.mem_freeAtoms_iff]
            exact hξ),
          Store.toAssignment_lookup_free]
  rw [← instantiateTerm_eq_of_agreeOn e hagree]
  exact ha

@[simp] theorem freeAtoms_wellFormed (d : Nat) (Δ : BasicEnv)
    (τ : ContextType) :
    (wellFormed d Δ τ).freeAtoms = Δ.domain := by
  rw [wellFormed, Formula.freeAtoms_fiberAtom]
  change LogicVar.freeAtomSet (Δ.domain.image LogicVar.free) = Δ.domain
  exact Formula.LogicVar.freeAtomSet_image_free Δ.domain

@[simp] theorem freeAtoms_basicTyping (Δ : BasicEnv) (e : Term)
    (T : SimpleType) :
    (basicTyping Δ e T).freeAtoms =
      Δ.domain ∪ LogicVar.freeAtomSet e.logicSupport := by
  rw [basicTyping, Formula.freeAtoms_fiberAtom]
  change LogicVar.freeAtomSet
      (Δ.domain.image LogicVar.free ∪ e.logicSupport) = _
  rw [Formula.LogicVar.freeAtomSet_union,
    Formula.LogicVar.freeAtomSet_image_free]

@[simp] theorem freeAtoms_total (e : Term) :
    (total e).freeAtoms = LogicVar.freeAtomSet e.logicSupport := by
  rw [total, Formula.freeAtoms_fiberAtom]
  rfl

/-- Totality is the pointwise universal termination obligation over stores. -/
theorem models_total_iff {m : Capability} {e : Term} (closed : e.locallyClosed) :
    m ⊨ total e ↔ e.support ⊆ m.domain ∧
      ∀ σ, σ ∈ m → (instantiateTerm e σ.toAssignment).MustTerminate := by
  constructor
  · intro h
    refine ⟨?_, fun σ hσ => models_total_term closed h hσ⟩
    simpa only [freeAtoms_total, freeAtomSet_term_logicSupport] using Formula.models_scope h
  · rintro ⟨scope, hterm⟩
    let q := totalQualifier e
    have hqfree : q.freeAtoms = e.support := freeAtomSet_term_logicSupport e
    have hqsupp : q.support = e.support.image LogicVar.free := by
      change e.logicSupport = e.support.image LogicVar.free
      rw [← freeAtomSet_term_logicSupport e]
      exact LogicVar.eq_image_free_of_locallyClosed (termLogicSupport_locallyClosed e closed)
    apply (Formula.models_fiberAtom_iff m q).2
    refine ⟨?_, by simpa [hqfree] using scope, ?_⟩
    · intro k hk
      exact (termLogicSupport_locallyClosed e closed k hk).elim
    · intro σ hσ
      let s := σ.restrict q.freeAtoms
      have hsdom : s.domain = q.freeAtoms := by
        rw [Store.domain_restrict, m.mem_domain hσ,
          Finset.inter_eq_right.2 (by simpa [hqfree] using scope)]
      let a : AssignmentOn q.support :=
        { assignment := s.toAssignment
          domain_eq := by rw [Store.toAssignment_domain, hsdom, hqfree, hqsupp] }
      refine ⟨hsdom, a, ?_, ?_⟩
      · change (instantiateTerm e a.assignment).MustTerminate
        have heq : instantiateTerm e a.assignment = instantiateTerm e σ.toAssignment := by
          apply instantiateTerm_eq_of_agreeOn
          intro ξ hξ
          cases ξ with
          | bound k => exact (termLogicSupport_locallyClosed e closed k hξ).elim
          | free x =>
              have hx : x ∈ e.support := by
                rw [← freeAtomSet_term_logicSupport, LogicVar.mem_freeAtomSet_iff]
                exact hξ
              simp [a, s, Store.toAssignment_lookup_free, hqfree, hx]
        rw [heq]
        exact hterm σ hσ
      · intro x
        simp [a, s]

/-- Universal termination is preserved when two same-domain capabilities
are combined by additive sum. -/
theorem models_total_sum {m₁ m₂ : Capability} {e : Term}
    (defined : Capability.SumDefined m₁ m₂) (closed : e.locallyClosed)
    (h₁ : m₁ ⊨ total e) (h₂ : m₂ ⊨ total e) :
    Capability.sum m₁ m₂ defined ⊨ total e := by
  apply (models_total_iff closed).2
  refine ⟨((models_total_iff closed).1 h₁).1, ?_⟩
  intro σ hσ
  rcases hσ with hσ | hσ
  · exact models_total_term closed h₁ hσ
  · exact models_total_term closed h₂ hσ

/-- Pointwise erased typing and a typed input world realize the supported
basic-typing atom. -/
theorem models_basicTyping_of_term {m : Capability} {Δ : BasicEnv}
    {e : Term} {T : SimpleType} (closed : e.locallyClosed)
    (support : e.support ⊆ Δ.domain) (world : m ⊨ basicWorld Δ)
    (typed : ∀ σ, σ ∈ m → BasicTermTyp ∅ (instantiateTerm e σ.toAssignment) T) :
    m ⊨ basicTyping Δ e T := by
  let q := basicTypingQualifier Δ e T
  have hlogic : e.logicSupport = e.support.image LogicVar.free := by
    rw [← freeAtomSet_term_logicSupport e]
    exact LogicVar.eq_image_free_of_locallyClosed (termLogicSupport_locallyClosed e closed)
  have hqsupp : q.support = Δ.domain.image LogicVar.free := by
    change Δ.domain.image LogicVar.free ∪ e.logicSupport = _
    rw [hlogic, Finset.union_eq_left.2 (Finset.image_subset_image support)]
  have hqfree : q.freeAtoms = Δ.domain := by
    change LogicVar.freeAtomSet q.support = _
    rw [hqsupp, Formula.LogicVar.freeAtomSet_image_free]
  have hw := (models_basicWorld_iff m Δ).1 world
  apply (Formula.models_fiberAtom_iff m q).2
  refine ⟨?_, by simpa [hqfree] using hw.1, ?_⟩
  · intro k hk
    rw [hqsupp] at hk
    simp at hk
  · intro σ hσ
    let s := σ.restrict q.freeAtoms
    have hsdom : s.domain = q.freeAtoms := by
      rw [Store.domain_restrict, m.mem_domain hσ,
        Finset.inter_eq_right.2 (by simpa [hqfree] using hw.1)]
    let a : AssignmentOn q.support :=
      { assignment := s.toAssignment
        domain_eq := by rw [Store.toAssignment_domain, hsdom, hqfree, hqsupp] }
    refine ⟨hsdom, a, ?_, ?_⟩
    · change e.support ⊆ Δ.domain ∧ _ ∧ _
      refine ⟨support, ?_, ?_⟩
      · intro ξ U hU
        cases ξ with
        | bound k => simp at hU
        | free x =>
            obtain ⟨v, hv, hvT⟩ := hw.2 σ hσ x U hU
            refine ⟨v, ?_, hvT⟩
            have hx : x ∈ Δ.domain :=
              (BasicValTyp.free hU).support_subset (by simp [Value.support])
            simp [a, s, Store.toAssignment_lookup_free, hqfree, hx, hv]
      · have heq : instantiateTerm e a.assignment = instantiateTerm e σ.toAssignment := by
          apply instantiateTerm_eq_of_agreeOn
          intro ξ hξ
          cases ξ with
          | bound k => exact (termLogicSupport_locallyClosed e closed k hξ).elim
          | free x =>
              have hx : x ∈ e.support := by
                rw [← freeAtomSet_term_logicSupport, LogicVar.mem_freeAtomSet_iff]
                exact hξ
              simp [a, s, Store.toAssignment_lookup_free, hqfree, support hx]
        rw [heq]
        exact typed σ hσ
    · intro x
      simp [a, s]

/-- A typed world realizes the basic-typing atom of every syntactically
well-typed term. -/
theorem models_basicTyping_of_world {m : Capability} {Δ : BasicEnv}
    {e : Term} {T : SimpleType} (typed : Δ ⊢ₑ e ⋮ T)
    (world : m ⊨ basicWorld Δ) : m ⊨ basicTyping Δ e T :=
  models_basicTyping_of_term typed.locallyClosed typed.support_subset world
    (fun σ hσ => instantiateTerm_typed typed
      ((models_basicWorld_iff m Δ).1 world |>.2 σ hσ))

/-- Static formation and typing, a typed input world, and totality establish
the guard after restricting the environment to its relevant variables. -/
theorem models_guard_relevant_of_world {m : Capability} {Δ : BasicEnv}
    {τ : ContextType} {e : Term} {d : Nat}
    (wfτ : τ.WellFormedAt d Δ.domain) (typed : Δ ⊢ₑ e ⋮ τ.erase)
    (world : m ⊨ basicWorld Δ) (terminates : m ⊨ total e) :
    m ⊨ guard d (relevantEnv Δ τ e) τ e := by
  let Δ' := relevantEnv Δ τ e
  have hτ : τ.freeAtoms ⊆ Δ'.domain := by
    intro x hx
    simp only [Δ', relevantEnv_domain, relevantAtoms]
    exact Finset.mem_inter.2
      ⟨wfτ.freeAtoms_subset hx, Finset.mem_union_left _ hx⟩
  have he : e.support ⊆ Δ'.domain := by
    intro x hx
    simp only [Δ', relevantEnv_domain, relevantAtoms]
    exact Finset.mem_inter.2
      ⟨typed.support_subset hx, Finset.mem_union_right _ hx⟩
  have hworld : m ⊨ basicWorld Δ' :=
    models_basicWorld_restrict (relevantAtoms τ e) world
  have hbasic : m ⊨ basicTyping Δ' e τ.erase :=
    models_basicTyping_of_term typed.locallyClosed he hworld
      (fun σ hσ => instantiateTerm_typed typed
        ((models_basicWorld_iff m Δ).1 world |>.2 σ hσ))
  have hformed : m ⊨ wellFormed d Δ' τ :=
    (models_wellFormed_iff m d Δ' τ).2
      ⟨(models_basicWorld_iff m Δ').1 hworld |>.1, wfτ.regularize hτ⟩
  exact Formula.models_and_intro hformed
    (Formula.models_and_intro hworld (Formula.models_and_intro hbasic terminates))

@[simp] theorem freeAtoms_guard (d : Nat) (Δ : BasicEnv)
    (τ : ContextType) (e : Term) :
    (guard d Δ τ e).freeAtoms =
      Δ.domain ∪ LogicVar.freeAtomSet e.logicSupport := by
  simp [guard]

@[simp] theorem freeAtoms_resultAt (X : Finset LogicVar) (e : Term)
    (ξ : LogicVar) :
    (resultAt X e ξ).freeAtoms =
      LogicVar.freeAtomSet X ∪ e.support ∪ ξ.freeAtoms := by
  rw [resultAt, Formula.freeAtoms_fiber, Formula.freeAtoms_atom]
  change LogicVar.freeAtomSet X ∪
      LogicVar.freeAtomSet (e.logicSupport ∪ {ξ}) = _
  rw [Formula.LogicVar.freeAtomSet_union, freeAtomSet_term_logicSupport]
  simp [LogicVar.freeAtomSet, Finset.union_comm,
    Finset.union_left_comm]

@[simp] theorem freeAtoms_result (e : Term) (ξ : LogicVar) :
    (result e ξ).freeAtoms = e.support ∪ ξ.freeAtoms := by
  simp [result]

@[simp] theorem freeAtoms_resultBasicTyping (b : BaseType) :
    (resultBasicTyping b).freeAtoms = ∅ := by
  simp [resultBasicTyping, Value.logicSupportAt, Term.logicSupportAt,
    boundLogicSupportAt, LogicVar.freeAtomSet, LogicVar.freeAtoms]

@[simp] theorem freeAtoms_overResult (b : BaseType) (q : Qualifier) :
    (overResult b q).freeAtoms = q.freeAtoms := by
  simp [overResult]

@[simp] theorem freeAtoms_underResult (b : BaseType) (q : Qualifier) :
    (underResult b q).freeAtoms = q.freeAtoms := by
  simp [underResult]

@[simp] theorem freeAtoms_overResultFiber (b : BaseType) (q : Qualifier) :
    (Formula.fiber (q.support \ {.bound 0}) (overResult b q)).freeAtoms =
      q.freeAtoms := by
  ext x
  simp only [Formula.freeAtoms_fiber, freeAtoms_overResult,
    Finset.mem_union]
  constructor
  · rintro (hx | hx)
    · rw [LogicVar.mem_freeAtomSet_iff] at hx
      exact (Qualifier.mem_freeAtoms_iff q x).2 (Finset.mem_sdiff.1 hx).1
    · exact hx
  · exact fun hx => Or.inr hx

@[simp] theorem freeAtoms_underResultFiber (b : BaseType) (q : Qualifier) :
    (Formula.fiber (q.support \ {.bound 0}) (underResult b q)).freeAtoms =
      q.freeAtoms := by
  ext x
  simp only [Formula.freeAtoms_fiber, freeAtoms_underResult,
    Finset.mem_union]
  constructor
  · rintro (hx | hx)
    · rw [LogicVar.mem_freeAtomSet_iff] at hx
      exact (Qualifier.mem_freeAtoms_iff q x).2 (Finset.mem_sdiff.1 hx).1
    · exact hx
  · exact fun hx => Or.inr hx

@[simp] theorem freeAtomSet_relevantSupport (Δ : BasicEnv)
    (τ : ContextType) (e : Term) :
    LogicVar.freeAtomSet (relevantSupport Δ τ e) =
      (relevantEnv Δ τ e).domain := by
  ext x
  rw [LogicVar.mem_freeAtomSet_iff]
  simp only [relevantSupport, Finset.mem_union, Finset.mem_image,
    Finset.mem_biUnion]
  constructor
  · rintro (⟨y, hy, same⟩ | ⟨ξ, hξ, h⟩)
    · cases same
      exact hy
    · cases ξ with
      | bound k => simp at h
      | free y => simp at h
  · intro hx
    exact Or.inl ⟨x, hx, rfl⟩

theorem freeAtomSet_image_shiftFrom (X : Finset LogicVar) (k : Nat) :
    LogicVar.freeAtomSet (X.image (LogicVar.shiftFrom k)) =
      LogicVar.freeAtomSet X := by
  ext x
  rw [LogicVar.mem_freeAtomSet_iff, LogicVar.mem_freeAtomSet_iff]
  constructor
  · intro hx
    rw [Finset.mem_image] at hx
    obtain ⟨ξ, hξ, same⟩ := hx
    cases ξ with
    | bound n =>
        by_cases h : k ≤ n <;> simp [LogicVar.shiftFrom, h] at same
    | free y =>
        have : y = x := by simpa [LogicVar.shiftFrom] using same
        simpa [this] using hξ
  · intro hx
    exact Finset.mem_image.2
      ⟨.free x, hx, by simp [LogicVar.shiftFrom]⟩

@[simp] theorem freeAtoms_resultFirst (Δ : BasicEnv) (τ : ContextType)
    (e : Term) :
    (resultFirst Δ τ e).freeAtoms =
      (relevantEnv Δ τ e).domain ∪ e.support := by
  simp [resultFirst, freeAtomSet_image_shiftFrom,
    LogicVar.freeAtoms]

theorem freeAtoms_guard_relevant_subset (d : Nat) (Δ : BasicEnv)
    (τ : ContextType) (e : Term) :
    (guard d (relevantEnv Δ τ e) τ e).freeAtoms ⊆
      τ.freeAtoms ∪ e.support := by
  intro x hx
  simp only [freeAtoms_guard, freeAtomSet_term_logicSupport,
    Finset.mem_union] at hx ⊢
  rcases hx with hx | hx
  · have hx' := Finset.mem_inter.1
      (by simpa only [relevantEnv_domain] using hx)
    exact (Finset.mem_union.1 hx'.2)
  · exact Or.inr hx

theorem freeAtoms_resultFirst_relevant_subset (Δ : BasicEnv)
    (τ : ContextType) (e : Term) :
    (resultFirst (relevantEnv Δ τ e) τ e).freeAtoms ⊆
      τ.freeAtoms ∪ e.support := by
  intro x hx
  rw [freeAtoms_resultFirst, relevantEnv_idem] at hx
  rcases Finset.mem_union.1 hx with hx | hx
  · have hx' := Finset.mem_inter.1
      (by simpa only [relevantEnv_domain] using hx)
    exact Finset.mem_union.2 (Finset.mem_union.1 hx'.2)
  · exact Finset.mem_union_right _ hx

/-! ## Result observations -/

theorem resultQualifier_substitute_holdsStore_iff
    {X : Finset LogicVar} {e : Term} {y : Atom} {s o : Store}
    (closedX : LogicVar.LocallyClosed X) (support : e.logicSupport ⊆ X)
    (fresh : LogicVar.free y ∉ X)
    (hs : s.domain = LogicVar.freeAtomSet X) (ho : o.domain = {y}) :
    let q := resultQualifier e (.free y)
    (q.substitute s.toAssignment).HoldsStore o ↔
      ∃ v, o.lookup y = some v ∧
        (instantiateTerm e s.toAssignment).reaches v := by
  let q := resultQualifier e (.free y)
  let r := q.substitute s.toAssignment
  have hsA : s.toAssignment.domain = X := by
    rw [Store.toAssignment_domain, hs]
    exact (LogicVar.eq_image_free_of_locallyClosed closedX).symm
  have hrsupp : r.support = {.free y} := by
    change (q.substitute s.toAssignment).support = {.free y}
    rw [Qualifier.support_substitute, hsA]
    apply Finset.ext
    intro ξ
    simp only [q, resultQualifier, Finset.mem_sdiff, Finset.mem_union,
      Finset.mem_singleton]
    constructor
    · rintro ⟨he | hy, hn⟩
      · exact (hn (support he)).elim
      · exact hy
    · intro hy
      subst ξ
      exact ⟨Or.inr rfl, fresh⟩
  have hrfree : r.freeAtoms = {y} := by
    change LogicVar.freeAtomSet r.support = {y}
    rw [hrsupp]
    simp
  have agree : ∀ (a : AssignmentOn r.support) (ξ : LogicVar),
      ξ ∈ e.logicSupport →
      (a.substituteBack q.support s.toAssignment).assignment.lookup ξ =
        s.toAssignment.lookup ξ := by
    intro a ξ hξ
    have hξX := support hξ
    have hξy : ξ ≠ .free y := fun same => by
      subst ξ
      exact fresh hξX
    have hξa : ξ ∉ a.assignment.domain := by
      rw [a.domain_eq, hrsupp]
      simpa using hξy
    have hξq : ξ ∈ q.support := by
      change ξ ∈ e.logicSupport ∪ {.free y}
      exact Finset.mem_union_left _ hξ
    change (a.assignment.merge
      (s.toAssignment.restrict q.support)).lookup ξ = _
    calc
      _ = (s.toAssignment.restrict q.support).lookup ξ :=
        Finmap.lookup_union_right hξa
      _ = s.toAssignment.lookup ξ := by
        rw [Assignment.lookup_restrict, if_pos hξq]
  have inst : ∀ a : AssignmentOn r.support,
      instantiateTerm e
          (a.substituteBack q.support s.toAssignment).assignment =
        instantiateTerm e s.toAssignment := by
    intro a
    exact instantiateTerm_eq_of_agreeOn e (agree a)
  constructor
  · rintro ⟨_, a, ha, look⟩
    change LogicVar.free y ∉ e.logicSupport ∧
      ∃ v,
        (a.substituteBack q.support s.toAssignment).assignment.lookup
            (.free y) = some v ∧
        (instantiateTerm e
          (a.substituteBack q.support s.toAssignment).assignment).reaches v
      at ha
    obtain ⟨v, hv, heval⟩ := ha.2
    refine ⟨v, ?_, ?_⟩
    · rw [← hv]
      symm
      change (a.assignment.merge
        (s.toAssignment.restrict q.support)).lookup (.free y) = o.lookup y
      have hyA : LogicVar.free y ∈ a.assignment.domain := by
        rw [a.domain_eq, hrsupp]
        simp
      calc
        _ = a.assignment.lookup (.free y) := Finmap.lookup_union_left hyA
        _ = o.lookup y := look y
    · rwa [inst a] at heval
  · rintro ⟨v, hv, heval⟩
    refine ⟨ho.trans hrfree.symm, ?_⟩
    let a : AssignmentOn r.support :=
      { assignment := o.toAssignment
        domain_eq := by
          rw [Store.toAssignment_domain, ho, hrsupp]
          simp }
    refine ⟨a, ?_, ?_⟩
    · change LogicVar.free y ∉ e.logicSupport ∧
        ∃ w,
          (a.substituteBack q.support s.toAssignment).assignment.lookup
              (.free y) = some w ∧
          (instantiateTerm e
            (a.substituteBack q.support s.toAssignment).assignment).reaches w
      refine ⟨fun hy => fresh (support hy), v, ?_, ?_⟩
      · change (a.assignment.merge
          (s.toAssignment.restrict q.support)).lookup (.free y) = some v
        have hyA : LogicVar.free y ∈ a.assignment.domain := by
          rw [a.domain_eq, hrsupp]
          simp
        calc
          _ = a.assignment.lookup (.free y) := Finmap.lookup_union_left hyA
          _ = o.lookup y := by simp [a]
          _ = some v := hv
      · rwa [inst a]
    · intro x
      simp [a]

theorem resultQualifier_shift_openAt (e : Term) (y : Atom)
    (closed : e.locallyClosed) (fresh : y ∉ e.support) :
    (resultQualifier (shiftTerm e) (.bound 0)).openAt 0 y =
      resultQualifier e (.free y) := by
  rw [shiftTerm_eq_of_locallyClosed e closed]
  let q := resultQualifier e (.bound 0)
  let r := resultQualifier e (.free y)
  have hsupp : LogicVar.openSupport 0 y e.logicSupport = e.logicSupport := by
    apply LogicVar.openSupport_eq_self_of_fresh
    · exact termLogicSupport_locallyClosed e closed 0
    · intro hy
      apply fresh
      rw [← freeAtomSet_term_logicSupport e,
        LogicVar.mem_freeAtomSet_iff]
      exact hy
  apply Qualifier.ext
  · change LogicVar.openSupport 0 y
        (e.logicSupport ∪ {.bound 0}) = e.logicSupport ∪ {.free y}
    rw [show LogicVar.openSupport 0 y
        (e.logicSupport ∪ {.bound 0}) =
          LogicVar.openSupport 0 y e.logicSupport ∪
            LogicVar.openSupport 0 y {.bound 0} by
      simp [LogicVar.openSupport]]
    rw [hsupp]
    simp [LogicVar.openSupport, LogicVar.openBinder, LogicVar.swap]
  · intro ρ σ same
    change (LogicVar.bound 0 ∉ e.logicSupport ∧
        ∃ v,
          (ρ.swapBack (.bound 0) (.free y)).assignment.lookup (.bound 0) =
              some v ∧
          (instantiateTerm e
            (ρ.swapBack (.bound 0) (.free y)).assignment).reaches v) ↔
      LogicVar.free y ∉ e.logicSupport ∧
        ∃ v, σ.assignment.lookup (.free y) = some v ∧
          (instantiateTerm e σ.assignment).reaches v
    have hbound : LogicVar.bound 0 ∉ e.logicSupport :=
      termLogicSupport_locallyClosed e closed 0
    have hfree : LogicVar.free y ∉ e.logicSupport := by
      intro hy
      apply fresh
      rw [← freeAtomSet_term_logicSupport e,
        LogicVar.mem_freeAtomSet_iff]
      exact hy
    have hagree : ∀ ξ, ξ ∈ e.logicSupport →
        (ρ.swapBack (.bound 0) (.free y)).assignment.lookup ξ =
          σ.assignment.lookup ξ := by
      intro ξ hξ
      simp only [AssignmentOn.swapBack, Assignment.lookup_swap]
      change ρ.assignment.lookup
          (LogicVar.swap (.bound 0) (.free y) ξ) =
        σ.assignment.lookup ξ
      have hb : ξ ≠ LogicVar.bound 0 := fun h => hbound (h ▸ hξ)
      have hf : ξ ≠ LogicVar.free y := fun h => hfree (h ▸ hξ)
      rw [show LogicVar.swap (.bound 0) (.free y) ξ = ξ by
        simp [LogicVar.swap, hb, hf]]
      exact congrArg (fun a => a.lookup ξ) same
    have hterm : instantiateTerm e
        (ρ.swapBack (.bound 0) (.free y)).assignment =
          instantiateTerm e σ.assignment :=
      instantiateTerm_eq_of_agreeOn e hagree
    have hresult :
        (ρ.swapBack (.bound 0) (.free y)).assignment.lookup (.bound 0) =
          σ.assignment.lookup (.free y) := by
      simp only [AssignmentOn.swapBack, Assignment.lookup_swap]
      change ρ.assignment.lookup
          (LogicVar.swap (.bound 0) (.free y) (.bound 0)) = _
      rw [LogicVar.swap_left]
      exact congrArg (fun a => a.lookup (.free y)) same
    simp only [hbound, hfree, not_false_eq_true, true_and]
    rw [hresult, hterm]

theorem resultAt_shift_openAt (X : Finset LogicVar) (e : Term) (y : Atom)
    (closedX : LogicVar.LocallyClosed X) (closedE : e.locallyClosed)
    (support : e.logicSupport ⊆ X) (fresh : LogicVar.free y ∉ X) :
    (resultAt (X.image (LogicVar.shiftFrom 0)) (shiftTerm e) (.bound 0)).openAt
        0 y = resultAt X e (.free y) := by
  have hshift : X.image (LogicVar.shiftFrom 0) = X :=
    LogicVar.image_shiftFrom_eq_of_locallyClosed X 0 closedX
  have hopen : LogicVar.openSupport 0 y X = X := by
    apply LogicVar.openSupport_eq_self_of_fresh
    · exact closedX 0
    · exact fresh
  have freshE : y ∉ e.support := by
    intro hy
    apply fresh
    apply support
    rw [← LogicVar.mem_freeAtomSet_iff,
      freeAtomSet_term_logicSupport]
    exact hy
  simp only [resultAt, Formula.openAt, hshift, hopen]
  rw [resultQualifier_shift_openAt e y closedE freshE]

theorem resultFirst_openAt (Δ : BasicEnv) (τ : ContextType) (e : Term)
    (y : Atom)
    (closed : LogicVar.LocallyClosed (relevantSupport Δ τ e))
    (closedE : e.locallyClosed)
    (support : e.logicSupport ⊆ relevantSupport Δ τ e)
    (fresh : LogicVar.free y ∉ relevantSupport Δ τ e) :
    (resultFirst Δ τ e).openAt 0 y =
      resultAt (relevantSupport Δ τ e) e (.free y) := by
  exact resultAt_shift_openAt (relevantSupport Δ τ e) e y closed closedE
    support fresh

/-- A result atom names the actual result reached from every store in its
ambient capability. -/
theorem models_resultAt_lookup {m : Capability} {X : Finset LogicVar}
    {e : Term} {y : Atom}
    (closed : LogicVar.LocallyClosed X)
    (support : e.logicSupport ⊆ X)
    (fresh : LogicVar.free y ∉ X)
    (h : m ⊨ resultAt X e (.free y)) :
    ∀ σ, σ ∈ m → ∃ v, σ.lookup y = some v ∧
      (instantiateTerm e σ.toAssignment).reaches v := by
  intro σ hσ
  let P := resultAt X e (.free y)
  let r := m.restrict P.freeAtoms
  let ρ := σ.restrict P.freeAtoms
  have hρ : ρ ∈ r := ⟨σ, hσ, rfl⟩
  have hX : LogicVar.freeAtomSet X ⊆ P.freeAtoms := by
    intro x hx
    simp only [P, freeAtoms_resultAt, Finset.mem_union]
    exact Or.inl (Or.inl hx)
  have hρX : ρ.restrict (LogicVar.freeAtomSet X) =
      σ.restrict (LogicVar.freeAtomSet X) := by
    simp only [ρ]
    rw [Store.restrict_restrict]
    apply Store.restrict_congr
    intro x hx
    simp only [Finset.mem_inter]
    exact ⟨fun h => h.2, fun h => ⟨hX h, h⟩⟩
  obtain ⟨f, hf, hρf⟩ :=
    Capability.fiber_from_store r (LogicVar.freeAtomSet X) hρ
  rw [hρX] at hf
  have hscope : P.freeAtoms ⊆ m.domain := Formula.models_scope h
  rw [resultAt, Formula.models_fiber_iff] at h
  have hi := h.2.2 (σ.restrict (LogicVar.freeAtomSet X)) f hf
  simp only [Formula.substituteStore] at hi
  let q := resultQualifier e (.free y)
  let s := σ.restrict (LogicVar.freeAtomSet X)
  have hsdom : s.domain = LogicVar.freeAtomSet X := by
    simp only [s]
    rw [Store.domain_restrict, m.mem_domain hσ,
      Finset.inter_eq_right.2 (Finset.Subset.trans hX hscope)]
  have hsA : s.toAssignment.domain = X := by
    rw [Store.toAssignment_domain, hsdom]
    exact (LogicVar.eq_image_free_of_locallyClosed closed).symm
  have hqsupp : (q.substitute s.toAssignment).support = {.free y} := by
    rw [Qualifier.support_substitute, hsA]
    apply Finset.ext
    intro ξ
    simp only [q, resultQualifier, Finset.mem_sdiff, Finset.mem_union,
      Finset.mem_singleton]
    constructor
    · rintro ⟨he | hy, hn⟩
      · exact (hn (support he)).elim
      · exact hy
    · intro hy
      subst ξ
      exact ⟨Or.inr rfl, fresh⟩
  have hqfree : (q.substitute s.toAssignment).freeAtoms = {y} := by
    change LogicVar.freeAtomSet (q.substitute s.toAssignment).support = {y}
    rw [hqsupp]
    simp
  have hs := Formula.models_atom_holdsStore hi hρf
  obtain ⟨_, a, ha, hlook⟩ := hs
  change q.holds (a.substituteBack q.support s.toAssignment) at ha
  change LogicVar.free y ∉ e.logicSupport ∧
      ∃ v,
        (a.substituteBack q.support s.toAssignment).assignment.lookup
            (.free y) = some v ∧
        (instantiateTerm e
          (a.substituteBack q.support s.toAssignment).assignment).reaches v
    at ha
  obtain ⟨v, hv, heval⟩ := ha.2
  have hay : LogicVar.free y ∈ a.assignment.domain := by
    rw [a.domain_eq, hqsupp]
    simp
  have hcombinedY :
      (a.substituteBack q.support s.toAssignment).assignment.lookup
          (.free y) = a.assignment.lookup (.free y) := by
    change (a.assignment.merge
      (s.toAssignment.restrict q.support)).lookup (.free y) = _
    exact Finmap.lookup_union_left hay
  have hyP : y ∈ P.freeAtoms := by
    simp [P, LogicVar.freeAtoms]
  have hvσ : σ.lookup y = some v := by
    rw [← hv, hcombinedY, hlook y, hqfree]
    simp [ρ, hyP]
  refine ⟨v, hvσ, ?_⟩
  rw [← instantiateTerm_eq_of_agreeOn e (by
    intro ξ hξ
    have hξX : ξ ∈ X := support hξ
    have hξy : ξ ≠ LogicVar.free y := fun same => by
      subst ξ
      exact fresh hξX
    have hξa : ξ ∉ a.assignment.domain := by
      rw [a.domain_eq, hqsupp]
      simpa using hξy
    change (a.assignment.merge
      (s.toAssignment.restrict q.support)).lookup ξ =
        σ.toAssignment.lookup ξ
    have hmerge :
        (a.assignment.merge (s.toAssignment.restrict q.support)).lookup ξ =
          (s.toAssignment.restrict q.support).lookup ξ := by
      exact Finmap.lookup_union_right hξa
    have hξq : ξ ∈ q.support := by
      change ξ ∈ e.logicSupport ∪ {.free y}
      exact Finset.mem_union_left _ hξ
    rw [hmerge, Assignment.lookup_restrict, if_pos hξq]
    cases ξ with
    | bound k => exact (closed k hξX).elim
    | free x =>
        simp only [s]
        rw [Store.toAssignment_lookup_free,
          Store.toAssignment_lookup_free, Store.lookup_restrict,
          if_pos ((LogicVar.mem_freeAtomSet_iff X x).2 hξX)])]
  exact heval

/-- Introduce an exact result graph from its two characteristic properties:
every store names an actual result, and every possible result is represented
by a store with the same input projection. -/
theorem models_resultAt_intro {m : Capability} {X : Finset LogicVar}
    {e : Term} {y : Atom}
    (closedX : LogicVar.LocallyClosed X) (support : e.logicSupport ⊆ X)
    (fresh : LogicVar.free y ∉ X)
    (scope : LogicVar.freeAtomSet X ∪ {y} ⊆ m.domain)
    (sound : ∀ σ, σ ∈ m → ∃ v, σ.lookup y = some v ∧
      (instantiateTerm e σ.toAssignment).reaches v)
    (complete : ∀ σ, σ ∈ m → ∀ v,
      (instantiateTerm e σ.toAssignment).reaches v →
      ∃ ρ, ρ ∈ m ∧
        ρ.restrict (LogicVar.freeAtomSet X) =
          σ.restrict (LogicVar.freeAtomSet X) ∧
        ρ.lookup y = some v) :
    m ⊨ resultAt X e (.free y) := by
  let A := LogicVar.freeAtomSet X
  let P := resultAt X e (.free y)
  let q := resultQualifier e (.free y)
  have hyA : y ∉ A := by
    intro hy
    exact fresh ((LogicVar.mem_freeAtomSet_iff X y).1 hy)
  have heA : e.support ⊆ A := by
    intro x hx
    rw [← freeAtomSet_term_logicSupport,
      LogicVar.mem_freeAtomSet_iff] at hx
    change x ∈ LogicVar.freeAtomSet X
    rw [LogicVar.mem_freeAtomSet_iff]
    exact support hx
  have hqfree : q.freeAtoms = e.support ∪ {y} := by
    change LogicVar.freeAtomSet (e.logicSupport ∪ {.free y}) = _
    rw [Formula.LogicVar.freeAtomSet_union,
      freeAtomSet_term_logicSupport]
    simp
  have hPfree : P.freeAtoms = A ∪ {y} := by
    change (resultAt X e (.free y)).freeAtoms = A ∪ {y}
    rw [freeAtoms_resultAt]
    rw [Finset.union_eq_left.2 heA]
    simp [A, LogicVar.freeAtoms]
  change m ⊨ Formula.fiber X (Formula.atom q)
  apply Formula.models_fiber_intro
  · simp only [Formula.freeAtoms_fiber, Formula.freeAtoms_atom]
    rw [hqfree]
    change A ∪ (e.support ∪ {y}) ⊆ m.domain
    rw [← Finset.union_assoc, Finset.union_eq_left.2 heA]
    exact scope
  · exact closedX
  · intro s f hf
    simp only [Formula.substituteStore]
    let r := q.substitute s.toAssignment
    change f ⊨ Formula.atom r
    have hrdom : (m.restrict P.freeAtoms).domain = P.freeAtoms := by
      rw [Capability.restrict_domain, Finset.inter_eq_right]
      simpa [hPfree] using scope
    have hsdom : s.domain = A := by
      have hs := (m.restrict P.freeAtoms).restrict A
        |>.mem_domain hf.projection_mem
      rw [Capability.restrict_domain, hrdom, hPfree] at hs
      simpa [A, hyA] using hs
    have hsA : s.toAssignment.domain = X := by
      rw [Store.toAssignment_domain, hsdom]
      exact (LogicVar.eq_image_free_of_locallyClosed closedX).symm
    have hrsupp : r.support = {.free y} := by
      change (q.substitute s.toAssignment).support = {.free y}
      rw [Qualifier.support_substitute, hsA]
      apply Finset.ext
      intro ξ
      simp only [q, resultQualifier, Finset.mem_sdiff, Finset.mem_union,
        Finset.mem_singleton]
      constructor
      · rintro ⟨he | hy, hn⟩
        · exact (hn (support he)).elim
        · exact hy
      · intro hy
        subst ξ
        exact ⟨Or.inr rfl, fresh⟩
    have hrfree : r.freeAtoms = {y} := by
      change LogicVar.freeAtomSet r.support = {y}
      rw [hrsupp]
      simp
    have hfdom : f.domain = A ∪ {y} := by
      have hfd := hf.domain_eq
      change f.domain = (m.restrict P.freeAtoms).domain at hfd
      rw [hrdom, hPfree] at hfd
      exact hfd
    rw [Formula.models_atom_iff]
    refine ⟨?_, ?_⟩
    · rw [Capability.restrict_domain, hrfree, hfdom]
      simp
    · refine ⟨?_, ?_, ?_⟩
      · intro k hk
        rw [hrsupp] at hk
        simp at hk
      · rw [Capability.restrict_domain, hrfree, hfdom]
        simp
      · intro o ho
        rw [hrfree] at ho
        rw [show r.HoldsStore o ↔ ∃ v, o.lookup y = some v ∧
          (instantiateTerm e s.toAssignment).reaches v from
          resultQualifier_substitute_holdsStore_iff closedX support fresh
            hsdom ho]
        constructor
        · rintro ⟨v, hv, heval⟩
          obtain ⟨t₀, ht₀R, ht₀s⟩ := hf.projection_mem
          obtain ⟨σ₀, hσ₀, hσ₀t⟩ := ht₀R
          change σ₀.restrict P.freeAtoms = t₀ at hσ₀t
          have hσ₀A : σ₀.restrict A = s := by
            calc
              σ₀.restrict A = (σ₀.restrict P.freeAtoms).restrict A := by
                rw [Store.restrict_restrict,
                  Finset.inter_eq_right.2 (by
                    rw [hPfree]
                    exact Finset.subset_union_left)]
              _ = t₀.restrict A := by rw [hσ₀t]
              _ = s := ht₀s
          have hinst : instantiateTerm e s.toAssignment =
              instantiateTerm e σ₀.toAssignment := by
            apply instantiateTerm_eq_of_restrict_eq e X s σ₀ closedX support
            rw [Store.restrict_eq_self s (by rw [hsdom])]
            exact hσ₀A.symm
          obtain ⟨ρ, hρ, hρA, hρy⟩ :=
            complete σ₀ hσ₀ v (by rwa [← hinst])
          let t := ρ.restrict P.freeAtoms
          have htR : t ∈ m.restrict P.freeAtoms := ⟨ρ, hρ, rfl⟩
          have htA : t.restrict A = s := by
            calc
              t.restrict A = ρ.restrict A := by
                simp only [t, Store.restrict_restrict]
                rw [Finset.inter_eq_right.2 (by
                  rw [hPfree]
                  exact Finset.subset_union_left)]
              _ = σ₀.restrict A := hρA
              _ = s := hσ₀A
          have htf : t ∈ f := by
            apply hf.mem_iff.2
            refine ⟨htR, ?_⟩
            simpa [hsdom] using htA
          have hto : t.restrict {y} = o := by
            apply Store.ext
            intro x
            by_cases hxy : x = y
            · subst x
              have hyP : y ∈ P.freeAtoms := by rw [hPfree]; simp
              simp [t, Store.lookup_restrict, hyP, hρy, hv]
            · have hox : o.lookup x = none :=
                (Store.lookup_eq_none_iff o x).2 (by
                  rw [ho]
                  exact fun hx => hxy (Finset.mem_singleton.1 hx))
              simp [t, Store.lookup_restrict, hxy, hox]
          rw [hrfree, Capability.restrict_restrict, Finset.inter_self]
          exact ⟨t, htf, hto⟩
        · intro homem
          rw [hrfree, Capability.restrict_restrict, Finset.inter_self] at homem
          obtain ⟨t, htf, hto⟩ := homem
          have htR := hf.source_mem htf
          obtain ⟨σ, hσ, hσt⟩ := htR
          change σ.restrict P.freeAtoms = t at hσt
          have htA : t.restrict A = s := hf.restrict_input htf
          have hσA : σ.restrict A = s := by
            calc
              σ.restrict A = (σ.restrict P.freeAtoms).restrict A := by
                rw [Store.restrict_restrict,
                  Finset.inter_eq_right.2 (by
                    rw [hPfree]
                    exact Finset.subset_union_left)]
              _ = t.restrict A := by rw [hσt]
              _ = s := htA
          obtain ⟨v, hσy, heval⟩ := sound σ hσ
          refine ⟨v, ?_, ?_⟩
          · have hty := congrArg (fun u => u.lookup y) hto
            change (t.restrict {y}).lookup y = o.lookup y at hty
            rw [Store.lookup_restrict, if_pos (by simp)] at hty
            have htsy := congrArg (fun u => u.lookup y) hσt
            change (σ.restrict P.freeAtoms).lookup y = t.lookup y at htsy
            rw [Store.lookup_restrict, if_pos (by rw [hPfree]; simp)] at htsy
            exact hty.symm.trans (htsy.symm.trans hσy)
          · have hinst : instantiateTerm e s.toAssignment =
                instantiateTerm e σ.toAssignment := by
              apply instantiateTerm_eq_of_restrict_eq e X s σ closedX support
              rw [Store.restrict_eq_self s (by rw [hsdom])]
              exact hσA.symm
            rwa [hinst]

/-- Every possible result has a representative store in the same input
fiber of an exact result graph. -/
theorem models_resultAt_complete {m : Capability} {X : Finset LogicVar}
    {e : Term} {y : Atom}
    (closedX : LogicVar.LocallyClosed X) (support : e.logicSupport ⊆ X)
    (fresh : LogicVar.free y ∉ X)
    (h : m ⊨ resultAt X e (.free y)) :
    ∀ σ, σ ∈ m → ∀ v,
      (instantiateTerm e σ.toAssignment).reaches v →
      ∃ ρ, ρ ∈ m ∧
        ρ.restrict (LogicVar.freeAtomSet X) =
          σ.restrict (LogicVar.freeAtomSet X) ∧
        ρ.lookup y = some v := by
  intro σ hσ v heval
  let A := LogicVar.freeAtomSet X
  let P := resultAt X e (.free y)
  let q := resultQualifier e (.free y)
  let r := m.restrict P.freeAtoms
  let t := σ.restrict P.freeAtoms
  let s := σ.restrict A
  have heA : e.support ⊆ A := by
    intro x hx
    rw [← freeAtomSet_term_logicSupport,
      LogicVar.mem_freeAtomSet_iff] at hx
    change x ∈ LogicVar.freeAtomSet X
    rw [LogicVar.mem_freeAtomSet_iff]
    exact support hx
  have hPfree : P.freeAtoms = A ∪ {y} := by
    change (resultAt X e (.free y)).freeAtoms = A ∪ {y}
    rw [freeAtoms_resultAt]
    rw [Finset.union_eq_left.2 heA]
    simp [A, LogicVar.freeAtoms]
  have ht : t ∈ r := ⟨σ, hσ, rfl⟩
  have hts : t.restrict A = s := by
    simp only [t, s, Store.restrict_restrict]
    rw [Finset.inter_eq_right.2]
    rw [hPfree]
    exact Finset.subset_union_left
  obtain ⟨f, hf, _⟩ := Capability.fiber_from_store r A ht
  rw [hts] at hf
  have hi : f ⊨ Formula.atom (q.substitute s.toAssignment) := by
    rw [resultAt, Formula.models_fiber_iff] at h
    exact h.2.2 s f hf
  have hsdom : s.domain = A := by
    simp only [s, A, Store.domain_restrict, m.mem_domain hσ]
    rw [Finset.inter_eq_right]
    have hscope := Formula.models_scope h
    rw [hPfree] at hscope
    exact Finset.Subset.trans Finset.subset_union_left hscope
  let o : Store := Finmap.singleton y v
  have hodom : o.domain = {y} := by
    simp [o, Store.domain]
  have hohold : (q.substitute s.toAssignment).HoldsStore o := by
    apply (resultQualifier_substitute_holdsStore_iff closedX support fresh
      hsdom hodom).2
    refine ⟨v, ?_, ?_⟩
    · simp [o, Store.lookup]
    · have hinst : instantiateTerm e s.toAssignment =
          instantiateTerm e σ.toAssignment := by
        apply instantiateTerm_eq_of_restrict_eq e X s σ closedX support
        rw [Store.restrict_eq_self s (by rw [hsdom])]
      rwa [hinst]
  let u := q.substitute s.toAssignment
  have husupp : u.support = {.free y} := by
    change (q.substitute s.toAssignment).support = {.free y}
    have hsX : s.toAssignment.domain = X := by
      rw [Store.toAssignment_domain, hsdom]
      exact (LogicVar.eq_image_free_of_locallyClosed closedX).symm
    rw [Qualifier.support_substitute, hsX]
    apply Finset.ext
    intro ξ
    simp only [q, resultQualifier, Finset.mem_sdiff, Finset.mem_union,
      Finset.mem_singleton]
    constructor
    · rintro ⟨he | hy, hn⟩
      · exact (hn (support he)).elim
      · exact hy
    · intro hy
      subst ξ
      exact ⟨Or.inr rfl, fresh⟩
  have hufree : u.freeAtoms = {y} := by
    change LogicVar.freeAtomSet u.support = {y}
    rw [husupp]
    simp
  have he := (Formula.models_atom_iff f u).1 hi
  have homem := (he.2.2.2 o (by simpa [hufree] using hodom)).1 hohold
  rw [hufree, Capability.restrict_restrict, Finset.inter_self] at homem
  obtain ⟨ρ, hρf, hρo⟩ := homem
  obtain ⟨υ, hυ, hυρ⟩ := hf.source_mem hρf
  refine ⟨υ, hυ, ?_, ?_⟩
  · calc
      υ.restrict A = (υ.restrict P.freeAtoms).restrict A := by
        rw [Store.restrict_restrict,
          Finset.inter_eq_right.2 (by
            rw [hPfree]
            exact Finset.subset_union_left)]
      _ = ρ.restrict A := by rw [hυρ]
      _ = s := hf.restrict_input hρf
      _ = σ.restrict A := rfl
  · have hυy := congrArg (fun w => w.lookup y) hυρ
    have hρy := congrArg (fun w => w.lookup y) hρo
    change (υ.restrict P.freeAtoms).lookup y = ρ.lookup y at hυy
    change (ρ.restrict {y}).lookup y = o.lookup y at hρy
    rw [Store.lookup_restrict, if_pos (by rw [hPfree]; simp)] at hυy
    rw [Store.lookup_restrict, if_pos (by simp)] at hρy
    simpa [o, Store.lookup] using hυy.trans hρy

/-- Dropping input variables unused by the term preserves an exact result
graph, including completeness for every possible nondeterministic result. -/
theorem models_resultAt_restrict_support {m : Capability}
    {X Y : Finset LogicVar} {e : Term} {y : Atom}
    (closedY : LogicVar.LocallyClosed Y) (hXY : X ⊆ Y)
    (support : e.logicSupport ⊆ X) (fresh : LogicVar.free y ∉ Y)
    (h : m ⊨ resultAt Y e (.free y)) :
    m.restrict (LogicVar.freeAtomSet X ∪ {y}) ⊨ resultAt X e (.free y) := by
  let A := LogicVar.freeAtomSet X
  let B := LogicVar.freeAtomSet Y
  let r := m.restrict (A ∪ {y})
  have hAB : A ⊆ B := by
    intro x hx
    rw [LogicVar.mem_freeAtomSet_iff] at hx ⊢
    exact hXY hx
  have closedX : LogicVar.LocallyClosed X := fun k hk => closedY k (hXY hk)
  have supportY : e.logicSupport ⊆ Y := Finset.Subset.trans support hXY
  have freshX : LogicVar.free y ∉ X := fun hy => fresh (hXY hy)
  have hscope : A ∪ {y} ⊆ m.domain := by
    intro x hx
    apply Formula.models_scope h
    rw [freeAtoms_resultAt]
    rcases Finset.mem_union.1 hx with hx | hx
    · exact Finset.mem_union_left _ (Finset.mem_union_left _ (hAB hx))
    · have hxy : x = y := Finset.mem_singleton.1 hx
      subst x
      simp [LogicVar.freeAtoms]
  have hinst : ∀ σ : Store,
      instantiateTerm e (σ.restrict (A ∪ {y})).toAssignment =
        instantiateTerm e σ.toAssignment := by
    intro σ
    apply instantiateTerm_eq_of_restrict_eq e X _ _ closedX support
    change (σ.restrict (A ∪ {y})).restrict A = σ.restrict A
    rw [Store.restrict_restrict, Finset.inter_eq_right.2 Finset.subset_union_left]
  apply models_resultAt_intro closedX support freshX
  · change A ∪ {y} ⊆ r.domain
    rw [Capability.restrict_domain, Finset.inter_eq_right.2 hscope]
  · rintro σ ⟨ρ, hρ, rfl⟩
    obtain ⟨v, hv, heval⟩ := models_resultAt_lookup closedY supportY fresh h ρ hρ
    refine ⟨v, ?_, ?_⟩
    · simp [Store.lookup_restrict, hv]
    · rwa [hinst]
  · rintro σ ⟨ρ, hρ, rfl⟩ v heval
    rw [hinst] at heval
    obtain ⟨υ, hυ, hυB, hυy⟩ := models_resultAt_complete closedY supportY fresh h ρ hρ v heval
    change υ.restrict B = ρ.restrict B at hυB
    refine ⟨υ.restrict (A ∪ {y}), ⟨υ, hυ, rfl⟩, ?_, ?_⟩
    · change (υ.restrict (A ∪ {y})).restrict A = (ρ.restrict (A ∪ {y})).restrict A
      simp only [Store.restrict_restrict, Finset.inter_eq_right.2 Finset.subset_union_left]
      have h := congrArg (fun σ : Store => σ.restrict A) hυB
      simpa only [Store.restrict_restrict, Finset.inter_eq_right.2 hAB] using h
    · simp [Store.lookup_restrict, hυy]

/-- Selecting entire input fibers preserves the exact result graph. -/
theorem models_resultAt_pullback {m p : Capability} {X : Finset LogicVar}
    {e : Term} {y : Atom}
    (closedX : LogicVar.LocallyClosed X) (support : e.logicSupport ⊆ X)
    (fresh : LogicVar.free y ∉ X)
    (domain : p.domain = LogicVar.freeAtomSet X)
    (sub : p ⊆ m.restrict p.domain)
    (h : m ⊨ resultAt X e (.free y)) :
    Capability.pullback m p sub ⊨ resultAt X e (.free y) := by
  apply models_resultAt_intro closedX support fresh
  · have scope := Formula.models_scope h
    rw [freeAtoms_resultAt] at scope
    intro x hx
    apply scope
    rcases Finset.mem_union.1 hx with hx | hx
    · exact Finset.mem_union_left _ (Finset.mem_union_left _ hx)
    · exact Finset.mem_union_right _ (by simpa [LogicVar.freeAtoms] using hx)
  · intro σ hσ
    exact models_resultAt_lookup closedX support fresh h σ hσ.1
  · intro σ hσ v heval
    obtain ⟨ρ, hρ, same, result⟩ :=
      models_resultAt_complete closedX support fresh h σ hσ.1 v heval
    refine ⟨ρ, ⟨hρ, ?_⟩, same, result⟩
    rw [domain, same, ← domain]
    exact hσ.2

/-- Pointwise equality of reachable results preserves an exact result graph. -/
theorem models_resultAt_of_reaches_iff {m : Capability}
    {X : Finset LogicVar} {e₁ e₂ : Term} {y : Atom}
    (closedX : LogicVar.LocallyClosed X)
    (support₁ : e₁.logicSupport ⊆ X) (support₂ : e₂.logicSupport ⊆ X)
    (fresh : LogicVar.free y ∉ X)
    (heval : ∀ σ, σ ∈ m → ∀ v,
      (instantiateTerm e₁ σ.toAssignment).reaches v ↔
        (instantiateTerm e₂ σ.toAssignment).reaches v)
    (h : m ⊨ resultAt X e₁ (.free y)) :
    m ⊨ resultAt X e₂ (.free y) := by
  apply models_resultAt_intro closedX support₂ fresh
  · intro x hx
    apply Formula.models_scope h
    rw [freeAtoms_resultAt]
    rcases Finset.mem_union.1 hx with hx | hx
    · exact Finset.mem_union_left _ (Finset.mem_union_left _ hx)
    · have hxy : x = y := Finset.mem_singleton.1 hx
      subst x
      simp [LogicVar.freeAtoms]
  · intro σ hσ
    obtain ⟨v, hv, reaches⟩ := models_resultAt_lookup closedX support₁ fresh h σ hσ
    exact ⟨v, hv, (heval σ hσ v).1 reaches⟩
  · intro σ hσ v reaches
    exact models_resultAt_complete closedX support₁ fresh h σ hσ v
      ((heval σ hσ v).2 reaches)

/-- A Boolean lookup reduces an instantiated match to exactly its selected
branch, including both directions of the nondeterministic result relation. -/
theorem instantiateTerm_matchBool_reaches_iff
    {σ : Store} {x : Atom} {b : Bool} {e₁ e₂ : Term} {v : Value}
    (lookup : σ.lookup x = some (.const (.bool b)))
    (closed : (instantiateTerm (.matchBool (.free x) e₁ e₂)
      σ.toAssignment).locallyClosed) :
    (instantiateTerm (.matchBool (.free x) e₁ e₂) σ.toAssignment).reaches v ↔
      (instantiateTerm (if b then e₁ else e₂) σ.toAssignment).reaches v := by
  have he : instantiateTerm (.matchBool (.free x) e₁ e₂) σ.toAssignment =
      .matchBool (.const (.bool b))
        (instantiateTerm e₁ σ.toAssignment) (instantiateTerm e₂ σ.toAssignment) := by
    simp [instantiateTerm, instantiateTermAt, instantiateValueAt,
      Store.toAssignment_lookup_free, lookup]
  rw [he] at closed ⊢
  cases b with
  | false => exact Term.match_false_reaches_iff closed.2.1 closed.2.2
  | true => exact Term.match_true_reaches_iff closed.2.1 closed.2.2

/-- Boolean lookup also preserves the universal termination obligation, not
only the set of reachable results. -/
theorem instantiateTerm_matchBool_mustTerminate_iff
    {σ : Store} {x : Atom} {b : Bool} {e₁ e₂ : Term}
    (lookup : σ.lookup x = some (.const (.bool b)))
    (closed : (instantiateTerm (.matchBool (.free x) e₁ e₂)
      σ.toAssignment).locallyClosed) :
    (instantiateTerm (.matchBool (.free x) e₁ e₂) σ.toAssignment).MustTerminate ↔
      (instantiateTerm (if b then e₁ else e₂) σ.toAssignment).MustTerminate := by
  have he : instantiateTerm (.matchBool (.free x) e₁ e₂) σ.toAssignment =
      .matchBool (.const (.bool b))
        (instantiateTerm e₁ σ.toAssignment) (instantiateTerm e₂ σ.toAssignment) := by
    simp [instantiateTerm, instantiateTermAt, instantiateValueAt,
      Store.toAssignment_lookup_free, lookup]
  rw [he] at closed ⊢
  cases b with
  | false => exact Term.match_false_mustTerminate_iff closed.2.1 closed.2.2
  | true => exact Term.match_true_mustTerminate_iff closed.2.1 closed.2.2

/-- Result-first universal obligations transport along pointwise equality of
results, even when the target observes additional input variables. -/
theorem models_all_resultAt_of_reaches_iff
    {m : Capability} {A B : Finset Atom} {e₁ e₂ : Term} {Q : Formula}
    (closed₁ : e₁.locallyClosed) (closed₂ : e₂.locallyClosed)
    (support₁ : e₁.support ⊆ A) (support₂ : e₂.support ⊆ B)
    (hAB : A ⊆ B) (supportQ : Q.freeAtoms ⊆ A) (scope : B ⊆ m.domain)
    (heval : ∀ σ, σ ∈ m → ∀ v,
      (instantiateTerm e₁ σ.toAssignment).reaches v ↔
        (instantiateTerm e₂ σ.toAssignment).reaches v)
    (h : m ⊨ Formula.all (resultAt (A.image LogicVar.free) e₁ (.bound 0) ⇒ᶜ Q)) :
    m ⊨ Formula.all (resultAt (B.image LogicVar.free) e₂ (.bound 0) ⇒ᶜ Q) := by
  let P₁ := resultAt (A.image LogicVar.free) e₁ (.bound 0) ⇒ᶜ Q
  let P₂ := resultAt (B.image LogicVar.free) e₂ (.bound 0) ⇒ᶜ Q
  have hclosed : ∀ X : Finset Atom, LogicVar.LocallyClosed (X.image LogicVar.free) := by
    intro X k hk
    simp at hk
  have hlogic : ∀ (e : Term) (X : Finset Atom), e.locallyClosed → e.support ⊆ X →
      e.logicSupport ⊆ X.image LogicVar.free := by
    intro e X closed support
    have he : e.logicSupport = e.support.image LogicVar.free := by
      rw [← freeAtomSet_term_logicSupport e]
      exact LogicVar.eq_image_free_of_locallyClosed (termLogicSupport_locallyClosed e closed)
    rw [he]
    exact Finset.image_subset_image support
  have hP₁ : P₁.freeAtoms = A := by
    simp only [P₁, Formula.freeAtoms_impl, freeAtoms_resultAt,
      Formula.LogicVar.freeAtomSet_image_free, LogicVar.freeAtoms, Finset.union_empty]
    rw [Finset.union_eq_left.2 support₁, Finset.union_eq_left.2 supportQ]
  have hP₂ : P₂.freeAtoms = B := by
    simp only [P₂, Formula.freeAtoms_impl, freeAtoms_resultAt,
      Formula.LogicVar.freeAtomSet_image_free, LogicVar.freeAtoms, Finset.union_empty]
    rw [Finset.union_eq_left.2 support₂,
      Finset.union_eq_left.2 (Finset.Subset.trans supportQ hAB)]
  have hopen : ∀ (X : Finset Atom) (e : Term) (y : Atom),
      e.locallyClosed → e.support ⊆ X → y ∉ X →
      (resultAt (X.image LogicVar.free) e (.bound 0)).openAt 0 y =
        resultAt (X.image LogicVar.free) e (.free y) := by
    intro X e y closed support fresh
    have hi := resultAt_shift_openAt (X.image LogicVar.free) e y (hclosed X) closed
      (hlogic e X closed support) (by simpa using fresh)
    rw [LogicVar.image_shiftFrom_eq_of_locallyClosed _ 0 (hclosed X),
      shiftTerm_eq_of_locallyClosed e closed] at hi
    exact hi
  obtain ⟨_, L, hall⟩ := (Formula.models_all_iff_refines m P₁).1 h
  apply (Formula.models_all_iff_refines m P₂).2
  refine ⟨by rw [hP₂]; exact scope, L, ?_⟩
  intro y hyL hyP n href hndom
  have hyB : y ∉ B := by rwa [hP₂] at hyP
  have hyA : y ∉ A := fun hy => hyB (hAB hy)
  have hQopen : (Q.openAt 0 y).freeAtoms ⊆ A ∪ {y} := by
    intro x hx
    rcases Finset.mem_union.1 (Formula.freeAtoms_openAt_subset Q 0 y hx) with hx | hx
    · exact Finset.mem_union_right _ hx
    · exact Finset.mem_union_left _ (supportQ hx)
  have hRfree : (resultAt (B.image LogicVar.free) e₂ (.free y)).freeAtoms = B ∪ {y} := by
    simp only [freeAtoms_resultAt, Formula.LogicVar.freeAtomSet_image_free,
      LogicVar.freeAtoms, Finset.union_eq_left.2 support₂]
  have hn : n.domain = B ∪ {y} := by rwa [hP₂] at hndom
  change n ⊨ ((resultAt (B.image LogicVar.free) e₂ (.bound 0)).openAt 0 y ⇒ᶜ
    Q.openAt 0 y)
  rw [hopen B e₂ y closed₂ support₂ hyB]
  apply Formula.models_impl_intro
  · simp only [Formula.freeAtoms_impl]
    rw [hRfree, hn]
    exact Finset.union_subset (Finset.Subset.refl _)
      (Finset.Subset.trans hQopen (Finset.union_subset_union hAB (Finset.Subset.refl _)))
  · intro k hnk hres
    have hnk' : n ⊑ k := by
      simp only [Formula.freeAtoms_impl] at hnk
      have hp : (resultAt (B.image LogicVar.free) e₂ (.free y)).freeAtoms ∪
          (Q.openAt 0 y).freeAtoms = B ∪ {y} := by
        rw [hRfree]
        exact Finset.union_eq_left.2
          (Finset.Subset.trans hQopen (Finset.union_subset_union hAB (Finset.Subset.refl _)))
      rwa [hp, ← hn, Capability.restrict_domain_self] at hnk
    have href' : m.restrict B ⊑ n := by rwa [hP₂] at href
    have hmB : m.restrict B = k.restrict B := by
      have hr := Capability.refines_trans href' hnk'
      change m.restrict B = k.restrict (m.restrict B).domain at hr
      rwa [Capability.restrict_domain, Finset.inter_eq_right.2 scope] at hr
    have hevalK : ∀ σ, σ ∈ k → ∀ v,
        (instantiateTerm e₁ σ.toAssignment).reaches v ↔
          (instantiateTerm e₂ σ.toAssignment).reaches v := by
      intro σ hσ v
      have hσm : σ.restrict B ∈ m.restrict B := by
        rw [hmB]
        exact ⟨σ, hσ, rfl⟩
      obtain ⟨ρ, hρ, hsame⟩ := hσm
      have hinst₁ := instantiateTerm_eq_of_restrict_eq e₁ (B.image LogicVar.free) σ ρ
        (hclosed B) (hlogic e₁ B closed₁ (Finset.Subset.trans support₁ hAB))
        (by simpa only [Formula.LogicVar.freeAtomSet_image_free] using hsame.symm)
      have hinst₂ := instantiateTerm_eq_of_restrict_eq e₂ (B.image LogicVar.free) σ ρ
        (hclosed B) (hlogic e₂ B closed₂ support₂)
        (by simpa only [Formula.LogicVar.freeAtomSet_image_free] using hsame.symm)
      rw [hinst₁, hinst₂]
      exact heval ρ hρ v
    have hres₁ : k ⊨ resultAt (B.image LogicVar.free) e₁ (.free y) :=
      models_resultAt_of_reaches_iff (hclosed B) (hlogic e₂ B closed₂ support₂)
        (hlogic e₁ B closed₁ (Finset.Subset.trans support₁ hAB))
        (by simpa using hyB) (fun σ hσ v => (hevalK σ hσ v).symm) hres
    let r := k.restrict (A ∪ {y})
    have hresA : r ⊨ resultAt (A.image LogicVar.free) e₁ (.free y) := by
      have hr := models_resultAt_restrict_support (hclosed B) (Finset.image_subset_image hAB)
        (hlogic e₁ A closed₁ support₁) (by simpa using hyB) hres₁
      simpa only [Formula.LogicVar.freeAtomSet_image_free] using hr
    have hrdom : r.domain = A ∪ {y} := by
      rw [Capability.restrict_domain, Finset.inter_eq_right]
      exact Finset.Subset.trans
        (Finset.union_subset_union hAB (Finset.Subset.refl _))
        (by rw [← hRfree]; exact Formula.models_scope hres)
    have hbase : m.restrict A ⊑ r := by
      change m.restrict A = r.restrict (m.restrict A).domain
      rw [Capability.restrict_domain,
        Finset.inter_eq_right.2 (Finset.Subset.trans hAB scope)]
      change m.restrict A = (k.restrict (A ∪ {y})).restrict A
      rw [Capability.restrict_restrict, Finset.inter_eq_right.2 Finset.subset_union_left]
      calc
        m.restrict A = (m.restrict B).restrict A := by
          rw [Capability.restrict_restrict, Finset.inter_eq_right.2 hAB]
        _ = (k.restrict B).restrict A := by rw [hmB]
        _ = k.restrict A := by
          rw [Capability.restrict_restrict, Finset.inter_eq_right.2 hAB]
    have hsource : r ⊨ P₁.openAt 0 y := hall y hyL (by rwa [hP₁]) r
      (by rwa [hP₁]) (by rwa [hP₁])
    have hQR : r ⊨ Q.openAt 0 y := by
      change r ⊨ ((resultAt (A.image LogicVar.free) e₁ (.bound 0)).openAt 0 y ⇒ᶜ
        Q.openAt 0 y) at hsource
      rw [hopen A e₁ y closed₁ support₁ hyA] at hsource
      exact Formula.models_impl_elim hsource hresA
    exact (Formula.models_restrict_superset k (Q.openAt 0 y) hQopen).2 hQR

/-- Compose an exact result graph with a returned result alias. -/
theorem models_resultAt_compose_ret {m : Capability}
    {X : Finset LogicVar} {e : Term} {y z : Atom}
    (closedX : LogicVar.LocallyClosed X)
    (support : e.logicSupport ⊆ X)
    (freshY : LogicVar.free y ∉ X)
    (freshZ : LogicVar.free z ∉ insert (.free y) X)
    (hxy : m ⊨ resultAt X e (.free y))
    (hyz : m ⊨ resultAt (insert (.free y) X)
      (.ret (.free y)) (.free z)) :
    m ⊨ resultAt X e (.free z) := by
  let Y := insert (.free y) X
  have closedY : LogicVar.LocallyClosed Y := by
    intro k hk
    simp only [Y, Finset.mem_insert] at hk
    rcases hk with hk | hk
    · simp at hk
    · exact closedX k hk
  have supportY : (.ret (.free y) : Term).logicSupport ⊆ Y := by
    simp [Y, Term.logicSupportAt, Value.logicSupportAt]
  have freshZX : LogicVar.free z ∉ X := fun hz => freshZ (by simp [hz])
  apply models_resultAt_intro closedX support freshZX
  · intro x hx
    rcases Finset.mem_union.1 hx with hx | hx
    · apply Formula.models_scope hyz
      rw [freeAtoms_resultAt]
      apply Finset.mem_union_left
      apply Finset.mem_union_left
      rw [LogicVar.mem_freeAtomSet_iff]
      rw [LogicVar.mem_freeAtomSet_iff] at hx
      exact Finset.mem_insert_of_mem hx
    · have hxz : x = z := Finset.mem_singleton.1 hx
      subst x
      apply Formula.models_scope hyz
      rw [freeAtoms_resultAt]
      simp [LogicVar.freeAtoms]
  · intro σ hσ
    obtain ⟨v, hyv, heval⟩ :=
      models_resultAt_lookup closedX support freshY hxy σ hσ
    obtain ⟨w, hzw, hyreach⟩ :=
      models_resultAt_lookup closedY supportY freshZ hyz σ hσ
    have hwv : w = v := by
      have hret : (Term.ret v).reaches w := by
        simpa [instantiateTerm, instantiateTermAt, instantiateValueAt,
          Store.toAssignment_lookup_free, hyv] using hyreach
      exact Term.ret.inj hret.ret_eq
    subst w
    exact ⟨v, hzw, heval⟩
  · intro σ hσ v heval
    obtain ⟨ρ, hρ, hρX, hρy⟩ :=
      models_resultAt_complete closedX support freshY hxy σ hσ v heval
    have hreaches :
        (instantiateTerm (.ret (.free y)) ρ.toAssignment).reaches v := by
      simpa [instantiateTerm, instantiateTermAt, instantiateValueAt,
        Store.toAssignment_lookup_free, hρy] using
        (Steps.refl (.ret v) heval.target_closed)
    obtain ⟨υ, hυ, hυY, hυz⟩ :=
      models_resultAt_complete closedY supportY freshZ hyz ρ hρ v hreaches
    refine ⟨υ, hυ, ?_, hυz⟩
    let A := LogicVar.freeAtomSet X
    let B := LogicVar.freeAtomSet Y
    have hAB : A ⊆ B := by
      intro x hx
      rw [LogicVar.mem_freeAtomSet_iff] at hx ⊢
      exact Finset.mem_insert_of_mem hx
    calc
      υ.restrict A = (υ.restrict B).restrict A := by
        rw [Store.restrict_restrict, Finset.inter_eq_right.2 hAB]
      _ = (ρ.restrict B).restrict A := by rw [hυY]
      _ = ρ.restrict A := by
        rw [Store.restrict_restrict, Finset.inter_eq_right.2 hAB]
      _ = σ.restrict A := hρX

/-- Compose a result graph after moving its source along the projection order.
This is the form used when a fresh result binder extends a source fiber. -/
theorem models_resultAt_compose_ret_of_refines {m n : Capability}
    {X : Finset LogicVar} {e : Term} {y z : Atom}
    (closedX : LogicVar.LocallyClosed X)
    (support : e.logicSupport ⊆ X)
    (freshY : LogicVar.free y ∉ X)
    (freshZ : LogicVar.free z ∉ insert (.free y) X)
    (refines : m ⊑ n)
    (hxy : m ⊨ resultAt X e (.free y))
    (hyz : n ⊨ resultAt (insert (.free y) X)
      (.ret (.free y)) (.free z)) :
    n ⊨ resultAt X e (.free z) := by
  exact models_resultAt_compose_ret closedX support freshY freshZ
    (Formula.models_kripke refines hxy) hyz

theorem models_resultAt_ret_free_lookup {m : Capability}
    {X : Finset LogicVar} {y z : Atom}
    (closedX : LogicVar.LocallyClosed X)
    (support : (.ret (.free y) : Term).logicSupport ⊆ X)
    (fresh : LogicVar.free z ∉ X)
    (h : m ⊨ resultAt X (.ret (.free y)) (.free z)) :
    ∀ σ, σ ∈ m → σ.lookup z = σ.lookup y := by
  intro σ hσ
  obtain ⟨v, hz, reaches⟩ :=
    models_resultAt_lookup closedX support fresh h σ hσ
  have hyX : LogicVar.free y ∈ X := by
    apply support
    simp [Term.logicSupportAt, Value.logicSupportAt]
  have hyM : y ∈ m.domain := by
    apply Formula.models_scope h
    rw [freeAtoms_resultAt]
    apply Finset.mem_union_left
    apply Finset.mem_union_left
    exact (LogicVar.mem_freeAtomSet_iff X y).2 hyX
  obtain ⟨w, hy⟩ := Store.mem_domain_iff σ y |>.1 (by
    simpa [m.mem_domain hσ] using hyM)
  have heq : v = w := by
    have : (Term.ret w).reaches v := by
      simpa [instantiateTerm, instantiateTermAt, instantiateValueAt,
        Store.toAssignment_lookup_free, hy] using reaches
    exact Term.ret.inj this.ret_eq
  rw [hz, hy, heq]

/-- The capability of all results over the observed input stores.  Every
input must have a result, but the constructor does not assert termination. -/
def resultCapability (m : Capability) (X : Finset Atom) (e : Term) (y : Atom)
    (scope : X ⊆ m.domain)
    (returns : ∀ σ, σ ∈ m → ∃ v, (instantiateTerm e σ.toAssignment).reaches v) :
    Capability where
  domain := X ∪ {y}
  stores := fun ρ => ∃ σ, σ ∈ m ∧ ∃ v,
    (instantiateTerm e σ.toAssignment).reaches v ∧
      ρ = (σ.restrict X).merge (Store.singleton y v)
  nonempty := by
    obtain ⟨σ, hσ⟩ := m.nonempty
    obtain ⟨v, hv⟩ := returns σ hσ
    exact ⟨(σ.restrict X).merge (Store.singleton y v), σ, hσ, v, hv, rfl⟩
  fixedDomain := by
    rintro ρ ⟨σ, hσ, v, hv, rfl⟩
    rw [Store.domain_merge, Store.domain_restrict, m.mem_domain hσ,
      Finset.inter_eq_right.2 scope, Store.domain_singleton]

@[simp] theorem resultCapability_domain (m : Capability) (X : Finset Atom)
    (e : Term) (y : Atom) (scope : X ⊆ m.domain)
    (returns : ∀ σ, σ ∈ m → ∃ v, (instantiateTerm e σ.toAssignment).reaches v) :
    (resultCapability m X e y scope returns).domain = X ∪ {y} := rfl

theorem resultCapability_restrict (m : Capability) (X : Finset Atom)
    (e : Term) (y : Atom) (scope : X ⊆ m.domain)
    (returns : ∀ σ, σ ∈ m → ∃ v, (instantiateTerm e σ.toAssignment).reaches v) :
    (resultCapability m X e y scope returns).restrict X = m.restrict X := by
  have hdom : ∀ σ, σ ∈ m → (σ.restrict X).domain = X := by
    intro σ hσ
    rw [Store.domain_restrict, m.mem_domain hσ, Finset.inter_eq_right.2 scope]
  apply Capability.ext
  · simp [Finset.inter_eq_right.2 scope]
  · intro ρ
    constructor
    · rintro ⟨υ, ⟨σ, hσ, v, hv, rfl⟩, rfl⟩
      exact ⟨σ, hσ, (Store.restrict_merge_left_full (hdom σ hσ)).symm⟩
    · rintro ⟨σ, hσ, rfl⟩
      obtain ⟨v, hv⟩ := returns σ hσ
      exact ⟨(σ.restrict X).merge (Store.singleton y v),
        ⟨σ, hσ, v, hv, rfl⟩, Store.restrict_merge_left_full (hdom σ hσ)⟩

theorem models_resultCapability (m : Capability) (X : Finset Atom)
    (e : Term) (y : Atom) (scope : X ⊆ m.domain)
    (returns : ∀ σ, σ ∈ m → ∃ v, (instantiateTerm e σ.toAssignment).reaches v)
    (closed : e.locallyClosed) (support : e.support ⊆ X) (fresh : y ∉ X) :
    resultCapability m X e y scope returns ⊨ resultAt (X.image LogicVar.free) e (.free y) := by
  have hclosed : LogicVar.LocallyClosed (X.image LogicVar.free) := by
    intro k hk
    simp at hk
  have hlogic : e.logicSupport ⊆ X.image LogicVar.free := by
    rw [LogicVar.eq_image_free_of_locallyClosed (termLogicSupport_locallyClosed e closed),
      freeAtomSet_term_logicSupport]
    exact Finset.image_subset_image support
  have hdom : ∀ σ, σ ∈ m → (σ.restrict X).domain = X := by
    intro σ hσ
    rw [Store.domain_restrict, m.mem_domain hσ, Finset.inter_eq_right.2 scope]
  have hbase : ∀ σ, σ ∈ m → ∀ v,
      ((σ.restrict X).merge (Store.singleton y v)).restrict X = σ.restrict X := by
    intro σ hσ v
    exact Store.restrict_merge_left_full (hdom σ hσ)
  have hinst : ∀ σ, σ ∈ m → ∀ v,
      instantiateTerm e ((σ.restrict X).merge (Store.singleton y v)).toAssignment =
        instantiateTerm e σ.toAssignment := by
    intro σ hσ v
    apply instantiateTerm_eq_of_restrict_eq e (X.image LogicVar.free) _ _ hclosed hlogic
    simpa only [Formula.LogicVar.freeAtomSet_image_free] using hbase σ hσ v
  have hlookup : ∀ σ, σ ∈ m → ∀ v,
      ((σ.restrict X).merge (Store.singleton y v)).lookup y = some v := by
    intro σ hσ v
    rw [Store.lookup_merge_right _ _ (by
      rw [hdom σ hσ]
      exact fresh),
      Store.lookup_singleton]
  apply models_resultAt_intro hclosed hlogic (by simpa using fresh)
  · simp only [Formula.LogicVar.freeAtomSet_image_free, resultCapability_domain]
    exact Finset.Subset.refl _
  · rintro ρ ⟨σ, hσ, v, hv, rfl⟩
    refine ⟨v, hlookup σ hσ v, ?_⟩
    rwa [hinst σ hσ v]
  · rintro ρ ⟨σ, hσ, v, hv, rfl⟩ w hw
    rw [hinst σ hσ v] at hw
    refine ⟨(σ.restrict X).merge (Store.singleton y w),
      ⟨σ, hσ, w, hw, rfl⟩, ?_, hlookup σ hσ w⟩
    simp only [Formula.LogicVar.freeAtomSet_image_free, hbase σ hσ]

/-- Replacing the named result `y` by an alias `z` preserves exactly the
observations of `B`, even when `e` has several results for each input. -/
theorem resultCapability_projection_alias {m k : Capability} {A B : Finset Atom}
    {e : Term} {y z : Atom} (scope : A ⊆ m.domain)
    (returns : ∀ σ, σ ∈ m → ∃ v, (instantiateTerm e σ.toAssignment).reaches v)
    (support : e.logicSupport ⊆ A.image LogicVar.free)
    (hBA : B ⊆ A) (freshY : y ∉ A) (freshZ : z ∉ A)
    (hres : m ⊨ resultAt (A.image LogicVar.free) e (.free y))
    (base : k.restrict (B ∪ {y}) = m.restrict (B ∪ {y}))
    (hlookup : ∀ ρ, ρ ∈ k → ρ.lookup z = ρ.lookup y) :
    (resultCapability m A e z scope returns).restrict (B ∪ {z}) =
      k.restrict (B ∪ {z}) := by
  have hclosed : LogicVar.LocallyClosed (A.image LogicVar.free) := by
    intro j hj
    simp at hj
  have hdom : ∀ σ, σ ∈ m → (σ.restrict A).domain = A := by
    intro σ hσ
    rw [Store.domain_restrict, m.mem_domain hσ, Finset.inter_eq_right.2 scope]
  have hcompare : ∀ σ, σ ∈ m → ∀ v, σ.lookup y = some v →
      ∀ ρ, ρ ∈ k → ρ.restrict (B ∪ {y}) = σ.restrict (B ∪ {y}) →
      ((σ.restrict A).merge (Store.singleton z v)).restrict (B ∪ {z}) =
        ρ.restrict (B ∪ {z}) := by
    intro σ hσ v hv ρ hρ same
    apply Store.ext
    intro x
    by_cases hx : x ∈ B ∪ {z}
    · simp only [Store.lookup_restrict, if_pos hx]
      by_cases hxB : x ∈ B
      · rw [Store.lookup_merge_left _ _ (by
          rw [hdom σ hσ]
          exact hBA hxB),
          Store.lookup_restrict, if_pos (hBA hxB)]
        have heq := congrArg (fun s : Store => s.lookup x) same
        simpa only [Store.lookup_restrict,
          if_pos (Finset.mem_union_left {y} hxB)] using heq.symm
      · have hxz : x = z := by simpa only [Finset.mem_union, hxB, false_or,
          Finset.mem_singleton] using hx
        subst x
        rw [Store.lookup_merge_right _ _ (by
          rw [hdom σ hσ]
          exact freshZ),
          Store.lookup_singleton, hlookup ρ hρ]
        have heq := congrArg (fun s : Store => s.lookup y) same
        have hy : ρ.lookup y = σ.lookup y := by
          simpa only [Store.lookup_restrict,
            if_pos (Finset.mem_union_right B (Finset.mem_singleton_self y))] using heq
        exact hv.symm.trans hy.symm
    · simp only [Store.lookup_restrict, if_neg hx]
  have hstores : ∀ ρ : Store,
      ρ ∈ (resultCapability m A e z scope returns).restrict (B ∪ {z}) ↔
        ρ ∈ k.restrict (B ∪ {z}) := by
    intro ρ
    constructor
    · rintro ⟨υ, ⟨σ, hσ, v, hv, rfl⟩, rfl⟩
      obtain ⟨σ', hσ', same, result⟩ :=
        models_resultAt_complete hclosed support (by simpa using freshY) hres σ hσ v hv
      have hσ'C : σ'.restrict (B ∪ {y}) ∈ k.restrict (B ∪ {y}) := by
        rw [base]
        exact ⟨σ', hσ', rfl⟩
      obtain ⟨ρ', hρ', hproj⟩ := hσ'C
      refine ⟨ρ', hρ', ?_⟩
      have hc := hcompare σ' hσ' v result ρ' hρ' hproj
      rw [Formula.LogicVar.freeAtomSet_image_free] at same
      rw [same] at hc
      exact hc.symm
    · rintro ⟨υ, hυ, rfl⟩
      have hυC : υ.restrict (B ∪ {y}) ∈ m.restrict (B ∪ {y}) := by
        rw [← base]
        exact ⟨υ, hυ, rfl⟩
      obtain ⟨σ, hσ, hproj⟩ := hυC
      obtain ⟨v, hv, heval⟩ :=
        models_resultAt_lookup hclosed support (by simpa using freshY) hres σ hσ
      exact ⟨(σ.restrict A).merge (Store.singleton z v),
        ⟨σ, hσ, v, heval, rfl⟩, hcompare σ hσ v hv υ hυ hproj.symm⟩
  apply Capability.ext
  · obtain ⟨σ, hσ⟩ := (resultCapability m A e z scope returns).restrict (B ∪ {z}) |>.nonempty
    exact ((resultCapability m A e z scope returns).restrict (B ∪ {z})).mem_domain hσ |>.symm.trans
      ((k.restrict (B ∪ {z})).mem_domain ((hstores σ).1 hσ))
  · exact hstores

/-- Naming a nondeterministic result preserves universal result-first
obligations whose body only observes `B` and the result binder. -/
theorem models_all_result_alias {m : Capability} {A B : Finset Atom}
    {e : Term} {y : Atom} {Q : Formula}
    (closed : e.locallyClosed) (support : e.support ⊆ A)
    (hBA : B ⊆ A) (supportQ : Q.freeAtoms ⊆ B) (fresh : y ∉ A)
    (hres : m ⊨ resultAt (A.image LogicVar.free) e (.free y))
    (hsource : m ⊨ Formula.all (resultAt (A.image LogicVar.free) e (.bound 0) ⇒ᶜ Q)) :
    m ⊨ Formula.all
      (resultAt ((B ∪ {y}).image LogicVar.free) (.ret (.free y)) (.bound 0) ⇒ᶜ Q) := by
  let C := B ∪ {y}
  let P₁ := resultAt (A.image LogicVar.free) e (.bound 0) ⇒ᶜ Q
  let P₂ := resultAt (C.image LogicVar.free) (.ret (.free y)) (.bound 0) ⇒ᶜ Q
  have hclosed : ∀ X : Finset Atom, LogicVar.LocallyClosed (X.image LogicVar.free) := by
    intro X j hj
    simp at hj
  have hlogic : ∀ (e : Term) (X : Finset Atom), e.locallyClosed → e.support ⊆ X →
      e.logicSupport ⊆ X.image LogicVar.free := by
    intro e X he hs
    rw [LogicVar.eq_image_free_of_locallyClosed (termLogicSupport_locallyClosed e he),
      freeAtomSet_term_logicSupport]
    exact Finset.image_subset_image hs
  have retClosed : (.ret (.free y) : Term).locallyClosed := by
    simp [Term.locallyClosedAt, Value.locallyClosedAt]
  have retSupport : (.ret (.free y) : Term).support ⊆ C := by
    simp [C, Term.support, Value.support]
  have hP₁ : P₁.freeAtoms = A := by
    simp only [P₁, Formula.freeAtoms_impl, freeAtoms_resultAt,
      Formula.LogicVar.freeAtomSet_image_free, LogicVar.freeAtoms, Finset.union_empty]
    rw [Finset.union_eq_left.2 support,
      Finset.union_eq_left.2 (Finset.Subset.trans supportQ hBA)]
  have hP₂ : P₂.freeAtoms = C := by
    simp only [P₂, Formula.freeAtoms_impl, freeAtoms_resultAt,
      Formula.LogicVar.freeAtomSet_image_free, LogicVar.freeAtoms, Finset.union_empty]
    rw [Finset.union_eq_left.2 retSupport,
      Finset.union_eq_left.2 (Finset.Subset.trans supportQ Finset.subset_union_left)]
  have hscope : A ∪ {y} ⊆ m.domain := by
    have hs := Formula.models_scope hres
    simpa only [freeAtoms_resultAt, Formula.LogicVar.freeAtomSet_image_free,
      Finset.union_eq_left.2 support, LogicVar.freeAtoms] using hs
  have scopeA : A ⊆ m.domain := Finset.Subset.trans Finset.subset_union_left hscope
  have scopeC : C ⊆ m.domain := Finset.Subset.trans
    (Finset.union_subset_union hBA (Finset.Subset.refl _)) hscope
  have returns : ∀ σ, σ ∈ m → ∃ v, (instantiateTerm e σ.toAssignment).reaches v := by
    intro σ hσ
    obtain ⟨v, _, hv⟩ := models_resultAt_lookup (hclosed A) (hlogic e A closed support)
      (by simpa using fresh) hres σ hσ
    exact ⟨v, hv⟩
  have hopen : ∀ (X : Finset Atom) (e : Term) (z : Atom),
      e.locallyClosed → e.support ⊆ X → z ∉ X →
      (resultAt (X.image LogicVar.free) e (.bound 0)).openAt 0 z =
        resultAt (X.image LogicVar.free) e (.free z) := by
    intro X e z he hs hz
    have hi := resultAt_shift_openAt (X.image LogicVar.free) e z (hclosed X) he
      (hlogic e X he hs) (by simpa using hz)
    rw [LogicVar.image_shiftFrom_eq_of_locallyClosed _ 0 (hclosed X),
      shiftTerm_eq_of_locallyClosed e he] at hi
    exact hi
  obtain ⟨_, L, hall⟩ := (Formula.models_all_iff_refines m P₁).1 hsource
  apply (Formula.models_all_iff_refines m P₂).2
  refine ⟨by
    rw [hP₂]
    exact scopeC, L ∪ A, ?_⟩
  intro z hzL hzP n href hndom
  have hzL' : z ∉ L := fun hz => hzL (Finset.mem_union_left A hz)
  have hzA : z ∉ A := fun hz => hzL (Finset.mem_union_right L hz)
  have hzC : z ∉ C := by rwa [hP₂] at hzP
  have hQscope : (Q.openAt 0 z).freeAtoms ⊆ B ∪ {z} := by
    intro x hx
    rcases Finset.mem_union.1 (Formula.freeAtoms_openAt_subset Q 0 z hx) with hx | hx
    · exact Finset.mem_union_right _ hx
    · exact Finset.mem_union_left _ (supportQ hx)
  have hRfree : (resultAt (C.image LogicVar.free) (.ret (.free y)) (.free z)).freeAtoms =
      C ∪ {z} := by
    simp only [freeAtoms_resultAt, Formula.LogicVar.freeAtomSet_image_free,
      Finset.union_eq_left.2 retSupport, LogicVar.freeAtoms]
  have hn : n.domain = C ∪ {z} := by rwa [hP₂] at hndom
  change n ⊨ ((resultAt (C.image LogicVar.free) (.ret (.free y)) (.bound 0)).openAt 0 z ⇒ᶜ
    Q.openAt 0 z)
  rw [hopen C (.ret (.free y)) z retClosed retSupport hzC]
  have hQC : (Q.openAt 0 z).freeAtoms ⊆ C ∪ {z} :=
    Finset.Subset.trans hQscope (Finset.union_subset_union Finset.subset_union_left
      (Finset.Subset.refl _))
  apply Formula.models_impl_intro
  · simp only [Formula.freeAtoms_impl, hRfree, hn]
    exact Finset.union_subset (Finset.Subset.refl _) hQC
  · intro k hnk hret
    have hnk' : n ⊑ k := by
      simp only [Formula.freeAtoms_impl, hRfree,
        Finset.union_eq_left.2 hQC] at hnk
      rw [← hn, Capability.restrict_domain_self] at hnk
      exact hnk
    have hmk : m.restrict C ⊑ k := Capability.refines_trans
      (by rwa [hP₂] at href) hnk'
    have base : k.restrict C = m.restrict C := by
      change m.restrict C = k.restrict (m.restrict C).domain at hmk
      rw [Capability.restrict_domain, Finset.inter_eq_right.2 scopeC] at hmk
      exact hmk.symm
    let g := resultCapability m A e z scopeA returns
    have hg : g ⊨ resultAt (A.image LogicVar.free) e (.free z) :=
      models_resultCapability m A e z scopeA returns closed support hzA
    have hgbase : m.restrict P₁.freeAtoms ⊑ g := by
      rw [hP₁]
      change m.restrict A = g.restrict (m.restrict A).domain
      rw [Capability.restrict_domain, Finset.inter_eq_right.2 scopeA]
      exact (resultCapability_restrict m A e z scopeA returns).symm
    have hgdom : g.domain = P₁.freeAtoms ∪ {z} := by
      rw [hP₁]
      rfl
    have hbody := hall z hzL' (by rwa [hP₁]) g hgbase hgdom
    change g ⊨ ((resultAt (A.image LogicVar.free) e (.bound 0)).openAt 0 z ⇒ᶜ
      Q.openAt 0 z) at hbody
    rw [hopen A e z closed support hzA] at hbody
    have hQ := Formula.models_impl_elim hbody hg
    have same := resultCapability_projection_alias scopeA returns (hlogic e A closed support)
      hBA fresh hzA hres base
      (models_resultAt_ret_free_lookup (hclosed C) (hlogic _ C retClosed retSupport)
        (by simpa using hzC) hret)
    exact (Formula.models_projection (B ∪ {z}) hQscope same).1 hQ

theorem models_resultAt_ret_lookup_eq_of_restrict_eq {m : Capability}
    {X : Finset LogicVar} {v : Value} {y : Atom}
    (closedX : LogicVar.LocallyClosed X)
    (support : (.ret v : Term).logicSupport ⊆ X)
    (fresh : LogicVar.free y ∉ X)
    (h : m ⊨ resultAt X (.ret v) (.free y))
    {σ ρ : Store} (hσ : σ ∈ m) (hρ : ρ ∈ m)
    (same : σ.restrict (LogicVar.freeAtomSet X) =
      ρ.restrict (LogicVar.freeAtomSet X)) :
    σ.lookup y = ρ.lookup y := by
  obtain ⟨u, hyσ, hu⟩ :=
    models_resultAt_lookup closedX support fresh h σ hσ
  obtain ⟨w, hyρ, hw⟩ :=
    models_resultAt_lookup closedX support fresh h ρ hρ
  have hagree : ∀ ξ, ξ ∈ v.logicSupport →
      σ.toAssignment.lookup ξ = ρ.toAssignment.lookup ξ := by
    intro ξ hξ
    have hξX := support (by simpa [Term.logicSupportAt] using hξ)
    cases ξ with
    | bound k => exact (closedX k hξX).elim
    | free x =>
        simp only [Store.toAssignment_lookup_free]
        have hs := congrArg (fun s => s.lookup x) same
        have hx : x ∈ LogicVar.freeAtomSet X :=
          (LogicVar.mem_freeAtomSet_iff X x).2 hξX
        simpa [Store.lookup_restrict, hx] using hs
  have hv : instantiateValueAt v 0 σ.toAssignment =
      instantiateValueAt v 0 ρ.toAssignment :=
    instantiateValueAt_eq_of_agreeOn v 0 hagree
  have hu' : u = instantiateValueAt v 0 σ.toAssignment := by
    exact Term.ret.inj hu.ret_eq
  have hw' : w = instantiateValueAt v 0 ρ.toAssignment := by
    exact Term.ret.inj hw.ret_eq
  rw [hyσ, hyρ, hu', hw', hv]

theorem models_resultFirst_openAt_lookup {m : Capability}
    {Δ : BasicEnv} {τ : ContextType} {e : Term} {y : Atom}
    (closed : LogicVar.LocallyClosed (relevantSupport Δ τ e))
    (closedE : e.locallyClosed)
    (support : e.logicSupport ⊆ relevantSupport Δ τ e)
    (fresh : LogicVar.free y ∉ relevantSupport Δ τ e)
    (h : m ⊨ (resultFirst Δ τ e).openAt 0 y) :
    ∀ σ, σ ∈ m → ∃ v, σ.lookup y = some v ∧
      (instantiateTerm e σ.toAssignment).reaches v := by
  rw [resultFirst_openAt Δ τ e y closed closedE support fresh] at h
  exact models_resultAt_lookup closed support fresh h

theorem models_resultFirst_ret_free_openAt_lookup {m : Capability}
    {Δ : BasicEnv} {τ : ContextType} {y z : Atom}
    (closed : LogicVar.LocallyClosed
      (relevantSupport Δ τ (.ret (.free y))))
    (support : (.ret (.free y) : Term).logicSupport ⊆
      relevantSupport Δ τ (.ret (.free y)))
    (fresh : LogicVar.free z ∉
      relevantSupport Δ τ (.ret (.free y)))
    (h : m ⊨ (resultFirst Δ τ (.ret (.free y))).openAt 0 z) :
    ∀ σ, σ ∈ m → σ.lookup z = σ.lookup y := by
  rw [resultFirst_openAt Δ τ (.ret (.free y)) z closed
    (by trivial) support fresh] at h
  exact models_resultAt_ret_free_lookup closed support fresh h

theorem models_resultFirst_ret_openAt_singleton
    {F : Capability.FiberExtension} {σ : Store} {m : Capability}
    {Δ : BasicEnv} {τ : ContextType} {v : Value} {y : Atom}
    (hExt : F.Extends (Capability.singleton σ) m)
    (hout : F.output = {y})
    (hX : LogicVar.freeAtomSet (relevantSupport Δ τ (.ret v)) ⊆ σ.domain)
    (closed : LogicVar.LocallyClosed (relevantSupport Δ τ (.ret v)))
    (closedV : v.locallyClosed)
    (support : (.ret v : Term).logicSupport ⊆
      relevantSupport Δ τ (.ret v))
    (fresh : LogicVar.free y ∉ relevantSupport Δ τ (.ret v))
    (h : m ⊨ (resultFirst Δ τ (.ret v)).openAt 0 y) :
    ∃ ρ, ρ ∈ m ∧ m = Capability.singleton ρ := by
  rw [resultFirst_openAt Δ τ (.ret v) y closed closedV support fresh] at h
  apply hExt.singleton_of_output_lookup hout
  intro ρ hρ υ hυ
  apply models_resultAt_ret_lookup_eq_of_restrict_eq closed support fresh h hρ hυ
  calc
    ρ.restrict (LogicVar.freeAtomSet (relevantSupport Δ τ (.ret v))) =
        (ρ.restrict σ.domain).restrict
          (LogicVar.freeAtomSet (relevantSupport Δ τ (.ret v))) := by
      rw [Store.restrict_restrict, Finset.inter_eq_right.2 hX]
    _ = (υ.restrict σ.domain).restrict
          (LogicVar.freeAtomSet (relevantSupport Δ τ (.ret v))) := by
      have hρbase : ρ.restrict σ.domain = σ := by
        have hmem : ρ.restrict (Capability.singleton σ).domain ∈
            m.restrict (Capability.singleton σ).domain := ⟨ρ, hρ, rfl⟩
        rw [hExt.restrict_base] at hmem
        exact hmem
      have hυbase : υ.restrict σ.domain = σ := by
        have hmem : υ.restrict (Capability.singleton σ).domain ∈
            m.restrict (Capability.singleton σ).domain := ⟨υ, hυ, rfl⟩
        rw [hExt.restrict_base] at hmem
        exact hmem
      rw [hρbase, hυbase]
    _ = υ.restrict
          (LogicVar.freeAtomSet (relevantSupport Δ τ (.ret v))) := by
      rw [Store.restrict_restrict, Finset.inter_eq_right.2 hX]

theorem models_resultAt_typed {m : Capability} {X : Finset LogicVar}
    {Δ : BasicEnv} {e : Term} {T : SimpleType} {y : Atom}
    (closedX : LogicVar.LocallyClosed X) (closedE : e.locallyClosed)
    (support : e.logicSupport ⊆ X) (fresh : LogicVar.free y ∉ X)
    (hres : m ⊨ resultAt X e (.free y))
    (htyped : m ⊨ basicTyping Δ e T) :
    ∀ σ, σ ∈ m → ∃ v, σ.lookup y = some v ∧ BasicValTyp ∅ v T := by
  intro σ hσ
  obtain ⟨v, hv, reaches⟩ :=
    models_resultAt_lookup closedX support fresh hres σ hσ
  exact ⟨v, hv, (models_basicTyping_term closedE htyped hσ).reaches reaches⟩

theorem models_basicTyping_ret_bound_openAt {m : Capability}
    {X : Finset LogicVar} {Δ Δ₀ : BasicEnv} {e : Term} {T : SimpleType}
    {y : Atom} (closedX : LogicVar.LocallyClosed X)
    (closedE : e.locallyClosed) (support : e.logicSupport ⊆ X)
    (fresh : LogicVar.free y ∉ X) (freshΔ : y ∉ Δ.domain)
    (hres : m ⊨ resultAt X e (.free y))
    (hworld : m ⊨ basicWorld Δ)
    (htyped : m ⊨ basicTyping Δ₀ e T) :
    m ⊨ (basicTyping Δ (.ret (.bound 0)) T).openAt 0 y := by
  unfold basicTyping Formula.fiberAtom
  simp only [Formula.openAt]
  let q := (basicTypingQualifier Δ (.ret (.bound 0)) T).openAt 0 y
  change m ⊨ Formula.fiberAtom q
  have hopenΔ : LogicVar.openSupport 0 y
      (Δ.domain.image LogicVar.free) = Δ.domain.image LogicVar.free := by
    apply LogicVar.openSupport_eq_self_of_fresh
    · simp
    · simpa using freshΔ
  have hqsupp : q.support = Δ.domain.image LogicVar.free ∪ {.free y} := by
    change LogicVar.openSupport 0 y
      (Δ.domain.image LogicVar.free ∪ {.bound 0}) = _
    rw [show LogicVar.openSupport 0 y
        (Δ.domain.image LogicVar.free ∪ {.bound 0}) =
          LogicVar.openSupport 0 y (Δ.domain.image LogicVar.free) ∪
            LogicVar.openSupport 0 y {.bound 0} by
      simp [LogicVar.openSupport]]
    rw [hopenΔ]
    simp [LogicVar.openSupport, LogicVar.openBinder, LogicVar.swap]
  have hqfree : q.freeAtoms = Δ.domain ∪ {y} := by
    change LogicVar.freeAtomSet q.support = Δ.domain ∪ {y}
    rw [hqsupp, Formula.LogicVar.freeAtomSet_union,
      Formula.LogicVar.freeAtomSet_image_free]
    simp
  have hscopeΔ := (models_basicWorld_iff m Δ).1 hworld |>.1
  have hyM : y ∈ m.domain := by
    apply Formula.models_scope hres
    simp [LogicVar.freeAtoms]
  apply (Formula.models_fiberAtom_iff m q).2
  refine ⟨?_, ?_, ?_⟩
  · intro k hk
    rw [hqsupp] at hk
    simp at hk
  · rw [hqfree]
    exact Finset.union_subset hscopeΔ (by simpa using hyM)
  · intro σ hσ
    obtain ⟨v, hv, hvT⟩ :=
      models_resultAt_typed closedX closedE support fresh hres htyped σ hσ
    let s := σ.restrict q.freeAtoms
    have hsdom : s.domain = q.freeAtoms := by
      simp only [s]
      rw [Store.domain_restrict, m.mem_domain hσ,
        Finset.inter_eq_right.2]
      rw [hqfree]
      exact Finset.union_subset hscopeΔ (by simpa using hyM)
    let a : AssignmentOn q.support :=
      { assignment := s.toAssignment
        domain_eq := by
          rw [Store.toAssignment_domain, hsdom, hqfree, hqsupp]
          simp }
    refine ⟨hsdom, a, ?_, ?_⟩
    · change (basicTypingQualifier Δ (.ret (.bound 0)) T).holds
        (a.swapBack (.bound 0) (.free y))
      refine ⟨by simp [Term.support, Value.support], ?_, ?_⟩
      · intro ξ U hU
        cases ξ with
        | bound k => simp at hU
        | free x =>
            obtain ⟨w, hw, hwU⟩ :=
              (models_basicWorld_iff m Δ).1 hworld |>.2 σ hσ x U hU
            refine ⟨w, ?_, hwU⟩
            have hxΔ : x ∈ Δ.domain := Finmap.mem_iff.mpr ⟨U, hU⟩
            have hxy : x ≠ y := fun same => freshΔ (same ▸ hxΔ)
            simp [a, s, hqfree, AssignmentOn.swapBack,
              Assignment.lookup_swap, LogicVar.swap, hxy, hxΔ,
              Store.lookup_restrict, hw]
      · simpa [a, s, hqfree, Store.lookup_restrict, hv,
          AssignmentOn.swapBack, Assignment.lookup_swap,
          LogicVar.swap, instantiateTerm, instantiateTermAt,
          instantiateValueAt] using BasicTermTyp.ret hvT
    · intro x
      simp [a, s]

theorem models_resultBasicTyping_openAt {m : Capability}
    {X : Finset LogicVar} {Δ : BasicEnv} {e : Term} {b : BaseType}
    {y : Atom} (closedX : LogicVar.LocallyClosed X)
    (closedE : e.locallyClosed) (support : e.logicSupport ⊆ X)
    (fresh : LogicVar.free y ∉ X)
    (hres : m ⊨ resultAt X e (.free y))
    (htyped : m ⊨ basicTyping Δ e (.base b)) :
    m ⊨ (resultBasicTyping b).openAt 0 y := by
  unfold resultBasicTyping basicTyping Formula.fiberAtom
  simp only [Formula.openAt]
  let q := (basicTypingQualifier ∅ (.ret (.bound 0)) (.base b)).openAt 0 y
  change m ⊨ Formula.fiberAtom q
  have hqsupp : q.support = {.free y} := by
    simp [q, basicTypingQualifier, Term.logicSupportAt,
      Value.logicSupportAt, boundLogicSupportAt, LogicVar.openSupport,
      LogicVar.openBinder, LogicVar.swap]
  have hqfree : q.freeAtoms = {y} := by
    change LogicVar.freeAtomSet q.support = {y}
    rw [hqsupp]
    simp
  apply (Formula.models_fiberAtom_iff m q).2
  refine ⟨?_, ?_, ?_⟩
  · intro k hk
    rw [hqsupp] at hk
    simp at hk
  · have hy : y ∈ m.domain := by
      apply Formula.models_scope hres
      simp [LogicVar.freeAtoms]
    simpa [hqfree] using hy
  · intro σ hσ
    obtain ⟨v, hv, hvT⟩ :=
      models_resultAt_typed closedX closedE support fresh hres htyped σ hσ
    let s := σ.restrict q.freeAtoms
    have hsdom : s.domain = q.freeAtoms := by
      simp only [s]
      rw [Store.domain_restrict, m.mem_domain hσ,
        Finset.inter_eq_right]
      rw [hqfree]
      intro x hx
      have hxy : x = y := Finset.mem_singleton.1 hx
      subst x
      exact Formula.models_scope hres (by simp [LogicVar.freeAtoms])
    let a : AssignmentOn q.support :=
      { assignment := s.toAssignment
        domain_eq := by
          rw [Store.toAssignment_domain, hsdom, hqfree]
          simp [hqsupp] }
    refine ⟨hsdom, a, ?_, ?_⟩
    · change (basicTypingQualifier ∅ (.ret (.bound 0)) (.base b)).holds
        (a.swapBack (.bound 0) (.free y))
      refine ⟨by simp [Term.support, Value.support], ?_, ?_⟩
      · intro ξ T hT
        cases ξ <;> simp at hT
      · simpa [a, s, hqfree, Store.lookup_restrict, hv,
          AssignmentOn.swapBack, Assignment.lookup_swap,
          LogicVar.swap, instantiateTerm, instantiateTermAt,
          instantiateValueAt] using BasicTermTyp.ret hvT
    · intro x
      simp [a, s]

theorem models_resultTotal_openAt {m : Capability}
    {X : Finset LogicVar} {Δ : BasicEnv} {e : Term} {T : SimpleType}
    {y : Atom} (closedX : LogicVar.LocallyClosed X)
    (closedE : e.locallyClosed) (support : e.logicSupport ⊆ X)
    (fresh : LogicVar.free y ∉ X)
    (hres : m ⊨ resultAt X e (.free y))
    (htyped : m ⊨ basicTyping Δ e T) :
    m ⊨ (total (.ret (.bound 0))).openAt 0 y := by
  unfold total Formula.fiberAtom
  simp only [Formula.openAt]
  let q := (totalQualifier (.ret (.bound 0))).openAt 0 y
  change m ⊨ Formula.fiberAtom q
  have hqsupp : q.support = {.free y} := by
    simp [q, totalQualifier, Term.logicSupportAt,
      Value.logicSupportAt, boundLogicSupportAt, LogicVar.openSupport,
      LogicVar.openBinder, LogicVar.swap]
  have hqfree : q.freeAtoms = {y} := by
    change LogicVar.freeAtomSet q.support = {y}
    rw [hqsupp]
    simp
  apply (Formula.models_fiberAtom_iff m q).2
  refine ⟨?_, ?_, ?_⟩
  · intro k hk
    rw [hqsupp] at hk
    simp at hk
  · have hy : y ∈ m.domain := by
      apply Formula.models_scope hres
      simp [LogicVar.freeAtoms]
    simpa [hqfree] using hy
  · intro σ hσ
    obtain ⟨v, hv, hvT⟩ :=
      models_resultAt_typed closedX closedE support fresh hres htyped σ hσ
    let s := σ.restrict q.freeAtoms
    have hsdom : s.domain = q.freeAtoms := by
      simp only [s]
      rw [Store.domain_restrict, m.mem_domain hσ,
        Finset.inter_eq_right]
      rw [hqfree]
      intro x hx
      have hxy : x = y := Finset.mem_singleton.1 hx
      subst x
      exact Formula.models_scope hres (by simp [LogicVar.freeAtoms])
    let a : AssignmentOn q.support :=
      { assignment := s.toAssignment
        domain_eq := by
          rw [Store.toAssignment_domain, hsdom, hqfree]
          simp [hqsupp] }
    refine ⟨hsdom, a, ?_, ?_⟩
    · change (totalQualifier (.ret (.bound 0))).holds
        (a.swapBack (.bound 0) (.free y))
      change (instantiateTerm (.ret (.bound 0))
        (a.swapBack (.bound 0) (.free y)).assignment).MustTerminate
      simpa [a, s, hqfree, Store.lookup_restrict, hv,
        AssignmentOn.swapBack, Assignment.lookup_swap,
        LogicVar.swap, instantiateTerm, instantiateTermAt,
        instantiateValueAt] using Term.MustTerminate.ret v hvT.locallyClosed
    · intro x
      simp [a, s]

theorem models_guard_shift_openAt_result_alias {m : Capability} {d : Nat}
    {Δ : BasicEnv} {τ : ContextType} {e : Term} {y : Atom}
    {X : Finset LogicVar}
    (closedX : LogicVar.LocallyClosed X) (closedE : e.locallyClosed)
    (support : e.logicSupport ⊆ X) (fresh : LogicVar.free y ∉ X)
    (freshΔ : y ∉ Δ.domain) (hres : m ⊨ resultAt X e (.free y))
    (hguard : m ⊨ guard d Δ τ e) :
    m ⊨ (guard (d + 1) Δ (τ.shiftFrom 0)
      (.ret (.bound 0))).openAt 0 y := by
  have hwf := Formula.models_and_elim_left hguard
  have hrest := Formula.models_and_elim_right hguard
  have hworld := Formula.models_and_elim_left hrest
  have hbasic := Formula.models_and_elim_left
    (Formula.models_and_elim_right hrest)
  simp only [guard, Formula.openAt]
  apply Formula.models_and_intro
  · exact models_wellFormed_shift_openAt freshΔ hwf
  · apply Formula.models_and_intro
    · rw [basicWorld_openAt_eq Δ 0 y freshΔ]
      exact hworld
    · apply Formula.models_and_intro
      · simpa using models_basicTyping_ret_bound_openAt closedX closedE
          support fresh freshΔ hres hworld hbasic
      · exact models_resultTotal_openAt closedX closedE support fresh
          hres hbasic

/-- Transport the guard to its actual relevant environment beneath an opened
result binder.  The returned result no longer observes the source term's free
variables through the basic environment. -/
theorem models_guard_relevant_shift_openAt_result_alias
    {m : Capability} {d : Nat} {Δ : BasicEnv} {τ : ContextType}
    {e : Term} {y : Atom} {X : Finset LogicVar}
    (closedX : LogicVar.LocallyClosed X) (closedE : e.locallyClosed)
    (support : e.logicSupport ⊆ X) (fresh : LogicVar.free y ∉ X)
    (freshΔ : y ∉ Δ.domain)
    (hres : m ⊨ resultAt X e (.free y))
    (hguard : m ⊨ guard d (relevantEnv Δ τ e) τ e) :
    m ⊨ (guard (d + 1)
      (relevantEnv Δ (τ.shiftFrom 0) (.ret (.bound 0)))
      (τ.shiftFrom 0) (.ret (.bound 0))).openAt 0 y := by
  let Δe := relevantEnv Δ τ e
  let Δτ := Δ.restrict τ.freeAtoms
  have henv : relevantEnv Δ (τ.shiftFrom 0) (.ret (.bound 0)) = Δτ := by
    simp [relevantEnv, relevantAtoms, Term.support, Value.support, Δτ]
  have hrestrict : Δe.restrict τ.freeAtoms = Δτ := by
    simp only [Δe, Δτ, relevantEnv, relevantAtoms,
      BasicEnv.restrict_restrict]
    rw [Finset.inter_eq_right.2
      (Finset.subset_union_left : τ.freeAtoms ⊆ τ.freeAtoms ∪ e.support)]
  have hwf := Formula.models_and_elim_left hguard
  have hrest := Formula.models_and_elim_right hguard
  have hworld := Formula.models_and_elim_left hrest
  have hbasic := Formula.models_and_elim_left
    (Formula.models_and_elim_right hrest)
  have hwfInfo := (models_wellFormed_iff m d Δe τ).1 hwf
  have hdomain : Δτ.domain ⊆ Δe.domain := by
    rw [← hrestrict]
    rw [BasicEnv.domain_restrict]
    exact Finset.inter_subset_left
  have hwfτ : m ⊨ wellFormed d Δτ τ := by
    apply (models_wellFormed_iff m d Δτ τ).2
    refine ⟨Finset.Subset.trans hdomain hwfInfo.1,
      hwfInfo.2.regularize ?_⟩
    intro x hx
    have hxΔ := hwfInfo.2.freeAtoms_subset hx
    rw [relevantEnv_domain] at hxΔ
    simp only [Δτ, BasicEnv.domain_restrict, Finset.mem_inter]
    exact ⟨(Finset.mem_inter.1 hxΔ).1, hx⟩
  have hworldτ : m ⊨ basicWorld Δτ := by
    rw [← hrestrict]
    exact models_basicWorld_restrict τ.freeAtoms hworld
  have hfreshτ : y ∉ Δτ.domain := by
    intro hy
    change y ∈ (Δ.restrict τ.freeAtoms).domain at hy
    rw [BasicEnv.domain_restrict] at hy
    exact freshΔ (Finset.mem_inter.1 hy).1
  rw [henv]
  simp only [guard, Formula.openAt]
  apply Formula.models_and_intro
  · exact models_wellFormed_shift_openAt hfreshτ hwfτ
  · apply Formula.models_and_intro
    · rw [basicWorld_openAt_eq Δτ 0 y hfreshτ]
      exact hworldτ
    · apply Formula.models_and_intro
      · simpa using models_basicTyping_ret_bound_openAt closedX closedE
          support fresh hfreshτ hres hworldτ hbasic
      · exact models_resultTotal_openAt closedX closedE support fresh
          hres hbasic

theorem models_guard_result_alias {m : Capability} {d : Nat}
    {Δ : BasicEnv} {τ : ContextType} {e : Term} {y : Atom}
    {X : Finset LogicVar}
    (closedX : LogicVar.LocallyClosed X) (closedE : e.locallyClosed)
    (he : e.logicSupport ⊆ X) (hτ : τ.support ⊆ X)
    (fresh : LogicVar.free y ∉ X)
    (lookup : Δ.lookup y = some τ.erase)
    (hres : m ⊨ resultAt X e (.free y))
    (hguard : m ⊨ guard d (relevantEnv Δ τ e) τ e) :
    m ⊨ guard d (relevantEnv Δ τ (.ret (.free y))) τ
      (.ret (.free y)) := by
  let Δe := relevantEnv Δ τ e
  let Δy := relevantEnv Δ τ (.ret (.free y))
  have hyτ : y ∉ τ.freeAtoms := by
    intro hy
    apply fresh
    exact hτ ((τ.free_mem_support_iff y).2 hy)
  have hye : y ∉ e.support := by
    intro hy
    apply fresh
    apply he
    rw [← LogicVar.mem_freeAtomSet_iff,
      freeAtomSet_term_logicSupport]
    exact hy
  have hyM : y ∈ m.domain := by
    apply Formula.models_scope hres
    simp [LogicVar.freeAtoms]
  have hlookupY : Δy.lookup y = some τ.erase := by
    simp [Δy, relevantEnv, relevantAtoms, Term.support, Value.support,
      hyτ, lookup]
  have hwf := Formula.models_and_elim_left hguard
  have hrest := Formula.models_and_elim_right hguard
  have hworld := Formula.models_and_elim_left hrest
  have hbasic := Formula.models_and_elim_left
    (Formula.models_and_elim_right hrest)
  have hwfInfo := (models_wellFormed_iff m d Δe τ).1 hwf
  have hworldInfo := (models_basicWorld_iff m Δe).1 hworld
  have hscopeY : Δy.domain ⊆ m.domain := by
    intro x hx
    rw [relevantEnv_domain] at hx
    have hx' := Finset.mem_inter.1 hx
    rcases Finset.mem_union.1 hx'.2 with hxτ | hxy
    · apply hwfInfo.1
      rw [relevantEnv_domain]
      exact Finset.mem_inter.2
        ⟨hx'.1, Finset.mem_union_left _ hxτ⟩
    · have hxy' : x = y := by
        simpa [Term.support, Value.support] using hxy
      subst x
      exact hyM
  have hwfY : m ⊨ wellFormed d Δy τ := by
    apply (models_wellFormed_iff m d Δy τ).2
    refine ⟨hscopeY, hwfInfo.2.regularize ?_⟩
    intro x hx
    rw [relevantEnv_domain]
    have hxE := hwfInfo.2.freeAtoms_subset hx
    rw [relevantEnv_domain] at hxE
    have hxE' := Finset.mem_inter.1 hxE
    exact Finset.mem_inter.2
      ⟨hxE'.1, Finset.mem_union_left _ hx⟩
  have hworldY : m ⊨ basicWorld Δy := by
    apply (models_basicWorld_iff m Δy).2
    refine ⟨hscopeY, ?_⟩
    intro σ hσ x T hx
    by_cases hxy : x = y
    · subst x
      have hT : T = τ.erase := by
        rw [hlookupY] at hx
        exact Option.some.inj hx.symm
      subst T
      exact models_resultAt_typed closedX closedE he fresh hres hbasic σ hσ
    · have hxin : x ∈ relevantAtoms τ (.ret (.free y)) := by
        by_contra hn
        simp [Δy, relevantEnv, BasicEnv.lookup_restrict, hn] at hx
      have hxΔ : Δ.lookup x = some T := by
        simpa [Δy, relevantEnv, BasicEnv.lookup_restrict, hxin] using hx
      have hxτ : x ∈ τ.freeAtoms := by
        rcases Finset.mem_union.1 hxin with hxτ | hxret
        · exact hxτ
        · have : x = y := by
            simpa [Term.support, Value.support] using hxret
          exact (hxy this).elim
      have hxE : Δe.lookup x = some T := by
        simp [Δe, relevantEnv, BasicEnv.lookup_restrict,
          relevantAtoms, hxτ, hxΔ]
      exact hworldInfo.2 σ hσ x T hxE
  unfold guard
  apply Formula.models_and_intro hwfY
  apply Formula.models_and_intro hworldY
  apply Formula.models_and_intro
  · exact models_basicTyping_ret_free hworldY hlookupY
  · exact models_total_ret_free hworldY hlookupY

mutual

theorem valueLogicSupport_bound_lt (v : Value) (d k : Nat)
    (closed : v.locallyClosedAt (d + k)) {j : Nat}
    (hj : LogicVar.bound j ∈ v.logicSupportAt d) : j < k := by
  cases v with
  | const c => simp [Value.logicSupportAt] at hj
  | free x => simp [Value.logicSupportAt] at hj
  | bound n =>
      simp only [Value.logicSupportAt, boundLogicSupportAt] at hj
      split_ifs at hj with hdn
      · have heq : j = n - d := by simpa using hj
        change n < d + k at closed
        omega
      · simp at hj
  | lam T e =>
      apply termLogicSupport_bound_lt e (d + 1) k
      · simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using closed
      · exact hj
  | fix T v =>
      apply valueLogicSupport_bound_lt v (d + 1) k
      · simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using closed
      · exact hj

theorem termLogicSupport_bound_lt (e : Term) (d k : Nat)
    (closed : e.locallyClosedAt (d + k)) {j : Nat}
    (hj : LogicVar.bound j ∈ e.logicSupportAt d) : j < k := by
  cases e with
  | ret v => exact valueLogicSupport_bound_lt v d k closed hj
  | letE e₁ e₂ =>
      rcases Finset.mem_union.1 hj with hj | hj
      · exact termLogicSupport_bound_lt e₁ d k closed.1 hj
      · apply termLogicSupport_bound_lt e₂ (d + 1) k
        · simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using closed.2
        · exact hj
  | primitive op v => exact valueLogicSupport_bound_lt v d k closed hj
  | app v₁ v₂ =>
      rcases Finset.mem_union.1 hj with hj | hj
      · exact valueLogicSupport_bound_lt v₁ d k closed.1 hj
      · exact valueLogicSupport_bound_lt v₂ d k closed.2 hj
  | matchBool v e₁ e₂ =>
      rcases Finset.mem_union.1 hj with hj | hj
      · rcases Finset.mem_union.1 hj with hj | hj
        · exact valueLogicSupport_bound_lt v d k closed.1 hj
        · exact termLogicSupport_bound_lt e₁ d k closed.2.1 hj
      · exact termLogicSupport_bound_lt e₂ d k closed.2.2 hj

end

theorem contextTypeSupport_bound_lt (τ : ContextType) (d k : Nat)
    (closed : τ.LocallyClosedAt (d + k)) {j : Nat}
    (hj : LogicVar.bound j ∈ τ.supportAt d) : j < k := by
  induction τ generalizing d k with
  | «over» b q | under b q =>
      obtain ⟨ξ, hξ, hjξ⟩ := Finset.mem_biUnion.1 hj
      cases ξ with
      | free x => simp [LogicVar.atDepth] at hjξ
      | bound n =>
          have hn := closed n hξ
          by_cases hdn : d + 1 ≤ n
          · have heq : j = n - (d + 1) := by
              simpa [LogicVar.atDepth, hdn] using hjξ
            omega
          · simp [LogicVar.atDepth, hdn] at hjξ
  | inter τ₁ τ₂ ih₁ ih₂ | union τ₁ τ₂ ih₁ ih₂ | sum τ₁ τ₂ ih₁ ih₂ =>
      rcases Finset.mem_union.1 hj with hj | hj
      · exact ih₁ d k closed.1 hj
      · exact ih₂ d k closed.2 hj
  | arrow τ₁ τ₂ ih₁ ih₂ | wand τ₁ τ₂ ih₁ ih₂ =>
      rcases Finset.mem_union.1 hj with hj | hj
      · exact ih₁ d k closed.1 hj
      · apply ih₂ (d + 1) k
        · simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using closed.2
        · exact hj
  | persist τ ih => exact ih d k closed hj

theorem guard_openAt_eq (d : Nat) (Δ : BasicEnv) (τ : ContextType)
    (e : Term) (k : Nat) (y : Atom)
    (closed : e.locallyClosedAt k) (freshΔ : y ∉ Δ.domain)
    (freshE : y ∉ e.support) : (guard d Δ τ e).openAt k y = guard d Δ τ e := by
  have htyping : (basicTyping Δ e τ.erase).openAt k y = basicTyping Δ e τ.erase := by
    let q := basicTypingQualifier Δ e τ.erase
    have hk : LogicVar.bound k ∉ q.support := by
      intro hk
      rcases Finset.mem_union.1 hk with hk | hk
      · simp at hk
      · have hlt := termLogicSupport_bound_lt e 0 k (by simpa using closed) hk
        omega
    have hy : LogicVar.free y ∉ q.support := by
      intro hy
      rcases Finset.mem_union.1 hy with hy | hy
      · exact freshΔ (by simpa using hy)
      · apply freshE
        rw [← freeAtomSet_term_logicSupport, LogicVar.mem_freeAtomSet_iff]
        exact hy
    simp only [basicTyping, Formula.fiberAtom, Formula.openAt]
    rw [LogicVar.openSupport_eq_self_of_fresh q.support k y hk hy,
      q.openAt_fresh k y hk hy]
  have htotal : (total e).openAt k y = total e := by
    let q := totalQualifier e
    have hk : LogicVar.bound k ∉ q.support := by
      intro hk
      have hlt := termLogicSupport_bound_lt e 0 k (by simpa using closed) hk
      omega
    have hy : LogicVar.free y ∉ q.support := by
      intro hy
      apply freshE
      rw [← freeAtomSet_term_logicSupport, LogicVar.mem_freeAtomSet_iff]
      exact hy
    simp only [total, Formula.fiberAtom, Formula.openAt]
    rw [LogicVar.openSupport_eq_self_of_fresh q.support k y hk hy,
      q.openAt_fresh k y hk hy]
  simp only [guard, Formula.openAt]
  rw [wellFormed_openAt_eq d Δ τ k y freshΔ, basicWorld_openAt_eq Δ k y freshΔ,
    htyping, htotal]

theorem resultFirst_openAt_fresh (Δ : BasicEnv) (τ : ContextType)
    (e : Term) (k : Nat) (y : Atom)
    (closedτ : τ.LocallyClosedAt k) (closedE : e.locallyClosedAt k)
    (freshΔ : y ∉ Δ.domain) (freshE : y ∉ e.support) :
    (resultFirst Δ τ e).openAt (k + 1) y = resultFirst Δ τ e := by
  let X := (relevantSupport Δ τ e).image (LogicVar.shiftFrom 0)
  let q := resultQualifier (shiftTerm e) (.bound 0)
  have hXbound : LogicVar.bound (k + 1) ∉ X := by
    intro hx
    obtain ⟨ξ, hξ, hsame⟩ := Finset.mem_image.1 hx
    cases ξ with
    | free x => simp [LogicVar.shiftFrom] at hsame
    | bound j =>
        have hj : j = k := by simpa [LogicVar.shiftFrom] using hsame
        subst j
        rcases Finset.mem_union.1 hξ with hξ | hξ
        · simp at hξ
        · obtain ⟨ζ, hζ, hkζ⟩ := Finset.mem_biUnion.1 hξ
          cases ζ with
          | free x => simp at hkζ
          | bound j =>
              have hj : k = j := by simpa using hkζ
              subst j
              rcases Finset.mem_union.1 hζ with hτ | he
              · have hlt := contextTypeSupport_bound_lt τ 0 k
                  (by simpa using closedτ) hτ
                omega
              · have hlt := termLogicSupport_bound_lt e 0 k
                  (by simpa using closedE) he
                omega
  have hXfree : LogicVar.free y ∉ X := by
    intro hy
    obtain ⟨ξ, hξ, hsame⟩ := Finset.mem_image.1 hy
    cases ξ with
    | bound j => simp [LogicVar.shiftFrom] at hsame
    | free x =>
        have hx : x = y := by simpa [LogicVar.shiftFrom] using hsame
        subst x
        have hyΔ : y ∈ (relevantEnv Δ τ e).domain := by
          rw [← freeAtomSet_relevantSupport, LogicVar.mem_freeAtomSet_iff]
          exact hξ
        rw [relevantEnv_domain] at hyΔ
        exact freshΔ (Finset.mem_inter.1 hyΔ).1
  have hqbound : LogicVar.bound (k + 1) ∉ q.support := by
    intro hk
    rcases Finset.mem_union.1 hk with hk | hk
    · rw [shiftTerm_logicSupport, Finset.mem_image] at hk
      obtain ⟨ξ, hξ, hsame⟩ := hk
      cases ξ with
      | free x => simp [LogicVar.shiftFrom] at hsame
      | bound j =>
          have hj : j = k := by simpa [LogicVar.shiftFrom] using hsame
          subst j
          have hlt := termLogicSupport_bound_lt e 0 k (by simpa using closedE) hξ
          omega
    · simp at hk
  have hqfree : LogicVar.free y ∉ q.support := by
    intro hy
    rcases Finset.mem_union.1 hy with hy | hy
    · apply freshE
      rw [← freeAtomSet_term_logicSupport, LogicVar.mem_freeAtomSet_iff]
      rw [shiftTerm_logicSupport, Finset.mem_image] at hy
      obtain ⟨ξ, hξ, hsame⟩ := hy
      cases ξ with
      | bound j => simp [LogicVar.shiftFrom] at hsame
      | free x =>
          have hx : x = y := by simpa [LogicVar.shiftFrom] using hsame
          simpa [hx] using hξ
    · simp at hy
  change (Formula.fiber X (Atom(q))).openAt (k + 1) y = Formula.fiber X (Atom(q))
  simp only [Formula.openAt]
  rw [LogicVar.openSupport_eq_self_of_fresh X (k + 1) y hXbound hXfree,
    q.openAt_fresh (k + 1) y hqbound hqfree]

theorem resultBasicTyping_openAt_fresh (b : BaseType) (k : Nat) (y : Atom) :
    (resultBasicTyping b).openAt (k + 1) y = resultBasicTyping b := by
  let q := basicTypingQualifier ∅ (.ret (.bound 0)) (.base b)
  have hb : LogicVar.bound (k + 1) ∉ q.support := by
    simp [q, basicTypingQualifier, Term.logicSupportAt, Value.logicSupportAt,
      boundLogicSupportAt]
  have hf : LogicVar.free y ∉ q.support := by
    simp [q, basicTypingQualifier, Term.logicSupportAt, Value.logicSupportAt,
      boundLogicSupportAt]
  simp only [resultBasicTyping, basicTyping, Formula.fiberAtom, Formula.openAt]
  rw [LogicVar.openSupport_eq_self_of_fresh q.support (k + 1) y hb hf,
    q.openAt_fresh (k + 1) y hb hf]

theorem overResultFiber_openAt_fresh (b : BaseType) (q : Qualifier)
    (k : Nat) (y : Atom) (closed : q.locallyClosedAt (k + 1))
    (fresh : y ∉ q.freeAtoms) :
    (Formula.fiber (q.support \ {.bound 0}) (overResult b q)).openAt (k + 1) y =
      Formula.fiber (q.support \ {.bound 0}) (overResult b q) := by
  have hb : LogicVar.bound (k + 1) ∉ q.support := by
    intro hb
    have := closed (k + 1) hb
    omega
  have hf : LogicVar.free y ∉ q.support := by
    rwa [← Qualifier.mem_freeAtoms_iff]
  simp only [Formula.openAt, overResult]
  rw [LogicVar.openSupport_eq_self_of_fresh (q.support \ {.bound 0}) (k + 1) y
    (fun hx => hb (Finset.mem_sdiff.1 hx).1) (fun hx => hf (Finset.mem_sdiff.1 hx).1)]
  rw [q.openAt_fresh (k + 1) y hb hf, resultBasicTyping_openAt_fresh]

theorem underResultFiber_openAt_fresh (b : BaseType) (q : Qualifier)
    (k : Nat) (y : Atom) (closed : q.locallyClosedAt (k + 1))
    (fresh : y ∉ q.freeAtoms) :
    (Formula.fiber (q.support \ {.bound 0}) (underResult b q)).openAt (k + 1) y =
      Formula.fiber (q.support \ {.bound 0}) (underResult b q) := by
  have hb : LogicVar.bound (k + 1) ∉ q.support := by
    intro hb
    have := closed (k + 1) hb
    omega
  have hf : LogicVar.free y ∉ q.support := by
    rwa [← Qualifier.mem_freeAtoms_iff]
  simp only [Formula.openAt, underResult]
  rw [LogicVar.openSupport_eq_self_of_fresh (q.support \ {.bound 0}) (k + 1) y
    (fun hx => hb (Finset.mem_sdiff.1 hx).1) (fun hx => hf (Finset.mem_sdiff.1 hx).1)]
  rw [q.openAt_fresh (k + 1) y hb hf, resultBasicTyping_openAt_fresh]

theorem wellFormed_eq_of_locallyClosedAt (Δ : BasicEnv) (τ : ContextType)
    (k d d' : Nat) (closed : τ.LocallyClosedAt k) (hk : k ≤ d) (hk' : k ≤ d') :
    wellFormed d Δ τ = wellFormed d' Δ τ := by
  have hq : wellFormedQualifier d Δ τ = wellFormedQualifier d' Δ τ := by
    apply Qualifier.ext
    · rfl
    · intro ρ σ _
      exact ContextType.wellFormedAt_iff_of_locallyClosedAt closed hk hk'
  exact congrArg Formula.fiberAtom hq

theorem guard_eq_of_locallyClosedAt (Δ : BasicEnv) (τ : ContextType)
    (e : Term) (k d d' : Nat) (closed : τ.LocallyClosedAt k)
    (hk : k ≤ d) (hk' : k ≤ d') :
    guard d Δ τ e = guard d' Δ τ e := by
  simp only [guard, wellFormed_eq_of_locallyClosedAt Δ τ k d d' closed hk hk']

/-- Open the ambient returned value while keeping the inner result binder. -/
theorem resultQualifier_ret_bound_openAt (y : Atom) :
    (resultQualifier (.ret (.bound 1)) (.bound 0)).openAt 1 y =
      resultQualifier (.ret (.free y)) (.bound 0) := by
  apply Qualifier.ext
  · simp [resultQualifier, Term.logicSupportAt, Value.logicSupportAt,
      boundLogicSupportAt, LogicVar.openSupport, LogicVar.openBinder, LogicVar.swap]
  · intro ρ σ same
    have hy : LogicVar.free y ∈ σ.assignment.domain := by
      rw [σ.domain_eq]
      simp [resultQualifier, Term.logicSupportAt, Value.logicSupportAt]
    obtain ⟨v, hv⟩ := (Assignment.mem_domain_iff σ.assignment (.free y)).1 hy
    simp only [Qualifier.openAt, resultQualifier, AssignmentOn.swapBack,
      Assignment.lookup_swap, instantiateTermAt, instantiateValueAt]
    rw [same]
    simp [Term.logicSupport, Term.logicSupportAt, Value.logicSupportAt,
      boundLogicSupportAt, LogicVar.swap, hv]

/-- Opening a symbolic returned result exposes its fresh alias in the input support. -/
theorem resultFirst_ret_bound_openAt (Δ : BasicEnv) (τ : ContextType)
    (y : Atom) (closed : τ.LocallyClosed) (fresh : y ∉ Δ.domain) :
    (resultFirst Δ τ (.ret (.bound 0))).openAt 1 y =
      resultAt (insert (.free y)
        ((relevantEnv Δ τ (.ret (.bound 0))).domain.image LogicVar.free))
        (.ret (.free y)) (.bound 0) := by
  have hsupp : relevantSupport Δ τ (.ret (.bound 0)) =
      insert (.bound 0)
        ((relevantEnv Δ τ (.ret (.bound 0))).domain.image LogicVar.free) := by
    ext ξ
    constructor
    · intro hξ
      rcases Finset.mem_union.1 hξ with hξ | hξ
      · exact Finset.mem_insert_of_mem hξ
      · obtain ⟨ζ, hζ, hξζ⟩ := Finset.mem_biUnion.1 hξ
        cases ζ with
        | free x => simp at hξζ
        | bound j =>
            have hsame : ξ = LogicVar.bound j := by simpa using hξζ
            subst ξ
            rcases Finset.mem_union.1 hζ with hζ | hζ
            · exact (contextTypeSupportAt_locallyClosed closed j hζ).elim
            · have hj : j = 0 := by
                simpa [Term.logicSupportAt, Value.logicSupportAt, boundLogicSupportAt] using hζ
              subst j
              exact Finset.mem_insert_self _ _
    · intro hξ
      rcases Finset.mem_insert.1 hξ with hξ | hξ
      · subst ξ
        apply Finset.mem_union_right
        apply Finset.mem_biUnion.2
        refine ⟨.bound 0, Finset.mem_union_right _ ?_, by simp⟩
        simp [Term.logicSupportAt, Value.logicSupportAt, boundLogicSupportAt]
      · exact Finset.mem_union_left _ hξ
  have hf : y ∉ (relevantEnv Δ τ (.ret (.bound 0))).domain := by
    rw [relevantEnv_domain]
    exact fun hy => fresh (Finset.mem_inter.1 hy).1
  have hopen : LogicVar.openSupport 1 y
      (((relevantEnv Δ τ (.ret (.bound 0))).domain.image LogicVar.free).image
        (LogicVar.shiftFrom 0)) =
      (relevantEnv Δ τ (.ret (.bound 0))).domain.image LogicVar.free := by
    rw [Finset.image_image]
    simp only [Function.comp_def, LogicVar.shiftFrom]
    exact LogicVar.openSupport_eq_self_of_fresh _ 1 y (by simp) (by simpa using hf)
  have hopenX : LogicVar.openSupport 1 y
      ((insert (.bound 0) ((relevantEnv Δ τ (.ret (.bound 0))).domain.image LogicVar.free)).image
        (LogicVar.shiftFrom 0)) =
      insert (.free y) ((relevantEnv Δ τ (.ret (.bound 0))).domain.image LogicVar.free) := by
    simp only [LogicVar.openSupport, Finset.image_insert]
    change insert (.free y) (LogicVar.openSupport 1 y
      (((relevantEnv Δ τ (.ret (.bound 0))).domain.image LogicVar.free).image
        (LogicVar.shiftFrom 0))) = _
    rw [hopen]
  have hterm : shiftTerm (.ret (.bound 0)) = .ret (.bound 1) := rfl
  simp only [resultFirst, resultAt, Formula.openAt, hsupp, hopenX, hterm,
    resultQualifier_ret_bound_openAt]


/-- A returned value has an exact result graph on any support observing that value. -/
theorem models_resultAt_ret_change_support {m : Capability}
    {X Y : Finset LogicVar} {v : Value} {y : Atom}
    (closedX : LogicVar.LocallyClosed X) (closedY : LogicVar.LocallyClosed Y)
    (supportX : (.ret v : Term).logicSupport ⊆ X)
    (supportY : (.ret v : Term).logicSupport ⊆ Y)
    (freshX : LogicVar.free y ∉ X) (freshY : LogicVar.free y ∉ Y)
    (scope : LogicVar.freeAtomSet Y ∪ {y} ⊆ m.domain)
    (hres : m ⊨ resultAt X (.ret v) (.free y)) :
    m ⊨ resultAt Y (.ret v) (.free y) := by
  apply models_resultAt_intro closedY supportY freshY scope
  · exact models_resultAt_lookup closedX supportX freshX hres
  · intro σ hσ w hw
    obtain ⟨u, hu, heval⟩ := models_resultAt_lookup closedX supportX freshX hres σ hσ
    have hwu : w = u := by
      have hret := hw.ret_eq.trans heval.ret_eq.symm
      exact Term.ret.inj hret
    subst w
    exact ⟨σ, hσ, rfl, hu⟩

/-- On a singleton input, result quantification can use a fresh name for the
returned value and retain only the atoms observed by the result body. -/
theorem models_all_ret_alias_singleton {ρ : Store} {A B : Finset Atom}
    {v : Value} {y : Atom} {Q : Formula}
    (closedV : v.locallyClosed) (supportV : v.support ⊆ A)
    (hBA : B ⊆ A) (supportQ : Q.freeAtoms ⊆ B) (freshY : y ∉ A)
    (hres : Capability.singleton ρ ⊨ resultAt (A.image LogicVar.free)
      (.ret v) (.free y))
    (hsource : Capability.singleton ρ ⊨ Formula.all
      (resultAt (A.image LogicVar.free) (.ret v) (.bound 0) ⇒ᶜ Q)) :
    Capability.singleton ρ ⊨ Formula.all
      (resultAt (insert (.free y) (B.image LogicVar.free))
        (.ret (.free y)) (.bound 0) ⇒ᶜ Q) := by
  let X := A.image LogicVar.free
  let Y := insert (.free y) (B.image LogicVar.free)
  let P := resultAt X (.ret v) (.bound 0) ⇒ᶜ Q
  let R := resultAt Y (.ret (.free y)) (.bound 0) ⇒ᶜ Q
  have closedX : LogicVar.LocallyClosed X := by intro j hj; simp [X] at hj
  have closedY : LogicVar.LocallyClosed Y := by intro j hj; simp [Y] at hj
  have heX : (.ret v : Term).logicSupport ⊆ X := by
    intro ξ hξ
    cases ξ with
    | bound j => exact (termLogicSupport_locallyClosed (.ret v) closedV j hξ).elim
    | free x =>
        apply Finset.mem_image.2
        refine ⟨x, supportV ?_, rfl⟩
        change x ∈ (.ret v : Term).support
        rw [← freeAtomSet_term_logicSupport (.ret v), LogicVar.mem_freeAtomSet_iff]
        exact hξ
  have freshYX : LogicVar.free y ∉ X := by simpa [X] using freshY
  have hA : A ∪ {y} ⊆ ρ.domain := by
    have hs := Formula.models_scope hres
    simpa only [freeAtoms_resultAt, Formula.LogicVar.freeAtomSet_image_free,
      Term.support, Finset.union_eq_left.2 supportV, LogicVar.freeAtoms] using hs
  have hPfree : P.freeAtoms = A := by
    simp only [P, Formula.freeAtoms_impl, freeAtoms_resultAt,
      Formula.LogicVar.freeAtomSet_image_free, X, Term.support, LogicVar.freeAtoms,
      Finset.union_empty]
    rw [Finset.union_eq_left.2 supportV,
      Finset.union_eq_left.2 (Finset.Subset.trans supportQ hBA)]
  have hYfree : LogicVar.freeAtomSet Y = B ∪ {y} := by
    change (insert (.free y) (B.image LogicVar.free)).biUnion LogicVar.freeAtoms = _
    rw [Finset.biUnion_insert]
    change {y} ∪ LogicVar.freeAtomSet (B.image LogicVar.free) = _
    rw [Formula.LogicVar.freeAtomSet_image_free, Finset.union_comm]
  have hRfree : R.freeAtoms = B ∪ {y} := by
    simp only [R, Formula.freeAtoms_impl, freeAtoms_resultAt,
      hYfree, LogicVar.freeAtoms, Term.support, Value.support, Finset.union_empty]
    rw [Finset.union_eq_left.2 (Finset.subset_union_right : {y} ⊆ B ∪ {y}),
      Finset.union_eq_left.2 (Finset.Subset.trans supportQ Finset.subset_union_left)]
  have hBY : B ∪ {y} ⊆ A ∪ {y} :=
    Finset.union_subset_union hBA (Finset.Subset.refl _)
  obtain ⟨u, hρy, heval⟩ := models_resultAt_lookup closedX heX freshYX hres ρ rfl
  have hu : u = instantiateValueAt v 0 ρ.toAssignment := Term.ret.inj heval.ret_eq
  obtain ⟨_, L, hall⟩ := (Formula.models_all_iff (Capability.singleton ρ) P).1 hsource
  apply Formula.models_all_intro
  · rw [hRfree]
    exact Finset.Subset.trans hBY hA
  · refine ⟨L ∪ ρ.domain ∪ A ∪ {y}, ?_⟩
    intro z hz F hFin hFout n hExt
    have hzL : z ∉ L := fun h => hz (by simp [h])
    have hzρ : z ∉ ρ.domain := fun h => hz (by simp [h])
    have hzA : z ∉ A := fun h => hz (by simp [h])
    have hzy : z ≠ y := fun h => hz (by simp [h])
    have hzX : LogicVar.free z ∉ X := by simpa [X] using hzA
    have hzY : LogicVar.free z ∉ Y := by
      simp only [Y, Finset.mem_insert, LogicVar.free.injEq, Finset.mem_image]
      rintro (h | ⟨x, hx, hsame⟩)
      · exact hzy h
      · have hxz : x = z := by simpa using hsame
        exact hzA (hxz ▸ hBA hx)
    have heY : (.ret (.free y) : Term).logicSupport ⊆ Y := by
      simp [Y, Term.logicSupportAt, Value.logicSupportAt]
    have hRopen : (resultAt Y (.ret (.free y)) (.bound 0)).openAt 0 z =
        resultAt Y (.ret (.free y)) (.free z) := by
      simpa only [LogicVar.image_shiftFrom_eq_of_locallyClosed Y 0 closedY,
        shiftTerm_eq_of_locallyClosed (.ret (.free y)) (by trivial)] using
        resultAt_shift_openAt Y (.ret (.free y)) z closedY (by trivial) heY hzY
    have hQscope : (Q.openAt 0 z).freeAtoms ⊆ B ∪ {z} := by
      intro x hx
      rcases Finset.mem_union.1 (Formula.freeAtoms_openAt_subset Q 0 z hx) with hx | hx
      · exact Finset.mem_union_right _ hx
      · exact Finset.mem_union_left _ (supportQ hx)
    have hRopenFree : (R.openAt 0 z).freeAtoms = (B ∪ {y}) ∪ {z} := by
      simp only [R, Formula.openAt, Formula.freeAtoms_impl, hRopen,
        freeAtoms_resultAt]
      rw [hYfree]
      simp only [Term.support, Value.support, LogicVar.freeAtoms]
      rw [Finset.union_eq_left.2 (Finset.subset_union_right : {y} ⊆ B ∪ {y}),
        Finset.union_eq_left.2 (Finset.Subset.trans hQscope (by
          intro x hx
          rcases Finset.mem_union.1 hx with hx | hx
          · exact Finset.mem_union_left _ (Finset.mem_union_left _ hx)
          · exact Finset.mem_union_right _ hx))]
    have hn : n.domain = (B ∪ {y}) ∪ {z} := by
      rw [hExt.domain_eq, Capability.restrict_domain, hRfree, hFout,
        Capability.singleton_domain,
        Finset.inter_eq_right.2
          (Finset.Subset.trans hBY hA)]
    have hRopened : R.openAt 0 z =
        (resultAt Y (.ret (.free y)) (.free z) ⇒ᶜ Q.openAt 0 z) := by
      simp only [R, Formula.openAt, hRopen]
    have hopenedFree :
        (resultAt Y (.ret (.free y)) (.free z) ⇒ᶜ Q.openAt 0 z).freeAtoms =
          (B ∪ {y}) ∪ {z} := by
      rw [← hRopened, hRopenFree]
    change n ⊨ R.openAt 0 z
    rw [hRopened]
    apply Formula.models_impl_intro
    · rw [hopenedFree, hn]
    · intro k href hret
      have hnk : n ⊑ k := by
        rw [hopenedFree, ← hn, Capability.restrict_domain_self] at href
        exact href
      have hbase : Capability.singleton (ρ.restrict (B ∪ {y})) ⊑ k := by
        have hbase' := Capability.refines_trans hExt.refines hnk
        change (Capability.singleton ρ).restrict R.freeAtoms ⊑ k at hbase'
        rwa [hRfree, Capability.restrict_singleton] at hbase'
      have hρB : (ρ.restrict (B ∪ {y})).domain = B ∪ {y} := by
        rw [Store.domain_restrict,
          Finset.inter_eq_right.2
            (Finset.Subset.trans hBY hA)]
      have hky : ∀ σ, σ ∈ k → σ.lookup y = some u := by
        intro σ hσ
        have hm : σ.restrict (B ∪ {y}) ∈
            k.restrict (Capability.singleton (ρ.restrict (B ∪ {y}))).domain := by
          rw [Capability.singleton_domain, hρB]
          exact ⟨σ, hσ, rfl⟩
        rw [← hbase] at hm
        have hs : σ.restrict (B ∪ {y}) = ρ.restrict (B ∪ {y}) := hm
        have hy := congrArg (fun s => s.lookup y) hs
        simpa [Store.lookup_restrict, hρy] using hy
      have hkz : ∀ σ, σ ∈ k → σ.lookup z = some u := by
        intro σ hσ
        rw [models_resultAt_ret_free_lookup closedY heY hzY hret σ hσ]
        exact hky σ hσ
      let s := ρ.restrict A
      let o := Store.singleton z u
      let t := s.merge o
      have hsdom : s.domain = A := by
        rw [Store.domain_restrict, Finset.inter_eq_right.2]
        exact Finset.Subset.trans Finset.subset_union_left hA
      have hodom : o.domain = {z} := Store.domain_singleton z u
      have hout : Disjoint o.domain s.domain := by
        rw [hodom, hsdom]
        exact Finset.disjoint_singleton_left.2 hzA
      let F₀ := Capability.FiberExtension.constant A o (by
        rw [hodom]; exact Finset.disjoint_singleton_right.2 hzA)
      have hExt₀ : F₀.Extends (Capability.singleton s) (Capability.singleton t) :=
        Capability.FiberExtension.constant_extends_singleton
          (by rw [hsdom]) hout
      have hbody : Capability.singleton t ⊨ P.openAt 0 z := by
        apply hall z hzL F₀
        · change A = P.freeAtoms
          exact hPfree.symm
        · exact hodom
        · simpa [hPfree, s] using hExt₀
      have htinst : instantiateTerm (.ret v) t.toAssignment = .ret u := by
        have hts : t.restrict A = s := Store.restrict_merge_left_full hsdom
        have hagree := instantiateTerm_eq_of_restrict_eq (.ret v) X t ρ closedX heX
          (by simpa [X, s, Formula.LogicVar.freeAtomSet_image_free] using hts)
        rw [hagree]
        exact congrArg Term.ret hu.symm
      have htz : t.lookup z = some u := by
        rw [Store.lookup_merge_right s o (by rw [hsdom]; exact hzA)]
        exact Store.lookup_singleton z u
      have hsourceRes : Capability.singleton t ⊨ resultAt X (.ret v) (.free z) := by
        apply models_resultAt_intro closedX heX hzX
        · simp only [X, Formula.LogicVar.freeAtomSet_image_free,
            Capability.singleton_domain, t, Store.domain_merge, hsdom, hodom]
          exact Finset.Subset.refl _
        · intro σ hσ
          have : σ = t := hσ
          subst σ
          refine ⟨u, htz, ?_⟩
          rw [htinst]
          exact Steps.refl (.ret u) heval.target_closed
        · intro σ hσ w hw
          have : σ = t := hσ
          subst σ
          have hwu : w = u := by rw [htinst] at hw; exact Term.ret.inj hw.ret_eq
          subst w
          exact ⟨t, rfl, rfl, htz⟩
      have hPopen : (resultAt X (.ret v) (.bound 0)).openAt 0 z =
          resultAt X (.ret v) (.free z) := by
        simpa only [LogicVar.image_shiftFrom_eq_of_locallyClosed X 0 closedX,
          shiftTerm_eq_of_locallyClosed (.ret v) closedV] using
          resultAt_shift_openAt X (.ret v) z closedX closedV heX hzX
      have hQ : Capability.singleton t ⊨ Q.openAt 0 z := by
        simp only [P, Formula.openAt, hPopen] at hbody
        exact Formula.models_impl_elim hbody hsourceRes
      have hlook : ∀ σ, σ ∈ k →
          t.restrict (B ∪ {z}) = σ.restrict (B ∪ {z}) := by
        intro σ hσ
        apply Store.ext
        intro x
        by_cases hx : x ∈ B ∪ {z}
        · simp only [Store.lookup_restrict, if_pos hx]
          by_cases hxz : x = z
          · subst x
            exact htz.trans (hkz σ hσ).symm
          · have hxB : x ∈ B := by
              rcases Finset.mem_union.1 hx with hx | hx
              · exact hx
              · exact (hxz (Finset.mem_singleton.1 hx)).elim
            have hm : σ.restrict (B ∪ {y}) ∈
                k.restrict (Capability.singleton (ρ.restrict (B ∪ {y}))).domain := by
              rw [Capability.singleton_domain, hρB]
              exact ⟨σ, hσ, rfl⟩
            rw [← hbase] at hm
            have hsame : σ.restrict (B ∪ {y}) = ρ.restrict (B ∪ {y}) := hm
            have hlook := congrArg (fun s => s.lookup x) hsame
            have hρx : σ.lookup x = ρ.lookup x := by
              simpa [Store.lookup_restrict, hxB] using hlook
            rw [Store.lookup_merge_left s o (by rw [hsdom]; exact hBA hxB)]
            simpa [s, Store.lookup_restrict, hBA hxB] using hρx.symm
        · rw [Store.lookup_restrict, Store.lookup_restrict, if_neg hx, if_neg hx]
      have hproj : k.restrict (B ∪ {z}) =
          (Capability.singleton t).restrict (B ∪ {z}) := by
        apply Capability.ext
        · simp only [Capability.restrict_domain,
            Capability.singleton_domain, t, Store.domain_merge, hsdom, hodom]
          have hscope := Formula.models_scope hret
          rw [freeAtoms_resultAt, hYfree] at hscope
          have hBk : B ∪ {z} ⊆ k.domain := by
            intro x hx
            apply hscope
            rcases Finset.mem_union.1 hx with hx | hx
            · exact Finset.mem_union_left _ (Finset.mem_union_left _
                (Finset.mem_union_left _ hx))
            · exact Finset.mem_union_right _ hx
          rw [Finset.inter_eq_right.2 hBk,
            Finset.inter_eq_right.2
              (Finset.union_subset_union hBA (Finset.Subset.refl _))]
        · intro σ
          constructor
          · rintro ⟨υ, hυ, hυσ⟩
            exact ⟨t, rfl, (hlook υ hυ).trans hυσ⟩
          · rintro ⟨υ, hυ, hυσ⟩
            have : υ = t := hυ
            subst υ
            obtain ⟨w, hw⟩ := k.nonempty
            exact ⟨w, hw, (hlook w hw).symm.trans hυσ⟩
      exact (Formula.models_projection (B ∪ {z}) hQscope hproj).2 hQ


/-- Transport result-first quantification along an exact nondeterministic
result alias, including the change in relevant input observations. -/
theorem models_resultFirst_result_alias
    {m : Capability} {Δ : BasicEnv} {τ : ContextType} {e : Term} {y : Atom}
    {X : Finset LogicVar} {Q : Formula}
    (wfτ : τ.WellFormed Δ.domain) (closedE : e.locallyClosed)
    (supportE : e.support ⊆ Δ.domain)
    (closedX : LogicVar.LocallyClosed X) (supportX : e.logicSupport ⊆ X)
    (typeSupport : τ.freeAtoms.image LogicVar.free ⊆ X)
    (freshX : LogicVar.free y ∉ X) (freshΔ : y ∉ Δ.domain)
    (supportQ : Q.freeAtoms ⊆ τ.freeAtoms)
    (hres : m ⊨ resultAt X e (.free y))
    (hsource : m ⊨ Formula.all
      (resultFirst (relevantEnv Δ τ e) τ e ⇒ᶜ Q)) :
    m ⊨ Formula.all
      ((resultFirst (relevantEnv Δ τ (.ret (.bound 0))) τ
        (.ret (.bound 0))).openAt 1 y ⇒ᶜ Q) := by
  let A := τ.freeAtoms ∪ e.support
  let B := τ.freeAtoms
  have hAΔ : A ⊆ Δ.domain := Finset.union_subset wfτ.freeAtoms_subset supportE
  have henv : (relevantEnv Δ τ e).domain = A := by
    rw [relevantEnv_domain]
    exact Finset.inter_eq_right.2 hAΔ
  have henvB : (relevantEnv Δ τ (.ret (.bound 0))).domain = B := by
    simp only [relevantEnv_domain, relevantAtoms, Term.support, Value.support,
      Finset.union_empty]
    exact Finset.inter_eq_right.2 wfτ.freeAtoms_subset
  have hclosed := relevantSupport_locallyClosed (relevantEnv Δ τ e) τ e
    wfτ.locallyClosedAt closedE
  have hsupport : relevantSupport (relevantEnv Δ τ e) τ e =
      A.image LogicVar.free := by
    rw [LogicVar.eq_image_free_of_locallyClosed hclosed,
      freeAtomSet_relevantSupport, relevantEnv_idem, henv]
  have hclosedA : LogicVar.LocallyClosed (A.image LogicVar.free) := by
    intro j hj
    simp at hj
  have hsourceR : resultFirst (relevantEnv Δ τ e) τ e =
      resultAt (A.image LogicVar.free) e (.bound 0) := by
    rw [resultFirst, hsupport,
      LogicVar.image_shiftFrom_eq_of_locallyClosed _ 0 hclosedA,
      shiftTerm_eq_of_locallyClosed e closedE]
  rw [hsourceR] at hsource
  have htargetR :
      (resultFirst (relevantEnv Δ τ (.ret (.bound 0))) τ (.ret (.bound 0))).openAt 1 y =
        resultAt (insert (.free y) (B.image LogicVar.free))
          (.ret (.free y)) (.bound 0) := by
    rw [resultFirst_ret_bound_openAt _ τ y wfτ.locallyClosedAt
      (by rw [henvB]; exact fun hy => freshΔ (wfτ.freeAtoms_subset hy))]
    rw [relevantEnv_idem, henvB]
  rw [htargetR]
  have heimage : e.logicSupport = e.support.image LogicVar.free := by
    rw [LogicVar.eq_image_free_of_locallyClosed (termLogicSupport_locallyClosed e closedE),
      freeAtomSet_term_logicSupport]
  have hAX : A.image LogicVar.free ⊆ X := by
    simp only [A, Finset.image_union]
    exact Finset.union_subset typeSupport (by rwa [← heimage])
  have heA : e.logicSupport ⊆ A.image LogicVar.free := by
    rw [heimage]
    exact Finset.image_subset_image Finset.subset_union_right
  have hresA : m ⊨ resultAt (A.image LogicVar.free) e (.free y) := by
    have hr := models_resultAt_restrict_support closedX hAX heA freshX hres
    exact Formula.models_kripke (Capability.restrict_refines m _) hr
  have h := models_all_result_alias closedE Finset.subset_union_right
    Finset.subset_union_left supportQ (fun hy => freshΔ (hAΔ hy)) hresA hsource
  simpa only [B, Finset.image_union, Finset.image_singleton,
    Finset.union_singleton, Finset.image_insert] using h

/-- Transport a result-first quantifier along a returned-value alias on a
singleton capability, accounting for both relevant environments. -/
theorem models_resultFirst_ret_alias_singleton
    {ρ : Store} {Δ : BasicEnv} {τ : ContextType} {v : Value} {y : Atom}
    {X : Finset LogicVar} {Q : Formula}
    (wfτ : τ.WellFormed Δ.domain) (closedV : v.locallyClosed)
    (supportV : v.support ⊆ Δ.domain)
    (closedX : LogicVar.LocallyClosed X)
    (supportX : (.ret v : Term).logicSupport ⊆ X)
    (freshX : LogicVar.free y ∉ X) (freshΔ : y ∉ Δ.domain)
    (supportQ : Q.freeAtoms ⊆ τ.freeAtoms)
    (hres : Capability.singleton ρ ⊨ resultAt X (.ret v) (.free y))
    (hsource : Capability.singleton ρ ⊨ Formula.all
      (resultFirst (relevantEnv Δ τ (.ret v)) τ (.ret v) ⇒ᶜ Q)) :
    Capability.singleton ρ ⊨ Formula.all
      ((resultFirst (relevantEnv Δ τ (.ret (.bound 0))) τ
        (.ret (.bound 0))).openAt 1 y ⇒ᶜ Q) := by
  let A := τ.freeAtoms ∪ v.support
  let B := τ.freeAtoms
  have hAΔ : A ⊆ Δ.domain := Finset.union_subset wfτ.freeAtoms_subset supportV
  have henv : (relevantEnv Δ τ (.ret v)).domain = A := by
    rw [relevantEnv_domain]
    exact Finset.inter_eq_right.2 hAΔ
  have henvB : (relevantEnv Δ τ (.ret (.bound 0))).domain = B := by
    simp only [relevantEnv_domain, relevantAtoms, Term.support, Value.support,
      Finset.union_empty]
    exact Finset.inter_eq_right.2 wfτ.freeAtoms_subset
  have hclosed : LogicVar.LocallyClosed
      (relevantSupport (relevantEnv Δ τ (.ret v)) τ (.ret v)) :=
    relevantSupport_locallyClosed _ τ (.ret v) wfτ.locallyClosedAt closedV
  have hsupport : relevantSupport (relevantEnv Δ τ (.ret v)) τ (.ret v) =
      A.image LogicVar.free := by
    rw [LogicVar.eq_image_free_of_locallyClosed hclosed,
      freeAtomSet_relevantSupport, relevantEnv_idem, henv]
  have hsourceR : resultFirst (relevantEnv Δ τ (.ret v)) τ (.ret v) =
      resultAt (A.image LogicVar.free) (.ret v) (.bound 0) := by
    have hAX : LogicVar.LocallyClosed (A.image LogicVar.free) := by
      intro j hj
      simp at hj
    rw [resultFirst, hsupport,
      LogicVar.image_shiftFrom_eq_of_locallyClosed _ 0 hAX,
      shiftTerm_eq_of_locallyClosed (.ret v) closedV]
  rw [hsourceR] at hsource
  have htargetR :
      (resultFirst (relevantEnv Δ τ (.ret (.bound 0))) τ (.ret (.bound 0))).openAt 1 y =
        resultAt (insert (.free y) (B.image LogicVar.free))
          (.ret (.free y)) (.bound 0) := by
    rw [resultFirst_ret_bound_openAt _ τ y wfτ.locallyClosedAt
      (by rw [henvB]; exact fun hy => freshΔ (wfτ.freeAtoms_subset hy))]
    rw [relevantEnv_idem, henvB]
  rw [htargetR]
  apply models_all_ret_alias_singleton closedV
    (Finset.subset_union_right : v.support ⊆ A)
    (Finset.subset_union_left : B ⊆ A) supportQ (fun hy => freshΔ (hAΔ hy))
    ?_ hsource
  have hAρ : A ⊆ ρ.domain := by
    have hs := Formula.models_scope hsource
    simp only [Formula.freeAtoms_all, Formula.freeAtoms_impl, freeAtoms_resultAt,
      Formula.LogicVar.freeAtomSet_image_free, LogicVar.freeAtoms] at hs
    exact fun x hx => hs (Finset.mem_union_left _
      (Finset.mem_union_left _ (Finset.mem_union_left _ hx)))
  have hyA : LogicVar.free y ∉ A.image LogicVar.free := by
    intro hy
    obtain ⟨x, hx, hsame⟩ := Finset.mem_image.1 hy
    have hxy : x = y := by simpa using hsame
    exact freshΔ (hAΔ (hxy ▸ hx))
  apply models_resultAt_ret_change_support closedX (by intro j hj; simp at hj)
    supportX ?_ freshX hyA ?_ hres
  · intro ξ hξ
    cases ξ with
    | bound j => exact (termLogicSupport_locallyClosed (.ret v) closedV j hξ).elim
    | free x =>
        apply Finset.mem_image.2
        refine ⟨x, Finset.mem_union_right _ ?_, rfl⟩
        change x ∈ (.ret v : Term).support
        rw [← freeAtomSet_term_logicSupport, LogicVar.mem_freeAtomSet_iff]
        exact hξ
  · rw [Formula.LogicVar.freeAtomSet_image_free]
    apply Finset.union_subset hAρ
    intro x hx
    have hxy : x = y := Finset.mem_singleton.1 hx
    subst x
    apply Formula.models_scope hres
    rw [freeAtoms_resultAt]
    simp [LogicVar.freeAtoms]

/-! ## Closed static atoms -/

theorem models_basicWorld_empty (m : Capability) :
    m ⊨ basicWorld ∅ := by
  apply Formula.models_fiberAtom_of_support_empty
  · simp [basicWorldQualifier]
  · intro ρ ξ T h
    cases ξ <;> simp at h

theorem models_wellFormed_empty (m : Capability) (d : Nat)
    (τ : ContextType) (hτ : τ.WellFormedAt d ∅) :
    m ⊨ wellFormed d ∅ τ := by
  apply Formula.models_fiberAtom_of_support_empty
  · simp [wellFormedQualifier]
  · intro ρ
    exact hτ

theorem models_basicTyping_ret_const (m : Capability) (c : Constant) :
    m ⊨ basicTyping ∅ (.ret (.const c)) (.base c.baseType) := by
  apply Formula.models_fiberAtom_of_support_empty
  · simp [basicTypingQualifier, Term.logicSupportAt,
      Value.logicSupportAt]
  · intro ρ
    refine ⟨by simp [Term.support, Value.support], ?_, ?_⟩
    · intro ξ T h
      cases ξ <;> simp at h
    · simpa [instantiateTerm, instantiateTermAt, instantiateValueAt] using
        BasicTermTyp.ret (BasicValTyp.const ∅ c)

theorem models_total_ret_const (m : Capability) (c : Constant) :
    m ⊨ total (.ret (.const c)) := by
  apply Formula.models_fiberAtom_of_support_empty
  · simp [totalQualifier, Term.logicSupportAt, Value.logicSupportAt]
  · intro ρ
    apply Term.MustTerminate.ret
    trivial

theorem models_guard_ret_const (m : Capability) (d : Nat)
    (τ : ContextType) (c : Constant) (hτ : τ.WellFormedAt d ∅)
    (erase : τ.erase = .base c.baseType) :
    m ⊨ guard d ∅ τ (.ret (.const c)) := by
  apply Formula.models_and_intro
  · exact models_wellFormed_empty m d τ hτ
  · apply Formula.models_and_intro
    · exact models_basicWorld_empty m
    · apply Formula.models_and_intro
      · rw [erase]
        exact models_basicTyping_ret_const m c
      · exact models_total_ret_const m c

/-! ## Constant result formulas -/

theorem resultQualifier_ret_const_openAt (c : Constant) (y : Atom) :
    (resultQualifier (.ret (.const c)) (.bound 0)).openAt 0 y =
      (Qualifier.equal (.bound 0) (.const c)).openAt 0 y := by
  apply Qualifier.ext
  · simp [resultQualifier, Qualifier.equal, Term.logicSupport,
      Term.logicSupportAt, Value.logicalSupport, Value.logicSupportAt]
  · intro ρ σ same
    simp only [Qualifier.openAt, resultQualifier, Qualifier.equal,
      Value.denoteAssignment, AssignmentOn.swapBack,
      Assignment.lookup_swap]
    rw [same]
    simp only [Term.logicSupport, Term.logicSupportAt,
      Value.logicSupportAt, Finset.notMem_empty, not_false_eq_true,
      true_and]
    constructor
    · rintro ⟨v, hv, reaches⟩
      have samev : v = .const c :=
        (Term.ret_reaches_iff (.const c) v
          (by simp [Value.locallyClosedAt])).1 reaches
      simpa [samev] using hv
    · intro hv
      exact ⟨.const c, hv,
        (Term.ret_reaches_iff (.const c) (.const c)
          (by simp [Value.locallyClosedAt])).2 rfl⟩

theorem resultFirst_ret_const_openAt (τ : ContextType) (c : Constant)
    (y : Atom) (hsupp : τ.support = ∅) :
    (resultFirst (relevantEnv ∅ τ (.ret (.const c))) τ
      (.ret (.const c))).openAt 0 y =
        Formula.fiber ∅
          (.atom ((Qualifier.equal (.bound 0) (.const c)).openAt 0 y)) := by
  simp [resultFirst, relevantEnv, relevantAtoms, relevantSupport, resultAt,
    LogicVar.openSupport, Qualifier.equal, Value.logicalSupport,
    Term.support, Value.support, Term.logicSupport, Term.logicSupportAt,
    Value.logicSupportAt, shiftTerm, shiftTermAt, shiftValueAt,
    Formula.openAt, resultQualifier_ret_const_openAt, hsupp]

theorem models_resultBasicTyping_ret_const_openAt
    (m : Capability) (c : Constant) (y : Atom)
    (h : m ⊨ Atom((Qualifier.equal (.bound 0) (.const c)).openAt 0 y)) :
    m ⊨ (resultBasicTyping c.baseType).openAt 0 y := by
  unfold resultBasicTyping basicTyping Formula.fiberAtom
  simp only [Formula.openAt]
  apply Formula.models_fiber_intro
  · simpa [basicTypingQualifier, Qualifier.equal, Qualifier.freeAtoms,
      Term.logicSupport, Term.logicSupportAt, Value.logicSupportAt,
      boundLogicSupportAt, LogicVar.freeAtomSet, LogicVar.openSupport,
      LogicVar.openBinder, LogicVar.swap, Value.logicalSupport] using
      Formula.models_scope h
  · intro k hk
    simp [basicTypingQualifier, Term.logicSupportAt,
      Value.logicSupportAt, boundLogicSupportAt, LogicVar.openSupport,
      LogicVar.openBinder, LogicVar.swap] at hk
  · intro σ f hf
    have hq :
        ((Qualifier.equal (.bound 0) (.const c)).openAt 0 y).freeAtoms =
          {y} := by
      simp [Qualifier.equal, Qualifier.freeAtoms, LogicVar.freeAtoms,
        LogicVar.openSupport, LogicVar.openBinder, LogicVar.swap,
        Value.logicalSupport]
    have hy : y ∈ m.domain := by
      apply Formula.models_scope h
      simp [hq]
    have hσdom : σ.domain = {y} := by
      have hdom := (m.restrict
          (Formula.fiber
            (LogicVar.openSupport 0 y
              (basicTypingQualifier ∅ (.ret (.bound 0))
                (.base c.baseType)).support)
            (.atom ((basicTypingQualifier ∅ (.ret (.bound 0))
              (.base c.baseType)).openAt 0 y))).freeAtoms).restrict
          (LogicVar.freeAtomSet
            (LogicVar.openSupport 0 y
              (basicTypingQualifier ∅ (.ret (.bound 0))
                (.base c.baseType)).support))
        |>.mem_domain hf.projection_mem
      simpa [basicTypingQualifier, Qualifier.freeAtoms,
        Term.logicSupport, Term.logicSupportAt, Value.logicSupportAt,
        boundLogicSupportAt, LogicVar.freeAtomSet, LogicVar.freeAtoms,
        LogicVar.openSupport, LogicVar.openBinder, LogicVar.swap, hy] using
        hdom
    have he := (Formula.models_atom_iff m
      ((Qualifier.equal (.bound 0) (.const c)).openAt 0 y)).1 h |>.2
    have hσ : σ ∈
        Capability.restrict
          (m.restrict
            ((Qualifier.equal (.bound 0) (.const c)).openAt 0 y).freeAtoms)
          ((Qualifier.equal (.bound 0) (.const c)).openAt 0 y).freeAtoms := by
      simpa [basicTypingQualifier, Qualifier.equal, Qualifier.freeAtoms,
        Term.logicSupport, Term.logicSupportAt, Value.logicSupportAt,
        boundLogicSupportAt, LogicVar.freeAtomSet, LogicVar.openSupport,
        LogicVar.openBinder, LogicVar.swap, Value.logicalSupport] using
        hf.projection_mem
    have hs := (he.2.2 σ (by
      simpa [Qualifier.equal, Qualifier.freeAtoms,
        LogicVar.freeAtomSet, LogicVar.openSupport,
        LogicVar.openBinder, LogicVar.swap,
        Value.logicalSupport] using hσdom)).2 hσ
    obtain ⟨_, ρ, hρ, look⟩ := hs
    have hlookup : σ.lookup y = some (.const c) := by
      rw [← look y]
      simpa [Qualifier.openAt, Qualifier.equal, Value.denoteAssignment,
        AssignmentOn.swapBack, Assignment.lookup_swap,
        LogicVar.swap] using hρ
    apply Formula.models_atom_of_support_empty
    · simp [Qualifier.substitute, Qualifier.openAt,
        basicTypingQualifier, Term.logicSupportAt,
        Value.logicSupportAt, boundLogicSupportAt,
        LogicVar.openSupport, LogicVar.openBinder, LogicVar.swap, hσdom]
    · intro a
      have hX :
          (((basicTypingQualifier ∅ (.ret (.bound 0))
            (.base c.baseType)).openAt 0 y).substitute
              σ.toAssignment).support = ∅ := by
        simp [Qualifier.substitute, Qualifier.openAt,
          basicTypingQualifier, Term.logicSupportAt,
          Value.logicSupportAt, boundLogicSupportAt,
          LogicVar.openSupport, LogicVar.openBinder, LogicVar.swap, hσdom]
      have hadom : a.assignment.domain = ∅ :=
        a.domain_eq.trans hX
      have ha : a.assignment = ∅ := by
        apply Assignment.ext
        intro ξ
        rw [Assignment.lookup_empty]
        apply (Assignment.lookup_eq_none_iff a.assignment ξ).2
        rw [hadom]
        exact Finset.notMem_empty ξ
      simp [Qualifier.substitute, Qualifier.openAt,
        basicTypingQualifier, AssignmentOn.substituteBack,
        AssignmentOn.swapBack, Assignment.lookup_swap,
        instantiateTermAt, instantiateValueAt, Term.logicSupportAt,
        Value.logicSupportAt, boundLogicSupportAt, LogicVar.openSupport,
        LogicVar.openBinder, LogicVar.swap, ha, hlookup,
        Term.support, Value.support]
      constructor
      · intro ξ T hT
        cases ξ <;> simp at hT
      · exact BasicTermTyp.ret (BasicValTyp.const ∅ c)

theorem models_resultBody_ret_const_openAt
    (m : Capability) (τ : ContextType) (c : Constant) (y : Atom)
    (hsupp : τ.support = ∅)
    (h : m ⊨
      (resultFirst (relevantEnv ∅ τ (.ret (.const c))) τ
        (.ret (.const c))).openAt 0 y) :
    m ⊨
      (Atom(Qualifier.equal (.bound 0) (.const c)) ∧ᶜ
        resultBasicTyping c.baseType).openAt 0 y := by
  rw [resultFirst_ret_const_openAt τ c y hsupp] at h
  have hq := (Formula.models_fiber_empty_iff m
    (.atom ((Qualifier.equal (.bound 0) (.const c)).openAt 0 y))).1 h
  have hb := models_resultBasicTyping_ret_const_openAt m c y hq
  exact Formula.models_and_intro hq hb

theorem models_overResult_ret_const_openAt
    (m : Capability) (c : Constant) (y : Atom)
    (h : m ⊨
      (resultFirst
        (relevantEnv ∅
          (.over c.baseType (Qualifier.equal (.bound 0) (.const c)))
          (.ret (.const c)))
        (.over c.baseType (Qualifier.equal (.bound 0) (.const c)))
        (.ret (.const c))).openAt 0 y) :
    m ⊨
      (Formula.fiber
        ((Qualifier.equal (.bound 0) (.const c)).support \ {.bound 0})
        (overResult c.baseType
          (Qualifier.equal (.bound 0) (.const c)))).openAt 0 y := by
  have hsupp :
      (ContextType.over c.baseType
        (Qualifier.equal (.bound 0) (.const c))).support = ∅ := by
    simp [ContextType.support, ContextType.supportAt,
      LogicVar.supportAtDepth, LogicVar.atDepth,
      Qualifier.equal, Value.logicalSupport]
  have hbody := models_resultBody_ret_const_openAt m _ c y hsupp h
  simp only [Formula.openAt]
  have hempty : LogicVar.openSupport 0 y
      ((Qualifier.equal (.bound 0) (.const c)).support \ {.bound 0}) = ∅ := by
    simp [Qualifier.equal, Value.logicalSupport, LogicVar.openSupport]
  rw [hempty]
  apply (Formula.models_fiber_empty_iff m _).2
  apply Formula.models_over_intro
  exact hbody

theorem models_underResult_ret_const_openAt
    (m : Capability) (c : Constant) (y : Atom)
    (h : m ⊨
      (resultFirst
        (relevantEnv ∅
          (.under c.baseType (Qualifier.equal (.bound 0) (.const c)))
          (.ret (.const c)))
        (.under c.baseType (Qualifier.equal (.bound 0) (.const c)))
        (.ret (.const c))).openAt 0 y) :
    m ⊨
      (Formula.fiber
        ((Qualifier.equal (.bound 0) (.const c)).support \ {.bound 0})
        (underResult c.baseType
          (Qualifier.equal (.bound 0) (.const c)))).openAt 0 y := by
  have hsupp :
      (ContextType.under c.baseType
        (Qualifier.equal (.bound 0) (.const c))).support = ∅ := by
    simp [ContextType.support, ContextType.supportAt,
      LogicVar.supportAtDepth, LogicVar.atDepth,
      Qualifier.equal, Value.logicalSupport]
  have hbody := models_resultBody_ret_const_openAt m _ c y hsupp h
  simp only [Formula.openAt]
  have hempty : LogicVar.openSupport 0 y
      ((Qualifier.equal (.bound 0) (.const c)).support \ {.bound 0}) = ∅ := by
    simp [Qualifier.equal, Value.logicalSupport, LogicVar.openSupport]
  rw [hempty]
  apply (Formula.models_fiber_empty_iff m _).2
  apply Formula.models_under_intro
  exact hbody

end Interp

namespace ContextType

/-! ## Result-first context-type interpretation -/

def measure : ContextType → Nat
  | .over _ _ | .under _ _ => 1
  | .inter τ₁ τ₂ | .union τ₁ τ₂ | .sum τ₁ τ₂
  | .arrow τ₁ τ₂ | .wand τ₁ τ₂ =>
      1 + max τ₁.measure τ₂.measure
  | .persist τ => 1 + τ.measure

@[simp] theorem measure_shiftFrom (τ : ContextType) (k : Nat) :
    (τ.shiftFrom k).measure = τ.measure := by
  induction τ generalizing k <;> simp_all [shiftFrom, measure]

theorem measure_pos (τ : ContextType) : 0 < τ.measure := by
  cases τ <;> simp only [measure] <;> omega

def interpFuel : Nat → Nat → BasicEnv → ContextType → Term → Formula
  | 0, d, Δ, τ, e =>
      let Δ' := Interp.relevantEnv Δ τ e
      Interp.guard d Δ' τ e ∧ᶜ ⊤ᶜ
  | gas + 1, d, Δ, τ, e =>
      let Δ' := Interp.relevantEnv Δ τ e
      let G := Interp.guard d Δ' τ e
      G ∧ᶜ
        match τ with
        | .over b q =>
            .all (Interp.resultFirst Δ' τ e ⇒ᶜ
              .fiber (q.support \ {.bound 0}) (Interp.overResult b q))
        | .under b q =>
            .all (Interp.resultFirst Δ' τ e ⇒ᶜ
              .fiber (q.support \ {.bound 0}) (Interp.underResult b q))
        | .inter τ₁ τ₂ =>
            interpFuel gas d Δ τ₁ e ∧ᶜ interpFuel gas d Δ τ₂ e
        | .union τ₁ τ₂ =>
            interpFuel gas d Δ τ₁ e ∨ᶜ interpFuel gas d Δ τ₂ e
        | .sum τ₁ τ₂ =>
            .all (Interp.resultFirst Δ' τ e ⇒ᶜ
              (interpFuel gas (d + 1) Δ' (τ₁.shiftFrom 0) (.ret (.bound 0)) ⊕
               interpFuel gas (d + 1) Δ' (τ₂.shiftFrom 0) (.ret (.bound 0))))
        | .arrow τ₁ τ₂ =>
            let τ₁' := (τ₁.shiftFrom 0).shiftFrom 0
            let τ₂' := τ₂.shiftFrom 1
            .all (Interp.resultFirst Δ' τ e ⇒ᶜ
              .all (interpFuel gas (d + 2) Δ' τ₁' (.ret (.bound 0)) ⇒ᶜ
                interpFuel gas (d + 2) Δ' τ₂'
                  (.app (.bound 1) (.bound 0))))
        | .wand τ₁ τ₂ =>
            let τ₁' := (τ₁.shiftFrom 0).shiftFrom 0
            let τ₂' := τ₂.shiftFrom 1
            .all (Interp.resultFirst Δ' τ e ⇒ᶜ
              (interpFuel gas (d + 2) Δ' τ₁' (.ret (.bound 0)) -∗[1]
                interpFuel gas (d + 2) Δ' τ₂'
                  (.app (.bound 1) (.bound 0))))
        | .persist τ =>
            .all (Interp.resultFirst Δ' (.persist τ) e ⇒ᶜ
              □ interpFuel gas (d + 1) Δ' (τ.shiftFrom 0) (.ret (.bound 0)))

/-- Once enough fuel is available to visit the entire context type, the
result-first interpretation is independent of the fuel allowance. -/
theorem interpFuel_eq_of_measure_le (gas gas' d : Nat) (Δ : BasicEnv)
    (τ : ContextType) (e : Term)
    (lower : τ.measure ≤ gas) (lower' : τ.measure ≤ gas') :
    interpFuel gas d Δ τ e = interpFuel gas' d Δ τ e := by
  have aux : ∀ n (τ : ContextType), τ.measure = n →
      ∀ gas gas' d Δ e, τ.measure ≤ gas → τ.measure ≤ gas' →
      interpFuel gas d Δ τ e = interpFuel gas' d Δ τ e := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
        intro τ hmeasure gas gas' d Δ e lower lower'
        cases gas with
        | zero =>
            have := τ.measure_pos
            omega
        | succ gas =>
            cases gas' with
            | zero =>
                have := τ.measure_pos
                omega
            | succ gas' =>
                have hchild (τ' : ContextType) (d' : Nat) (Δ' : BasicEnv) (e' : Term)
                    (smaller : τ'.measure < τ.measure) :
                    interpFuel gas d' Δ' τ' e' = interpFuel gas' d' Δ' τ' e' :=
                  ih τ'.measure (by omega) τ' rfl gas gas' d' Δ' e'
                    (by omega) (by omega)
                cases τ with
                | «over» b q => rfl
                | under b q => rfl
                | inter τ₁ τ₂ =>
                    have h₁ := hchild τ₁ d Δ e (by
                      simp only [measure]
                      omega)
                    have h₂ := hchild τ₂ d Δ e (by
                      simp only [measure]
                      omega)
                    simp only [interpFuel]
                    rw [h₁, h₂]
                | union τ₁ τ₂ =>
                    have h₁ := hchild τ₁ d Δ e (by
                      simp only [measure]
                      omega)
                    have h₂ := hchild τ₂ d Δ e (by
                      simp only [measure]
                      omega)
                    simp only [interpFuel]
                    rw [h₁, h₂]
                | sum τ₁ τ₂ =>
                    have h₁ := hchild (τ₁.shiftFrom 0) (d + 1)
                      (Interp.relevantEnv Δ (.sum τ₁ τ₂) e) (.ret (.bound 0)) (by
                        simp only [measure_shiftFrom, measure]
                        omega)
                    have h₂ := hchild (τ₂.shiftFrom 0) (d + 1)
                      (Interp.relevantEnv Δ (.sum τ₁ τ₂) e) (.ret (.bound 0)) (by
                        simp only [measure_shiftFrom, measure]
                        omega)
                    simp only [interpFuel]
                    rw [h₁, h₂]
                | arrow τ₁ τ₂ =>
                    have h₁ := hchild ((τ₁.shiftFrom 0).shiftFrom 0) (d + 2)
                      (Interp.relevantEnv Δ (.arrow τ₁ τ₂) e) (.ret (.bound 0)) (by
                        simp only [measure_shiftFrom, measure]
                        omega)
                    have h₂ := hchild (τ₂.shiftFrom 1) (d + 2)
                      (Interp.relevantEnv Δ (.arrow τ₁ τ₂) e)
                      (.app (.bound 1) (.bound 0)) (by
                        simp only [measure_shiftFrom, measure]
                        omega)
                    simp only [interpFuel]
                    rw [h₁, h₂]
                | wand τ₁ τ₂ =>
                    have h₁ := hchild ((τ₁.shiftFrom 0).shiftFrom 0) (d + 2)
                      (Interp.relevantEnv Δ (.wand τ₁ τ₂) e) (.ret (.bound 0)) (by
                        simp only [measure_shiftFrom, measure]
                        omega)
                    have h₂ := hchild (τ₂.shiftFrom 1) (d + 2)
                      (Interp.relevantEnv Δ (.wand τ₁ τ₂) e)
                      (.app (.bound 1) (.bound 0)) (by
                        simp only [measure_shiftFrom, measure]
                        omega)
                    simp only [interpFuel]
                    rw [h₁, h₂]
                | persist τ =>
                    have hτ := hchild (τ.shiftFrom 0) (d + 1)
                      (Interp.relevantEnv Δ (.persist τ) e) (.ret (.bound 0)) (by
                        simp only [measure_shiftFrom, measure]
                        omega)
                    simp only [interpFuel]
                    rw [hτ]
  exact aux τ.measure τ rfl gas gas' d Δ e lower lower'

/-- Interpretation of a context type at a core term. -/
def interp (Δ : BasicEnv) (τ : ContextType) (e : Term) : Formula :=
  interpFuel τ.measure 0 Δ τ e

theorem interp_persist (Δ : BasicEnv) (τ : ContextType) (e : Term) :
    interp Δ (.persist τ) e =
      (Interp.guard 0 (Interp.relevantEnv Δ τ e) τ e ∧ᶜ
        Formula.all
          (Interp.resultFirst (Interp.relevantEnv Δ τ e) (.persist τ) e ⇒ᶜ
            □ interpFuel τ.measure 1 (Interp.relevantEnv Δ τ e)
              (τ.shiftFrom 0) (.ret (.bound 0)))) := by
  unfold interp
  rw [show (ContextType.persist τ).measure = τ.measure + 1 by
    simp [measure, Nat.add_comm]]
  simp only [interpFuel, Interp.relevantEnv_persist,
    Interp.guard_persist, Nat.zero_add]

theorem freeAtoms_interpFuel_subset (gas d : Nat) (Δ : BasicEnv)
    (τ : ContextType) (e : Term) :
    (interpFuel gas d Δ τ e).freeAtoms ⊆ τ.freeAtoms ∪ e.support := by
  induction gas generalizing d Δ τ e with
  | zero =>
      simpa [interpFuel] using
        Interp.freeAtoms_guard_relevant_subset d Δ τ e
  | succ gas ih =>
      cases τ with
      | «over» b q =>
          simp only [interpFuel, Formula.freeAtoms_and,
            Formula.freeAtoms_all, Formula.freeAtoms_impl,
            Interp.freeAtoms_overResultFiber, ContextType.freeAtoms]
          exact Finset.union_subset
            (Interp.freeAtoms_guard_relevant_subset d Δ (.over b q) e)
            (Finset.union_subset
              (Interp.freeAtoms_resultFirst_relevant_subset Δ (.over b q) e)
              Finset.subset_union_left)
      | under b q =>
          simp only [interpFuel, Formula.freeAtoms_and,
            Formula.freeAtoms_all, Formula.freeAtoms_impl,
            Interp.freeAtoms_underResultFiber, ContextType.freeAtoms]
          exact Finset.union_subset
            (Interp.freeAtoms_guard_relevant_subset d Δ (.under b q) e)
            (Finset.union_subset
              (Interp.freeAtoms_resultFirst_relevant_subset Δ (.under b q) e)
              Finset.subset_union_left)
      | inter τ₁ τ₂ =>
          simp only [interpFuel, Formula.freeAtoms_and, ContextType.freeAtoms]
          refine Finset.union_subset
            (Interp.freeAtoms_guard_relevant_subset d Δ (.inter τ₁ τ₂) e)
            (Finset.union_subset ?_ ?_)
          · intro x hx
            rcases Finset.mem_union.1 (ih d Δ τ₁ e hx) with hx | hx
            · exact Finset.mem_union_left _ (Finset.mem_union_left _ hx)
            · exact Finset.mem_union_right _ hx
          · intro x hx
            rcases Finset.mem_union.1 (ih d Δ τ₂ e hx) with hx | hx
            · exact Finset.mem_union_left _ (Finset.mem_union_right _ hx)
            · exact Finset.mem_union_right _ hx
      | union τ₁ τ₂ =>
          simp only [interpFuel, Formula.freeAtoms_and, Formula.freeAtoms_or,
            ContextType.freeAtoms]
          refine Finset.union_subset
            (Interp.freeAtoms_guard_relevant_subset d Δ (.union τ₁ τ₂) e)
            (Finset.union_subset ?_ ?_)
          · intro x hx
            rcases Finset.mem_union.1 (ih d Δ τ₁ e hx) with hx | hx
            · exact Finset.mem_union_left _ (Finset.mem_union_left _ hx)
            · exact Finset.mem_union_right _ hx
          · intro x hx
            rcases Finset.mem_union.1 (ih d Δ τ₂ e hx) with hx | hx
            · exact Finset.mem_union_left _ (Finset.mem_union_right _ hx)
            · exact Finset.mem_union_right _ hx
      | sum τ₁ τ₂ =>
          simp only [interpFuel, Formula.freeAtoms_and,
            Formula.freeAtoms_all, Formula.freeAtoms_impl,
            Formula.freeAtoms_sum, ContextType.freeAtoms]
          refine Finset.union_subset
            (Interp.freeAtoms_guard_relevant_subset d Δ (.sum τ₁ τ₂) e)
            (Finset.union_subset
              (Interp.freeAtoms_resultFirst_relevant_subset Δ (.sum τ₁ τ₂) e)
              (Finset.union_subset ?_ ?_))
          · intro x hx
            have h := ih (d + 1) (Interp.relevantEnv Δ (.sum τ₁ τ₂) e)
              (τ₁.shiftFrom 0) (.ret (.bound 0)) hx
            simp [Term.support, Value.support] at h
            exact Finset.mem_union_left _ (Finset.mem_union_left _ h)
          · intro x hx
            have h := ih (d + 1) (Interp.relevantEnv Δ (.sum τ₁ τ₂) e)
              (τ₂.shiftFrom 0) (.ret (.bound 0)) hx
            simp [Term.support, Value.support] at h
            exact Finset.mem_union_left _ (Finset.mem_union_right _ h)
      | arrow τ₁ τ₂ =>
          simp only [interpFuel, Formula.freeAtoms_and,
            Formula.freeAtoms_all, Formula.freeAtoms_impl,
            ContextType.freeAtoms]
          refine Finset.union_subset
            (Interp.freeAtoms_guard_relevant_subset d Δ (.arrow τ₁ τ₂) e)
            (Finset.union_subset
              (Interp.freeAtoms_resultFirst_relevant_subset Δ (.arrow τ₁ τ₂) e)
              (Finset.union_subset ?_ ?_))
          · intro x hx
            have h := ih (d + 2) (Interp.relevantEnv Δ (.arrow τ₁ τ₂) e)
              ((τ₁.shiftFrom 0).shiftFrom 0) (.ret (.bound 0)) hx
            simp [Term.support, Value.support] at h
            exact Finset.mem_union_left _ (Finset.mem_union_left _ h)
          · intro x hx
            have h := ih (d + 2) (Interp.relevantEnv Δ (.arrow τ₁ τ₂) e)
              (τ₂.shiftFrom 1) (.app (.bound 1) (.bound 0)) hx
            simp [Term.support, Value.support] at h
            exact Finset.mem_union_left _ (Finset.mem_union_right _ h)
      | wand τ₁ τ₂ =>
          simp only [interpFuel, Formula.freeAtoms_and,
            Formula.freeAtoms_all, Formula.freeAtoms_impl,
            Formula.freeAtoms_wand, ContextType.freeAtoms]
          refine Finset.union_subset
            (Interp.freeAtoms_guard_relevant_subset d Δ (.wand τ₁ τ₂) e)
            (Finset.union_subset
              (Interp.freeAtoms_resultFirst_relevant_subset Δ (.wand τ₁ τ₂) e)
              (Finset.union_subset ?_ ?_))
          · intro x hx
            have h := ih (d + 2) (Interp.relevantEnv Δ (.wand τ₁ τ₂) e)
              ((τ₁.shiftFrom 0).shiftFrom 0) (.ret (.bound 0)) hx
            simp [Term.support, Value.support] at h
            exact Finset.mem_union_left _ (Finset.mem_union_left _ h)
          · intro x hx
            have h := ih (d + 2) (Interp.relevantEnv Δ (.wand τ₁ τ₂) e)
              (τ₂.shiftFrom 1) (.app (.bound 1) (.bound 0)) hx
            simp [Term.support, Value.support] at h
            exact Finset.mem_union_left _ (Finset.mem_union_right _ h)
      | persist τ =>
          simp only [interpFuel, Formula.freeAtoms_and,
            Formula.freeAtoms_all, Formula.freeAtoms_impl,
            Formula.freeAtoms_persist, ContextType.freeAtoms]
          refine Finset.union_subset
            (Interp.freeAtoms_guard_relevant_subset d Δ (.persist τ) e)
            (Finset.union_subset
              (Interp.freeAtoms_resultFirst_relevant_subset Δ (.persist τ) e)
              ?_)
          intro x hx
          have h := ih (d + 1) (Interp.relevantEnv Δ (.persist τ) e)
            (τ.shiftFrom 0) (.ret (.bound 0)) hx
          simp [Term.support, Value.support] at h
          exact Finset.mem_union_left _ h

theorem freeAtoms_interp_subset (Δ : BasicEnv) (τ : ContextType)
    (e : Term) : (interp Δ τ e).freeAtoms ⊆ τ.freeAtoms ∪ e.support :=
  freeAtoms_interpFuel_subset τ.measure 0 Δ τ e

theorem interpFuel_eq_guard_and (gas d : Nat) (Δ : BasicEnv)
    (τ : ContextType) (e : Term) :
    ∃ P, interpFuel gas d Δ τ e =
      (Interp.guard d (Interp.relevantEnv Δ τ e) τ e ∧ᶜ P) := by
  cases gas with
  | zero => exact ⟨⊤ᶜ, rfl⟩
  | succ gas => exact ⟨_, rfl⟩

theorem models_interpFuel_guard {m : Capability} {gas d : Nat}
    {Δ : BasicEnv} {τ : ContextType} {e : Term}
    (h : m ⊨ interpFuel gas d Δ τ e) :
    m ⊨ Interp.guard d (Interp.relevantEnv Δ τ e) τ e := by
  obtain ⟨P, eq⟩ := interpFuel_eq_guard_and gas d Δ τ e
  rw [eq] at h
  exact Formula.models_and_elim_left h

theorem models_interp_guard {m : Capability} {Δ : BasicEnv}
    {τ : ContextType} {e : Term} (h : m ⊨ interp Δ τ e) :
    m ⊨ Interp.guard 0 (Interp.relevantEnv Δ τ e) τ e :=
  models_interpFuel_guard h

theorem models_interp_basicWorld {m : Capability} {Δ : BasicEnv}
    {τ : ContextType} {e : Term} (h : m ⊨ interp Δ τ e) :
    m ⊨ Interp.basicWorld (Interp.relevantEnv Δ τ e) := by
  have hg := models_interp_guard h
  exact Formula.models_and_elim_left (Formula.models_and_elim_right hg)

theorem models_interp_basicTyping {m : Capability} {Δ : BasicEnv}
    {τ : ContextType} {e : Term} (h : m ⊨ interp Δ τ e) :
    m ⊨ Interp.basicTyping (Interp.relevantEnv Δ τ e) e τ.erase := by
  have hg := models_interp_guard h
  exact Formula.models_and_elim_left
    (Formula.models_and_elim_right (Formula.models_and_elim_right hg))

theorem models_interp_total {m : Capability} {Δ : BasicEnv}
    {τ : ContextType} {e : Term} (h : m ⊨ interp Δ τ e) :
    m ⊨ Interp.total e := by
  have hg := models_interp_guard h
  exact Formula.models_and_elim_right
    (Formula.models_and_elim_right (Formula.models_and_elim_right hg))

theorem models_interp_restrict {m : Capability} {Δ : BasicEnv}
    {τ : ContextType} {e : Term} {X : Finset Atom}
    (hX : τ.freeAtoms ∪ e.support ⊆ X) :
    m ⊨ interp Δ τ e ↔ m.restrict X ⊨ interp Δ τ e :=
  Formula.models_restrict_superset m (interp Δ τ e)
    (Finset.Subset.trans (freeAtoms_interp_subset Δ τ e) hX)

theorem models_interp_projection {m n : Capability} {Δ : BasicEnv}
    {τ : ContextType} {e : Term} (X : Finset Atom)
    (hX : τ.freeAtoms ∪ e.support ⊆ X)
    (same : m.restrict X = n.restrict X) :
    m ⊨ interp Δ τ e ↔ n ⊨ interp Δ τ e :=
  Formula.models_projection X
    (Finset.Subset.trans (freeAtoms_interp_subset Δ τ e) hX) same

set_option hygiene false in
scoped[ContextTypes] notation:20 (name := contextTypeInterp)
    "⟦" τ "⟧[" Δ "] " e:20 =>
  ContextTypes.ContextType.interp Δ τ e

end ContextType

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

end

/-! ## Semantic subtyping -/

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

def BasicEnv.AgreeOn (X : Finset Atom) (Δ₁ Δ₂ : BasicEnv) : Prop :=
  ∀ x, x ∈ X → Δ₁.lookup x = Δ₂.lookup x

namespace BasicEnv

theorem AgreeOn.mono {X Y : Finset Atom} {Δ₁ Δ₂ : BasicEnv}
    (h : AgreeOn X Δ₁ Δ₂) (hYX : Y ⊆ X) : AgreeOn Y Δ₁ Δ₂ :=
  fun x hx => h x (hYX hx)

theorem restrict_eq_of_agreeOn {X : Finset Atom} {Δ₁ Δ₂ : BasicEnv}
    (h : AgreeOn X Δ₁ Δ₂) : Δ₁.restrict X = Δ₂.restrict X := by
  apply Finmap.ext_lookup
  intro x
  change (Δ₁.restrict X).lookup x = (Δ₂.restrict X).lookup x
  simp only [lookup_restrict]
  by_cases hx : x ∈ X
  · simp only [if_pos hx]
    exact h x hx
  · simp [hx]

end BasicEnv

namespace Interp

theorem relevantEnv_eq_of_agreeOn {Δ₁ Δ₂ : BasicEnv}
    {τ : ContextType} {e : Term}
    (h : BasicEnv.AgreeOn (τ.freeAtoms ∪ e.support) Δ₁ Δ₂) :
    relevantEnv Δ₁ τ e = relevantEnv Δ₂ τ e :=
  BasicEnv.restrict_eq_of_agreeOn h

end Interp

namespace ContextType

theorem interpFuel_eq_of_agreeOn (gas d : Nat) {Δ₁ Δ₂ : BasicEnv}
    {τ : ContextType} {e : Term}
    (h : BasicEnv.AgreeOn (τ.freeAtoms ∪ e.support) Δ₁ Δ₂) :
    interpFuel gas d Δ₁ τ e = interpFuel gas d Δ₂ τ e := by
  induction gas generalizing d Δ₁ Δ₂ τ e with
  | zero =>
      simp only [interpFuel]
      rw [Interp.relevantEnv_eq_of_agreeOn h]
  | succ gas ih =>
      cases τ with
      | «over» b q =>
          simp only [interpFuel]
          rw [Interp.relevantEnv_eq_of_agreeOn h]
      | under b q =>
          simp only [interpFuel]
          rw [Interp.relevantEnv_eq_of_agreeOn h]
      | sum τ₁ τ₂ =>
          simp only [interpFuel]
          rw [Interp.relevantEnv_eq_of_agreeOn h]
      | arrow τ₁ τ₂ =>
          simp only [interpFuel]
          rw [Interp.relevantEnv_eq_of_agreeOn h]
      | wand τ₁ τ₂ =>
          simp only [interpFuel]
          rw [Interp.relevantEnv_eq_of_agreeOn h]
      | persist τ =>
          simp only [interpFuel]
          rw [Interp.relevantEnv_eq_of_agreeOn h]
      | inter τ₁ τ₂ =>
          have h₁ : BasicEnv.AgreeOn (τ₁.freeAtoms ∪ e.support) Δ₁ Δ₂ :=
            h.mono (by
              intro x hx
              rcases Finset.mem_union.1 hx with hx | hx
              · exact Finset.mem_union_left _ (Finset.mem_union_left _ hx)
              · exact Finset.mem_union_right _ hx)
          have h₂ : BasicEnv.AgreeOn (τ₂.freeAtoms ∪ e.support) Δ₁ Δ₂ :=
            h.mono (by
              intro x hx
              rcases Finset.mem_union.1 hx with hx | hx
              · exact Finset.mem_union_left _ (Finset.mem_union_right _ hx)
              · exact Finset.mem_union_right _ hx)
          simp only [interpFuel]
          rw [Interp.relevantEnv_eq_of_agreeOn h]
          rw [ih _ h₁]
          rw [ih _ h₂]
      | union τ₁ τ₂ =>
          have h₁ : BasicEnv.AgreeOn (τ₁.freeAtoms ∪ e.support) Δ₁ Δ₂ :=
            h.mono (by
              intro x hx
              rcases Finset.mem_union.1 hx with hx | hx
              · exact Finset.mem_union_left _ (Finset.mem_union_left _ hx)
              · exact Finset.mem_union_right _ hx)
          have h₂ : BasicEnv.AgreeOn (τ₂.freeAtoms ∪ e.support) Δ₁ Δ₂ :=
            h.mono (by
              intro x hx
              rcases Finset.mem_union.1 hx with hx | hx
              · exact Finset.mem_union_left _ (Finset.mem_union_right _ hx)
              · exact Finset.mem_union_right _ hx)
          simp only [interpFuel]
          rw [Interp.relevantEnv_eq_of_agreeOn h]
          rw [ih _ h₁]
          rw [ih _ h₂]

theorem interpFuel_eq_of_locallyClosedAt (gas : Nat) (Δ : BasicEnv)
    (τ : ContextType) (e : Term) (k d d' : Nat)
    (closed : τ.LocallyClosedAt k) (hk : k ≤ d) (hk' : k ≤ d') :
    interpFuel gas d Δ τ e = interpFuel gas d' Δ τ e := by
  induction gas generalizing Δ τ e k d d' with
  | zero =>
      simp only [interpFuel]
      rw [Interp.guard_eq_of_locallyClosedAt _ τ e k d d' closed hk hk']
  | succ gas ih =>
      have hguard := Interp.guard_eq_of_locallyClosedAt
        (Interp.relevantEnv Δ τ e) τ e k d d' closed hk hk'
      cases τ with
      | «over» b q | under b q =>
          simp only [interpFuel]
          rw [hguard]
      | inter τ₁ τ₂ | union τ₁ τ₂ =>
          simp only [interpFuel]
          rw [hguard, ih Δ τ₁ e k d d' closed.1 hk hk',
            ih Δ τ₂ e k d d' closed.2 hk hk']
      | sum τ₁ τ₂ =>
          simp only [interpFuel]
          rw [hguard,
            ih _ (τ₁.shiftFrom 0) _ (k + 1) (d + 1) (d' + 1)
              (closed.1.shiftFrom 0) (Nat.add_le_add_right hk 1) (Nat.add_le_add_right hk' 1),
            ih _ (τ₂.shiftFrom 0) _ (k + 1) (d + 1) (d' + 1)
              (closed.2.shiftFrom 0) (Nat.add_le_add_right hk 1) (Nat.add_le_add_right hk' 1)]
      | arrow τ₁ τ₂ | wand τ₁ τ₂ =>
          simp only [interpFuel]
          rw [hguard,
            ih _ ((τ₁.shiftFrom 0).shiftFrom 0) _ (k + 1 + 1) (d + 2) (d' + 2)
              ((closed.1.shiftFrom 0).shiftFrom 0) (by omega) (by omega),
            ih _ (τ₂.shiftFrom 1) _ (k + 1 + 1) (d + 2) (d' + 2)
              (closed.2.shiftFrom 1) (by omega) (by omega)]
      | persist τ =>
          simp only [interpFuel]
          rw [hguard,
            ih _ (τ.shiftFrom 0) _ (k + 1) (d + 1) (d' + 1)
              (closed.shiftFrom 0) (Nat.add_le_add_right hk 1) (Nat.add_le_add_right hk' 1)]

theorem interpFuel_openAt_fresh (gas d : Nat) (Δ : BasicEnv)
    (τ : ContextType) (e : Term) (k : Nat) (y : Atom)
    (closedτ : τ.LocallyClosedAt k) (closedE : e.locallyClosedAt k)
    (freshΔ : y ∉ Δ.domain) (freshτ : y ∉ τ.freeAtoms)
    (freshE : y ∉ e.support) :
    (interpFuel gas d Δ τ e).openAt k y = interpFuel gas d Δ τ e := by
  induction gas generalizing d Δ τ e k with
  | zero =>
      have hΔ : y ∉ (Interp.relevantEnv Δ τ e).domain := by
        rw [Interp.relevantEnv_domain]
        exact fun hy => freshΔ (Finset.mem_inter.1 hy).1
      simp only [interpFuel, Formula.openAt]
      rw [Interp.guard_openAt_eq d _ τ e k y closedE hΔ freshE]
  | succ gas ih =>
      have hΔ : y ∉ (Interp.relevantEnv Δ τ e).domain := by
        rw [Interp.relevantEnv_domain]
        exact fun hy => freshΔ (Finset.mem_inter.1 hy).1
      have hguard := Interp.guard_openAt_eq d (Interp.relevantEnv Δ τ e)
        τ e k y closedE hΔ freshE
      have hresult := Interp.resultFirst_openAt_fresh (Interp.relevantEnv Δ τ e)
        τ e k y closedτ closedE hΔ freshE
      cases τ with
      | «over» b q =>
          have hbody := Interp.overResultFiber_openAt_fresh b q k y closedτ freshτ
          simp only [Formula.openAt] at hbody
          simp only [interpFuel, Formula.openAt]
          rw [hguard, hresult, hbody]
      | under b q =>
          have hbody := Interp.underResultFiber_openAt_fresh b q k y closedτ freshτ
          simp only [Formula.openAt] at hbody
          simp only [interpFuel, Formula.openAt]
          rw [hguard, hresult, hbody]
      | inter τ₁ τ₂ =>
          have hf : y ∉ τ₁.freeAtoms ∧ y ∉ τ₂.freeAtoms := by
            simpa [freeAtoms] using freshτ
          simp only [interpFuel, Formula.openAt]
          rw [hguard, ih d Δ τ₁ e k closedτ.1 closedE freshΔ hf.1 freshE,
            ih d Δ τ₂ e k closedτ.2 closedE freshΔ hf.2 freshE]
      | union τ₁ τ₂ =>
          have hf : y ∉ τ₁.freeAtoms ∧ y ∉ τ₂.freeAtoms := by
            simpa [freeAtoms] using freshτ
          simp only [interpFuel, Formula.openAt]
          rw [hguard, ih d Δ τ₁ e k closedτ.1 closedE freshΔ hf.1 freshE,
            ih d Δ τ₂ e k closedτ.2 closedE freshΔ hf.2 freshE]
      | sum τ₁ τ₂ =>
          have hf : y ∉ τ₁.freeAtoms ∧ y ∉ τ₂.freeAtoms := by
            simpa [freeAtoms] using freshτ
          simp only [interpFuel, Formula.openAt]
          rw [hguard, hresult,
            ih (d + 1) _ (τ₁.shiftFrom 0) (.ret (.bound 0)) (k + 1)
              (closedτ.1.shiftFrom 0) (by simp [Term.locallyClosedAt, Value.locallyClosedAt])
              hΔ (by simpa using hf.1) (by simp [Term.support, Value.support]),
            ih (d + 1) _ (τ₂.shiftFrom 0) (.ret (.bound 0)) (k + 1)
              (closedτ.2.shiftFrom 0) (by simp [Term.locallyClosedAt, Value.locallyClosedAt])
              hΔ (by simpa using hf.2) (by simp [Term.support, Value.support])]
      | arrow τ₁ τ₂ =>
          have hf : y ∉ τ₁.freeAtoms ∧ y ∉ τ₂.freeAtoms := by
            simpa [freeAtoms] using freshτ
          simp only [interpFuel, Formula.openAt]
          rw [hguard, hresult,
            ih (d + 2) _ ((τ₁.shiftFrom 0).shiftFrom 0) (.ret (.bound 0)) ((k + 1) + 1)
              ((closedτ.1.shiftFrom 0).shiftFrom 0)
              (by simp [Term.locallyClosedAt, Value.locallyClosedAt])
              hΔ (by simpa using hf.1) (by simp [Term.support, Value.support]),
            ih (d + 2) _ (τ₂.shiftFrom 1) (.app (.bound 1) (.bound 0)) ((k + 1) + 1)
              (closedτ.2.shiftFrom 1)
              (by simp [Term.locallyClosedAt, Value.locallyClosedAt])
              hΔ (by simpa using hf.2) (by simp [Term.support, Value.support])]
      | wand τ₁ τ₂ =>
          have hf : y ∉ τ₁.freeAtoms ∧ y ∉ τ₂.freeAtoms := by
            simpa [freeAtoms] using freshτ
          simp only [interpFuel, Formula.openAt]
          rw [hguard, hresult,
            ih (d + 2) _ ((τ₁.shiftFrom 0).shiftFrom 0) (.ret (.bound 0)) ((k + 1) + 1)
              ((closedτ.1.shiftFrom 0).shiftFrom 0)
              (by simp [Term.locallyClosedAt, Value.locallyClosedAt])
              hΔ (by simpa using hf.1) (by simp [Term.support, Value.support]),
            ih (d + 2) _ (τ₂.shiftFrom 1) (.app (.bound 1) (.bound 0)) ((k + 1) + 1)
              (closedτ.2.shiftFrom 1)
              (by simp [Term.locallyClosedAt, Value.locallyClosedAt])
              hΔ (by simpa using hf.2) (by simp [Term.support, Value.support])]
      | persist τ =>
          simp only [interpFuel, Formula.openAt]
          rw [hguard, hresult,
            ih (d + 1) _ (τ.shiftFrom 0) (.ret (.bound 0)) (k + 1)
              (closedτ.shiftFrom 0) (by simp [Term.locallyClosedAt, Value.locallyClosedAt])
              hΔ (by simpa using freshτ) (by simp [Term.support, Value.support])]

/-- Pointwise result equivalence transports the full result-first
interpretation, including the static and universal-termination guard. -/
theorem models_interpFuel_of_reaches_iff
    {m : Capability} {Δ : BasicEnv} {τ : ContextType} {e₁ e₂ : Term} {gas : Nat}
    (wfτ : τ.WellFormed Δ.domain)
    (typed₁ : Δ ⊢ₑ e₁ ⋮ τ.erase) (typed₂ : Δ ⊢ₑ e₂ ⋮ τ.erase)
    (world : m ⊨ Interp.basicWorld Δ) (terminates : m ⊨ Interp.total e₂)
    (support : e₁.support ⊆ e₂.support)
    (heval : ∀ σ, σ ∈ m → ∀ v,
      (Interp.instantiateTerm e₁ σ.toAssignment).reaches v ↔
        (Interp.instantiateTerm e₂ σ.toAssignment).reaches v)
    (h : m ⊨ interpFuel gas 0 Δ τ e₁) :
    m ⊨ interpFuel gas 0 Δ τ e₂ := by
  induction gas generalizing τ with
  | zero =>
      exact Formula.models_and_intro
        (Interp.models_guard_relevant_of_world wfτ typed₂ world terminates)
        (Formula.models_top m)
  | succ gas ih =>
      let X := τ.freeAtoms ∪ e₁.support
      let Y := τ.freeAtoms ∪ e₂.support
      let Δ₁ := Interp.relevantEnv Δ τ e₁
      let Δ₂ := Interp.relevantEnv Δ τ e₂
      have hΔ₁ : Δ₁.domain = X := by
        rw [Interp.relevantEnv_domain]
        exact Finset.inter_eq_right.2
          (Finset.union_subset wfτ.freeAtoms_subset typed₁.support_subset)
      have hΔ₂ : Δ₂.domain = Y := by
        rw [Interp.relevantEnv_domain]
        exact Finset.inter_eq_right.2
          (Finset.union_subset wfτ.freeAtoms_subset typed₂.support_subset)
      have hres : ∀ (e : Term), e.locallyClosed →
          (Interp.relevantEnv Δ τ e).domain = τ.freeAtoms ∪ e.support →
          Interp.resultFirst (Interp.relevantEnv Δ τ e) τ e =
            Interp.resultAt ((τ.freeAtoms ∪ e.support).image LogicVar.free) e (.bound 0) := by
        intro e closed hdom
        let Δ' := Interp.relevantEnv Δ τ e
        have hX : Interp.relevantSupport Δ' τ e =
            (τ.freeAtoms ∪ e.support).image LogicVar.free := by
          rw [LogicVar.eq_image_free_of_locallyClosed
            (Interp.relevantSupport_locallyClosed Δ' τ e wfτ.locallyClosedAt closed)]
          rw [Interp.freeAtomSet_relevantSupport, Interp.relevantEnv_idem, hdom]
        change Interp.resultAt ((Interp.relevantSupport Δ' τ e).image (LogicVar.shiftFrom 0))
          (Interp.shiftTerm e) (.bound 0) = _
        have hclosed : LogicVar.LocallyClosed ((τ.freeAtoms ∪ e.support).image LogicVar.free) := by
          intro k hk
          simp at hk
        rw [hX, LogicVar.image_shiftFrom_eq_of_locallyClosed _ 0 hclosed,
          Interp.shiftTerm_eq_of_locallyClosed e closed]
      have hr₁ := hres e₁ typed₁.locallyClosed hΔ₁
      have hr₂ := hres e₂ typed₂.locallyClosed hΔ₂
      have hworldScope := (Interp.models_basicWorld_iff m Δ).1 world |>.1
      have hXY : X ⊆ Y := Finset.union_subset_union (Finset.Subset.refl _) support
      have hY : Y ⊆ m.domain := Finset.Subset.trans
        (Finset.union_subset wfτ.freeAtoms_subset typed₂.support_subset) hworldScope
      have hall (Q : Formula) (hQ : Q.freeAtoms ⊆ τ.freeAtoms)
          (hq : m ⊨ Formula.all (Interp.resultFirst Δ₁ τ e₁ ⇒ᶜ Q)) :
          m ⊨ Formula.all (Interp.resultFirst Δ₂ τ e₂ ⇒ᶜ Q) := by
        rw [hr₁] at hq
        rw [hr₂]
        exact Interp.models_all_resultAt_of_reaches_iff typed₁.locallyClosed typed₂.locallyClosed
          Finset.subset_union_right Finset.subset_union_right hXY
          (Finset.Subset.trans hQ Finset.subset_union_left) hY heval hq
      have hagree : BasicEnv.AgreeOn τ.freeAtoms Δ₁ Δ₂ := by
        intro x hx
        simp only [Δ₁, Δ₂, Interp.relevantEnv, BasicEnv.lookup_restrict,
          Interp.relevantAtoms, if_pos (Finset.mem_union_left _ hx)]
      have hfuel (τ' : ContextType) (e : Term) (d : Nat)
          (hs : τ'.freeAtoms ∪ e.support ⊆ τ.freeAtoms) :
          interpFuel gas d Δ₁ τ' e = interpFuel gas d Δ₂ τ' e :=
        interpFuel_eq_of_agreeOn gas d (hagree.mono hs)
      have hfree (τ' : ContextType) (e : Term) (d : Nat)
          (hs : τ'.freeAtoms ∪ e.support ⊆ τ.freeAtoms) :
          (interpFuel gas d Δ₁ τ' e).freeAtoms ⊆ τ.freeAtoms :=
        Finset.Subset.trans (freeAtoms_interpFuel_subset gas d Δ₁ τ' e) hs
      have hscope (τ' : ContextType) (hs : τ'.freeAtoms ⊆ τ.freeAtoms) :
          (interpFuel gas 0 Δ τ' e₂).freeAtoms ⊆ m.domain :=
        Finset.Subset.trans (freeAtoms_interpFuel_subset gas 0 Δ τ' e₂)
          (Finset.Subset.trans (Finset.union_subset_union hs (Finset.Subset.refl _)) hY)
      have hguard := Interp.models_guard_relevant_of_world wfτ typed₂ world terminates
      have hbody := Formula.models_and_elim_right h
      cases τ with
      | «over» b q =>
          dsimp only at hbody ⊢
          apply Formula.models_and_intro hguard
          exact hall _ (by rw [Interp.freeAtoms_overResultFiber]; exact Finset.Subset.refl _) hbody
      | under b q =>
          dsimp only at hbody ⊢
          apply Formula.models_and_intro hguard
          exact hall _ (by rw [Interp.freeAtoms_underResultFiber]; exact Finset.Subset.refl _) hbody
      | inter τ₁ τ₂ =>
          dsimp only at hbody ⊢
          apply Formula.models_and_intro hguard
          apply Formula.models_and_intro
          · exact ih wfτ.1 typed₁ typed₂ (Formula.models_and_elim_left hbody)
          · have ht₁ : Δ ⊢ₑ e₁ ⋮ τ₂.erase := by simpa only [ContextType.erase, wfτ.2.2] using typed₁
            have ht₂ : Δ ⊢ₑ e₂ ⋮ τ₂.erase := by simpa only [ContextType.erase, wfτ.2.2] using typed₂
            exact ih wfτ.2.1 ht₁ ht₂ (Formula.models_and_elim_right hbody)
      | union τ₁ τ₂ =>
          dsimp only at hbody ⊢
          apply Formula.models_and_intro hguard
          have hs := (Formula.models_or_iff m _ _ (Formula.models_scope hbody)).1 hbody
          rcases hs with hs | hs
          · exact Formula.models_or_intro_left (ih wfτ.1 typed₁ typed₂ hs)
              (hscope τ₂ Finset.subset_union_right)
          · have ht₁ : Δ ⊢ₑ e₁ ⋮ τ₂.erase := by simpa only [ContextType.erase, wfτ.2.2] using typed₁
            have ht₂ : Δ ⊢ₑ e₂ ⋮ τ₂.erase := by simpa only [ContextType.erase, wfτ.2.2] using typed₂
            exact Formula.models_or_intro_right (hscope τ₁ Finset.subset_union_left)
              (ih wfτ.2.1 ht₁ ht₂ hs)
      | sum τ₁ τ₂ =>
          dsimp only at hbody ⊢
          have hs₁ : (τ₁.shiftFrom 0).freeAtoms ∪ (.ret (.bound 0) : Term).support ⊆
              (τ₁ ⊕ τ₂ : ContextType).freeAtoms := by
            simpa only [freeAtoms_shiftFrom, Term.support, Value.support, Finset.union_empty] using
              (Finset.subset_union_left : τ₁.freeAtoms ⊆ τ₁.freeAtoms ∪ τ₂.freeAtoms)
          have hs₂ : (τ₂.shiftFrom 0).freeAtoms ∪ (.ret (.bound 0) : Term).support ⊆
              (τ₁ ⊕ τ₂ : ContextType).freeAtoms := by
            simpa only [freeAtoms_shiftFrom, Term.support, Value.support, Finset.union_empty] using
              (Finset.subset_union_right : τ₂.freeAtoms ⊆ τ₁.freeAtoms ∪ τ₂.freeAtoms)
          apply Formula.models_and_intro hguard
          dsimp only
          rw [← hfuel _ _ 1 hs₁, ← hfuel _ _ 1 hs₂]
          apply hall _ _ hbody
          simp only [Formula.freeAtoms_sum]
          exact Finset.union_subset (hfree _ _ 1 hs₁) (hfree _ _ 1 hs₂)
      | arrow τ₁ τ₂ =>
          dsimp only at hbody ⊢
          have hs₁ : ((τ₁.shiftFrom 0).shiftFrom 0).freeAtoms ∪
              (.ret (.bound 0) : Term).support ⊆ (ContextType.arrow τ₁ τ₂).freeAtoms := by
            simpa only [freeAtoms_shiftFrom, Term.support, Value.support, Finset.union_empty] using
              (Finset.subset_union_left : τ₁.freeAtoms ⊆ τ₁.freeAtoms ∪ τ₂.freeAtoms)
          have hs₂ : (τ₂.shiftFrom 1).freeAtoms ∪
              (.app (.bound 1) (.bound 0) : Term).support ⊆ (ContextType.arrow τ₁ τ₂).freeAtoms := by
            simpa only [freeAtoms_shiftFrom, Term.support, Value.support, Finset.union_empty] using
              (Finset.subset_union_right : τ₂.freeAtoms ⊆ τ₁.freeAtoms ∪ τ₂.freeAtoms)
          apply Formula.models_and_intro hguard
          dsimp only
          rw [← hfuel _ _ 2 hs₁, ← hfuel _ _ 2 hs₂]
          apply hall _ _ hbody
          simp only [Formula.freeAtoms_all, Formula.freeAtoms_impl]
          exact Finset.union_subset (hfree _ _ 2 hs₁) (hfree _ _ 2 hs₂)
      | wand τ₁ τ₂ =>
          dsimp only at hbody ⊢
          have hs₁ : ((τ₁.shiftFrom 0).shiftFrom 0).freeAtoms ∪
              (.ret (.bound 0) : Term).support ⊆ (ContextType.wand τ₁ τ₂).freeAtoms := by
            simpa only [freeAtoms_shiftFrom, Term.support, Value.support, Finset.union_empty] using
              (Finset.subset_union_left : τ₁.freeAtoms ⊆ τ₁.freeAtoms ∪ τ₂.freeAtoms)
          have hs₂ : (τ₂.shiftFrom 1).freeAtoms ∪
              (.app (.bound 1) (.bound 0) : Term).support ⊆ (ContextType.wand τ₁ τ₂).freeAtoms := by
            simpa only [freeAtoms_shiftFrom, Term.support, Value.support, Finset.union_empty] using
              (Finset.subset_union_right : τ₂.freeAtoms ⊆ τ₁.freeAtoms ∪ τ₂.freeAtoms)
          apply Formula.models_and_intro hguard
          dsimp only
          rw [← hfuel _ _ 2 hs₁, ← hfuel _ _ 2 hs₂]
          apply hall _ _ hbody
          simp only [Formula.freeAtoms_wand]
          exact Finset.union_subset (hfree _ _ 2 hs₁) (hfree _ _ 2 hs₂)
      | persist τ =>
          dsimp only at hbody ⊢
          have hs : (τ.shiftFrom 0).freeAtoms ∪ (.ret (.bound 0) : Term).support ⊆
              (ContextType.persist τ).freeAtoms := by
            simpa only [freeAtoms_shiftFrom, Term.support, Value.support, Finset.union_empty] using
              (Finset.Subset.refl τ.freeAtoms)
          apply Formula.models_and_intro hguard
          dsimp only
          rw [← hfuel _ _ 1 hs]
          apply hall _ _ hbody
          simp only [Formula.freeAtoms_persist]
          exact hfree _ _ 1 hs

/-- Pointwise result equivalence transports a well-formed context-type
interpretation when the target's totality obligation is established. -/
theorem models_interp_of_reaches_iff
    {m : Capability} {Δ : BasicEnv} {τ : ContextType} {e₁ e₂ : Term}
    (wfτ : τ.WellFormed Δ.domain)
    (typed₁ : Δ ⊢ₑ e₁ ⋮ τ.erase) (typed₂ : Δ ⊢ₑ e₂ ⋮ τ.erase)
    (world : m ⊨ Interp.basicWorld Δ) (terminates : m ⊨ Interp.total e₂)
    (support : e₁.support ⊆ e₂.support)
    (heval : ∀ σ, σ ∈ m → ∀ v,
      (Interp.instantiateTerm e₁ σ.toAssignment).reaches v ↔
        (Interp.instantiateTerm e₂ σ.toAssignment).reaches v)
    (h : m ⊨ interp Δ τ e₁) : m ⊨ interp Δ τ e₂ :=
  models_interpFuel_of_reaches_iff wfτ typed₁ typed₂ world terminates support heval h

/-- Name every result of a nondeterministic term beneath a fresh binder,
preserving the whole context-type interpretation. -/
theorem models_interpFuel_result_alias
    {m : Capability} {Δ : BasicEnv} {τ : ContextType}
    {gas d : Nat} {e : Term} {y : Atom} {X : Finset LogicVar}
    (closedX : LogicVar.LocallyClosed X) (closedE : e.locallyClosed)
    (supportX : e.logicSupport ⊆ X)
    (freshX : LogicVar.free y ∉ X) (freshΔ : y ∉ Δ.domain)
    (wfτ : τ.WellFormed Δ.domain) (supportE : e.support ⊆ Δ.domain)
    (typeSupport : τ.freeAtoms.image LogicVar.free ⊆ X)
    (hres : m ⊨ Interp.resultAt X e (.free y))
    (hsource : m ⊨ interpFuel gas d Δ τ e) :
    m ⊨ (interpFuel gas (d + 1) Δ (τ.shiftFrom 0)
      (.ret (.bound 0))).openAt 0 y := by
  induction gas generalizing d Δ τ with
  | zero =>
      simp only [interpFuel, Formula.openAt]
      apply Formula.models_and_intro
      · exact Interp.models_guard_relevant_shift_openAt_result_alias (e := e) closedX closedE
          supportX freshX freshΔ hres (models_interpFuel_guard hsource)
      · exact Formula.models_top _
  | succ gas ih =>
      have hguard := models_interpFuel_guard hsource
      have hbody := Formula.models_and_elim_right hsource
      have hclosed := wfτ.locallyClosedAt
      have hshift := τ.shiftFrom_eq_of_locallyClosedAt 0 hclosed
      let Δe := Interp.relevantEnv Δ τ e
      let Δτ := Interp.relevantEnv Δ τ (.ret (.bound 0))
      have hΔτ : y ∉ Δτ.domain := by
        rw [Interp.relevantEnv_domain]
        exact fun hy => freshΔ (Finset.mem_inter.1 hy).1
      have hall : ∀ Q : Formula, Q.freeAtoms ⊆ τ.freeAtoms →
          m ⊨ Formula.all
            (Interp.resultFirst Δe τ e ⇒ᶜ Q) →
          m ⊨ Formula.all
            ((Interp.resultFirst Δτ τ (.ret (.bound 0))).openAt 1 y ⇒ᶜ Q) := by
        intro Q hQ h
        exact Interp.models_resultFirst_result_alias wfτ closedE supportE
          closedX supportX typeSupport freshX freshΔ hQ hres h
      have hfuel : ∀ (υ : ContextType) (e : Term) (k n n' : Nat),
          υ.LocallyClosedAt k → e.locallyClosedAt k → e.support = ∅ →
          υ.freeAtoms ⊆ τ.freeAtoms → k ≤ n → k ≤ n' →
          (interpFuel gas n' Δτ υ e).openAt k y = interpFuel gas n Δe υ e := by
        intro υ e k n n' hυ he hefree hυτ hkn hkn'
        have hfree : y ∉ υ.freeAtoms := fun hy => freshΔ (wfτ.freeAtoms_subset (hυτ hy))
        rw [interpFuel_openAt_fresh gas n' Δτ υ e k y hυ he hΔτ hfree
          (by rw [hefree]; exact Finset.notMem_empty _),
          interpFuel_eq_of_locallyClosedAt gas Δτ υ e k n' n hυ hkn' hkn]
        apply interpFuel_eq_of_agreeOn
        intro x hx
        have hxυ : x ∈ υ.freeAtoms := by simpa [hefree] using hx
        have hxτ := hυτ hxυ
        simp [Δτ, Δe, Interp.relevantEnv, Interp.relevantAtoms,
          BasicEnv.lookup_restrict, hxτ, Term.support, Value.support]
      have hscopeInner : ∀ (υ : ContextType) (e : Term) (n : Nat),
          e.support = ∅ → υ.freeAtoms ⊆ τ.freeAtoms →
          (interpFuel gas n Δe υ e).freeAtoms ⊆ τ.freeAtoms := by
        intro υ e n he hυ
        have hs := freeAtoms_interpFuel_subset gas n Δe υ e
        rw [he, Finset.union_empty] at hs
        exact Finset.Subset.trans hs hυ
      have hTypeSupport (υ : ContextType) (hυ : υ.freeAtoms ⊆ τ.freeAtoms) :
          υ.freeAtoms.image LogicVar.free ⊆ X :=
        Finset.Subset.trans (Finset.image_subset_image hυ) typeSupport
      have htargetGuard : m ⊨
          (Interp.guard (d + 1) Δτ τ (.ret (.bound 0))).openAt 0 y := by
        simpa only [hshift] using
          Interp.models_guard_relevant_shift_openAt_result_alias (e := e) closedX closedE
            supportX freshX freshΔ hres hguard
      have hτScope : τ.freeAtoms ⊆ m.domain := by
        have hwf := (Interp.models_wellFormed_iff m d Δe τ).1
          (Formula.models_and_elim_left hguard)
        exact Finset.Subset.trans hwf.2.freeAtoms_subset hwf.1
      have hyScope : y ∈ m.domain := by
        apply Formula.models_scope hres
        rw [Interp.freeAtoms_resultAt]
        simp [LogicVar.freeAtoms]
      have scopeOpened : ∀ υ : ContextType, υ.freeAtoms ⊆ τ.freeAtoms →
          ((interpFuel gas (d + 1) Δ υ (.ret (.bound 0))).openAt 0 y).freeAtoms ⊆ m.domain := by
        intro υ hυ x hx
        rcases Finset.mem_union.1
          (Formula.freeAtoms_openAt_subset _ 0 y hx) with hx | hx
        · have hxy := Finset.mem_singleton.1 hx
          subst x
          exact hyScope
        · apply hτScope
          apply hυ
          have hs := freeAtoms_interpFuel_subset gas (d + 1) Δ υ (.ret (.bound 0)) hx
          simpa [Term.support, Value.support] using hs
      rw [hshift]
      cases τ with
      | inter τ₁ τ₂ =>
          have hshift₁ := τ₁.shiftFrom_eq_of_locallyClosedAt 0 wfτ.1.locallyClosedAt
          have hshift₂ := τ₂.shiftFrom_eq_of_locallyClosedAt 0 wfτ.2.1.locallyClosedAt
          simp only [interpFuel, Formula.openAt]
          apply Formula.models_and_intro htargetGuard
          apply Formula.models_and_intro
          · simpa only [hshift₁] using ih freshΔ wfτ.1 supportE (hTypeSupport τ₁ Finset.subset_union_left)
              (Formula.models_and_elim_left hbody)
          · simpa only [hshift₂] using ih freshΔ wfτ.2.1 supportE (hTypeSupport τ₂ Finset.subset_union_right)
              (Formula.models_and_elim_right hbody)
      | union τ₁ τ₂ =>
          have hshift₁ := τ₁.shiftFrom_eq_of_locallyClosedAt 0 wfτ.1.locallyClosedAt
          have hshift₂ := τ₂.shiftFrom_eq_of_locallyClosedAt 0 wfτ.2.1.locallyClosedAt
          simp only [interpFuel, Formula.openAt]
          apply Formula.models_and_intro htargetGuard
          rcases (Formula.models_or_iff _ _ _ (Formula.models_scope hbody)).1 hbody with h₁ | h₂
          · apply Formula.models_or_intro_left
            · simpa only [hshift₁] using ih freshΔ wfτ.1 supportE (hTypeSupport τ₁ Finset.subset_union_left) h₁
            · exact scopeOpened τ₂ Finset.subset_union_right
          · apply Formula.models_or_intro_right
            · exact scopeOpened τ₁ Finset.subset_union_left
            · simpa only [hshift₂] using ih freshΔ wfτ.2.1 supportE (hTypeSupport τ₂ Finset.subset_union_right) h₂
      | «over» b q =>
          have hQ := Interp.overResultFiber_openAt_fresh b q 0 y hclosed
            (fun hy => freshΔ (wfτ.freeAtoms_subset hy))
          simp only [Formula.openAt] at hQ
          simp only [interpFuel, Formula.openAt]
          apply Formula.models_and_intro htargetGuard
          rw [hQ]
          exact hall _ (by rw [Interp.freeAtoms_overResultFiber]; exact Finset.Subset.refl _) hbody
      | under b q =>
          have hQ := Interp.underResultFiber_openAt_fresh b q 0 y hclosed
            (fun hy => freshΔ (wfτ.freeAtoms_subset hy))
          simp only [Formula.openAt] at hQ
          simp only [interpFuel, Formula.openAt]
          apply Formula.models_and_intro htargetGuard
          rw [hQ]
          exact hall _ (by rw [Interp.freeAtoms_underResultFiber]; exact Finset.Subset.refl _) hbody
      | sum τ₁ τ₂ =>
          have hs₁ : (τ₁.shiftFrom 0).freeAtoms ⊆ (τ₁.sum τ₂).freeAtoms := by
            simpa only [freeAtoms_shiftFrom] using
              (Finset.subset_union_left : τ₁.freeAtoms ⊆ τ₁.freeAtoms ∪ τ₂.freeAtoms)
          have hs₂ : (τ₂.shiftFrom 0).freeAtoms ⊆ (τ₁.sum τ₂).freeAtoms := by
            simpa only [freeAtoms_shiftFrom] using
              (Finset.subset_union_right : τ₂.freeAtoms ⊆ τ₁.freeAtoms ∪ τ₂.freeAtoms)
          have h₁ := hfuel (τ₁.shiftFrom 0) (.ret (.bound 0)) 1 (d + 1) (d + 1 + 1)
            (wfτ.1.locallyClosedAt.shiftFrom 0)
            (by simp [Term.locallyClosedAt, Value.locallyClosedAt]) rfl hs₁ (by omega) (by omega)
          have h₂ := hfuel (τ₂.shiftFrom 0) (.ret (.bound 0)) 1 (d + 1) (d + 1 + 1)
            (wfτ.2.1.locallyClosedAt.shiftFrom 0)
            (by simp [Term.locallyClosedAt, Value.locallyClosedAt]) rfl hs₂ (by omega) (by omega)
          simp only [interpFuel, Formula.openAt]
          apply Formula.models_and_intro htargetGuard
          rw [h₁, h₂]
          apply hall _ ?_ hbody
          simp only [Formula.freeAtoms_sum]
          exact Finset.union_subset (hscopeInner _ _ _ rfl hs₁) (hscopeInner _ _ _ rfl hs₂)
      | arrow τ₁ τ₂ =>
          have hs₁ : ((τ₁.shiftFrom 0).shiftFrom 0).freeAtoms ⊆ (τ₁.arrow τ₂).freeAtoms := by
            simpa only [freeAtoms_shiftFrom] using
              (Finset.subset_union_left : τ₁.freeAtoms ⊆ τ₁.freeAtoms ∪ τ₂.freeAtoms)
          have hs₂ : (τ₂.shiftFrom 1).freeAtoms ⊆ (τ₁.arrow τ₂).freeAtoms := by
            simpa only [freeAtoms_shiftFrom] using
              (Finset.subset_union_right : τ₂.freeAtoms ⊆ τ₁.freeAtoms ∪ τ₂.freeAtoms)
          have h₁ := hfuel ((τ₁.shiftFrom 0).shiftFrom 0) (.ret (.bound 0)) 2 (d + 2) (d + 1 + 2)
            ((wfτ.1.locallyClosedAt.shiftFrom 0).shiftFrom 0)
            (by simp [Term.locallyClosedAt, Value.locallyClosedAt]) rfl hs₁ (by omega) (by omega)
          have h₂ := hfuel (τ₂.shiftFrom 1) (.app (.bound 1) (.bound 0)) 2 (d + 2) (d + 1 + 2)
            (wfτ.2.locallyClosedAt.shiftFrom 1)
            (by simp [Term.locallyClosedAt, Value.locallyClosedAt]) rfl hs₂ (by omega) (by omega)
          simp only [interpFuel, Formula.openAt]
          apply Formula.models_and_intro htargetGuard
          rw [h₁, h₂]
          apply hall _ ?_ hbody
          simp only [Formula.freeAtoms_all, Formula.freeAtoms_impl]
          exact Finset.union_subset (hscopeInner _ _ _ rfl hs₁) (hscopeInner _ _ _ rfl hs₂)
      | wand τ₁ τ₂ =>
          have hs₁ : ((τ₁.shiftFrom 0).shiftFrom 0).freeAtoms ⊆ (τ₁.wand τ₂).freeAtoms := by
            simpa only [freeAtoms_shiftFrom] using
              (Finset.subset_union_left : τ₁.freeAtoms ⊆ τ₁.freeAtoms ∪ τ₂.freeAtoms)
          have hs₂ : (τ₂.shiftFrom 1).freeAtoms ⊆ (τ₁.wand τ₂).freeAtoms := by
            simpa only [freeAtoms_shiftFrom] using
              (Finset.subset_union_right : τ₂.freeAtoms ⊆ τ₁.freeAtoms ∪ τ₂.freeAtoms)
          have h₁ := hfuel ((τ₁.shiftFrom 0).shiftFrom 0) (.ret (.bound 0)) 2 (d + 2) (d + 1 + 2)
            ((wfτ.1.locallyClosedAt.shiftFrom 0).shiftFrom 0)
            (by simp [Term.locallyClosedAt, Value.locallyClosedAt]) rfl hs₁ (by omega) (by omega)
          have h₂ := hfuel (τ₂.shiftFrom 1) (.app (.bound 1) (.bound 0)) 2 (d + 2) (d + 1 + 2)
            (wfτ.2.locallyClosedAt.shiftFrom 1)
            (by simp [Term.locallyClosedAt, Value.locallyClosedAt]) rfl hs₂ (by omega) (by omega)
          simp only [interpFuel, Formula.openAt]
          apply Formula.models_and_intro htargetGuard
          rw [h₁, h₂]
          apply hall _ ?_ hbody
          simp only [Formula.freeAtoms_wand]
          exact Finset.union_subset (hscopeInner _ _ _ rfl hs₁) (hscopeInner _ _ _ rfl hs₂)
      | persist τ =>
          have hs : (τ.shiftFrom 0).freeAtoms ⊆ (ContextType.persist τ).freeAtoms := by
            rw [freeAtoms_shiftFrom]
            exact Finset.Subset.refl _
          have h := hfuel (τ.shiftFrom 0) (.ret (.bound 0)) 1 (d + 1) (d + 1 + 1)
            (wfτ.locallyClosedAt.shiftFrom 0)
            (by simp [Term.locallyClosedAt, Value.locallyClosedAt]) rfl hs (by omega) (by omega)
          simp only [interpFuel, Formula.openAt]
          apply Formula.models_and_intro htargetGuard
          rw [h]
          apply hall _ ?_ hbody
          simp only [Formula.freeAtoms_persist]
          exact hscopeInner _ _ _ rfl hs

/-- Name a returned value beneath a fresh result binder without changing its
type interpretation on a singleton capability. -/
theorem models_interpFuel_ret_alias_singleton
    {m : Capability} {ρ : Store} {Δ : BasicEnv} {τ : ContextType}
    {gas d : Nat} {v : Value} {y : Atom} {X : Finset LogicVar}
    (closedX : LogicVar.LocallyClosed X) (closedV : v.locallyClosed)
    (supportX : (.ret v : Term).logicSupport ⊆ X)
    (freshX : LogicVar.free y ∉ X) (freshΔ : y ∉ Δ.domain)
    (wfτ : τ.WellFormed Δ.domain) (supportV : v.support ⊆ Δ.domain)
    (single : m = Capability.singleton ρ)
    (hres : m ⊨ Interp.resultAt X (.ret v) (.free y))
    (hsource : m ⊨ interpFuel gas d Δ τ (.ret v)) :
    m ⊨ (interpFuel gas (d + 1) Δ (τ.shiftFrom 0)
      (.ret (.bound 0))).openAt 0 y := by
  subst m
  induction gas generalizing d Δ τ with
  | zero =>
      simp only [interpFuel, Formula.openAt]
      apply Formula.models_and_intro
      · exact Interp.models_guard_relevant_shift_openAt_result_alias (e := .ret v) closedX closedV
          supportX freshX freshΔ hres (models_interpFuel_guard hsource)
      · exact Formula.models_top _
  | succ gas ih =>
      have hguard := models_interpFuel_guard hsource
      have hbody := Formula.models_and_elim_right hsource
      have hclosed := wfτ.locallyClosedAt
      have hshift := τ.shiftFrom_eq_of_locallyClosedAt 0 hclosed
      let Δe := Interp.relevantEnv Δ τ (.ret v)
      let Δτ := Interp.relevantEnv Δ τ (.ret (.bound 0))
      have hΔτ : y ∉ Δτ.domain := by
        rw [Interp.relevantEnv_domain]
        exact fun hy => freshΔ (Finset.mem_inter.1 hy).1
      have hall : ∀ Q : Formula, Q.freeAtoms ⊆ τ.freeAtoms →
          Capability.singleton ρ ⊨ Formula.all
            (Interp.resultFirst Δe τ (.ret v) ⇒ᶜ Q) →
          Capability.singleton ρ ⊨ Formula.all
            ((Interp.resultFirst Δτ τ (.ret (.bound 0))).openAt 1 y ⇒ᶜ Q) := by
        intro Q hQ h
        exact Interp.models_resultFirst_ret_alias_singleton wfτ closedV supportV
          closedX supportX freshX freshΔ hQ hres h
      have hfuel : ∀ (υ : ContextType) (e : Term) (k n n' : Nat),
          υ.LocallyClosedAt k → e.locallyClosedAt k → e.support = ∅ →
          υ.freeAtoms ⊆ τ.freeAtoms → k ≤ n → k ≤ n' →
          (interpFuel gas n' Δτ υ e).openAt k y = interpFuel gas n Δe υ e := by
        intro υ e k n n' hυ he hefree hυτ hkn hkn'
        have hfree : y ∉ υ.freeAtoms := fun hy => freshΔ (wfτ.freeAtoms_subset (hυτ hy))
        rw [interpFuel_openAt_fresh gas n' Δτ υ e k y hυ he hΔτ hfree
          (by rw [hefree]; exact Finset.notMem_empty _),
          interpFuel_eq_of_locallyClosedAt gas Δτ υ e k n' n hυ hkn' hkn]
        apply interpFuel_eq_of_agreeOn
        intro x hx
        have hxυ : x ∈ υ.freeAtoms := by simpa [hefree] using hx
        have hxτ := hυτ hxυ
        simp [Δτ, Δe, Interp.relevantEnv, Interp.relevantAtoms,
          BasicEnv.lookup_restrict, hxτ, Term.support, Value.support]
      have hscopeInner : ∀ (υ : ContextType) (e : Term) (n : Nat),
          e.support = ∅ → υ.freeAtoms ⊆ τ.freeAtoms →
          (interpFuel gas n Δe υ e).freeAtoms ⊆ τ.freeAtoms := by
        intro υ e n he hυ
        have hs := freeAtoms_interpFuel_subset gas n Δe υ e
        rw [he, Finset.union_empty] at hs
        exact Finset.Subset.trans hs hυ
      have htargetGuard : Capability.singleton ρ ⊨
          (Interp.guard (d + 1) Δτ τ (.ret (.bound 0))).openAt 0 y := by
        simpa only [hshift] using
          Interp.models_guard_relevant_shift_openAt_result_alias (e := .ret v) closedX closedV
            supportX freshX freshΔ hres hguard
      have hτScope : τ.freeAtoms ⊆ ρ.domain := by
        have hwf := (Interp.models_wellFormed_iff (Capability.singleton ρ) d Δe τ).1
          (Formula.models_and_elim_left hguard)
        exact Finset.Subset.trans hwf.2.freeAtoms_subset hwf.1
      have hyScope : y ∈ ρ.domain := by
        apply Formula.models_scope hres
        rw [Interp.freeAtoms_resultAt]
        simp [LogicVar.freeAtoms]
      have scopeOpened : ∀ υ : ContextType, υ.freeAtoms ⊆ τ.freeAtoms →
          ((interpFuel gas (d + 1) Δ υ (.ret (.bound 0))).openAt 0 y).freeAtoms ⊆ ρ.domain := by
        intro υ hυ x hx
        rcases Finset.mem_union.1
          (Formula.freeAtoms_openAt_subset _ 0 y hx) with hx | hx
        · have hxy := Finset.mem_singleton.1 hx
          subst x
          exact hyScope
        · apply hτScope
          apply hυ
          have hs := freeAtoms_interpFuel_subset gas (d + 1) Δ υ (.ret (.bound 0)) hx
          simpa [Term.support, Value.support] using hs
      rw [hshift]
      cases τ with
      | inter τ₁ τ₂ =>
          have hshift₁ := τ₁.shiftFrom_eq_of_locallyClosedAt 0 wfτ.1.locallyClosedAt
          have hshift₂ := τ₂.shiftFrom_eq_of_locallyClosedAt 0 wfτ.2.1.locallyClosedAt
          simp only [interpFuel, Formula.openAt]
          apply Formula.models_and_intro htargetGuard
          apply Formula.models_and_intro
          · simpa only [hshift₁] using ih freshΔ wfτ.1 supportV
              (Formula.models_and_elim_left hbody)
          · simpa only [hshift₂] using ih freshΔ wfτ.2.1 supportV
              (Formula.models_and_elim_right hbody)
      | union τ₁ τ₂ =>
          have hshift₁ := τ₁.shiftFrom_eq_of_locallyClosedAt 0 wfτ.1.locallyClosedAt
          have hshift₂ := τ₂.shiftFrom_eq_of_locallyClosedAt 0 wfτ.2.1.locallyClosedAt
          simp only [interpFuel, Formula.openAt]
          apply Formula.models_and_intro htargetGuard
          rcases (Formula.models_or_iff _ _ _ (Formula.models_scope hbody)).1 hbody with h₁ | h₂
          · apply Formula.models_or_intro_left
            · simpa only [hshift₁] using ih freshΔ wfτ.1 supportV h₁
            · exact scopeOpened τ₂ Finset.subset_union_right
          · apply Formula.models_or_intro_right
            · exact scopeOpened τ₁ Finset.subset_union_left
            · simpa only [hshift₂] using ih freshΔ wfτ.2.1 supportV h₂
      | «over» b q =>
          have hQ := Interp.overResultFiber_openAt_fresh b q 0 y hclosed
            (fun hy => freshΔ (wfτ.freeAtoms_subset hy))
          simp only [Formula.openAt] at hQ
          simp only [interpFuel, Formula.openAt]
          apply Formula.models_and_intro htargetGuard
          rw [hQ]
          exact hall _ (by rw [Interp.freeAtoms_overResultFiber]; exact Finset.Subset.refl _) hbody
      | under b q =>
          have hQ := Interp.underResultFiber_openAt_fresh b q 0 y hclosed
            (fun hy => freshΔ (wfτ.freeAtoms_subset hy))
          simp only [Formula.openAt] at hQ
          simp only [interpFuel, Formula.openAt]
          apply Formula.models_and_intro htargetGuard
          rw [hQ]
          exact hall _ (by rw [Interp.freeAtoms_underResultFiber]; exact Finset.Subset.refl _) hbody
      | sum τ₁ τ₂ =>
          have hs₁ : (τ₁.shiftFrom 0).freeAtoms ⊆ (τ₁.sum τ₂).freeAtoms := by
            simpa only [freeAtoms_shiftFrom] using
              (Finset.subset_union_left : τ₁.freeAtoms ⊆ τ₁.freeAtoms ∪ τ₂.freeAtoms)
          have hs₂ : (τ₂.shiftFrom 0).freeAtoms ⊆ (τ₁.sum τ₂).freeAtoms := by
            simpa only [freeAtoms_shiftFrom] using
              (Finset.subset_union_right : τ₂.freeAtoms ⊆ τ₁.freeAtoms ∪ τ₂.freeAtoms)
          have h₁ := hfuel (τ₁.shiftFrom 0) (.ret (.bound 0)) 1 (d + 1) (d + 1 + 1)
            (wfτ.1.locallyClosedAt.shiftFrom 0)
            (by simp [Term.locallyClosedAt, Value.locallyClosedAt]) rfl hs₁ (by omega) (by omega)
          have h₂ := hfuel (τ₂.shiftFrom 0) (.ret (.bound 0)) 1 (d + 1) (d + 1 + 1)
            (wfτ.2.1.locallyClosedAt.shiftFrom 0)
            (by simp [Term.locallyClosedAt, Value.locallyClosedAt]) rfl hs₂ (by omega) (by omega)
          simp only [interpFuel, Formula.openAt]
          apply Formula.models_and_intro htargetGuard
          rw [h₁, h₂]
          apply hall _ ?_ hbody
          simp only [Formula.freeAtoms_sum]
          exact Finset.union_subset (hscopeInner _ _ _ rfl hs₁) (hscopeInner _ _ _ rfl hs₂)
      | arrow τ₁ τ₂ =>
          have hs₁ : ((τ₁.shiftFrom 0).shiftFrom 0).freeAtoms ⊆ (τ₁.arrow τ₂).freeAtoms := by
            simpa only [freeAtoms_shiftFrom] using
              (Finset.subset_union_left : τ₁.freeAtoms ⊆ τ₁.freeAtoms ∪ τ₂.freeAtoms)
          have hs₂ : (τ₂.shiftFrom 1).freeAtoms ⊆ (τ₁.arrow τ₂).freeAtoms := by
            simpa only [freeAtoms_shiftFrom] using
              (Finset.subset_union_right : τ₂.freeAtoms ⊆ τ₁.freeAtoms ∪ τ₂.freeAtoms)
          have h₁ := hfuel ((τ₁.shiftFrom 0).shiftFrom 0) (.ret (.bound 0)) 2 (d + 2) (d + 1 + 2)
            ((wfτ.1.locallyClosedAt.shiftFrom 0).shiftFrom 0)
            (by simp [Term.locallyClosedAt, Value.locallyClosedAt]) rfl hs₁ (by omega) (by omega)
          have h₂ := hfuel (τ₂.shiftFrom 1) (.app (.bound 1) (.bound 0)) 2 (d + 2) (d + 1 + 2)
            (wfτ.2.locallyClosedAt.shiftFrom 1)
            (by simp [Term.locallyClosedAt, Value.locallyClosedAt]) rfl hs₂ (by omega) (by omega)
          simp only [interpFuel, Formula.openAt]
          apply Formula.models_and_intro htargetGuard
          rw [h₁, h₂]
          apply hall _ ?_ hbody
          simp only [Formula.freeAtoms_all, Formula.freeAtoms_impl]
          exact Finset.union_subset (hscopeInner _ _ _ rfl hs₁) (hscopeInner _ _ _ rfl hs₂)
      | wand τ₁ τ₂ =>
          have hs₁ : ((τ₁.shiftFrom 0).shiftFrom 0).freeAtoms ⊆ (τ₁.wand τ₂).freeAtoms := by
            simpa only [freeAtoms_shiftFrom] using
              (Finset.subset_union_left : τ₁.freeAtoms ⊆ τ₁.freeAtoms ∪ τ₂.freeAtoms)
          have hs₂ : (τ₂.shiftFrom 1).freeAtoms ⊆ (τ₁.wand τ₂).freeAtoms := by
            simpa only [freeAtoms_shiftFrom] using
              (Finset.subset_union_right : τ₂.freeAtoms ⊆ τ₁.freeAtoms ∪ τ₂.freeAtoms)
          have h₁ := hfuel ((τ₁.shiftFrom 0).shiftFrom 0) (.ret (.bound 0)) 2 (d + 2) (d + 1 + 2)
            ((wfτ.1.locallyClosedAt.shiftFrom 0).shiftFrom 0)
            (by simp [Term.locallyClosedAt, Value.locallyClosedAt]) rfl hs₁ (by omega) (by omega)
          have h₂ := hfuel (τ₂.shiftFrom 1) (.app (.bound 1) (.bound 0)) 2 (d + 2) (d + 1 + 2)
            (wfτ.2.locallyClosedAt.shiftFrom 1)
            (by simp [Term.locallyClosedAt, Value.locallyClosedAt]) rfl hs₂ (by omega) (by omega)
          simp only [interpFuel, Formula.openAt]
          apply Formula.models_and_intro htargetGuard
          rw [h₁, h₂]
          apply hall _ ?_ hbody
          simp only [Formula.freeAtoms_wand]
          exact Finset.union_subset (hscopeInner _ _ _ rfl hs₁) (hscopeInner _ _ _ rfl hs₂)
      | persist τ =>
          have hs : (τ.shiftFrom 0).freeAtoms ⊆ (ContextType.persist τ).freeAtoms := by
            rw [freeAtoms_shiftFrom]
            exact Finset.Subset.refl _
          have h := hfuel (τ.shiftFrom 0) (.ret (.bound 0)) 1 (d + 1) (d + 1 + 1)
            (wfτ.locallyClosedAt.shiftFrom 0)
            (by simp [Term.locallyClosedAt, Value.locallyClosedAt]) rfl hs (by omega) (by omega)
          simp only [interpFuel, Formula.openAt]
          apply Formula.models_and_intro htargetGuard
          rw [h]
          apply hall _ ?_ hbody
          simp only [Formula.freeAtoms_persist]
          exact hscopeInner _ _ _ rfl hs

/-- Additive input splitting and branch interpretations establish the
result-first sum type, retaining the complete result graph in each branch. -/
theorem models_interp_sum_intro {m m₁ m₂ : Capability} {Δ : BasicEnv}
    {τ₁ τ₂ : ContextType} {e : Term}
    (defined : Capability.SumDefined m₁ m₂) (same : Capability.sum m₁ m₂ defined = m)
    (wfτ : (τ₁.sum τ₂).WellFormed Δ.domain)
    (typed : Δ ⊢ₑ e ⋮ (τ₁.sum τ₂).erase)
    (world : m ⊨ Interp.basicWorld Δ)
    (h₁ : m₁ ⊨ interp Δ τ₁ e) (h₂ : m₂ ⊨ interp Δ τ₂ e) :
    m ⊨ interp Δ (τ₁.sum τ₂) e := by
  let τ := τ₁.sum τ₂
  let A := τ.freeAtoms ∪ e.support
  let Δ' := Interp.relevantEnv Δ τ e
  let gas := max τ₁.measure τ₂.measure
  let Q := interpFuel gas 1 Δ' (τ₁.shiftFrom 0) (.ret (.bound 0)) ⊕
    interpFuel gas 1 Δ' (τ₂.shiftFrom 0) (.ret (.bound 0))
  let P := Interp.resultAt (A.image LogicVar.free) e (.bound 0) ⇒ᶜ Q
  have hAΔ : A ⊆ Δ.domain := Finset.union_subset wfτ.freeAtoms_subset typed.support_subset
  have scope : A ⊆ m.domain := Finset.Subset.trans hAΔ
    ((Interp.models_basicWorld_iff m Δ).1 world).1
  have domain₁ : m₁.domain = m.domain := by
    rw [← same]
    rfl
  have domain₂ : m₂.domain = m.domain := by
    rw [← same]
    exact defined.symm
  have scope₁ : A ⊆ m₁.domain := by rwa [domain₁]
  have scope₂ : A ⊆ m₂.domain := by rwa [domain₂]
  have support₁ : τ₁.freeAtoms ∪ e.support ⊆ A :=
    Finset.union_subset
      (Finset.Subset.trans Finset.subset_union_left Finset.subset_union_left)
      Finset.subset_union_right
  have support₂ : τ₂.freeAtoms ∪ e.support ⊆ A :=
    Finset.union_subset
      (Finset.Subset.trans Finset.subset_union_right Finset.subset_union_left)
      Finset.subset_union_right
  have supportE : e.support ⊆ A := Finset.subset_union_right
  have closedA : LogicVar.LocallyClosed (A.image LogicVar.free) := by
    intro j hj
    simp at hj
  have logicA : e.logicSupport ⊆ A.image LogicVar.free := by
    rw [LogicVar.eq_image_free_of_locallyClosed
      (Interp.termLogicSupport_locallyClosed e typed.locallyClosed),
      Interp.freeAtomSet_term_logicSupport]
    exact Finset.image_subset_image Finset.subset_union_right
  have hQfree : Q.freeAtoms ⊆ τ.freeAtoms := by
    simp only [Q, Formula.freeAtoms_sum]
    apply Finset.union_subset
    · have hs := freeAtoms_interpFuel_subset gas 1 Δ' (τ₁.shiftFrom 0) (.ret (.bound 0))
      simp only [freeAtoms_shiftFrom, Term.support, Value.support, Finset.union_empty] at hs
      exact Finset.Subset.trans hs Finset.subset_union_left
    · have hs := freeAtoms_interpFuel_subset gas 1 Δ' (τ₂.shiftFrom 0) (.ret (.bound 0))
      simp only [freeAtoms_shiftFrom, Term.support, Value.support, Finset.union_empty] at hs
      exact Finset.Subset.trans hs Finset.subset_union_right
  have hPfree : P.freeAtoms = A := by
    simp only [P, Formula.freeAtoms_impl, Interp.freeAtoms_resultAt,
      Formula.LogicVar.freeAtomSet_image_free, LogicVar.freeAtoms, Finset.union_empty]
    rw [Finset.union_eq_left.2 Finset.subset_union_right,
      Finset.union_eq_left.2 (Finset.Subset.trans hQfree Finset.subset_union_left)]
  have resultFirst : Interp.resultFirst Δ' τ e =
      Interp.resultAt (A.image LogicVar.free) e (.bound 0) := by
    have henv : Δ'.domain = A := by
      rw [Interp.relevantEnv_domain]
      change Δ.domain ∩ A = A
      exact Finset.inter_eq_right.2 hAΔ
    have hclosed := Interp.relevantSupport_locallyClosed Δ' τ e
      wfτ.locallyClosedAt typed.locallyClosed
    have hsupport : Interp.relevantSupport Δ' τ e = A.image LogicVar.free := by
      rw [LogicVar.eq_image_free_of_locallyClosed hclosed, Interp.freeAtomSet_relevantSupport,
        Interp.relevantEnv_idem, henv]
    rw [Interp.resultFirst, hsupport,
      LogicVar.image_shiftFrom_eq_of_locallyClosed _ 0 closedA,
      Interp.shiftTerm_eq_of_locallyClosed e typed.locallyClosed]
  have terminates : m ⊨ Interp.total e := by
    rw [← same]
    exact Interp.models_total_sum defined typed.locallyClosed
      (models_interp_total h₁) (models_interp_total h₂)
  unfold interp
  rw [show (τ₁.sum τ₂).measure = gas + 1 by simp [measure, gas, Nat.add_comm]]
  simp only [interpFuel, Nat.zero_add]
  apply Formula.models_and_intro
    (Interp.models_guard_relevant_of_world wfτ typed world terminates)
  change m ⊨ Formula.all (Interp.resultFirst Δ' τ e ⇒ᶜ Q)
  rw [resultFirst]
  apply (Formula.models_all_iff_refines m P).2
  refine ⟨by rw [hPfree]; exact scope, Δ.domain, ?_⟩
  intro y hy _ n href hndom
  have freshA : y ∉ A := fun hm => hy (hAΔ hm)
  have hQopen : (Q.openAt 0 y).freeAtoms ⊆ A ∪ {y} := by
    intro x hx
    rcases Finset.mem_union.1 (Formula.freeAtoms_openAt_subset Q 0 y hx) with hx | hx
    · exact Finset.mem_union_right _ hx
    · exact Finset.mem_union_left _ (Finset.subset_union_left (hQfree hx))
  have hopen : (Interp.resultAt (A.image LogicVar.free) e (.bound 0)).openAt 0 y =
      Interp.resultAt (A.image LogicVar.free) e (.free y) := by
    have hi := Interp.resultAt_shift_openAt (A.image LogicVar.free) e y closedA
      typed.locallyClosed logicA (by simpa using freshA)
    rw [LogicVar.image_shiftFrom_eq_of_locallyClosed _ 0 closedA,
      Interp.shiftTerm_eq_of_locallyClosed e typed.locallyClosed] at hi
    exact hi
  have hRfree : (Interp.resultAt (A.image LogicVar.free) e (.free y)).freeAtoms = A ∪ {y} := by
    simp only [Interp.freeAtoms_resultAt, Formula.LogicVar.freeAtomSet_image_free,
      Finset.union_eq_left.2 supportE, LogicVar.freeAtoms]
  have hn : n.domain = A ∪ {y} := by rwa [hPfree] at hndom
  change n ⊨ ((Interp.resultAt (A.image LogicVar.free) e (.bound 0)).openAt 0 y ⇒ᶜ
    Q.openAt 0 y)
  rw [hopen]
  apply Formula.models_impl_intro
  · simp only [Formula.freeAtoms_impl, hRfree]
    rw [hn]
    exact Finset.union_subset (Finset.Subset.refl _) hQopen
  · intro k hnk hres
    have hnk' : n ⊑ k := by
      simp only [Formula.freeAtoms_impl, hRfree, Finset.union_eq_left.2 hQopen] at hnk
      rwa [← hn, Capability.restrict_domain_self] at hnk
    have hmk : m.restrict A ⊑ k := Capability.refines_trans
      (by rwa [hPfree] at href) hnk'
    have defA : Capability.SumDefined (m₁.restrict A) (m₂.restrict A) := by
      simp only [Capability.SumDefined, Capability.restrict_domain, domain₁, domain₂]
    have sumA : Capability.sum (m₁.restrict A) (m₂.restrict A) defA = m.restrict A := by
      rw [← same, Capability.restrict_sum]
    obtain ⟨sub₁, sub₂, split⟩ := Capability.sum_pullback defA (by rwa [sumA])
    let k₁ := Capability.pullback k (m₁.restrict A) sub₁
    let k₂ := Capability.pullback k (m₂.restrict A) sub₂
    have hsource₁ : k₁ ⊨ interp Δ τ₁ e := by
      apply Formula.models_kripke
        (m := m₁.restrict A) (n := k₁)
        (Capability.restrict_pullback k (m₁.restrict A) sub₁).symm
      exact (models_interp_restrict support₁).1 h₁
    have hsource₂ : k₂ ⊨ interp Δ τ₂ e := by
      apply Formula.models_kripke
        (m := m₂.restrict A) (n := k₂)
        (Capability.restrict_pullback k (m₂.restrict A) sub₂).symm
      exact (models_interp_restrict support₂).1 h₂
    have hres₁ : k₁ ⊨ Interp.resultAt (A.image LogicVar.free) e (.free y) :=
      Interp.models_resultAt_pullback closedA logicA (by simpa using freshA)
        (by simp [Finset.inter_eq_right.2 scope₁]) sub₁ hres
    have hres₂ : k₂ ⊨ Interp.resultAt (A.image LogicVar.free) e (.free y) :=
      Interp.models_resultAt_pullback closedA logicA (by simpa using freshA)
        (by simp [Finset.inter_eq_right.2 scope₂]) sub₂ hres
    have child (υ : ContextType) (wfυ : υ.WellFormed Δ.domain)
        (supportυ : υ.freeAtoms ⊆ τ.freeAtoms) (measureυ : υ.measure ≤ gas)
        (r : Capability) (hsource : r ⊨ interp Δ υ e)
        (result : r ⊨ Interp.resultAt (A.image LogicVar.free) e (.free y)) :
        r ⊨ (interpFuel gas 1 Δ' (υ.shiftFrom 0) (.ret (.bound 0))).openAt 0 y := by
      have h := models_interpFuel_result_alias closedA typed.locallyClosed logicA
        (by simpa using freshA) hy wfυ typed.support_subset
        (Finset.image_subset_image (Finset.Subset.trans supportυ Finset.subset_union_left))
        result hsource
      have heq : interpFuel gas 1 Δ' (υ.shiftFrom 0) (.ret (.bound 0)) =
          interpFuel υ.measure 1 Δ (υ.shiftFrom 0) (.ret (.bound 0)) := by
        rw [interpFuel_eq_of_measure_le gas υ.measure 1 Δ' (υ.shiftFrom 0)
          (.ret (.bound 0)) (by simpa only [measure_shiftFrom] using measureυ)
          (by simpa only [measure_shiftFrom] using Nat.le_refl υ.measure)]
        apply interpFuel_eq_of_agreeOn
        intro x hx
        have hxυ : x ∈ υ.freeAtoms := by
          simpa only [freeAtoms_shiftFrom, Term.support, Value.support, Finset.union_empty] using hx
        have hxA : x ∈ A := Finset.subset_union_left (supportυ hxυ)
        change (Δ.restrict A).lookup x = Δ.lookup x
        rw [BasicEnv.lookup_restrict, if_pos hxA]
      rw [heq]
      exact h
    apply (Formula.models_sum_iff_eq _ _ _).2
    refine ⟨k₁, k₂, rfl, split, ?_, ?_⟩
    · exact child τ₁ wfτ.1 Finset.subset_union_left (Nat.le_max_left _ _) k₁ hsource₁ hres₁
    · exact child τ₂ wfτ.2.1 Finset.subset_union_right (Nat.le_max_right _ _) k₂ hsource₂ hres₂

theorem interp_eq_of_agreeOn {Δ₁ Δ₂ : BasicEnv} {τ : ContextType}
    {e : Term}
    (h : BasicEnv.AgreeOn (τ.freeAtoms ∪ e.support) Δ₁ Δ₂) :
    interp Δ₁ τ e = interp Δ₂ τ e :=
  interpFuel_eq_of_agreeOn τ.measure 0 h

/-- An overapproximate constant refinement fixes the value of a returned
variable in every possible store. -/
theorem models_over_constant_ret_free_lookup
    {m : Capability} {Δ : BasicEnv} {x : Atom} {c : Constant}
    (typed : Δ ⊢ᵥ (.free x) ⋮ (.base c.baseType))
    (h : m ⊨ interp Δ
      (.over c.baseType (Qualifier.equal (.bound 0) (.const c)))
      (.ret (.free x))) :
    ∀ σ, σ ∈ m → σ.lookup x = some (.const c) := by
  let q := Qualifier.equal (.bound 0) (.const c)
  let τ := ContextType.over c.baseType q
  let e := Term.ret (.free x)
  let Δ' := Interp.relevantEnv Δ τ e
  let P := Interp.resultFirst Δ' τ e ⇒ᶜ
    Formula.fiber (q.support \ {.bound 0}) (Interp.overResult c.baseType q)
  have hxΔ : x ∈ Δ.domain := typed.support_subset (by simp [Value.support])
  have hx : Δ.lookup x = some (.base c.baseType) := by
    cases typed with
    | free hx => exact hx
  have hΔ' : Δ'.domain = {x} := by
    simp [Δ', Interp.relevantEnv_domain, Interp.relevantAtoms, τ, q, e,
      ContextType.freeAtoms, Qualifier.equal, Qualifier.freeAtoms,
      Value.logicalSupport, Term.support, Value.support, LogicVar.freeAtoms,
      hxΔ]
  have hrel : Interp.relevantEnv Δ' τ e = Δ' :=
    Interp.relevantEnv_idem Δ τ e
  have hX : Interp.relevantSupport Δ' τ e = {LogicVar.free x} := by
    simp only [Interp.relevantSupport, hrel, hΔ']
    simp [τ, q, e,
      ContextType.support, ContextType.supportAt, Qualifier.equal,
      Value.logicalSupport, LogicVar.supportAtDepth, LogicVar.atDepth,
      Term.logicSupportAt, Value.logicSupportAt]
  have hP : P.freeAtoms = {x} := by
    simp only [P, Formula.freeAtoms_impl, Interp.freeAtoms_resultFirst,
      Interp.freeAtoms_overResultFiber, hrel, hΔ']
    simp [q, e, Qualifier.equal, Qualifier.freeAtoms,
      Value.logicalSupport, Term.support, Value.support, LogicVar.freeAtoms]
  have hall : m ⊨ Formula.all P := Formula.models_and_elim_right h
  obtain ⟨hdom, L, hall⟩ := (Formula.models_all_iff m P).1 hall
  obtain ⟨y, hy⟩ := Finset.exists_nat_subset_range (L ∪ {x})
  have hyfresh : y ∉ L ∪ {x} := by
    intro hmem
    have := hy hmem
    simp at this
  have hyL : y ∉ L := fun hy => hyfresh (Finset.mem_union_left _ hy)
  have hxy : y ≠ x := by simpa using fun hy => hyfresh (Finset.mem_union_right L hy)
  let r := m.restrict P.freeAtoms
  have hrdom : r.domain = {x} := hdom.trans hP
  have hworld : r ⊨ Interp.basicWorld Δ' := by
    have hw := (Formula.models_restrict_iff m (Interp.basicWorld Δ')).1
      (models_interp_basicWorld h)
    simpa [Interp.freeAtoms_basicWorld, hΔ', r, hP] using hw
  have hvalues : ∀ σ, σ ∈ r → ∃ v,
      σ.lookup x = some v ∧ v.locallyClosed := by
    intro σ hσ
    obtain ⟨v, hv, hvT⟩ := (Interp.models_basicWorld_iff r Δ').1 hworld
      |>.2 σ hσ x (.base c.baseType) (by
        simp [Δ', Interp.relevantEnv, Interp.relevantAtoms, τ, q, e,
          ContextType.freeAtoms, Qualifier.equal, Qualifier.freeAtoms,
          Value.logicalSupport, Term.support, Value.support, LogicVar.freeAtoms, hx])
    exact ⟨v, hv, hvT.locallyClosed⟩
  let F := Capability.FiberExtension.ofMap {x} {y}
    (fun σ => Store.singleton y ((σ.lookup x).getD (.const .unit)))
    (by simp [Ne.symm hxy])
    (by
      intro σ _
      simp)
  have hFin : F.input = P.freeAtoms := by simp [F, Capability.FiberExtension.ofMap, hP]
  have hFout : F.output = {y} := rfl
  have happ : F.Applicable r := by
    constructor
    · simp [F, Capability.FiberExtension.ofMap, hrdom]
    · simp [F, Capability.FiberExtension.ofMap, hrdom, hxy]
  obtain ⟨n, hExt⟩ := F.extends_exists r happ
  have hnvalues : ∀ ρ, ρ ∈ n → ∃ v,
      ρ.lookup x = some v ∧ ρ.lookup y = some v ∧ v.locallyClosed := by
    intro ρ hρ
    obtain ⟨σ, w, o, hσ, hw, ho, rfl⟩ := (hExt.mem_iff ρ).1 hρ
    change w = Capability.singleton
      (Store.singleton y (((σ.restrict {x}).lookup x).getD (.const .unit))) at hw
    subst w
    rw [Capability.mem_singleton_iff] at ho
    subst o
    obtain ⟨v, hv, hclosed⟩ := hvalues σ hσ
    have hxσ : x ∈ σ.domain := by
      rw [r.mem_domain hσ, hrdom]
      simp
    have hyσ : y ∉ σ.domain := by
      rw [r.mem_domain hσ, hrdom]
      simpa using hxy
    refine ⟨v, ?_, ?_, hclosed⟩
    · rwa [Store.lookup_merge_left _ _ hxσ]
    · rw [Store.lookup_merge_right _ _ hyσ]
      simp [hv]
  have hres : n ⊨ Interp.resultAt {LogicVar.free x} e (.free y) := by
    apply Interp.models_resultAt_intro
    · intro k hk
      simp at hk
    · simp [e, Term.logicSupportAt, Value.logicSupportAt]
    · simpa using hxy
    · simp [hExt.domain_eq, hrdom, hFout, LogicVar.freeAtomSet, LogicVar.freeAtoms]
    · intro ρ hρ
      obtain ⟨v, hxv, hyv, hclosed⟩ := hnvalues ρ hρ
      refine ⟨v, hyv, ?_⟩
      simpa [e, Interp.instantiateTerm, Interp.instantiateTermAt,
        Interp.instantiateValueAt, Store.toAssignment_lookup_free, hxv] using
        Steps.refl (.ret v) hclosed
    · intro ρ hρ v heval
      obtain ⟨u, hxu, hyu, _⟩ := hnvalues ρ hρ
      have hvu : v = u := by
        have : (Term.ret u).reaches v := by
          simpa [e, Interp.instantiateTerm, Interp.instantiateTermAt,
            Interp.instantiateValueAt, Store.toAssignment_lookup_free, hxu] using heval
        exact Term.ret.inj this.ret_eq
      exact ⟨ρ, hρ, rfl, by simpa [hvu] using hyu⟩
  have hsource := hall y hyL F hFin hFout n hExt
  have hopen : (Interp.resultFirst Δ' τ e).openAt 0 y =
      Interp.resultAt {LogicVar.free x} e (.free y) := by
    rw [Interp.resultFirst_openAt]
    · rw [hX]
    · rw [hX]
      intro k hk
      simp at hk
    · trivial
    · simp [hX, e, Term.logicSupportAt, Value.logicSupportAt]
    · simpa [hX] using hxy
  have hbody : n ⊨ (Interp.overResult c.baseType q).openAt 0 y := by
    change n ⊨ ((Interp.resultFirst Δ' τ e).openAt 0 y ⇒ᶜ
      (Formula.fiber (q.support \ {.bound 0})
        (Interp.overResult c.baseType q)).openAt 0 y) at hsource
    rw [hopen] at hsource
    have hb := Formula.models_impl_elim hsource hres
    simpa [Formula.openAt, q, Qualifier.equal, Value.logicalSupport, LogicVar.openSupport,
      Formula.models_fiber_empty_iff] using hb
  have hnconstant : ∀ ρ, ρ ∈ n → ρ.lookup x = some (.const c) := by
    intro ρ hρ
    obtain ⟨_, a, ha, hlook⟩ :=
      Formula.models_over_and_atom_holdsStore hbody hρ
    have hyc : ρ.lookup y = some (.const c) := by
      have hafree : (q.openAt 0 y).freeAtoms = {y} := by
        simp [q, Qualifier.equal, Qualifier.freeAtoms, LogicVar.openSupport,
          LogicVar.openBinder, LogicVar.swap, Value.logicalSupport, LogicVar.freeAtoms]
      have halook : a.assignment.lookup (.free y) = some (.const c) := by
        simpa [q, Qualifier.openAt, Qualifier.equal, Value.denoteAssignment,
          AssignmentOn.swapBack, Assignment.lookup_swap, LogicVar.swap] using ha
      rw [hlook y, hafree, Store.lookup_restrict, if_pos (by simp)] at halook
      exact halook
    obtain ⟨v, hxv, hyv, _⟩ := hnvalues ρ hρ
    exact hxv.trans (hyv.symm.trans hyc)
  intro σ hσ
  have hσr : σ.restrict {x} ∈ r := by
    change σ.restrict {x} ∈ m.restrict P.freeAtoms
    rw [hP]
    exact ⟨σ, hσ, rfl⟩
  have hσn : σ.restrict {x} ∈ n.restrict r.domain := by
    rw [hExt.restrict_base]
    exact hσr
  obtain ⟨ρ, hρ, hproj⟩ := hσn
  have hlook := congrArg (fun s : Store => s.lookup x) hproj
  change (ρ.restrict r.domain).lookup x = (σ.restrict {x}).lookup x at hlook
  rw [Store.lookup_restrict, if_pos (by simp [hrdom]),
    Store.lookup_restrict, if_pos (by simp)] at hlook
  exact hlook.symm.trans (hnconstant ρ hρ)

/-- A precise constant type fixes its returned variable pointwise. -/
theorem models_constantPrecise_ret_free_lookup
    {m : Capability} {Δ : BasicEnv} {x : Atom} {c : Constant}
    (typed : Δ ⊢ᵥ (.free x) ⋮ (.base c.baseType))
    (h : m ⊨ interp Δ (constantPrecise c) (.ret (.free x))) :
    ∀ σ, σ ∈ m → σ.lookup x = some (.const c) := by
  have hover : m ⊨ interp Δ
      (.over c.baseType (Qualifier.equal (.bound 0) (.const c)))
      (.ret (.free x)) :=
    Formula.models_and_elim_left (Formula.models_and_elim_right h)
  exact models_over_constant_ret_free_lookup typed hover

end ContextType

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
