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

theorem interp_eq_of_agreeOn {Δ₁ Δ₂ : BasicEnv} {τ : ContextType}
    {e : Term}
    (h : BasicEnv.AgreeOn (τ.freeAtoms ∪ e.support) Δ₁ Δ₂) :
    interp Δ₁ τ e = interp Δ₂ τ e :=
  interpFuel_eq_of_agreeOn τ.measure 0 h

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
