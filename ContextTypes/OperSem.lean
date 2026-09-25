import ContextTypes.Syntax

set_option autoImplicit false

namespace ContextTypes

/-!
# Operational semantics

Relational call-by-value semantics for the let-normal core language.  The
generator primitives make evaluation nondeterministic, so the result view is
kept relational throughout.
-/

namespace Primitive

/-- Evaluation of a unary primitive on constants. -/
inductive Step : Primitive → Constant → Constant → Prop where
  | eqZero (n : Nat) :
      Step .eqZero (.nat n) (.bool (n == 0))
  | plusOne (n : Nat) :
      Step .plusOne (.nat n) (.nat (n + 1))
  | minusOne (n : Nat) :
      Step .minusOne (.nat n) (.nat n.pred)
  | boolGen (b : Bool) :
      Step .boolGen .unit (.bool b)
  | natGen (n : Nat) :
      Step .natGen .unit (.nat n)

end Primitive

/-- Reduction of a redex, without an evaluation context. -/
inductive HeadStep : Term → Term → Prop where
  | letRet (v : Value) (e : Term)
      (closed : (Term.letE (.ret v) e).locallyClosed) :
      HeadStep (.letE (.ret v) e) (e.openAt 0 v)
  | primitive (op : Primitive) (c c' : Constant)
      (steps : Primitive.Step op c c')
      (closed : (Term.primitive op (.const c)).locallyClosed) :
      HeadStep (.primitive op (.const c)) (.ret (.const c'))
  | beta (T : SimpleType) (e : Term) (v : Value)
      (closed : (Term.app (.lam T e) v).locallyClosed) :
      HeadStep (.app (.lam T e) v) (e.openAt 0 v)
  | fix (T : SimpleType) (vf v : Value)
      (closed : (Term.app (.fix T vf) v).locallyClosed) :
      HeadStep (.app (.fix T vf) v)
        (.app (vf.openAt 0 v) (.fix T vf))
  | matchTrue (e₁ e₂ : Term)
      (closed : (Term.matchBool (.const (.bool true)) e₁ e₂).locallyClosed) :
      HeadStep (.matchBool (.const (.bool true)) e₁ e₂) e₁
  | matchFalse (e₁ e₂ : Term)
      (closed : (Term.matchBool (.const (.bool false)) e₁ e₂).locallyClosed) :
      HeadStep (.matchBool (.const (.bool false)) e₁ e₂) e₂

/-- One call-by-value reduction step.  The only nontrivial evaluation context
of the let-normal language is `let □ in e`. -/
inductive Step : Term → Term → Prop where
  | head {e e' : Term} (step : HeadStep e e') : Step e e'
  | letE {e₁ e₁' e₂ : Term} (step : Step e₁ e₁')
      (closed : (Term.letE e₁ e₂).locallyClosed) :
      Step (.letE e₁ e₂) (.letE e₁' e₂)

/-- Reflexive-transitive reduction, with local closure recorded at the
reflexive endpoint. -/
inductive Steps : Term → Term → Prop where
  | refl (e : Term) (closed : e.locallyClosed) : Steps e e
  | tail {e₁ e₂ e₃ : Term} (step : Step e₁ e₂) (steps : Steps e₂ e₃) :
      Steps e₁ e₃

namespace HeadStep

/-- Head reduction preserves local closure. -/
theorem regular {e e' : Term} (step : HeadStep e e') :
    e.locallyClosed ∧ e'.locallyClosed := by
  cases step with
  | letRet v e closed =>
      exact ⟨closed,
        Term.locallyClosedAt_openAt e 0 v closed.2 closed.1⟩
  | primitive op c c' steps closed =>
      exact ⟨closed, trivial⟩
  | beta T e v closed =>
      exact ⟨closed,
        Term.locallyClosedAt_openAt e 0 v closed.1 closed.2⟩
  | fix T vf v closed =>
      exact ⟨closed,
        ⟨Value.locallyClosedAt_openAt vf 0 v closed.1 closed.2,
          closed.1⟩⟩
  | matchTrue e₁ e₂ closed => exact ⟨closed, closed.2.1⟩
  | matchFalse e₁ e₂ closed => exact ⟨closed, closed.2.2⟩

/-- Head reduction does not introduce free atoms. -/
theorem support_subset {e e' : Term} (step : HeadStep e e') :
    e'.support ⊆ e.support := by
  cases step with
  | letRet v e closed =>
      simpa [Term.support, Finset.union_comm] using
        Term.support_openAt_subset e 0 v
  | primitive op c c' steps closed =>
      simp [Term.support, Value.support]
  | beta T e v closed =>
      simpa [Term.support, Value.support, Finset.union_comm] using
        Term.support_openAt_subset e 0 v
  | fix T vf v closed =>
      intro x hx
      simp only [Term.support, Value.support, Finset.mem_union] at hx ⊢
      rcases hx with hx | hx
      · rcases Finset.mem_union.mp (Value.support_openAt_subset vf 0 v hx) with
          hx | hx
        · exact Or.inl hx
        · exact Or.inr hx
      · exact Or.inl hx
  | matchTrue e₁ e₂ closed =>
      simp [Term.support, Value.support]
  | matchFalse e₁ e₂ closed =>
      simp [Term.support, Value.support]

end HeadStep

namespace Step

/-- A small step preserves local closure. -/
theorem regular {e e' : Term} (step : Step e e') :
    e.locallyClosed ∧ e'.locallyClosed := by
  induction step with
  | head step => exact step.regular
  | letE step closed ih =>
      exact ⟨closed, ⟨ih.2, closed.2⟩⟩

/-- A small step does not introduce free atoms. -/
theorem support_subset {e e' : Term} (step : Step e e') :
    e'.support ⊆ e.support := by
  induction step with
  | head step => exact step.support_subset
  | letE step closed ih =>
      exact Finset.union_subset_union ih (fun _ h => h)

end Step

namespace Steps

/-- Compose two multi-step reductions. -/
theorem trans {e₁ e₂ e₃ : Term} (steps₁ : Steps e₁ e₂)
    (steps₂ : Steps e₂ e₃) : Steps e₁ e₃ := by
  induction steps₁ with
  | refl => exact steps₂
  | tail step steps ih => exact .tail step (ih steps₂)

/-- Embed one small step as a multi-step reduction. -/
theorem single {e e' : Term} (step : Step e e') : Steps e e' :=
  .tail step (.refl e' step.regular.2)

/-- The source of a multi-step reduction is locally closed. -/
theorem source_closed {e e' : Term} (steps : Steps e e') :
    e.locallyClosed := by
  cases steps with
  | refl e closed => exact closed
  | tail step steps => exact step.regular.1

/-- The target of a multi-step reduction is locally closed. -/
theorem target_closed {e e' : Term} (steps : Steps e e') :
    e'.locallyClosed := by
  induction steps with
  | refl e closed => exact closed
  | tail step steps ih => exact ih

/-- Multi-step reduction does not introduce free atoms. -/
theorem support_subset {e e' : Term} (steps : Steps e e') :
    e'.support ⊆ e.support := by
  induction steps with
  | refl e closed => exact fun _ h => h
  | tail step steps ih => exact Finset.Subset.trans ih step.support_subset

/-- A returned value cannot take a small step. -/
theorem ret_no_step (v : Value) {e : Term} : ¬ Step (.ret v) e := by
  intro step
  cases step with
  | head step => cases step

/-- A multi-step reduction starting at a returned value is reflexive. -/
theorem ret_eq {v : Value} {e : Term} (steps : Steps (.ret v) e) :
    e = .ret v := by
  cases steps with
  | refl => rfl
  | tail step steps => exact (ret_no_step v step).elim

/-- Invert the first step of a multi-step reduction. -/
theorem cases_head {e e' : Term} (steps : Steps e e') :
    (e = e' ∧ e.locallyClosed) ∨ ∃ e'', Step e e'' ∧ Steps e'' e' := by
  cases steps with
  | refl e closed => exact Or.inl ⟨rfl, closed⟩
  | tail step steps => exact Or.inr ⟨_, step, steps⟩

/-- Lift a multi-step reduction through the bound side of a let. -/
theorem underLet {e₁ e₁' e₂ : Term} (steps : Steps e₁ e₁')
    (body : e₂.locallyClosedAt 1) :
    Steps (.letE e₁ e₂) (.letE e₁' e₂) := by
  induction steps with
  | refl e closed => exact .refl _ ⟨closed, body⟩
  | tail step steps ih =>
      exact .tail (.letE step ⟨step.regular.1, body⟩) ih

end Steps

namespace Term

/-- A term is syntactically a returned value. -/
def isValue (e : Term) : Prop :=
  ∃ v, e = .ret v

/-- A closed returned value is an operational result. -/
def IsResult (e : Term) : Prop :=
  ∃ v, e = .ret v ∧ v.locallyClosed

/-- A term can take at least one reduction step. -/
def CanStep (e : Term) : Prop :=
  ∃ e', Step e e'

/-- Every reduction branch reaches a result after finitely many steps. -/
inductive MustTerminate : Term → Prop where
  | result {e : Term} (result : e.IsResult) : e.MustTerminate
  | step {e : Term} (steps : e.CanStep)
      (next : ∀ e', Step e e' → e'.MustTerminate) : e.MustTerminate

theorem MustTerminate.ret (v : Value) (closed : v.locallyClosed) :
    MustTerminate (.ret v) :=
  .result ⟨v, rfl, closed⟩

theorem MustTerminate.step_inv {e e' : Term} (terminates : e.MustTerminate)
    (step : Step e e') : e'.MustTerminate := by
  cases terminates with
  | result result =>
      obtain ⟨v, rfl, closed⟩ := result
      exact (Steps.ret_no_step v step).elim
  | step steps next => exact next e' step

/-- Evaluation of `e` may return `v`. -/
def reaches (e : Term) (v : Value) : Prop :=
  Steps e (.ret v)

theorem MustTerminate.reaches_result {e : Term} (terminates : e.MustTerminate) :
    ∃ v, e.reaches v := by
  induction terminates with
  | result result =>
      obtain ⟨v, rfl, closed⟩ := result
      exact ⟨v, .refl _ closed⟩
  | step steps next ih =>
      obtain ⟨e', step⟩ := steps
      obtain ⟨v, reaches⟩ := ih e' step
      exact ⟨v, .tail step reaches⟩

/-- The relational set of all possible results of a term. -/
def results (e : Term) : Set Value :=
  {v | e.reaches v}

/-- Every possible result of a term satisfies `P`. -/
def allResults (e : Term) (P : Value → Prop) : Prop :=
  ∀ v, e.reaches v → P v

/-- Returned values have exactly themselves as a result. -/
@[simp] theorem ret_reaches_iff (v w : Value) (closed : v.locallyClosed) :
    (Term.ret v).reaches w ↔ w = v := by
  constructor
  · intro steps
    exact Term.ret.inj (steps.ret_eq)
  · intro same
    subst w
    exact .refl (.ret v) closed

/-- Decompose evaluation of a let expression. -/
theorem let_reaches {e₁ e₂ : Term} {v : Value}
    (steps : (Term.letE e₁ e₂).reaches v) :
    ∃ u, e₁.reaches u ∧ (e₂.openAt 0 u).reaches v := by
  change Steps (.letE e₁ e₂) (.ret v) at steps
  generalize sourceEq : Term.letE e₁ e₂ = source at steps
  generalize targetEq : Term.ret v = target at steps
  induction steps generalizing e₁ e₂ v with
  | refl e closed =>
      rw [← sourceEq] at targetEq
      cases targetEq
  | tail step steps ih =>
      cases sourceEq
      cases step with
      | head head =>
          cases head with
          | letRet u e₂ closed =>
              rw [← targetEq] at steps
              exact ⟨u, .refl (.ret u) closed.1, steps⟩
      | letE step closed =>
          obtain ⟨u, steps₁, steps₂⟩ := ih rfl targetEq
          exact ⟨u, .tail step steps₁, steps₂⟩

/-- Compose evaluation of the bound term and let body. -/
theorem let_reaches_intro {e₁ e₂ : Term} {u v : Value}
    (body : e₂.locallyClosedAt 1) (steps₁ : e₁.reaches u)
    (steps₂ : (e₂.openAt 0 u).reaches v) :
    (Term.letE e₁ e₂).reaches v := by
  exact Steps.trans (steps₁.underLet body) <|
    Steps.trans
      (Steps.single (.head (.letRet u e₂ ⟨steps₁.target_closed, body⟩)))
      steps₂

/-- Result characterization for let. -/
theorem let_reaches_iff {e₁ e₂ : Term} {v : Value}
    (body : e₂.locallyClosedAt 1) :
    (Term.letE e₁ e₂).reaches v ↔
      ∃ u, e₁.reaches u ∧ (e₂.openAt 0 u).reaches v := by
  exact ⟨let_reaches, fun ⟨u, h₁, h₂⟩ => let_reaches_intro body h₁ h₂⟩

/-- Result characterization for beta reduction. -/
theorem beta_reaches_iff {T : SimpleType} {e : Term} {u v : Value}
    (body : e.locallyClosedAt 1) (closed : u.locallyClosed) :
    (Term.app (.lam T e) u).reaches v ↔ (e.openAt 0 u).reaches v := by
  constructor
  · intro steps
    rcases steps.cases_head with ⟨same, _⟩ | ⟨e', step, rest⟩
    · cases same
    · cases step with
      | head head => cases head; exact rest
  · intro steps
    exact Steps.trans
      (Steps.single (.head (.beta T e u ⟨body, closed⟩))) steps

/-- Result characterization for fixed-point unfolding. -/
theorem fix_reaches_iff {T : SimpleType} {vf u v : Value}
    (body : vf.locallyClosedAt 1) (closed : u.locallyClosed) :
    (Term.app (.fix T vf) u).reaches v ↔
      (Term.app (vf.openAt 0 u) (.fix T vf)).reaches v := by
  constructor
  · intro steps
    rcases steps.cases_head with ⟨same, _⟩ | ⟨e', step, rest⟩
    · cases same
    · cases step with
      | head head => cases head; exact rest
  · intro steps
    exact Steps.trans
      (Steps.single (.head (.fix T vf u ⟨body, closed⟩))) steps

/-- Primitive evaluation reaches exactly a primitive result. -/
theorem primitive_reaches_iff {op : Primitive} {c : Constant} {v : Value} :
    (Term.primitive op (.const c)).reaches v ↔
      ∃ c', Primitive.Step op c c' ∧ v = .const c' := by
  constructor
  · intro steps
    rcases steps.cases_head with ⟨same, _⟩ | ⟨e', step, rest⟩
    · cases same
    · cases step with
      | head head =>
          cases head with
          | primitive op c c' primitive closed =>
              exact ⟨c', primitive, Term.ret.inj rest.ret_eq⟩
  · rintro ⟨c', primitive, rfl⟩
    exact Steps.single (.head (.primitive op c c' primitive trivial))

/-- Result characterization for the true branch. -/
theorem match_true_reaches_iff {e₁ e₂ : Term} {v : Value}
    (closed₁ : e₁.locallyClosed) (closed₂ : e₂.locallyClosed) :
    (Term.matchBool (.const (.bool true)) e₁ e₂).reaches v ↔ e₁.reaches v := by
  constructor
  · intro steps
    rcases steps.cases_head with ⟨same, _⟩ | ⟨e', step, rest⟩
    · cases same
    · cases step with
      | head head => cases head; exact rest
  · intro steps
    exact Steps.trans
      (Steps.single (.head (.matchTrue e₁ e₂ ⟨trivial, closed₁, closed₂⟩))) steps

/-- Result characterization for the false branch. -/
theorem match_false_reaches_iff {e₁ e₂ : Term} {v : Value}
    (closed₁ : e₁.locallyClosed) (closed₂ : e₂.locallyClosed) :
    (Term.matchBool (.const (.bool false)) e₁ e₂).reaches v ↔ e₂.reaches v := by
  constructor
  · intro steps
    rcases steps.cases_head with ⟨same, _⟩ | ⟨e', step, rest⟩
    · cases same
    · cases step with
      | head head => cases head; exact rest
  · intro steps
    exact Steps.trans
      (Steps.single (.head (.matchFalse e₁ e₂ ⟨trivial, closed₁, closed₂⟩))) steps

end Term

end ContextTypes
