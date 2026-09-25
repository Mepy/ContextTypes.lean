import ContextTypes.Syntax

set_option autoImplicit false

namespace ContextTypes

/-!
# Free-variable substitution

Substitution acts on free atoms.  Bound occurrences remain de Bruijn indices
and are instantiated by `Value.openAt` and `Term.openAt` from `Syntax.lean`.
-/

mutual

  /-- Capture-avoiding substitution for a free atom in a value. -/
  def Value.substitute : Value → Atom → Value → Value
    | .const c, _, _ => .const c
    | .free y, x, u => if y = x then u else .free y
    | .bound k, _, _ => .bound k
    | .lam T e, x, u => .lam T (e.substitute x u)
    | .fix T v, x, u => .fix T (v.substitute x u)

  /-- Capture-avoiding substitution for a free atom in a term. -/
  def Term.substitute : Term → Atom → Value → Term
    | .ret v, x, u => .ret (v.substitute x u)
    | .letE e₁ e₂, x, u => .letE (e₁.substitute x u) (e₂.substitute x u)
    | .primitive op v, x, u => .primitive op (v.substitute x u)
    | .app v₁ v₂, x, u => .app (v₁.substitute x u) (v₂.substitute x u)
    | .matchBool v e₁ e₂, x, u =>
        .matchBool (v.substitute x u) (e₁.substitute x u) (e₂.substitute x u)

end

mutual

  theorem Value.substitute_eq_self (v : Value) (x : Atom) (u : Value)
      (fresh : x ∉ v.support) :
      v.substitute x u = v := by
    cases v with
    | const c => rfl
    | free y =>
        simp only [Value.support, Finset.mem_singleton] at fresh
        simp [Value.substitute, Ne.symm fresh]
    | bound k => rfl
    | lam T e =>
        exact congrArg (Value.lam T) (Term.substitute_eq_self e x u fresh)
    | fix T v =>
        exact congrArg (Value.fix T) (Value.substitute_eq_self v x u fresh)

  theorem Term.substitute_eq_self (e : Term) (x : Atom) (u : Value)
      (fresh : x ∉ e.support) :
      e.substitute x u = e := by
    cases e with
    | ret v =>
        exact congrArg Term.ret (Value.substitute_eq_self v x u fresh)
    | letE e₁ e₂ =>
        simp only [Term.support, Finset.mem_union, not_or] at fresh
        simp [Term.substitute, Term.substitute_eq_self e₁ x u fresh.1,
          Term.substitute_eq_self e₂ x u fresh.2]
    | primitive op v =>
        exact congrArg (Term.primitive op) (Value.substitute_eq_self v x u fresh)
    | app v₁ v₂ =>
        simp only [Term.support, Finset.mem_union, not_or] at fresh
        simp [Term.substitute, Value.substitute_eq_self v₁ x u fresh.1,
          Value.substitute_eq_self v₂ x u fresh.2]
    | matchBool v e₁ e₂ =>
        simp only [Term.support, Finset.mem_union, not_or] at fresh
        simp [Term.substitute, Value.substitute_eq_self v x u fresh.1.1,
          Term.substitute_eq_self e₁ x u fresh.1.2,
          Term.substitute_eq_self e₂ x u fresh.2]

end

private theorem union_subset_pair {α : Type} [DecidableEq α]
    {A B C A' B' : Finset α}
    (hA : A ⊆ A' ∪ C) (hB : B ⊆ B' ∪ C) :
    A ∪ B ⊆ (A' ∪ B') ∪ C := by
  intro x hx
  simp only [Finset.mem_union] at hx ⊢
  rcases hx with hx | hx
  · rcases Finset.mem_union.mp (hA hx) with hx | hx
    · exact Or.inl (Or.inl hx)
    · exact Or.inr hx
  · rcases Finset.mem_union.mp (hB hx) with hx | hx
    · exact Or.inl (Or.inr hx)
    · exact Or.inr hx

mutual

  theorem Value.support_substitute_subset (v : Value) (x : Atom) (u : Value) :
      (v.substitute x u).support ⊆ v.support ∪ u.support := by
    cases v with
    | const c => simp [Value.substitute, Value.support]
    | free y =>
        by_cases same : y = x <;>
          simp [Value.substitute, Value.support, same]
    | bound k => simp [Value.substitute, Value.support]
    | lam T e => exact Term.support_substitute_subset e x u
    | fix T v => exact Value.support_substitute_subset v x u

  theorem Term.support_substitute_subset (e : Term) (x : Atom) (u : Value) :
      (e.substitute x u).support ⊆ e.support ∪ u.support := by
    cases e with
    | ret v => exact Value.support_substitute_subset v x u
    | letE e₁ e₂ =>
        exact union_subset_pair
          (Term.support_substitute_subset e₁ x u)
          (Term.support_substitute_subset e₂ x u)
    | primitive op v => exact Value.support_substitute_subset v x u
    | app v₁ v₂ =>
        exact union_subset_pair
          (Value.support_substitute_subset v₁ x u)
          (Value.support_substitute_subset v₂ x u)
    | matchBool v e₁ e₂ =>
        exact union_subset_pair
          (union_subset_pair
            (Value.support_substitute_subset v x u)
            (Term.support_substitute_subset e₁ x u))
          (Term.support_substitute_subset e₂ x u)

end

mutual

  theorem Value.locallyClosedAt_substitute (v : Value) (d : Nat)
      (x : Atom) (u : Value) (source : v.locallyClosedAt d)
      (closed : u.locallyClosed) :
      (v.substitute x u).locallyClosedAt d := by
    cases v with
    | const c => trivial
    | free y =>
        by_cases same : y = x
        · subst y
          simpa [Value.substitute] using
            Value.locallyClosedAt_mono u closed (Nat.zero_le d)
        · simp [Value.substitute, Value.locallyClosedAt, same]
    | bound k => exact source
    | lam T e =>
        exact Term.locallyClosedAt_substitute e (d + 1) x u source closed
    | fix T v =>
        exact Value.locallyClosedAt_substitute v (d + 1) x u source closed

  theorem Term.locallyClosedAt_substitute (e : Term) (d : Nat)
      (x : Atom) (u : Value) (source : e.locallyClosedAt d)
      (closed : u.locallyClosed) :
      (e.substitute x u).locallyClosedAt d := by
    cases e with
    | ret v => exact Value.locallyClosedAt_substitute v d x u source closed
    | letE e₁ e₂ =>
        exact ⟨Term.locallyClosedAt_substitute e₁ d x u source.1 closed,
          Term.locallyClosedAt_substitute e₂ (d + 1) x u source.2 closed⟩
    | primitive op v =>
        exact Value.locallyClosedAt_substitute v d x u source closed
    | app v₁ v₂ =>
        exact ⟨Value.locallyClosedAt_substitute v₁ d x u source.1 closed,
          Value.locallyClosedAt_substitute v₂ d x u source.2 closed⟩
    | matchBool v e₁ e₂ =>
        exact ⟨Value.locallyClosedAt_substitute v d x u source.1 closed,
          Term.locallyClosedAt_substitute e₁ d x u source.2.1 closed,
          Term.locallyClosedAt_substitute e₂ d x u source.2.2 closed⟩

end

mutual

  theorem Value.substitute_openAt (v : Value) (x : Atom) (w u : Value)
      (closed : w.locallyClosed) (d : Nat) :
      (v.openAt d u).substitute x w =
        (v.substitute x w).openAt d (u.substitute x w) := by
    cases v with
    | const c => rfl
    | free y =>
        by_cases same : y = x
        · subst y
          simp [Value.openAt, Value.substitute,
            Value.openAt_eq_self_of_locallyClosed w (u.substitute x w) d closed]
        · simp [Value.openAt, Value.substitute, same]
    | bound k =>
        by_cases same : k = d <;>
          simp [Value.openAt, Value.substitute, same]
    | lam T e =>
        simp [Value.openAt, Value.substitute,
          Term.substitute_openAt e x w u closed (d + 1)]
    | fix T v =>
        simp [Value.openAt, Value.substitute,
          Value.substitute_openAt v x w u closed (d + 1)]

  theorem Term.substitute_openAt (e : Term) (x : Atom) (w u : Value)
      (closed : w.locallyClosed) (d : Nat) :
      (e.openAt d u).substitute x w =
        (e.substitute x w).openAt d (u.substitute x w) := by
    cases e with
    | ret v =>
        simp [Term.openAt, Term.substitute,
          Value.substitute_openAt v x w u closed d]
    | letE e₁ e₂ =>
        simp [Term.openAt, Term.substitute,
          Term.substitute_openAt e₁ x w u closed d,
          Term.substitute_openAt e₂ x w u closed (d + 1)]
    | primitive op v =>
        simp [Term.openAt, Term.substitute,
          Value.substitute_openAt v x w u closed d]
    | app v₁ v₂ =>
        simp [Term.openAt, Term.substitute,
          Value.substitute_openAt v₁ x w u closed d,
          Value.substitute_openAt v₂ x w u closed d]
    | matchBool v e₁ e₂ =>
        simp [Term.openAt, Term.substitute,
          Value.substitute_openAt v x w u closed d,
          Term.substitute_openAt e₁ x w u closed d,
          Term.substitute_openAt e₂ x w u closed d]

end

theorem Value.substitute_openVar (v : Value) (x : Atom) (w : Value)
    (d : Nat) (fresh : x ∉ v.support) (closed : w.locallyClosed) :
    (v.openAt d (.free x)).substitute x w = v.openAt d w := by
  rw [Value.substitute_openAt v x w (.free x) closed d]
  simp [Value.substitute, Value.substitute_eq_self v x w fresh]

theorem Term.substitute_openVar (e : Term) (x : Atom) (w : Value)
    (d : Nat) (fresh : x ∉ e.support) (closed : w.locallyClosed) :
    (e.openAt d (.free x)).substitute x w = e.openAt d w := by
  rw [Term.substitute_openAt e x w (.free x) closed d]
  simp [Value.substitute, Term.substitute_eq_self e x w fresh]

end ContextTypes
