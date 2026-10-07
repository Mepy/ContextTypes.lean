import Mathlib.Data.Finset.Basic
import Mathlib.Tactic

set_option autoImplicit false

namespace ContextTypes

/-!
# Core language syntax

The executable language from the paper, represented in locally nameless form.
Free variables are atoms and bound variables are de Bruijn indices.  The
`Value` and `Term` operations in this file are the shared binding API for the
rest of the development.
-/

/-- Names of free program and logical variables. -/
abbrev Atom := Nat

/-- A locally nameless logical variable. -/
inductive LogicVar where
  | bound (k : Nat)
  | free (x : Atom)
  deriving DecidableEq, Repr

namespace LogicVar

/-- Swap two logical variables.  Logical-variable opening is represented by
such a transposition, following the finite-support development. -/
def swap (ξ₁ ξ₂ ξ : LogicVar) : LogicVar :=
  if ξ = ξ₁ then ξ₂
  else if ξ = ξ₂ then ξ₁
  else ξ

/-- Open logical binder `k` with the fresh atom `x`.

This operation is deliberately involutive: it swaps the bound and free keys.
The one-sided operation is provided separately for situations where the
inverse action is not wanted. -/
def openBinder (k : Nat) (x : Atom) : LogicVar → LogicVar :=
  swap (.bound k) (.free x)

/-- Replace one bound logical variable by a free variable. -/
def openOneSided (k : Nat) (x : Atom) : LogicVar → LogicVar
  | .bound j => if j = k then .free x else .bound j
  | .free y => .free y

/-- The free-atom support of a logical variable. -/
def freeAtoms : LogicVar → Finset Atom
  | .bound _ => ∅
  | .free x => {x}

/-- Shift every bound logical variable by `d`. -/
def shift (d : Nat) : LogicVar → LogicVar
  | .bound k => .bound (d + k)
  | .free x => .free x

/-- Open every key in a finite logical-variable support. -/
def openSupport (k : Nat) (x : Atom) (X : Finset LogicVar) : Finset LogicVar :=
  X.image (openBinder k x)

@[simp] theorem swap_left (ξ₁ ξ₂ : LogicVar) :
    swap ξ₁ ξ₂ ξ₁ = ξ₂ := by
  simp [swap]

@[simp] theorem swap_right (ξ₁ ξ₂ : LogicVar) :
    swap ξ₁ ξ₂ ξ₂ = ξ₁ := by
  by_cases same : ξ₂ = ξ₁
  · subst ξ₂
    simp [swap]
  · simp [swap, same]

@[simp] theorem swap_involutive (ξ₁ ξ₂ ξ : LogicVar) :
    swap ξ₁ ξ₂ (swap ξ₁ ξ₂ ξ) = ξ := by
  by_cases ξ = ξ₁ <;> by_cases ξ = ξ₂ <;>
    simp_all [swap]

@[simp] theorem open_involutive (k : Nat) (x : Atom) (ξ : LogicVar) :
    openBinder k x (openBinder k x ξ) = ξ := by
  exact swap_involutive _ _ _

/-- Openings of distinct binders with distinct names commute. -/
theorem openBinder_comm (k l : Nat) (x y : Atom)
    (hkl : k ≠ l) (hxy : x ≠ y) (ξ : LogicVar) :
    openBinder k x (openBinder l y ξ) = openBinder l y (openBinder k x ξ) := by
  cases ξ with
  | bound j =>
      by_cases hjk : j = k <;> by_cases hjl : j = l
      all_goals simp_all [openBinder, swap, Ne.symm hkl, Ne.symm hxy]
  | free z =>
      by_cases hzx : z = x <;> by_cases hzy : z = y
      all_goals simp_all [openBinder, swap, Ne.symm hkl, Ne.symm hxy]

@[simp] theorem mem_openSupport (k : Nat) (x : Atom) (X : Finset LogicVar)
    (ξ : LogicVar) :
    ξ ∈ openSupport k x X ↔ openBinder k x ξ ∈ X := by
  constructor
  · intro h
    rw [openSupport, Finset.mem_image] at h
    obtain ⟨ζ, hζ, rfl⟩ := h
    simpa using hζ
  · intro h
    rw [openSupport, Finset.mem_image]
    exact ⟨openBinder k x ξ, h, open_involutive k x ξ⟩

@[simp] theorem openSupport_involutive (k : Nat) (x : Atom)
    (X : Finset LogicVar) :
    openSupport k x (openSupport k x X) = X := by
  ext ξ
  simp

/-- Independent binder openings commute on finite logical supports. -/
theorem openSupport_comm (k l : Nat) (x y : Atom)
    (hkl : k ≠ l) (hxy : x ≠ y) (X : Finset LogicVar) :
    openSupport k x (openSupport l y X) = openSupport l y (openSupport k x X) := by
  ext ξ
  simp only [mem_openSupport]
  rw [openBinder_comm k l x y hkl hxy]

theorem openSupport_eq_self_of_fresh (X : Finset LogicVar) (k : Nat)
    (x : Atom) (bound : LogicVar.bound k ∉ X)
    (free : LogicVar.free x ∉ X) : openSupport k x X = X := by
  ext ξ
  rw [mem_openSupport]
  cases ξ with
  | bound n =>
      by_cases h : n = k
      · subst n
        simp [openBinder, swap, bound, free]
      · simp [openBinder, swap, h]
  | free y =>
      by_cases h : y = x
      · subst y
        simp [openBinder, swap, bound, free]
      · simp [openBinder, swap, h]

end LogicVar

/-- Base types of constants. -/
inductive BaseType where
  | unit
  | bool
  | nat
  deriving DecidableEq, Repr

/-- Erased/simple types used by the operational language. -/
inductive SimpleType where
  | base (b : BaseType)
  | arrow (T U : SimpleType)
  deriving DecidableEq, Repr

/-- Core-language constants. -/
inductive Constant where
  | unit
  | bool (b : Bool)
  | nat (n : Nat)
  deriving DecidableEq, Repr

/-- Unary primitive operations.  The generators are nondeterministic and
ignore their argument. -/
inductive Primitive where
  | eqZero
  | plusOne
  | minusOne
  | boolGen
  | natGen
  deriving DecidableEq, Repr

namespace Constant

/-- The base type of a constant. -/
def baseType : Constant → BaseType
  | .unit => .unit
  | .bool _ => .bool
  | .nat _ => .nat

end Constant

mutual

  /-- Core values.  Lambdas and fixed points bind index zero in their body. -/
  inductive Value where
    | const (c : Constant)
    | free (x : Atom)
    | bound (k : Nat)
    | lam (T : SimpleType) (e : Term)
    /-- HATs-style fixed point.  Index zero is the ordinary argument; after
    opening it, `v` is expected to accept the recursive self reference. -/
    | fix (T : SimpleType) (v : Value)
    deriving DecidableEq, Repr

  /-- Core call-by-value terms. -/
  inductive Term where
    | ret (v : Value)
    | letE (e₁ e₂ : Term)
    | primitive (op : Primitive) (v : Value)
    | app (v₁ v₂ : Value)
    | matchBool (v : Value) (e₁ e₂ : Term)
    deriving DecidableEq, Repr

end

mutual

  /-- Open de Bruijn index `d` in a value. -/
  def Value.openAt : Value → Nat → Value → Value
    | .const c, _, _ => .const c
    | .free x, _, _ => .free x
    | .bound k, d, u => if k = d then u else .bound k
    | .lam T e, d, u => .lam T (e.openAt (d + 1) u)
    | .fix T v, d, u => .fix T (v.openAt (d + 1) u)

  /-- Open de Bruijn index `d` in a term. -/
  def Term.openAt : Term → Nat → Value → Term
    | .ret v, d, u => .ret (v.openAt d u)
    | .letE e₁ e₂, d, u => .letE (e₁.openAt d u) (e₂.openAt (d + 1) u)
    | .primitive op v, d, u => .primitive op (v.openAt d u)
    | .app v₁ v₂, d, u => .app (v₁.openAt d u) (v₂.openAt d u)
    | .matchBool v e₁ e₂, d, u =>
        .matchBool (v.openAt d u) (e₁.openAt d u) (e₂.openAt d u)

end

namespace Value

/-- Open the outermost binder in a value. -/
abbrev openOuter (v u : Value) : Value :=
  v.openAt 0 u

end Value

namespace Term

/-- Open the outermost binder in a term. -/
abbrev openOuter (e : Term) (u : Value) : Term :=
  e.openAt 0 u

end Term

mutual

  /-- Close free atom `x` as de Bruijn index `d` in a value. -/
  def Value.closeAt : Value → Atom → Nat → Value
    | .const c, _, _ => .const c
    | .free y, x, d => if y = x then .bound d else .free y
    | .bound k, _, _ => .bound k
    | .lam T e, x, d => .lam T (e.closeAt x (d + 1))
    | .fix T v, x, d => .fix T (v.closeAt x (d + 1))

  /-- Close free atom `x` as de Bruijn index `d` in a term. -/
  def Term.closeAt : Term → Atom → Nat → Term
    | .ret v, x, d => .ret (v.closeAt x d)
    | .letE e₁ e₂, x, d => .letE (e₁.closeAt x d) (e₂.closeAt x (d + 1))
    | .primitive op v, x, d => .primitive op (v.closeAt x d)
    | .app v₁ v₂, x, d => .app (v₁.closeAt x d) (v₂.closeAt x d)
    | .matchBool v e₁ e₂, x, d =>
        .matchBool (v.closeAt x d) (e₁.closeAt x d) (e₂.closeAt x d)

end

namespace Value

/-- Close a free atom as the outermost binder in a value. -/
abbrev close (v : Value) (x : Atom) : Value :=
  v.closeAt x 0

end Value

namespace Term

/-- Close a free atom as the outermost binder in a term. -/
abbrev close (e : Term) (x : Atom) : Term :=
  e.closeAt x 0

end Term

/-- Swap two free atoms. -/
def swapAtom (x y z : Atom) : Atom :=
  if z = x then y
  else if z = y then x
  else z

mutual

  /-- Swap two free atoms throughout a value. -/
  def Value.swap (x y : Atom) : Value → Value
    | .const c => .const c
    | .free z => .free (swapAtom x y z)
    | .bound k => .bound k
    | .lam T e => .lam T (e.swap x y)
    | .fix T v => .fix T (v.swap x y)

  /-- Swap two free atoms throughout a term. -/
  def Term.swap (x y : Atom) : Term → Term
    | .ret v => .ret (v.swap x y)
    | .letE e₁ e₂ => .letE (e₁.swap x y) (e₂.swap x y)
    | .primitive op v => .primitive op (v.swap x y)
    | .app v₁ v₂ => .app (v₁.swap x y) (v₂.swap x y)
    | .matchBool v e₁ e₂ =>
        .matchBool (v.swap x y) (e₁.swap x y) (e₂.swap x y)

end

mutual

  /-- Free atoms occurring in a value. -/
  def Value.support : Value → Finset Atom
    | .const _ => ∅
    | .free x => {x}
    | .bound _ => ∅
    | .lam _ e => e.support
    | .fix _ v => v.support

  /-- Free atoms occurring in a term. -/
  def Term.support : Term → Finset Atom
    | .ret v => v.support
    | .letE e₁ e₂ => e₁.support ∪ e₂.support
    | .primitive _ v => v.support
    | .app v₁ v₂ => v₁.support ∪ v₂.support
    | .matchBool v e₁ e₂ => v.support ∪ e₁.support ∪ e₂.support

end

/-- The externally visible logical-variable key for a bound occurrence at a
given binder cutoff. -/
def boundLogicSupportAt (d k : Nat) : Finset LogicVar :=
  if d ≤ k then {.bound (k - d)} else ∅

mutual

  /-- Logical-variable support of a value, relative to a binder cutoff. -/
  def Value.logicSupportAt (d : Nat) : Value → Finset LogicVar
    | .const _ => ∅
    | .free x => {.free x}
    | .bound k => boundLogicSupportAt d k
    | .lam _ e => e.logicSupportAt (d + 1)
    | .fix _ v => v.logicSupportAt (d + 1)

  /-- Logical-variable support of a term, relative to a binder cutoff. -/
  def Term.logicSupportAt (d : Nat) : Term → Finset LogicVar
    | .ret v => v.logicSupportAt d
    | .letE e₁ e₂ => e₁.logicSupportAt d ∪ e₂.logicSupportAt (d + 1)
    | .primitive _ v => v.logicSupportAt d
    | .app v₁ v₂ => v₁.logicSupportAt d ∪ v₂.logicSupportAt d
    | .matchBool v e₁ e₂ =>
        v.logicSupportAt d ∪ e₁.logicSupportAt d ∪ e₂.logicSupportAt d

end

namespace Value

/-- Logical-variable support at the outermost level. -/
abbrev logicSupport (v : Value) : Finset LogicVar :=
  v.logicSupportAt 0

end Value

namespace Term

/-- Logical-variable support at the outermost level. -/
abbrev logicSupport (e : Term) : Finset LogicVar :=
  e.logicSupportAt 0

end Term

mutual
/-- Core-value openings at distinct indices commute, since inserted free
values are unaffected by subsequent bound-variable opening. -/
theorem Value.openAt_free_comm (v : Value) (k l : Nat) (x y : Atom) (hkl : k ≠ l) :
    (v.openAt k (.free x)).openAt l (.free y) =
      (v.openAt l (.free y)).openAt k (.free x) := by
  cases v with
  | const c | free z => rfl
  | bound j =>
      by_cases hjk : j = k <;> by_cases hjl : j = l
      all_goals simp_all [Value.openAt]
  | lam T e =>
      simp only [Value.openAt]
      rw [Term.openAt_free_comm e (k + 1) (l + 1) x y (by omega)]
  | fix T v =>
      simp only [Value.openAt]
      rw [Value.openAt_free_comm v (k + 1) (l + 1) x y (by omega)]

/-- Core-term openings at distinct indices commute. -/
theorem Term.openAt_free_comm (e : Term) (k l : Nat) (x y : Atom) (hkl : k ≠ l) :
    (e.openAt k (.free x)).openAt l (.free y) =
      (e.openAt l (.free y)).openAt k (.free x) := by
  cases e with
  | ret v => simp only [Term.openAt, Value.openAt_free_comm v k l x y hkl]
  | letE e₁ e₂ =>
      simp only [Term.openAt]
      rw [Term.openAt_free_comm e₁ k l x y hkl,
        Term.openAt_free_comm e₂ (k + 1) (l + 1) x y (by omega)]
  | primitive op v => simp only [Term.openAt, Value.openAt_free_comm v k l x y hkl]
  | app v₁ v₂ =>
      simp only [Term.openAt, Value.openAt_free_comm v₁ k l x y hkl,
        Value.openAt_free_comm v₂ k l x y hkl]
  | matchBool v e₁ e₂ =>
      simp only [Term.openAt, Value.openAt_free_comm v k l x y hkl,
        Term.openAt_free_comm e₁ k l x y hkl, Term.openAt_free_comm e₂ k l x y hkl]
end

mutual
/-- Opening transports the externally visible support of a value. -/
theorem Value.logicSupportAt_openAt (v : Value) (d k : Nat) (y : Atom)
    (fresh : y ∉ v.support) :
    (v.openAt (k + d) (.free y)).logicSupportAt d =
      LogicVar.openSupport k y (v.logicSupportAt d) := by
  cases v with
  | const c => simp [Value.openAt, Value.logicSupportAt, LogicVar.openSupport]
  | free x =>
      have hxy : x ≠ y := by intro h; subst x; simp [Value.support] at fresh
      simp [Value.openAt, Value.logicSupportAt, LogicVar.openSupport, LogicVar.openBinder, LogicVar.swap, hxy]
  | bound j =>
      by_cases same : j = k + d
      · subst j
        simp [Value.openAt, Value.logicSupportAt, boundLogicSupportAt,
          LogicVar.openSupport, LogicVar.openBinder, LogicVar.swap]
      · by_cases hdj : d ≤ j
        · have hjk : j - d ≠ k := by omega
          simp [Value.openAt, Value.logicSupportAt, boundLogicSupportAt, same, hdj,
            LogicVar.openSupport, LogicVar.openBinder, LogicVar.swap, hjk]
        · simp [Value.openAt, Value.logicSupportAt, boundLogicSupportAt, same, hdj,
            LogicVar.openSupport]
  | lam T e =>
      simp only [Value.openAt, Value.logicSupportAt]
      rw [show k + d + 1 = k + (d + 1) by omega,
        Term.logicSupportAt_openAt e (d + 1) k y fresh]
  | fix T v =>
      simp only [Value.openAt, Value.logicSupportAt]
      rw [show k + d + 1 = k + (d + 1) by omega,
        Value.logicSupportAt_openAt v (d + 1) k y fresh]

/-- Opening transports the externally visible support of a term. -/
theorem Term.logicSupportAt_openAt (e : Term) (d k : Nat) (y : Atom)
    (fresh : y ∉ e.support) :
    (e.openAt (k + d) (.free y)).logicSupportAt d =
      LogicVar.openSupport k y (e.logicSupportAt d) := by
  cases e with
  | ret v => exact Value.logicSupportAt_openAt v d k y fresh
  | letE e₁ e₂ =>
      have hf : y ∉ e₁.support ∧ y ∉ e₂.support := by simpa [Term.support] using fresh
      simp only [Term.openAt, Term.logicSupportAt]
      rw [Term.logicSupportAt_openAt e₁ d k y hf.1,
        show k + d + 1 = k + (d + 1) by omega,
        Term.logicSupportAt_openAt e₂ (d + 1) k y hf.2]
      simp [LogicVar.openSupport, Finset.image_union]
  | primitive op v => exact Value.logicSupportAt_openAt v d k y fresh
  | app v₁ v₂ =>
      have hf : y ∉ v₁.support ∧ y ∉ v₂.support := by simpa [Term.support] using fresh
      simp only [Term.openAt, Term.logicSupportAt]
      rw [Value.logicSupportAt_openAt v₁ d k y hf.1, Value.logicSupportAt_openAt v₂ d k y hf.2]
      simp [LogicVar.openSupport, Finset.image_union]
  | matchBool v e₁ e₂ =>
      have hf : y ∉ v.support ∧ y ∉ e₁.support ∧ y ∉ e₂.support := by
        simpa [Term.support, and_assoc] using fresh
      simp only [Term.openAt, Term.logicSupportAt]
      rw [Value.logicSupportAt_openAt v d k y hf.1,
        Term.logicSupportAt_openAt e₁ d k y hf.2.1, Term.logicSupportAt_openAt e₂ d k y hf.2.2]
      simp [LogicVar.openSupport, Finset.image_union]
end

mutual

  /-- Every bound occurrence in a value is below the ambient binder depth. -/
  def Value.locallyClosedAt (d : Nat) : Value → Prop
    | .const _ => True
    | .free _ => True
    | .bound k => k < d
    | .lam _ e => e.locallyClosedAt (d + 1)
    | .fix _ v => v.locallyClosedAt (d + 1)

  /-- Every bound occurrence in a term is below the ambient binder depth. -/
  def Term.locallyClosedAt (d : Nat) : Term → Prop
    | .ret v => v.locallyClosedAt d
    | .letE e₁ e₂ => e₁.locallyClosedAt d ∧ e₂.locallyClosedAt (d + 1)
    | .primitive _ v => v.locallyClosedAt d
    | .app v₁ v₂ => v₁.locallyClosedAt d ∧ v₂.locallyClosedAt d
    | .matchBool v e₁ e₂ =>
        v.locallyClosedAt d ∧ e₁.locallyClosedAt d ∧ e₂.locallyClosedAt d

end

namespace Value

/-- A value with no dangling bound variables. -/
abbrev locallyClosed (v : Value) : Prop :=
  v.locallyClosedAt 0

end Value

namespace Term

/-- A term with no dangling bound variables. -/
abbrev locallyClosed (e : Term) : Prop :=
  e.locallyClosedAt 0

end Term

/-! ## Binding regularity -/

@[simp] theorem swapAtom_involutive (x y z : Atom) :
    swapAtom x y (swapAtom x y z) = z := by
  by_cases z = x <;> by_cases z = y <;>
    simp_all [swapAtom]

mutual

  @[simp] theorem Value.swap_involutive (v : Value) (x y : Atom) :
      (v.swap x y).swap x y = v := by
    cases v with
    | const c => rfl
    | free z => simp [Value.swap]
    | bound k => rfl
    | lam T e => simp [Value.swap, Term.swap_involutive]
    | fix T v => simp [Value.swap, Value.swap_involutive]

  @[simp] theorem Term.swap_involutive (e : Term) (x y : Atom) :
      (e.swap x y).swap x y = e := by
    cases e with
    | ret v => simp [Term.swap, Value.swap_involutive]
    | letE e₁ e₂ => simp [Term.swap, Term.swap_involutive]
    | primitive op v => simp [Term.swap, Value.swap_involutive]
    | app v₁ v₂ => simp [Term.swap, Value.swap_involutive]
    | matchBool v e₁ e₂ =>
        simp [Term.swap, Value.swap_involutive, Term.swap_involutive]

end

mutual

  /-- Opening a value never removes any free atom already present in it. -/
  theorem Value.support_subset_openAt (v : Value) (d : Nat) (u : Value) :
      v.support ⊆ (v.openAt d u).support := by
    cases v with
    | const c => simp [Value.support, Value.openAt]
    | free x => simp [Value.support, Value.openAt]
    | bound k => simp [Value.support]
    | lam T e => exact Term.support_subset_openAt e (d + 1) u
    | fix T v => exact Value.support_subset_openAt v (d + 1) u

  /-- Opening a term never removes any free atom already present in it. -/
  theorem Term.support_subset_openAt (e : Term) (d : Nat) (u : Value) :
      e.support ⊆ (e.openAt d u).support := by
    cases e with
    | ret v => exact Value.support_subset_openAt v d u
    | letE e₁ e₂ =>
        exact Finset.union_subset_union
          (Term.support_subset_openAt e₁ d u)
          (Term.support_subset_openAt e₂ (d + 1) u)
    | primitive op v => exact Value.support_subset_openAt v d u
    | app v₁ v₂ =>
        exact Finset.union_subset_union
          (Value.support_subset_openAt v₁ d u)
          (Value.support_subset_openAt v₂ d u)
    | matchBool v e₁ e₂ =>
        exact Finset.union_subset_union
          (Finset.union_subset_union
            (Value.support_subset_openAt v d u)
            (Term.support_subset_openAt e₁ d u))
          (Term.support_subset_openAt e₂ d u)

end


mutual

  theorem Value.closeAt_openAt (v : Value) (x : Atom) (d : Nat)
      (fresh : x ∉ v.support) :
      (v.openAt d (.free x)).closeAt x d = v := by
    cases v with
    | const c => rfl
    | free y =>
        simp only [Value.support, Finset.mem_singleton] at fresh
        simp [Value.openAt, Value.closeAt, Ne.symm fresh]
    | bound k =>
        by_cases same : k = d <;>
          simp [Value.openAt, Value.closeAt, same]
    | lam T e =>
        simp [Value.openAt, Value.closeAt, Term.closeAt_openAt e x (d + 1) fresh]
    | fix T v =>
        simp [Value.openAt, Value.closeAt, Value.closeAt_openAt v x (d + 1) fresh]

  theorem Term.closeAt_openAt (e : Term) (x : Atom) (d : Nat)
      (fresh : x ∉ e.support) :
      (e.openAt d (.free x)).closeAt x d = e := by
    cases e with
    | ret v =>
        simp [Term.openAt, Term.closeAt, Value.closeAt_openAt v x d fresh]
    | letE e₁ e₂ =>
        simp only [Term.support, Finset.mem_union, not_or] at fresh
        simp [Term.openAt, Term.closeAt,
          Term.closeAt_openAt e₁ x d fresh.1,
          Term.closeAt_openAt e₂ x (d + 1) fresh.2]
    | primitive op v =>
        simp [Term.openAt, Term.closeAt, Value.closeAt_openAt v x d fresh]
    | app v₁ v₂ =>
        simp only [Term.support, Finset.mem_union, not_or] at fresh
        simp [Term.openAt, Term.closeAt,
          Value.closeAt_openAt v₁ x d fresh.1,
          Value.closeAt_openAt v₂ x d fresh.2]
    | matchBool v e₁ e₂ =>
        simp only [Term.support, Finset.mem_union, not_or] at fresh
        simp [Term.openAt, Term.closeAt,
          Value.closeAt_openAt v x d fresh.1.1,
          Term.closeAt_openAt e₁ x d fresh.1.2,
          Term.closeAt_openAt e₂ x d fresh.2]

end


mutual

  theorem Value.locallyClosedAt_mono (v : Value) {d d' : Nat}
      (closed : v.locallyClosedAt d) (le : d ≤ d') :
      v.locallyClosedAt d' := by
    cases v with
    | const c => trivial
    | free x => trivial
    | bound k => exact lt_of_lt_of_le closed le
    | lam T e =>
        exact Term.locallyClosedAt_mono e closed (Nat.add_le_add_right le 1)
    | fix T v =>
        exact Value.locallyClosedAt_mono v closed (Nat.add_le_add_right le 1)

  theorem Term.locallyClosedAt_mono (e : Term) {d d' : Nat}
      (closed : e.locallyClosedAt d) (le : d ≤ d') :
      e.locallyClosedAt d' := by
    cases e with
    | ret v => exact Value.locallyClosedAt_mono v closed le
    | letE e₁ e₂ =>
        exact ⟨Term.locallyClosedAt_mono e₁ closed.1 le,
          Term.locallyClosedAt_mono e₂ closed.2 (Nat.add_le_add_right le 1)⟩
    | primitive op v => exact Value.locallyClosedAt_mono v closed le
    | app v₁ v₂ =>
        exact ⟨Value.locallyClosedAt_mono v₁ closed.1 le,
          Value.locallyClosedAt_mono v₂ closed.2 le⟩
    | matchBool v e₁ e₂ =>
        exact ⟨Value.locallyClosedAt_mono v closed.1 le,
          Term.locallyClosedAt_mono e₁ closed.2.1 le,
          Term.locallyClosedAt_mono e₂ closed.2.2 le⟩

end


mutual

  theorem Value.openAt_eq_self (v : Value) (d k : Nat) (u : Value)
      (closed : v.locallyClosedAt d) (le : d ≤ k) :
      v.openAt k u = v := by
    cases v with
    | const c => rfl
    | free x => rfl
    | bound j =>
        change j < d at closed
        have ne : j ≠ k := by omega
        simp [Value.openAt, ne]
    | lam T e =>
        simp [Value.openAt,
          Term.openAt_eq_self e (d + 1) (k + 1) u closed
            (Nat.add_le_add_right le 1)]
    | fix T v =>
        simp [Value.openAt,
          Value.openAt_eq_self v (d + 1) (k + 1) u closed
            (Nat.add_le_add_right le 1)]

  theorem Term.openAt_eq_self (e : Term) (d k : Nat) (u : Value)
      (closed : e.locallyClosedAt d) (le : d ≤ k) :
      e.openAt k u = e := by
    cases e with
    | ret v =>
        simp [Term.openAt, Value.openAt_eq_self v d k u closed le]
    | letE e₁ e₂ =>
        simp [Term.openAt, Term.openAt_eq_self e₁ d k u closed.1 le,
          Term.openAt_eq_self e₂ (d + 1) (k + 1) u closed.2
            (Nat.add_le_add_right le 1)]
    | primitive op v =>
        simp [Term.openAt, Value.openAt_eq_self v d k u closed le]
    | app v₁ v₂ =>
        simp [Term.openAt, Value.openAt_eq_self v₁ d k u closed.1 le,
          Value.openAt_eq_self v₂ d k u closed.2 le]
    | matchBool v e₁ e₂ =>
        simp [Term.openAt, Value.openAt_eq_self v d k u closed.1 le,
          Term.openAt_eq_self e₁ d k u closed.2.1 le,
          Term.openAt_eq_self e₂ d k u closed.2.2 le]

end


@[simp] theorem Value.openAt_eq_self_of_locallyClosed (v u : Value) (k : Nat)
    (closed : v.locallyClosed) :
    v.openAt k u = v :=
  Value.openAt_eq_self v 0 k u closed (Nat.zero_le k)

@[simp] theorem Term.openAt_eq_self_of_locallyClosed (e : Term) (u : Value)
    (k : Nat) (closed : e.locallyClosed) :
    e.openAt k u = e :=
  Term.openAt_eq_self e 0 k u closed (Nat.zero_le k)

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

  theorem Value.support_openAt_subset (v : Value) (d : Nat) (u : Value) :
      (v.openAt d u).support ⊆ v.support ∪ u.support := by
    cases v with
    | const c => simp [Value.openAt, Value.support]
    | free x => simp [Value.openAt, Value.support]
    | bound k =>
        by_cases same : k = d <;>
          simp [Value.openAt, Value.support, same]
    | lam T e =>
        exact Term.support_openAt_subset e (d + 1) u
    | fix T v =>
        exact Value.support_openAt_subset v (d + 1) u

  theorem Term.support_openAt_subset (e : Term) (d : Nat) (u : Value) :
      (e.openAt d u).support ⊆ e.support ∪ u.support := by
    cases e with
    | ret v => exact Value.support_openAt_subset v d u
    | letE e₁ e₂ =>
        exact union_subset_pair
          (Term.support_openAt_subset e₁ d u)
          (Term.support_openAt_subset e₂ (d + 1) u)
    | primitive op v => exact Value.support_openAt_subset v d u
    | app v₁ v₂ =>
        exact union_subset_pair
          (Value.support_openAt_subset v₁ d u)
          (Value.support_openAt_subset v₂ d u)
    | matchBool v e₁ e₂ =>
        exact union_subset_pair
          (union_subset_pair
            (Value.support_openAt_subset v d u)
            (Term.support_openAt_subset e₁ d u))
          (Term.support_openAt_subset e₂ d u)

end


mutual

  theorem Value.locallyClosedAt_closeAt (v : Value) (x : Atom) (d : Nat)
      (closed : v.locallyClosedAt d) :
      (v.closeAt x d).locallyClosedAt (d + 1) := by
    cases v with
    | const c => trivial
    | free y =>
        by_cases same : y = x <;>
          simp [Value.closeAt, Value.locallyClosedAt, same]
    | bound k =>
        change k < d at closed
        change k < d + 1
        omega
    | lam T e =>
        exact Term.locallyClosedAt_closeAt e x (d + 1) closed
    | fix T v =>
        exact Value.locallyClosedAt_closeAt v x (d + 1) closed

  theorem Term.locallyClosedAt_closeAt (e : Term) (x : Atom) (d : Nat)
      (closed : e.locallyClosedAt d) :
      (e.closeAt x d).locallyClosedAt (d + 1) := by
    cases e with
    | ret v => exact Value.locallyClosedAt_closeAt v x d closed
    | letE e₁ e₂ =>
        exact ⟨Term.locallyClosedAt_closeAt e₁ x d closed.1,
          Term.locallyClosedAt_closeAt e₂ x (d + 1) closed.2⟩
    | primitive op v => exact Value.locallyClosedAt_closeAt v x d closed
    | app v₁ v₂ =>
        exact ⟨Value.locallyClosedAt_closeAt v₁ x d closed.1,
          Value.locallyClosedAt_closeAt v₂ x d closed.2⟩
    | matchBool v e₁ e₂ =>
        exact ⟨Value.locallyClosedAt_closeAt v x d closed.1,
          Term.locallyClosedAt_closeAt e₁ x d closed.2.1,
          Term.locallyClosedAt_closeAt e₂ x d closed.2.2⟩

end


mutual

  theorem Value.locallyClosedAt_openAt (v : Value) (d : Nat) (u : Value)
      (body : v.locallyClosedAt (d + 1)) (closed : u.locallyClosed) :
      (v.openAt d u).locallyClosedAt d := by
    cases v with
    | const c => trivial
    | free x => trivial
    | bound k =>
        change k < d + 1 at body
        by_cases same : k = d
        · subst k
          simpa [Value.openAt] using
            Value.locallyClosedAt_mono u closed (Nat.zero_le d)
        · simp only [Value.openAt, same, ↓reduceIte]
          change k < d
          omega
    | lam T e =>
        exact Term.locallyClosedAt_openAt e (d + 1) u body closed
    | fix T v =>
        exact Value.locallyClosedAt_openAt v (d + 1) u body closed

  theorem Term.locallyClosedAt_openAt (e : Term) (d : Nat) (u : Value)
      (body : e.locallyClosedAt (d + 1)) (closed : u.locallyClosed) :
      (e.openAt d u).locallyClosedAt d := by
    cases e with
    | ret v => exact Value.locallyClosedAt_openAt v d u body closed
    | letE e₁ e₂ =>
        exact ⟨Term.locallyClosedAt_openAt e₁ d u body.1 closed,
          Term.locallyClosedAt_openAt e₂ (d + 1) u body.2 closed⟩
    | primitive op v => exact Value.locallyClosedAt_openAt v d u body closed
    | app v₁ v₂ =>
        exact ⟨Value.locallyClosedAt_openAt v₁ d u body.1 closed,
          Value.locallyClosedAt_openAt v₂ d u body.2 closed⟩
    | matchBool v e₁ e₂ =>
        exact ⟨Value.locallyClosedAt_openAt v d u body.1 closed,
          Term.locallyClosedAt_openAt e₁ d u body.2.1 closed,
          Term.locallyClosedAt_openAt e₂ d u body.2.2 closed⟩

end


namespace LogicVar

/-- Open a finite consecutive family of logical keys, beginning at `k`. -/
def openManyAt (k : Nat) : (d : Nat) → (Fin d → Atom) → LogicVar → LogicVar
  | 0, _, ξ => ξ
  | d + 1, η, ξ => openBinder (k + d) (η (Fin.last d))
      (openManyAt k d (fun i => η i.castSucc) ξ)

theorem openManyAt_cons (k d : Nat) (x : Atom) (η : Fin d → Atom) (ξ : LogicVar) :
    openManyAt k (d + 1) (Fin.cons x η) ξ =
      openManyAt (k + 1) d η (openBinder k x ξ) := by
  induction d generalizing k ξ with
  | zero => simp [openManyAt]
  | succ d ih =>
      have hη : (fun i : Fin (d + 1) => Fin.cons (α := fun _ => Atom) x η i.castSucc) =
          Fin.cons (α := fun _ => Atom) x (fun i : Fin d => η i.castSucc) := by
        funext i
        refine Fin.cases ?_ (fun j => ?_) i <;> simp
      rw [openManyAt, hη, ih]
      conv_rhs => rw [openManyAt]
      simp only [Fin.cons_last]
      congr 1
      omega

/-- A finite external opening leaves every binder below its cutoff untouched. -/
theorem openManyAt_bound_of_lt (k d : Nat) (η : Fin d → Atom) (j : Nat) (hj : j < k) :
    openManyAt k d η (.bound j) = .bound j := by
  induction d with
  | zero => rfl
  | succ d ih =>
      rw [openManyAt, ih]
      have apart : j ≠ k + d := by omega
      simp [openBinder, swap, apart]

/-- A free key distinct from all selected names is unaffected by finite opening. -/
theorem openManyAt_free_of_apart (k d : Nat) (η : Fin d → Atom) (x : Atom)
    (apart : ∀ i, x ≠ η i) :
    openManyAt k d η (.free x) = .free x := by
  induction d with
  | zero => rfl
  | succ d ih =>
      rw [openManyAt, ih _ (fun i => apart i.castSucc)]
      simp [openBinder, swap, apart (Fin.last d)]

end LogicVar

namespace Value

/-- Name a finite consecutive family of external core-value binders. -/
def openManyAt (k : Nat) : (d : Nat) → (Fin d → Atom) → Value → Value
  | 0, _, v => v
  | d + 1, η, v => (openManyAt k d (fun i => η i.castSucc) v).openAt
      (k + d) (.free (η (Fin.last d)))

end Value

namespace Term

/-- Name a finite consecutive family of external core-term binders. -/
def openManyAt (k : Nat) : (d : Nat) → (Fin d → Atom) → Term → Term
  | 0, _, e => e
  | d + 1, η, e => (openManyAt k d (fun i => η i.castSucc) e).openAt
      (k + d) (.free (η (Fin.last d)))

theorem openManyAt_ret (v : Value) (k d : Nat) (η : Fin d → Atom) :
    (Term.ret v).openManyAt k d η = .ret (v.openManyAt k d η) := by
  induction d with
  | zero => rfl
  | succ d ih => simp [openManyAt, ih, Value.openManyAt, Term.openAt]

theorem openManyAt_cons (e : Term) (k d : Nat) (x : Atom) (η : Fin d → Atom) :
    e.openManyAt k (d + 1) (Fin.cons x η) =
      (e.openAt k (.free x)).openManyAt (k + 1) d η := by
  induction d generalizing k e with
  | zero => simp [openManyAt]
  | succ d ih =>
      have hη : (fun i : Fin (d + 1) => Fin.cons (α := fun _ => Atom) x η i.castSucc) =
          Fin.cons (α := fun _ => Atom) x (fun i : Fin d => η i.castSucc) := by
        funext i
        refine Fin.cases ?_ (fun j => ?_) i <;> simp
      rw [openManyAt, hη, ih]
      conv_rhs => rw [openManyAt]
      simp only [Fin.cons_last]
      congr 1
      omega

/-- Opening a distinct external binder commutes with opening a finite family. -/
theorem openManyAt_openAt_free_comm (e : Term) (k d : Nat) (η : Fin d → Atom)
    (l : Nat) (x : Atom) (apart : ∀ i : Fin d, k + i.val ≠ l) :
    (e.openManyAt k d η).openAt l (.free x) =
      (e.openAt l (.free x)).openManyAt k d η := by
  induction d with
  | zero => rfl
  | succ d ih =>
      rw [openManyAt, Term.openAt_free_comm _ (k + d) l _ x
        (by simpa using apart (Fin.last d)),
        ih (fun i => η i.castSucc) (fun i => by simpa using apart i.castSucc)]
      rfl

/-- Opening all selected external binders leaves exactly the enclosing `n` binders. -/
theorem locallyClosedAt_openManyAt (e : Term) (n d : Nat) (η : Fin d → Atom)
    (closed : e.locallyClosedAt (n + d)) :
    (e.openManyAt n d η).locallyClosedAt n := by
  induction d generalizing e with
  | zero => simpa [openManyAt] using closed
  | succ d ih =>
      rw [openManyAt, openManyAt_openAt_free_comm e n d (fun i => η i.castSucc)
        (n + d) (η (Fin.last d)) (fun i => by omega)]
      exact ih _ (fun i => η i.castSucc) (Term.locallyClosedAt_openAt e (n + d)
        (.free (η (Fin.last d))) closed trivial)

/-- A finite opening adds only the selected names to the term's support. -/
theorem support_openManyAt_subset (e : Term) (k d : Nat) (η : Fin d → Atom) :
    (e.openManyAt k d η).support ⊆ e.support ∪ Finset.univ.image η := by
  induction d with
  | zero => simp [openManyAt]
  | succ d ih =>
      intro x hx
      have h := Term.support_openAt_subset
        (e.openManyAt k d (fun i => η i.castSucc)) (k + d) (.free (η (Fin.last d))) hx
      rcases Finset.mem_union.1 h with h | h
      · rcases Finset.mem_union.1 (ih _ h) with h | h
        · exact Finset.mem_union_left _ h
        · obtain ⟨i, _, rfl⟩ := Finset.mem_image.1 h
          exact Finset.mem_union_right _ (Finset.mem_image.2 ⟨i.castSucc, Finset.mem_univ _, rfl⟩)
      · have hx : x = η (Fin.last d) := by simpa [Value.support] using h
        subst x
        exact Finset.mem_union_right _ (Finset.mem_image.2 ⟨Fin.last d, Finset.mem_univ _, rfl⟩)

/-- An atom absent from both the original term and all selected names stays fresh. -/
theorem fresh_openManyAt (e : Term) (k d : Nat) (η : Fin d → Atom) {x : Atom}
    (fresh : x ∉ e.support) (apart : ∀ i, x ≠ η i) :
    x ∉ (e.openManyAt k d η).support := by
  intro hx
  rcases Finset.mem_union.1 (e.support_openManyAt_subset k d η hx) with hx | hx
  · exact fresh hx
  · obtain ⟨i, _, same⟩ := Finset.mem_image.1 hx
    exact apart i same.symm

/-- A fresh injective opening transports all externally visible term keys. -/
theorem logicSupportAt_openManyAt (e : Term) (n k d : Nat) (η : Fin d → Atom)
    (inj : Function.Injective η) (fresh : ∀ i, η i ∉ e.support) :
    (e.openManyAt (k + n) d η).logicSupportAt n =
      (e.logicSupportAt n).image (LogicVar.openManyAt k d η) := by
  induction d with
  | zero => simp [openManyAt, LogicVar.openManyAt]
  | succ d ih =>
      have freshLast : η (Fin.last d) ∉
          (e.openManyAt (k + n) d (fun i => η i.castSucc)).support := by
        intro hx
        rcases Finset.mem_union.1 (support_openManyAt_subset e (k + n) d _ hx) with hx | hx
        · exact fresh (Fin.last d) hx
        · obtain ⟨i, _, hi⟩ := Finset.mem_image.1 hx
          have same := inj hi
          have := congrArg Fin.val same
          simp at this
          omega
      rw [openManyAt, show k + n + d = (k + d) + n by omega,
        Term.logicSupportAt_openAt _ n (k + d) _ freshLast,
        ih (fun i : Fin d => η i.castSucc)
          (fun i j h => Fin.castSucc_injective d (inj h)) (fun i => fresh i.castSucc)]
      simp only [LogicVar.openSupport, Finset.image_image]
      rfl

end Term

namespace Value

/-- Finite opening eliminates external value binders without capturing internal ones. -/
theorem locallyClosedAt_openManyAt (v : Value) (n d : Nat) (η : Fin d → Atom)
    (closed : v.locallyClosedAt (n + d)) :
    (v.openManyAt n d η).locallyClosedAt n := by
  have h := Term.locallyClosedAt_openManyAt (.ret v) n d η closed
  simpa only [Term.openManyAt_ret, Term.locallyClosedAt] using h

theorem openManyAt_lam (T : SimpleType) (e : Term) (k d : Nat) (η : Fin d → Atom) :
    (Value.lam T e).openManyAt k d η = .lam T (e.openManyAt (k + 1) d η) := by
  induction d with
  | zero => rfl
  | succ d ih =>
      simp [openManyAt, Value.openAt, ih, Term.openManyAt,
        Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

theorem openManyAt_fix (T : SimpleType) (v : Value) (k d : Nat) (η : Fin d → Atom) :
    (Value.fix T v).openManyAt k d η = .fix T (v.openManyAt (k + 1) d η) := by
  induction d with
  | zero => rfl
  | succ d ih =>
      simp [openManyAt, Value.openAt, ih, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

end Value

end ContextTypes
