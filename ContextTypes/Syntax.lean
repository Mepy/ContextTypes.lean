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

  /-- Every bound occurrence in a value is below the ambient binder depth. -/
  def Value.LocallyClosedAt (d : Nat) : Value → Prop
    | .const _ => True
    | .free _ => True
    | .bound k => k < d
    | .lam _ e => e.LocallyClosedAt (d + 1)
    | .fix _ v => v.LocallyClosedAt (d + 1)

  /-- Every bound occurrence in a term is below the ambient binder depth. -/
  def Term.LocallyClosedAt (d : Nat) : Term → Prop
    | .ret v => v.LocallyClosedAt d
    | .letE e₁ e₂ => e₁.LocallyClosedAt d ∧ e₂.LocallyClosedAt (d + 1)
    | .primitive _ v => v.LocallyClosedAt d
    | .app v₁ v₂ => v₁.LocallyClosedAt d ∧ v₂.LocallyClosedAt d
    | .matchBool v e₁ e₂ =>
        v.LocallyClosedAt d ∧ e₁.LocallyClosedAt d ∧ e₂.LocallyClosedAt d

end

namespace Value

/-- A value with no dangling bound variables. -/
abbrev LocallyClosed (v : Value) : Prop :=
  v.LocallyClosedAt 0

end Value

namespace Term

/-- A term with no dangling bound variables. -/
abbrev LocallyClosed (e : Term) : Prop :=
  e.LocallyClosedAt 0

end Term

end ContextTypes
