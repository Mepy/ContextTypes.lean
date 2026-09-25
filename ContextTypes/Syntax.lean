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
  | bound (index : Nat)
  | free (name : Atom)
  deriving DecidableEq, Repr

namespace LogicVar

/-- Swap two logical variables.  Logical-variable opening is represented by
such a transposition, following the finite-support development. -/
def swap (left right : LogicVar) (target : LogicVar) : LogicVar :=
  if target = left then right
  else if target = right then left
  else target

/-- Open logical binder `index` with the fresh atom `name`.

This operation is deliberately involutive: it swaps the bound and free keys.
The one-sided operation is provided separately for situations where the
inverse action is not wanted. -/
def openBinder (index : Nat) (name : Atom) : LogicVar → LogicVar :=
  swap (.bound index) (.free name)

/-- Replace one bound logical variable by a free variable. -/
def openOneSided (index : Nat) (name : Atom) : LogicVar → LogicVar
  | .bound other => if other = index then .free name else .bound other
  | .free other => .free other

/-- The free-atom support of a logical variable. -/
def freeAtoms : LogicVar → Finset Atom
  | .bound _ => ∅
  | .free name => {name}

/-- Shift every bound logical variable by `amount`. -/
def shift (amount : Nat) : LogicVar → LogicVar
  | .bound index => .bound (amount + index)
  | .free name => .free name

@[simp] theorem swap_left (left right : LogicVar) :
    swap left right left = right := by
  simp [swap]

@[simp] theorem swap_right (left right : LogicVar) :
    swap left right right = left := by
  by_cases same : right = left
  · subst right
    simp [swap]
  · simp [swap, same]

@[simp] theorem swap_involutive (left right target : LogicVar) :
    swap left right (swap left right target) = target := by
  by_cases target = left <;> by_cases target = right <;>
    simp_all [swap]

@[simp] theorem open_involutive (index : Nat) (name : Atom)
    (target : LogicVar) :
    openBinder index name (openBinder index name target) = target := by
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
  | base (type : BaseType)
  | arrow (domain codomain : SimpleType)
  deriving DecidableEq, Repr

/-- Core-language constants. -/
inductive Constant where
  | unit
  | bool (value : Bool)
  | nat (value : Nat)
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
    | const (constant : Constant)
    | free (name : Atom)
    | bound (index : Nat)
    | lam (domain : SimpleType) (body : Term)
    /-- HATs-style fixed point.  Index zero is the ordinary argument; after
    opening it, `body` is expected to accept the recursive self reference. -/
    | fix (functionType : SimpleType) (body : Value)
    deriving DecidableEq, Repr

  /-- Core call-by-value terms. -/
  inductive Term where
    | ret (value : Value)
    | letE (bound body : Term)
    | primitive (operation : Primitive) (argument : Value)
    | app (function argument : Value)
    | matchBool (discriminant : Value) (ifTrue ifFalse : Term)
    deriving DecidableEq, Repr

end

mutual

  /-- Open de Bruijn index `depth` in a value. -/
  def Value.openAt : Value → Nat → Value → Value
    | .const constant, _, _ => .const constant
    | .free name, _, _ => .free name
    | .bound index, depth, replacement =>
        if index = depth then replacement else .bound index
    | .lam domain body, depth, replacement =>
        .lam domain (body.openAt (depth + 1) replacement)
    | .fix functionType body, depth, replacement =>
        .fix functionType (body.openAt (depth + 1) replacement)

  /-- Open de Bruijn index `depth` in a term. -/
  def Term.openAt : Term → Nat → Value → Term
    | .ret value, depth, replacement => .ret (value.openAt depth replacement)
    | .letE bound body, depth, replacement =>
        .letE (bound.openAt depth replacement)
          (body.openAt (depth + 1) replacement)
    | .primitive operation argument, depth, replacement =>
        .primitive operation (argument.openAt depth replacement)
    | .app function argument, depth, replacement =>
        .app (function.openAt depth replacement)
          (argument.openAt depth replacement)
    | .matchBool discriminant ifTrue ifFalse, depth, replacement =>
        .matchBool (discriminant.openAt depth replacement)
          (ifTrue.openAt depth replacement) (ifFalse.openAt depth replacement)

end

namespace Value

/-- Open the outermost binder in a value. -/
abbrev openOuter (value replacement : Value) : Value :=
  value.openAt 0 replacement

end Value

namespace Term

/-- Open the outermost binder in a term. -/
abbrev openOuter (term : Term) (replacement : Value) : Term :=
  term.openAt 0 replacement

end Term

mutual

  /-- Close free atom `name` as de Bruijn index `depth` in a value. -/
  def Value.closeAt : Value → Atom → Nat → Value
    | .const constant, _, _ => .const constant
    | .free other, name, depth =>
        if other = name then .bound depth else .free other
    | .bound index, _, _ => .bound index
    | .lam domain body, name, depth =>
        .lam domain (body.closeAt name (depth + 1))
    | .fix functionType body, name, depth =>
        .fix functionType (body.closeAt name (depth + 1))

  /-- Close free atom `name` as de Bruijn index `depth` in a term. -/
  def Term.closeAt : Term → Atom → Nat → Term
    | .ret value, name, depth => .ret (value.closeAt name depth)
    | .letE bound body, name, depth =>
        .letE (bound.closeAt name depth) (body.closeAt name (depth + 1))
    | .primitive operation argument, name, depth =>
        .primitive operation (argument.closeAt name depth)
    | .app function argument, name, depth =>
        .app (function.closeAt name depth) (argument.closeAt name depth)
    | .matchBool discriminant ifTrue ifFalse, name, depth =>
        .matchBool (discriminant.closeAt name depth)
          (ifTrue.closeAt name depth) (ifFalse.closeAt name depth)

end

namespace Value

/-- Close a free atom as the outermost binder in a value. -/
abbrev close (value : Value) (name : Atom) : Value :=
  value.closeAt name 0

end Value

namespace Term

/-- Close a free atom as the outermost binder in a term. -/
abbrev close (term : Term) (name : Atom) : Term :=
  term.closeAt name 0

end Term

mutual

  /-- Capture-avoiding substitution for a free atom in a value. -/
  def Value.substitute : Value → Atom → Value → Value
    | .const constant, _, _ => .const constant
    | .free other, name, replacement =>
        if other = name then replacement else .free other
    | .bound index, _, _ => .bound index
    | .lam domain body, name, replacement =>
        .lam domain (body.substitute name replacement)
    | .fix functionType body, name, replacement =>
        .fix functionType (body.substitute name replacement)

  /-- Capture-avoiding substitution for a free atom in a term. -/
  def Term.substitute : Term → Atom → Value → Term
    | .ret value, name, replacement => .ret (value.substitute name replacement)
    | .letE bound body, name, replacement =>
        .letE (bound.substitute name replacement)
          (body.substitute name replacement)
    | .primitive operation argument, name, replacement =>
        .primitive operation (argument.substitute name replacement)
    | .app function argument, name, replacement =>
        .app (function.substitute name replacement)
          (argument.substitute name replacement)
    | .matchBool discriminant ifTrue ifFalse, name, replacement =>
        .matchBool (discriminant.substitute name replacement)
          (ifTrue.substitute name replacement)
          (ifFalse.substitute name replacement)

end

/-- Swap two free atoms. -/
def swapAtom (left right name : Atom) : Atom :=
  if name = left then right
  else if name = right then left
  else name

mutual

  /-- Swap two free atoms throughout a value. -/
  def Value.swap (left right : Atom) : Value → Value
    | .const constant => .const constant
    | .free name => .free (swapAtom left right name)
    | .bound index => .bound index
    | .lam domain body => .lam domain (body.swap left right)
    | .fix functionType body => .fix functionType (body.swap left right)

  /-- Swap two free atoms throughout a term. -/
  def Term.swap (left right : Atom) : Term → Term
    | .ret value => .ret (value.swap left right)
    | .letE bound body => .letE (bound.swap left right) (body.swap left right)
    | .primitive operation argument =>
        .primitive operation (argument.swap left right)
    | .app function argument =>
        .app (function.swap left right) (argument.swap left right)
    | .matchBool discriminant ifTrue ifFalse =>
        .matchBool (discriminant.swap left right)
          (ifTrue.swap left right) (ifFalse.swap left right)

end

mutual

  /-- Free atoms occurring in a value. -/
  def Value.support : Value → Finset Atom
    | .const _ => ∅
    | .free name => {name}
    | .bound _ => ∅
    | .lam _ body => body.support
    | .fix _ body => body.support

  /-- Free atoms occurring in a term. -/
  def Term.support : Term → Finset Atom
    | .ret value => value.support
    | .letE bound body => bound.support ∪ body.support
    | .primitive _ argument => argument.support
    | .app function argument => function.support ∪ argument.support
    | .matchBool discriminant ifTrue ifFalse =>
        discriminant.support ∪ ifTrue.support ∪ ifFalse.support

end

/-- The externally visible logical-variable key for a bound occurrence at a
given binder cutoff. -/
def boundLogicSupportAt (cutoff index : Nat) : Finset LogicVar :=
  if cutoff ≤ index then {.bound (index - cutoff)} else ∅

mutual

  /-- Logical-variable support of a value, relative to a binder cutoff. -/
  def Value.logicSupportAt (cutoff : Nat) : Value → Finset LogicVar
    | .const _ => ∅
    | .free name => {.free name}
    | .bound index => boundLogicSupportAt cutoff index
    | .lam _ body => body.logicSupportAt (cutoff + 1)
    | .fix _ body => body.logicSupportAt (cutoff + 1)

  /-- Logical-variable support of a term, relative to a binder cutoff. -/
  def Term.logicSupportAt (cutoff : Nat) : Term → Finset LogicVar
    | .ret value => value.logicSupportAt cutoff
    | .letE bound body =>
        bound.logicSupportAt cutoff ∪ body.logicSupportAt (cutoff + 1)
    | .primitive _ argument => argument.logicSupportAt cutoff
    | .app function argument =>
        function.logicSupportAt cutoff ∪ argument.logicSupportAt cutoff
    | .matchBool discriminant ifTrue ifFalse =>
        discriminant.logicSupportAt cutoff ∪
          ifTrue.logicSupportAt cutoff ∪ ifFalse.logicSupportAt cutoff

end

namespace Value

/-- Logical-variable support at the outermost level. -/
abbrev logicSupport (value : Value) : Finset LogicVar :=
  value.logicSupportAt 0

end Value

namespace Term

/-- Logical-variable support at the outermost level. -/
abbrev logicSupport (term : Term) : Finset LogicVar :=
  term.logicSupportAt 0

end Term

mutual

  /-- Every bound occurrence in a value is below the ambient binder depth. -/
  def Value.LocallyClosedAt (depth : Nat) : Value → Prop
    | .const _ => True
    | .free _ => True
    | .bound index => index < depth
    | .lam _ body => body.LocallyClosedAt (depth + 1)
    | .fix _ body => body.LocallyClosedAt (depth + 1)

  /-- Every bound occurrence in a term is below the ambient binder depth. -/
  def Term.LocallyClosedAt (depth : Nat) : Term → Prop
    | .ret value => value.LocallyClosedAt depth
    | .letE bound body =>
        bound.LocallyClosedAt depth ∧ body.LocallyClosedAt (depth + 1)
    | .primitive _ argument => argument.LocallyClosedAt depth
    | .app function argument =>
        function.LocallyClosedAt depth ∧ argument.LocallyClosedAt depth
    | .matchBool discriminant ifTrue ifFalse =>
        discriminant.LocallyClosedAt depth ∧
          ifTrue.LocallyClosedAt depth ∧ ifFalse.LocallyClosedAt depth

end

namespace Value

/-- A value with no dangling bound variables. -/
abbrev LocallyClosed (value : Value) : Prop :=
  value.LocallyClosedAt 0

end Value

namespace Term

/-- A term with no dangling bound variables. -/
abbrev LocallyClosed (term : Term) : Prop :=
  term.LocallyClosedAt 0

end Term

end ContextTypes
