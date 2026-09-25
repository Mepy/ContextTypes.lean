import ContextTypes.Qualifier
import Mathlib.Data.Finmap
import Mathlib.Tactic

set_option autoImplicit false

namespace ContextTypes

/-!
# Context types and bunched contexts

This module owns the syntax below the typing judgments: over- and
underapproximate context types, bunched contexts, locally nameless operations,
support, and erasure to the simple core language.
-/

/-- Context types.  Arrow and wand bind one logical result variable in their
codomain; each base qualifier has its own result binder. -/
inductive ContextType where
  | over (b : BaseType) (q : Qualifier)
  | under (b : BaseType) (q : Qualifier)
  | inter (τ₁ τ₂ : ContextType)
  | union (τ₁ τ₂ : ContextType)
  | sum (τ₁ τ₂ : ContextType)
  | arrow (τ₁ τ₂ : ContextType)
  | wand (τ₁ τ₂ : ContextType)
  | persist (τ : ContextType)

/-- Bunched contexts of context types. -/
inductive Context where
  | empty
  | bind (x : Atom) (τ : ContextType)
  | comma (Γ₁ Γ₂ : Context)
  | star (Γ₁ Γ₂ : Context)
  | sum (Γ₁ Γ₂ : Context)

namespace LogicVar

/-- Remove `d` enclosing binders and rebase the remaining bound index. -/
def atDepth (d : Nat) : LogicVar → Option LogicVar
  | .free x => some (.free x)
  | .bound k => if d ≤ k then some (.bound (k - d)) else none

/-- Apply `atDepth` to a finite support. -/
def supportAtDepth (d : Nat) (X : Finset LogicVar) : Finset LogicVar :=
  X.biUnion fun ξ =>
    match atDepth d ξ with
    | some ζ => {ζ}
    | none => ∅

@[simp] theorem supportAtDepth_empty (d : Nat) :
    supportAtDepth d ∅ = ∅ := by
  simp [supportAtDepth]

theorem free_mem_supportAtDepth_iff (d : Nat) (X : Finset LogicVar)
    (x : Atom) :
    LogicVar.free x ∈ supportAtDepth d X ↔ LogicVar.free x ∈ X := by
  constructor
  · intro hx
    obtain ⟨ξ, hξ, hxξ⟩ := Finset.mem_biUnion.1 hx
    cases ξ with
    | bound k =>
        by_cases hdk : d ≤ k <;> simp [atDepth, hdk] at hxξ
    | free y =>
        simp only [atDepth, Finset.mem_singleton] at hxξ
        cases hxξ
        exact hξ
  · intro hx
    apply Finset.mem_biUnion.2
    exact ⟨.free x, hx, by simp [atDepth]⟩

end LogicVar

namespace ContextType

/-- Logical-variable support visible outside `d` enclosing binders. -/
def supportAt : ContextType → Nat → Finset LogicVar
  | .over _ q, d | .under _ q, d =>
      LogicVar.supportAtDepth (d + 1) q.support
  | .inter τ₁ τ₂, d | .union τ₁ τ₂, d | .sum τ₁ τ₂, d =>
      τ₁.supportAt d ∪ τ₂.supportAt d
  | .arrow τ₁ τ₂, d | .wand τ₁ τ₂, d =>
      τ₁.supportAt d ∪ τ₂.supportAt (d + 1)
  | .persist τ, d => τ.supportAt d

/-- Free logical-variable support of a context type. -/
abbrev support (τ : ContextType) : Finset LogicVar :=
  τ.supportAt 0

/-- Free program atoms mentioned by a context type. -/
def freeAtoms : ContextType → Finset Atom
  | .over _ q | .under _ q => q.freeAtoms
  | .inter τ₁ τ₂ | .union τ₁ τ₂ | .sum τ₁ τ₂
  | .arrow τ₁ τ₂ | .wand τ₁ τ₂ =>
      τ₁.freeAtoms ∪ τ₂.freeAtoms
  | .persist τ => τ.freeAtoms

theorem free_mem_supportAt_iff (τ : ContextType) (d : Nat) (x : Atom) :
    LogicVar.free x ∈ τ.supportAt d ↔ x ∈ τ.freeAtoms := by
  induction τ generalizing d <;>
    simp_all [supportAt, freeAtoms, LogicVar.free_mem_supportAtDepth_iff,
      Qualifier.mem_freeAtoms_iff]

theorem free_mem_support_iff (τ : ContextType) (x : Atom) :
    LogicVar.free x ∈ τ.support ↔ x ∈ τ.freeAtoms :=
  free_mem_supportAt_iff τ 0 x

/-- Open context-type binder `k` with atom `x`. -/
def openAt : ContextType → Nat → Atom → ContextType
  | .over b q, k, x => .over b (q.openAt (k + 1) x)
  | .under b q, k, x => .under b (q.openAt (k + 1) x)
  | .inter τ₁ τ₂, k, x => .inter (τ₁.openAt k x) (τ₂.openAt k x)
  | .union τ₁ τ₂, k, x => .union (τ₁.openAt k x) (τ₂.openAt k x)
  | .sum τ₁ τ₂, k, x => .sum (τ₁.openAt k x) (τ₂.openAt k x)
  | .arrow τ₁ τ₂, k, x => .arrow (τ₁.openAt k x) (τ₂.openAt (k + 1) x)
  | .wand τ₁ τ₂, k, x => .wand (τ₁.openAt k x) (τ₂.openAt (k + 1) x)
  | .persist τ, k, x => .persist (τ.openAt k x)

/-- Open the outermost context-type binder. -/
abbrev openOuter (τ : ContextType) (x : Atom) : ContextType :=
  τ.openAt 0 x

/-- Shift context-type binders at or above `k`. -/
def shiftFrom : ContextType → Nat → ContextType
  | .over b q, k => .over b (q.shiftFrom (k + 1))
  | .under b q, k => .under b (q.shiftFrom (k + 1))
  | .inter τ₁ τ₂, k => .inter (τ₁.shiftFrom k) (τ₂.shiftFrom k)
  | .union τ₁ τ₂, k => .union (τ₁.shiftFrom k) (τ₂.shiftFrom k)
  | .sum τ₁ τ₂, k => .sum (τ₁.shiftFrom k) (τ₂.shiftFrom k)
  | .arrow τ₁ τ₂, k => .arrow (τ₁.shiftFrom k) (τ₂.shiftFrom (k + 1))
  | .wand τ₁ τ₂, k => .wand (τ₁.shiftFrom k) (τ₂.shiftFrom (k + 1))
  | .persist τ, k => .persist (τ.shiftFrom k)

/-- Substitute a finite logical-variable assignment. -/
def substitute : ContextType → Assignment → ContextType
  | .over b q, ρ => .over b (q.substitute ρ)
  | .under b q, ρ => .under b (q.substitute ρ)
  | .inter τ₁ τ₂, ρ => .inter (τ₁.substitute ρ) (τ₂.substitute ρ)
  | .union τ₁ τ₂, ρ => .union (τ₁.substitute ρ) (τ₂.substitute ρ)
  | .sum τ₁ τ₂, ρ => .sum (τ₁.substitute ρ) (τ₂.substitute ρ)
  | .arrow τ₁ τ₂, ρ => .arrow (τ₁.substitute ρ) (τ₂.substitute ρ)
  | .wand τ₁ τ₂, ρ => .wand (τ₁.substitute ρ) (τ₂.substitute ρ)
  | .persist τ, ρ => .persist (τ.substitute ρ)

/-- Swap two free atoms in all embedded qualifiers. -/
def swap : ContextType → Atom → Atom → ContextType
  | .over b q, x, y => .over b (q.swap x y)
  | .under b q, x, y => .under b (q.swap x y)
  | .inter τ₁ τ₂, x, y => .inter (τ₁.swap x y) (τ₂.swap x y)
  | .union τ₁ τ₂, x, y => .union (τ₁.swap x y) (τ₂.swap x y)
  | .sum τ₁ τ₂, x, y => .sum (τ₁.swap x y) (τ₂.swap x y)
  | .arrow τ₁ τ₂, x, y => .arrow (τ₁.swap x y) (τ₂.swap x y)
  | .wand τ₁ τ₂, x, y => .wand (τ₁.swap x y) (τ₂.swap x y)
  | .persist τ, x, y => .persist (τ.swap x y)

/-- Erase refinements and bunched structure to a simple type. -/
def erase : ContextType → SimpleType
  | .over b _ | .under b _ => .base b
  | .inter τ _ | .union τ _ | .sum τ _ => τ.erase
  | .arrow τ₁ τ₂ | .wand τ₁ τ₂ => .arrow τ₁.erase τ₂.erase
  | .persist τ => τ.erase

/-- Lift a simple type to an unconstrained overapproximate context type. -/
def lift : SimpleType → ContextType
  | .base b => .over b Qualifier.top
  | .arrow T U => .arrow (lift T) (lift U)

/-- Exact over/under refinement at one base type. -/
def precise (b : BaseType) (q : Qualifier) : ContextType :=
  .inter (.over b q) (.under b q)

@[simp] theorem erase_openAt (τ : ContextType) (k : Nat) (x : Atom) :
    (τ.openAt k x).erase = τ.erase := by
  induction τ generalizing k <;> simp_all [openAt, erase]

@[simp] theorem erase_shiftFrom (τ : ContextType) (k : Nat) :
    (τ.shiftFrom k).erase = τ.erase := by
  induction τ generalizing k <;> simp_all [shiftFrom, erase]

@[simp] theorem freeAtoms_shiftFrom (τ : ContextType) (k : Nat) :
    (τ.shiftFrom k).freeAtoms = τ.freeAtoms := by
  induction τ generalizing k <;> simp_all [shiftFrom, freeAtoms]

@[simp] theorem erase_substitute (τ : ContextType) (ρ : Assignment) :
    (τ.substitute ρ).erase = τ.erase := by
  induction τ <;> simp_all [substitute, erase]

@[simp] theorem erase_swap (τ : ContextType) (x y : Atom) :
    (τ.swap x y).erase = τ.erase := by
  induction τ <;> simp_all [swap, erase]

@[simp] theorem erase_lift (T : SimpleType) : erase (lift T) = T := by
  induction T <;> simp_all [lift, erase]

@[simp] theorem freeAtoms_lift (T : SimpleType) :
    (lift T).freeAtoms = ∅ := by
  induction T <;>
    simp_all [lift, freeAtoms, Qualifier.freeAtoms, LogicVar.freeAtoms]

@[simp] theorem supportAt_lift (T : SimpleType) (d : Nat) :
    (lift T).supportAt d = ∅ := by
  induction T generalizing d <;>
    simp_all [lift, supportAt, Qualifier.top, Qualifier.topOn,
      LogicVar.supportAtDepth, LogicVar.atDepth]

@[simp] theorem support_lift (T : SimpleType) :
    (lift T).support = ∅ := supportAt_lift T 0

@[simp] theorem substitute_empty (τ : ContextType) :
    τ.substitute ∅ = τ := by
  induction τ <;> simp_all [substitute]

@[simp] theorem swap_involutive (τ : ContextType) (x y : Atom) :
    (τ.swap x y).swap x y = τ := by
  induction τ <;> simp_all [swap]

end ContextType

/-! ## Paper-facing base qualifiers -/

mutual

  /-- Logical variables mentioned by a value when it occurs inside a
  qualifier. -/
  def Value.logicalSupport : Value → Finset LogicVar
    | .const _ => ∅
    | .free x => {.free x}
    | .bound k => {.bound k}
    | .lam _ e => e.logicalSupport
    | .fix _ v => v.logicalSupport

  /-- Logical variables mentioned by a term embedded in a qualifier value. -/
  def Term.logicalSupport : Term → Finset LogicVar
    | .ret v => v.logicalSupport
    | .letE e₁ e₂ => e₁.logicalSupport ∪ e₂.logicalSupport
    | .primitive _ v => v.logicalSupport
    | .app v₁ v₂ => v₁.logicalSupport ∪ v₂.logicalSupport
    | .matchBool v e₁ e₂ =>
        v.logicalSupport ∪ e₁.logicalSupport ∪ e₂.logicalSupport

end

namespace Value

/-- Interpret a value as a logical-variable expression in an assignment. -/
def denoteAssignment (ρ : Assignment) : Value → Option Value
  | .bound k => ρ.lookup (.bound k)
  | .free x => ρ.lookup (.free x)
  | v@(.const _) | v@(.lam _ _) | v@(.fix _ _) => some v

end Value

namespace Qualifier

/-- Equality between two value expressions. -/
def equal (v w : Value) : Qualifier where
  support := v.logicalSupport ∪ w.logicalSupport
  holds := fun ρ =>
    v.denoteAssignment ρ.assignment = w.denoteAssignment ρ.assignment

/-- A base-specific well-founded measure on constants. -/
def constantMeasure (_b : BaseType) : Constant → Nat
  | .unit => 0
  | .bool false => 0
  | .bool true => 1
  | .nat n => n

/-- Strict decrease between two base-typed value expressions. -/
def lessThanBase (b : BaseType) (v w : Value) : Qualifier where
  support := v.logicalSupport ∪ w.logicalSupport
  holds := fun ρ => ∃ c₁ c₂,
    v.denoteAssignment ρ.assignment = some (.const c₁) ∧
    w.denoteAssignment ρ.assignment = some (.const c₂) ∧
    constantMeasure b c₁ < constantMeasure b c₂

end Qualifier

namespace ContextType

/-- Precise type of one constant. -/
def constantPrecise (c : Constant) : ContextType :=
  precise c.baseType (Qualifier.equal (.bound 0) (.const c))

/-- Precise Boolean singleton type. -/
def boolPrecise (b : Bool) : ContextType :=
  constantPrecise (.bool b)

/-- Unary primitive signature with an overapproximate argument and precise
result. -/
def primitiveType (b₁ : BaseType) (q₁ : Qualifier)
    (b₂ : BaseType) (q₂ : Qualifier) : ContextType :=
  .arrow (.over b₁ q₁) (precise b₂ q₂)

/-- Type of the recursive call exposed in a fixed-point body. -/
def recursiveCall (b : BaseType) (x : Atom) (τ₁ τ₂ : ContextType) :
    ContextType :=
  .arrow (.inter τ₁ (.over b (Qualifier.lessThanBase b (.bound 0) (.free x)))) τ₂

end ContextType

/-! ## Erased environments -/

/-- A finite erased typing environment. -/
def BasicEnv := Finmap (fun _ : Atom => SimpleType)

namespace BasicEnv

instance : EmptyCollection BasicEnv :=
  inferInstanceAs (EmptyCollection (Finmap (fun _ : Atom => SimpleType)))

instance : DecidableEq BasicEnv :=
  inferInstanceAs (DecidableEq (Finmap (fun _ : Atom => SimpleType)))

def domain (Δ : BasicEnv) : Finset Atom :=
  (show Finmap (fun _ : Atom => SimpleType) from Δ).keys

def lookup (Δ : BasicEnv) (x : Atom) : Option SimpleType :=
  (show Finmap (fun _ : Atom => SimpleType) from Δ).lookup x

def singleton (x : Atom) (T : SimpleType) : BasicEnv :=
  Finmap.singleton x T

def merge (Δ₁ Δ₂ : BasicEnv) : BasicEnv :=
  Finmap.union Δ₁ Δ₂

/-- Restrict an erased environment to a finite atom set. -/
def restrict (Δ : BasicEnv) (X : Finset Atom) : BasicEnv :=
  Finmap.keysLookupEquiv.symm
    ⟨(Δ.domain ∩ X, fun x => if x ∈ X then Δ.lookup x else none), by
      intro x
      by_cases hx : x ∈ X
      · simp only [hx, if_pos, Finset.mem_inter, and_true]
        exact Finmap.lookup_isSome.trans Finmap.mem_keys.symm
      · simp [hx]⟩

@[simp] theorem domain_empty : domain (∅ : BasicEnv) = ∅ :=
  rfl

@[simp] theorem domain_singleton (x : Atom) (T : SimpleType) :
    (singleton x T).domain = {x} :=
  Finmap.keys_singleton x T

@[simp] theorem domain_merge (Δ₁ Δ₂ : BasicEnv) :
    (Δ₁.merge Δ₂).domain = Δ₁.domain ∪ Δ₂.domain :=
  Finmap.keys_union

@[simp] theorem domain_restrict (Δ : BasicEnv) (X : Finset Atom) :
    (Δ.restrict X).domain = Δ.domain ∩ X :=
  Finmap.keysLookupEquiv_symm_apply_keys _

@[simp] theorem lookup_empty (x : Atom) : lookup (∅ : BasicEnv) x = none :=
  Finmap.lookup_empty x

@[simp] theorem lookup_singleton (x : Atom) (T : SimpleType) :
    (singleton x T).lookup x = some T :=
  Finmap.lookup_singleton_eq

@[simp] theorem lookup_restrict (Δ : BasicEnv) (X : Finset Atom) (x : Atom) :
    (Δ.restrict X).lookup x = if x ∈ X then Δ.lookup x else none :=
  Finmap.keysLookupEquiv_symm_apply_lookup _ _

theorem restrict_restrict (Δ : BasicEnv) (X Y : Finset Atom) :
    (Δ.restrict X).restrict Y = Δ.restrict (X ∩ Y) := by
  apply Finmap.ext_lookup
  intro x
  change ((Δ.restrict X).restrict Y).lookup x =
    (Δ.restrict (X ∩ Y)).lookup x
  simp only [lookup_restrict]
  by_cases hx : x ∈ X <;> by_cases hy : x ∈ Y <;> simp [hx, hy]

@[simp] theorem restrict_empty (Δ : BasicEnv) : Δ.restrict ∅ = ∅ := by
  apply Finmap.ext_lookup
  intro x
  change (Δ.restrict ∅).lookup x = (∅ : BasicEnv).lookup x
  simp

theorem restrict_eq_self (Δ : BasicEnv) {X : Finset Atom}
    (h : Δ.domain ⊆ X) : Δ.restrict X = Δ := by
  apply Finmap.ext_lookup
  intro x
  change (Δ.restrict X).lookup x = Δ.lookup x
  rw [lookup_restrict]
  by_cases hx : x ∈ X
  · simp [hx]
  · have absent : Δ.lookup x = none := by
      apply Finmap.lookup_eq_none.2
      exact fun hdom => hx (h hdom)
    simp [hx, absent]

@[simp] theorem restrict_domain_self (Δ : BasicEnv) :
    Δ.restrict Δ.domain = Δ :=
  restrict_eq_self Δ Finset.Subset.rfl

end BasicEnv

namespace Context

/-- Program atoms bound by a bunched context. -/
def domain : Context → Finset Atom
  | .empty => ∅
  | .bind x _ => {x}
  | .comma Γ₁ Γ₂ | .star Γ₁ Γ₂ | .sum Γ₁ Γ₂ => Γ₁.domain ∪ Γ₂.domain

/-- Free program atoms mentioned by context types, respecting comma scope. -/
def freeAtoms : Context → Finset Atom
  | .empty => ∅
  | .bind _ τ => τ.freeAtoms
  | .comma Γ₁ Γ₂ => Γ₁.freeAtoms ∪ (Γ₂.freeAtoms \ Γ₁.domain)
  | .star Γ₁ Γ₂ | .sum Γ₁ Γ₂ => Γ₁.freeAtoms ∪ Γ₂.freeAtoms

/-- All atoms that must remain fresh for a context. -/
def support : Context → Finset Atom
  | .empty => ∅
  | .bind x τ => {x} ∪ τ.freeAtoms
  | .comma Γ₁ Γ₂ | .star Γ₁ Γ₂ | .sum Γ₁ Γ₂ =>
      Γ₁.support ∪ Γ₂.support

/-- Substitute a logical assignment through all types in a context. -/
def substitute : Context → Assignment → Context
  | .empty, _ => .empty
  | .bind x τ, ρ => .bind x (τ.substitute ρ)
  | .comma Γ₁ Γ₂, ρ => .comma (Γ₁.substitute ρ) (Γ₂.substitute ρ)
  | .star Γ₁ Γ₂, ρ => .star (Γ₁.substitute ρ) (Γ₂.substitute ρ)
  | .sum Γ₁ Γ₂, ρ => .sum (Γ₁.substitute ρ) (Γ₂.substitute ρ)

/-- Erase all context types.  Additive branches are required by
well-formedness to erase identically, so erasure takes the left branch. -/
def erase : Context → BasicEnv
  | .empty => ∅
  | .bind x τ => BasicEnv.singleton x τ.erase
  | .comma Γ₁ Γ₂ | .star Γ₁ Γ₂ => Γ₁.erase.merge Γ₂.erase
  | .sum Γ₁ _ => Γ₁.erase

theorem support_eq_freeAtoms_union_domain (Γ : Context) :
    Γ.support = Γ.freeAtoms ∪ Γ.domain := by
  induction Γ with
  | empty => simp [support, freeAtoms, domain]
  | bind x τ => simp [support, freeAtoms, domain, Finset.union_comm]
  | comma Γ₁ Γ₂ ih₁ ih₂ =>
      simp only [support, freeAtoms, domain, ih₁, ih₂]
      ext x
      simp only [Finset.mem_union, Finset.mem_sdiff]
      tauto
  | star Γ₁ Γ₂ ih₁ ih₂ | sum Γ₁ Γ₂ ih₁ ih₂ =>
      simp only [support, freeAtoms, domain, ih₁, ih₂]
      ext x
      simp only [Finset.mem_union]
      tauto

@[simp] theorem substitute_empty (Γ : Context) : Γ.substitute ∅ = Γ := by
  induction Γ <;> simp_all [substitute]

@[simp] theorem erase_substitute (Γ : Context) (ρ : Assignment) :
    (Γ.substitute ρ).erase = Γ.erase := by
  induction Γ <;> simp_all [substitute, erase]

end Context

end ContextTypes
