import ContextTypes.Capability
import ContextTypes.Qualifier
import Mathlib.Tactic

set_option autoImplicit false

namespace ContextTypes

/-!
# Context logic

Formulas are locally nameless and interpreted over contextual capabilities.
Satisfaction first projects a capability to the free atoms observed by the
formula; this makes the finite-support invariant explicit.
-/

namespace Store

/-- Lift an atom-keyed store to a logical assignment on free variables. -/
def toAssignment (σ : Store) : Assignment :=
  Finmap.keysLookupEquiv.symm
    ⟨(σ.domain.image LogicVar.free,
      fun ξ =>
        match ξ with
        | .bound _ => none
        | .free x => σ.lookup x),
      by
        intro ξ
        cases ξ with
        | bound k => simp
        | free x => simp [Store.mem_domain_iff, Option.isSome_iff_exists]⟩

@[simp] theorem toAssignment_domain (σ : Store) :
    σ.toAssignment.domain = σ.domain.image LogicVar.free := by
  simp [toAssignment, Assignment.domain]

@[simp] theorem toAssignment_lookup_bound (σ : Store) (k : Nat) :
    σ.toAssignment.lookup (.bound k) = none := by
  simp [toAssignment, Assignment.lookup]

@[simp] theorem toAssignment_lookup_free (σ : Store) (x : Atom) :
    σ.toAssignment.lookup (.free x) = σ.lookup x := by
  simp [toAssignment, Assignment.lookup]

end Store

namespace LogicVar

/-- Free program atoms represented by a logical-variable support. -/
def freeAtomSet (X : Finset LogicVar) : Finset Atom :=
  X.biUnion LogicVar.freeAtoms

/-- A support has no dangling bound logical variables. -/
def LocallyClosed (X : Finset LogicVar) : Prop :=
  ∀ k, LogicVar.bound k ∉ X

@[simp] theorem freeAtomSet_empty : freeAtomSet ∅ = ∅ := by
  simp [freeAtomSet]

theorem mem_freeAtomSet_iff (X : Finset LogicVar) (x : Atom) :
    x ∈ freeAtomSet X ↔ LogicVar.free x ∈ X := by
  constructor
  · intro hx
    obtain ⟨ξ, hξ, hxξ⟩ := Finset.mem_biUnion.1 hx
    cases ξ with
    | bound k => simp [LogicVar.freeAtoms] at hxξ
    | free y =>
        simp [LogicVar.freeAtoms] at hxξ
        simpa [hxξ] using hξ
  · intro hx
    exact Finset.mem_biUnion.2 ⟨.free x, hx, by simp [LogicVar.freeAtoms]⟩

end LogicVar

/-- Formulas of context logic.  `wand d P Q` binds `d` logical variables in
both operands; `all P` binds one logical variable in `P`. -/
inductive Formula where
  | top
  | bot
  | atom (q : Qualifier)
  | and (P Q : Formula)
  | or (P Q : Formula)
  | impl (P Q : Formula)
  | star (P Q : Formula)
  | wand (d : Nat) (P Q : Formula)
  | sum (P Q : Formula)
  | all (P : Formula)
  | over (P : Formula)
  | under (P : Formula)
  | persist (P : Formula)
  | fiber (X : Finset LogicVar) (P : Formula)

namespace Formula

/-- Paper-facing one-binder magic wand. -/
abbrev wandOne (P Q : Formula) : Formula :=
  .wand 1 P Q

/-- Paper-facing universal binder.  `x` is a display name; occurrences in
`P` use the locally nameless index `LogicVar.bound 0`. -/
def allNamed (_x : Atom) (P : Formula) : Formula :=
  .all P

set_option hygiene false in
scoped[ContextTypes] notation:max (name := formulaTop) "⊤ᶜ" =>
  ContextTypes.Formula.top

set_option hygiene false in
scoped[ContextTypes] notation:max (name := formulaBot) "⊥ᶜ" =>
  ContextTypes.Formula.bot

set_option hygiene false in
scoped[ContextTypes] notation:max (name := formulaAtom) "Atom(" q ")" =>
  ContextTypes.Formula.atom q

set_option hygiene false in
scoped[ContextTypes] infixr:35 (name := formulaAnd) " ∧ᶜ " =>
  ContextTypes.Formula.and

set_option hygiene false in
scoped[ContextTypes] infixr:30 (name := formulaOr) " ∨ᶜ " =>
  ContextTypes.Formula.or

set_option hygiene false in
scoped[ContextTypes] infixr:25 (name := formulaImpl) " ⇒ᶜ " =>
  ContextTypes.Formula.impl

set_option hygiene false in
scoped[ContextTypes] infixr:40 (name := formulaStar) " ∗ " =>
  ContextTypes.Formula.star

set_option hygiene false in
scoped[ContextTypes] infixr:60 (name := formulaWand) " -∗ " =>
  ContextTypes.Formula.wandOne

set_option hygiene false in
scoped[ContextTypes] notation:60 (name := formulaWandDepth)
    P:61 " -∗[" d "] " Q:60 =>
  ContextTypes.Formula.wand d P Q

set_option hygiene false in
scoped[ContextTypes] notation:25 (name := formulaAll) "∀ " x ", " P:25 =>
  ContextTypes.Formula.allNamed x P

set_option hygiene false in
scoped[ContextTypes] prefix:30 (name := formulaOver) "🄾 " =>
  ContextTypes.Formula.over

set_option hygiene false in
scoped[ContextTypes] prefix:30 (name := formulaUnder) "🅄 " =>
  ContextTypes.Formula.under

set_option hygiene false in
scoped[ContextTypes] infixr:70 (name := formulaSum) " ⊕ " =>
  ContextTypes.Formula.sum

set_option hygiene false in
scoped[ContextTypes] prefix:30 (name := formulaPersist) "□ " =>
  ContextTypes.Formula.persist

open scoped ContextTypes

/-- Remove `d` enclosing binders from one finite logical-variable support. -/
def supportSetAtDepth (d : Nat) (X : Finset LogicVar) : Finset LogicVar :=
  X.biUnion fun ξ =>
    match ξ with
    | .free x => {.free x}
    | .bound k => if d ≤ k then {.bound (k - d)} else ∅

@[simp] theorem supportSetAtDepth_zero (X : Finset LogicVar) :
    supportSetAtDepth 0 X = X := by
  unfold supportSetAtDepth
  calc
    X.biUnion (fun ξ =>
        match ξ with
        | .free x => {.free x}
        | .bound k => if 0 ≤ k then {.bound (k - 0)} else ∅) =
        X.biUnion (fun ξ => {ξ}) := by
          congr 1
          funext ξ
          cases ξ <;> simp
    _ = X := Finset.biUnion_singleton_eq_self

/-- Logical-variable support visible outside `d` enclosing binders. -/
def supportAt : Formula → Nat → Finset LogicVar
  | .top, _ | .bot, _ => ∅
  | .atom q, d => supportSetAtDepth d q.support
  | .and P Q, d | .or P Q, d | .impl P Q, d
  | .star P Q, d | .sum P Q, d => P.supportAt d ∪ Q.supportAt d
  | .wand n P Q, d => P.supportAt (d + n) ∪ Q.supportAt (d + n)
  | .all P, d => P.supportAt (d + 1)
  | .over P, d | .under P, d | .persist P, d => P.supportAt d
  | .fiber X P, d => supportSetAtDepth d X ∪ P.supportAt d

/-- Logical-variable support visible at the outside of a formula. -/
abbrev support (P : Formula) : Finset LogicVar :=
  P.supportAt 0

/-- Free program atoms observed by a formula. -/
def freeAtoms (P : Formula) : Finset Atom :=
  LogicVar.freeAtomSet P.support

@[simp] theorem LogicVar.freeAtomSet_union (X Y : Finset LogicVar) :
    LogicVar.freeAtomSet (X ∪ Y) =
      LogicVar.freeAtomSet X ∪ LogicVar.freeAtomSet Y := by
  ext x
  simp only [LogicVar.freeAtomSet, Finset.mem_biUnion, Finset.mem_union]
  aesop

@[simp] theorem freeAtomSet_supportSetAtDepth (d : Nat)
    (X : Finset LogicVar) :
    ContextTypes.LogicVar.freeAtomSet (supportSetAtDepth d X) =
      ContextTypes.LogicVar.freeAtomSet X := by
  ext x
  rw [ContextTypes.LogicVar.mem_freeAtomSet_iff,
    ContextTypes.LogicVar.mem_freeAtomSet_iff]
  constructor
  · intro hx
    obtain ⟨ξ, hξ, hxξ⟩ := Finset.mem_biUnion.1 hx
    cases ξ with
    | bound k =>
        by_cases hdk : d ≤ k <;> simp [hdk] at hxξ
    | free y =>
        simp only [Finset.mem_singleton] at hxξ
        simpa [hxξ] using hξ
  · intro hx
    exact Finset.mem_biUnion.2
      ⟨.free x, hx, by simp⟩

theorem freeAtomSet_supportAt_eq (P : Formula) (d d' : Nat) :
    ContextTypes.LogicVar.freeAtomSet (P.supportAt d) =
      ContextTypes.LogicVar.freeAtomSet (P.supportAt d') := by
  induction P generalizing d d' with
  | top | bot => rfl
  | atom q => simp [supportAt]
  | and P Q ihP ihQ =>
      simp only [supportAt, LogicVar.freeAtomSet_union]
      rw [ihP d d', ihQ d d']
  | or P Q ihP ihQ =>
      simp only [supportAt, LogicVar.freeAtomSet_union]
      rw [ihP d d', ihQ d d']
  | impl P Q ihP ihQ =>
      simp only [supportAt, LogicVar.freeAtomSet_union]
      rw [ihP d d', ihQ d d']
  | star P Q ihP ihQ =>
      simp only [supportAt, LogicVar.freeAtomSet_union]
      rw [ihP d d', ihQ d d']
  | wand n P Q ihP ihQ =>
      simp only [supportAt, LogicVar.freeAtomSet_union]
      rw [ihP (d + n) (d' + n), ihQ (d + n) (d' + n)]
  | sum P Q ihP ihQ =>
      simp only [supportAt, LogicVar.freeAtomSet_union]
      rw [ihP d d', ihQ d d']
  | all P ihP =>
      exact ihP (d + 1) (d' + 1)
  | «over» P ihP | «under» P ihP | persist P ihP =>
      exact ihP d d'
  | fiber X P ihP =>
      simp only [supportAt, LogicVar.freeAtomSet_union,
        freeAtomSet_supportSetAtDepth]
      rw [ihP d d']

theorem freeAtomSet_supportAt (P : Formula) (d : Nat) :
    ContextTypes.LogicVar.freeAtomSet (P.supportAt d) = P.freeAtoms :=
  freeAtomSet_supportAt_eq P d 0

@[simp] theorem freeAtoms_top : (⊤ᶜ : Formula).freeAtoms = ∅ := by
  simp [freeAtoms, support, supportAt]

@[simp] theorem freeAtoms_bot : (⊥ᶜ : Formula).freeAtoms = ∅ := by
  simp [freeAtoms, support, supportAt]

@[simp] theorem freeAtoms_atom (q : Qualifier) :
    Atom(q).freeAtoms = q.freeAtoms := by
  simp [freeAtoms, support, supportAt, Qualifier.freeAtoms,
    ContextTypes.LogicVar.freeAtomSet]

@[simp] theorem freeAtoms_and (P Q : Formula) :
    (P ∧ᶜ Q).freeAtoms = P.freeAtoms ∪ Q.freeAtoms := by
  simp [freeAtoms, support, supportAt]

@[simp] theorem freeAtoms_or (P Q : Formula) :
    (P ∨ᶜ Q).freeAtoms = P.freeAtoms ∪ Q.freeAtoms := by
  simp [freeAtoms, support, supportAt]

@[simp] theorem freeAtoms_impl (P Q : Formula) :
    (P ⇒ᶜ Q).freeAtoms = P.freeAtoms ∪ Q.freeAtoms := by
  simp [freeAtoms, support, supportAt]

@[simp] theorem freeAtoms_star (P Q : Formula) :
    (P ∗ Q).freeAtoms = P.freeAtoms ∪ Q.freeAtoms := by
  simp [freeAtoms, support, supportAt]

@[simp] theorem freeAtoms_wand (d : Nat) (P Q : Formula) :
    (P -∗[d] Q).freeAtoms = P.freeAtoms ∪ Q.freeAtoms := by
  simp only [freeAtoms, support, supportAt, LogicVar.freeAtomSet_union]
  simp only [Nat.zero_add]
  rw [freeAtomSet_supportAt_eq P d 0,
    freeAtomSet_supportAt_eq Q d 0]

@[simp] theorem freeAtoms_sum (P Q : Formula) :
    (P ⊕ Q).freeAtoms = P.freeAtoms ∪ Q.freeAtoms := by
  simp [freeAtoms, support, supportAt]

@[simp] theorem freeAtoms_all (P : Formula) :
    (Formula.all P).freeAtoms = P.freeAtoms := by
  simp only [freeAtoms, support, supportAt]
  exact freeAtomSet_supportAt_eq P 1 0

@[simp] theorem freeAtoms_over (P : Formula) :
    (🄾 P).freeAtoms = P.freeAtoms := by
  simp [freeAtoms, support, supportAt]

@[simp] theorem freeAtoms_under (P : Formula) :
    (🅄 P).freeAtoms = P.freeAtoms := by
  simp [freeAtoms, support, supportAt]

@[simp] theorem freeAtoms_persist (P : Formula) :
    (□ P).freeAtoms = P.freeAtoms := by
  simp [freeAtoms, support, supportAt]

@[simp] theorem freeAtoms_fiber (X : Finset LogicVar) (P : Formula) :
    (Formula.fiber X P).freeAtoms =
      ContextTypes.LogicVar.freeAtomSet X ∪ P.freeAtoms := by
  simp only [freeAtoms, support, supportAt, LogicVar.freeAtomSet_union,
    freeAtomSet_supportSetAtDepth]

@[simp] theorem LogicVar.freeAtomSet_image_free (X : Finset Atom) :
    ContextTypes.LogicVar.freeAtomSet (X.image LogicVar.free) = X := by
  ext x
  rw [ContextTypes.LogicVar.mem_freeAtomSet_iff]
  simp

@[simp] theorem LogicVar.freeAtomSet_singleton_free (x : Atom) :
    ContextTypes.LogicVar.freeAtomSet {LogicVar.free x} = {x} := by
  ext y
  rw [ContextTypes.LogicVar.mem_freeAtomSet_iff]
  simp

/-- Open logical binder `k` with atom `x`. -/
def openAt : Formula → Nat → Atom → Formula
  | .top, _, _ => .top
  | .bot, _, _ => .bot
  | .atom q, k, x => .atom (q.openAt k x)
  | .and P Q, k, x => .and (P.openAt k x) (Q.openAt k x)
  | .or P Q, k, x => .or (P.openAt k x) (Q.openAt k x)
  | .impl P Q, k, x => .impl (P.openAt k x) (Q.openAt k x)
  | .star P Q, k, x => .star (P.openAt k x) (Q.openAt k x)
  | .wand d P Q, k, x =>
      .wand d (P.openAt (k + d) x) (Q.openAt (k + d) x)
  | .sum P Q, k, x => .sum (P.openAt k x) (Q.openAt k x)
  | .all P, k, x => .all (P.openAt (k + 1) x)
  | .over P, k, x => .over (P.openAt k x)
  | .under P, k, x => .under (P.openAt k x)
  | .persist P, k, x => .persist (P.openAt k x)
  | .fiber X P, k, x =>
      .fiber (LogicVar.openSupport k x X) (P.openAt k x)

/-- Open the outermost logical binder. -/
abbrev openOuter (P : Formula) (x : Atom) : Formula :=
  P.openAt 0 x

/-- Swap two free atoms throughout a formula. -/
def swap : Formula → Atom → Atom → Formula
  | .top, _, _ => .top
  | .bot, _, _ => .bot
  | .atom q, x, y => .atom (q.swap x y)
  | .and P Q, x, y => .and (P.swap x y) (Q.swap x y)
  | .or P Q, x, y => .or (P.swap x y) (Q.swap x y)
  | .impl P Q, x, y => .impl (P.swap x y) (Q.swap x y)
  | .star P Q, x, y => .star (P.swap x y) (Q.swap x y)
  | .wand d P Q, x, y => .wand d (P.swap x y) (Q.swap x y)
  | .sum P Q, x, y => .sum (P.swap x y) (Q.swap x y)
  | .all P, x, y => .all (P.swap x y)
  | .over P, x, y => .over (P.swap x y)
  | .under P, x, y => .under (P.swap x y)
  | .persist P, x, y => .persist (P.swap x y)
  | .fiber X P, x, y =>
      .fiber (X.image (LogicVar.swap (.free x) (.free y))) (P.swap x y)

/-- Instantiate logical variables in a formula. -/
def substitute : Formula → Assignment → Formula
  | .top, _ => .top
  | .bot, _ => .bot
  | .atom q, ρ => .atom (q.substitute ρ)
  | .and P Q, ρ => .and (P.substitute ρ) (Q.substitute ρ)
  | .or P Q, ρ => .or (P.substitute ρ) (Q.substitute ρ)
  | .impl P Q, ρ => .impl (P.substitute ρ) (Q.substitute ρ)
  | .star P Q, ρ => .star (P.substitute ρ) (Q.substitute ρ)
  | .wand d P Q, ρ => .wand d (P.substitute ρ) (Q.substitute ρ)
  | .sum P Q, ρ => .sum (P.substitute ρ) (Q.substitute ρ)
  | .all P, ρ => .all (P.substitute ρ)
  | .over P, ρ => .over (P.substitute ρ)
  | .under P, ρ => .under (P.substitute ρ)
  | .persist P, ρ => .persist (P.substitute ρ)
  | .fiber X P, ρ => .fiber (X \ ρ.domain) (P.substitute ρ)

/-- Instantiate the free variables supplied by an atom-keyed store. -/
def substituteStore (P : Formula) (σ : Store) : Formula :=
  P.substitute σ.toAssignment

/-- Open bound indices `0, ..., d-1` using a canonical finite family. -/
def openMany : (d : Nat) → (Fin d → Atom) → Formula → Formula
  | 0, _, P => P
  | d + 1, η, P =>
      (P.openMany d (fun i => η i.castSucc)).openAt d (η (Fin.last d))

/-- Structural size used to make the recursive satisfaction relation total. -/
def measure : Formula → Nat
  | .top | .bot | .atom _ => 1
  | .and P Q | .or P Q | .impl P Q | .star P Q
  | .wand _ P Q | .sum P Q => 1 + P.measure + Q.measure
  | .all P | .over P | .under P | .persist P | .fiber _ P =>
      1 + P.measure

/-- Structural well-formedness of binder-aware magic wand. -/
def WellFormed : Formula → Prop
  | .top | .bot | .atom _ => True
  | .and P Q | .or P Q | .impl P Q | .star P Q | .sum P Q =>
      P.WellFormed ∧ Q.WellFormed
  | .wand d P Q =>
      P.WellFormed ∧ Q.WellFormed ∧
      LogicVar.freeAtomSet (P.supportAt d) ⊆ Q.freeAtoms
  | .all P | .over P | .under P | .persist P | .fiber _ P => P.WellFormed

/-- Binding reference for one free program atom. -/
def bind (x : Atom) (P : Formula) : Formula :=
  .fiber {LogicVar.free x} P

/-- Binding reference for a finite set of free program atoms. -/
def bindSet (X : Finset Atom) (P : Formula) : Formula :=
  .fiber (X.image LogicVar.free) P

/-- An exact qualifier atom checked independently on every selected fiber. -/
def fiberAtom (q : Qualifier) : Formula :=
  .fiber q.support (.atom q)

set_option hygiene false in
scoped[ContextTypes] notation:55 (name := formulaBind) x:56 " ▷ " P:55 =>
  ContextTypes.Formula.bind x P

set_option hygiene false in
scoped[ContextTypes] notation:55 (name := formulaBindSet) X:56 " ▷ " P:55 =>
  ContextTypes.Formula.bindSet X P

@[simp] theorem freeAtoms_bind (x : Atom) (P : Formula) :
    (x ▷ P).freeAtoms = {x} ∪ P.freeAtoms := by
  simp [bind]

@[simp] theorem freeAtoms_bindSet (X : Finset Atom) (P : Formula) :
    (X ▷ P).freeAtoms = X ∪ P.freeAtoms := by
  simp [bindSet]

@[simp] theorem freeAtoms_fiberAtom (q : Qualifier) :
    (fiberAtom q).freeAtoms = q.freeAtoms := by
  simp [fiberAtom, Qualifier.freeAtoms,
    ContextTypes.LogicVar.freeAtomSet]

@[simp] theorem measure_openAt (P : Formula) (k : Nat) (x : Atom) :
    (P.openAt k x).measure = P.measure := by
  induction P generalizing k <;> simp_all [openAt, measure]

@[simp] theorem measure_substitute (P : Formula) (ρ : Assignment) :
    (P.substitute ρ).measure = P.measure := by
  induction P <;> simp_all [substitute, measure]

@[simp] theorem measure_swap (P : Formula) (x y : Atom) :
    (P.swap x y).measure = P.measure := by
  induction P <;> simp_all [swap, measure]

@[simp] theorem measure_substituteStore (P : Formula) (σ : Store) :
    (P.substituteStore σ).measure = P.measure := by
  simp [substituteStore]

@[simp] theorem measure_openMany (P : Formula) (d : Nat) (η : Fin d → Atom) :
    (P.openMany d η).measure = P.measure := by
  induction d with
  | zero => rfl
  | succ d ih => simp [openMany, ih]

@[simp] theorem openAt_involutive (P : Formula) (k : Nat) (x : Atom) :
    (P.openAt k x).openAt k x = P := by
  induction P generalizing k <;> simp_all [openAt]

@[simp] theorem swap_involutive (P : Formula) (x y : Atom) :
    (P.swap x y).swap x y = P := by
  induction P <;> simp_all [swap]
  rw [Finset.image_image]
  simp [Function.comp_def]

@[simp] theorem substitute_empty (P : Formula) :
    P.substitute ∅ = P := by
  induction P <;> simp_all [substitute]

end Formula

namespace Qualifier

/-- A store realizes exactly one supported qualifier assignment. -/
def HoldsStore (q : Qualifier) (σ : Store) : Prop :=
  σ.domain = q.freeAtoms ∧
  ∃ ρ : AssignmentOn q.support,
    q.holds ρ ∧
    ∀ x, ρ.assignment.lookup (.free x) = σ.lookup x

/-- Exact qualifier atoms identify the accepted stores of a capability
projection, rather than merely testing each existing store. -/
def Exactly (q : Qualifier) (m : Capability) : Prop :=
  q.locallyClosed ∧ q.freeAtoms ⊆ m.domain ∧
  ∀ σ, σ.domain = q.freeAtoms →
    (q.HoldsStore σ ↔ σ ∈ m.restrict q.freeAtoms)

end Qualifier

namespace Formula

/-- Atoms chosen by a finite binder opening. -/
def openingAtoms {d : Nat} (η : Fin d → Atom) : Finset Atom :=
  Finset.univ.image η

/-- The opening maps distinct binders to distinct atoms. -/
def OpeningInjective {d : Nat} (η : Fin d → Atom) : Prop :=
  Function.Injective η

/-- Formula satisfaction.  The well-founded recursion follows formula size;
opening and store substitution preserve the size of recursive subformulas. -/
def Models (m : Capability) (P : Formula) : Prop :=
  let r := m.restrict P.freeAtoms
  r.domain = P.freeAtoms ∧
  match P with
  | .top => True
  | .bot => False
  | .atom q => q.Exactly r
  | .and P Q => Models r P ∧ Models r Q
  | .or P Q => Models r P ∨ Models r Q
  | .impl P Q => ∀ n, r ⊑ n → Models n P → Models n Q
  | .star P Q =>
      ∃ (m₁ m₂ : Capability) (h : Capability.Compatible m₁ m₂),
        Capability.product m₁ m₂ h ⊑ r ∧ Models m₁ P ∧ Models m₂ Q
  | .wand d P Q =>
      ∃ L : Finset Atom,
        ∀ (η : Fin d → Atom), OpeningInjective η →
          Disjoint (openingAtoms η) L →
          ∀ n (h : Capability.Compatible n r),
            (Capability.product n r h).domain = r.domain ∪ openingAtoms η →
            Models n (P.openMany d η) →
            Models (Capability.product n r h) (Q.openMany d η)
  | .sum P Q =>
      ∃ (m₁ m₂ : Capability) (h : Capability.SumDefined m₁ m₂),
        Capability.sum m₁ m₂ h ⊑ r ∧ Models m₁ P ∧ Models m₂ Q
  | .all P =>
      ∃ L : Finset Atom,
        ∀ y, y ∉ L →
          ∀ F : Capability.FiberExtension,
            F.input = P.freeAtoms → F.output = {y} →
            ∀ n, F.Extends r n → Models n (P.openAt 0 y)
  | .over P => ∃ n, r ⊆ n ∧ Models n P
  | .under P => ∃ n, n ⊆ r ∧ Models n P
  | .persist P =>
      ∃ σ, σ.domain = P.freeAtoms ∧
        r = Capability.singleton σ ∧ Models (Capability.singleton σ) P
  | .fiber X P =>
      LogicVar.LocallyClosed X ∧
      ∀ σ f, Capability.IsFiber f r (LogicVar.freeAtomSet X) σ →
        Models f (P.substituteStore σ)
termination_by P.measure
decreasing_by
  all_goals simp_wf
  all_goals simp [measure]
  all_goals omega

set_option hygiene false in
scoped[ContextTypes] notation:50 (name := formulaModels) m:51 " ⊨ " P:51 =>
  ContextTypes.Formula.Models m P

/-- Semantic entailment between formulas. -/
def Entails (P Q : Formula) : Prop :=
  ∀ m, m ⊨ P → m ⊨ Q

set_option hygiene false in
scoped[ContextTypes] infix:20 (name := formulaEntails) " ⊫ " =>
  ContextTypes.Formula.Entails

/-- Semantic equivalence between formulas. -/
def Equiv (P Q : Formula) : Prop :=
  (P ⊫ Q) ∧ (Q ⊫ P)

set_option hygiene false in
scoped[ContextTypes] infix:20 (name := formulaEquiv) " ⊣⊢ " =>
  ContextTypes.Formula.Equiv

/-- Satisfaction depends only on the capability projected to the atoms
observed by the formula. -/
theorem models_congr_restrict {m n : Capability} {P : Formula}
    (h : m.restrict P.freeAtoms = n.restrict P.freeAtoms) :
    m ⊨ P ↔ n ⊨ P := by
  rw [Models.eq_def m P, Models.eq_def n P, h]

/-- Projecting to the exact support of a formula preserves satisfaction. -/
theorem models_restrict_iff (m : Capability) (P : Formula) :
    m ⊨ P ↔ m.restrict P.freeAtoms ⊨ P := by
  apply models_congr_restrict
  rw [Capability.restrict_restrict, Finset.inter_self]

/-- Restricting to any superset of the observed atoms preserves
satisfaction. -/
theorem models_restrict_superset (m : Capability) (P : Formula)
    {X : Finset Atom} (support : P.freeAtoms ⊆ X) :
    m ⊨ P ↔ m.restrict X ⊨ P := by
  apply models_congr_restrict
  rw [Capability.restrict_restrict,
    Finset.inter_eq_right.2 support]

/-- A satisfied formula observes only atoms present in the capability. -/
theorem models_scope {m : Capability} {P : Formula} (h : m ⊨ P) :
    P.freeAtoms ⊆ m.domain := by
  rw [Models.eq_def m P] at h
  exact Finset.inter_eq_right.1 h.1

/-- Two capabilities agreeing on a superset of a formula's support satisfy
the same formula. -/
theorem models_projection {m n : Capability} {P : Formula}
    (X : Finset Atom) (support : P.freeAtoms ⊆ X)
    (same : m.restrict X = n.restrict X) :
    m ⊨ P ↔ n ⊨ P := by
  apply models_congr_restrict
  calc
    m.restrict P.freeAtoms = (m.restrict X).restrict P.freeAtoms := by
      rw [Capability.restrict_restrict,
        Finset.inter_eq_right.2 support]
    _ = (n.restrict X).restrict P.freeAtoms := by rw [same]
    _ = n.restrict P.freeAtoms := by
      rw [Capability.restrict_restrict,
        Finset.inter_eq_right.2 support]

/-- Context-logic satisfaction is monotone in the projection/Kripke order. -/
theorem models_kripke {m n : Capability} {P : Formula}
    (hmn : m ⊑ n) (hP : m ⊨ P) : n ⊨ P := by
  apply (models_congr_restrict (m := m) (n := n) (P := P) ?_).1 hP
  calc
    m.restrict P.freeAtoms =
        (n.restrict m.domain).restrict P.freeAtoms := by rw [← hmn]
    _ = n.restrict (m.domain ∩ P.freeAtoms) :=
      Capability.restrict_restrict _ _ _
    _ = n.restrict P.freeAtoms := by
      rw [Finset.inter_eq_right.2 (models_scope hP)]

theorem entails_refl (P : Formula) : P ⊫ P :=
  fun _ hP => hP

theorem entails_trans {P Q R : Formula} (hPQ : P ⊫ Q)
    (hQR : Q ⊫ R) : P ⊫ R :=
  fun m hP => hQR m (hPQ m hP)

theorem equiv_refl (P : Formula) : P ⊣⊢ P :=
  ⟨entails_refl P, entails_refl P⟩

theorem Equiv.symm {P Q : Formula} (h : P ⊣⊢ Q) : Q ⊣⊢ P :=
  ⟨h.2, h.1⟩

theorem Equiv.trans {P Q R : Formula} (hPQ : P ⊣⊢ Q)
    (hQR : Q ⊣⊢ R) : P ⊣⊢ R :=
  ⟨entails_trans hPQ.1 hQR.1, entails_trans hQR.2 hPQ.2⟩

@[simp] theorem models_top (m : Capability) : m ⊨ (⊤ᶜ : Formula) := by
  rw [Models.eq_def m ⊤ᶜ]
  simp

@[simp] theorem not_models_bot (m : Capability) : ¬m ⊨ (⊥ᶜ : Formula) := by
  rw [Models.eq_def m ⊥ᶜ]
  simp

theorem models_atom_iff (m : Capability) (q : Qualifier) :
    m ⊨ Atom(q) ↔
      (m.restrict q.freeAtoms).domain = q.freeAtoms ∧
        q.Exactly (m.restrict q.freeAtoms) := by
  rw [Models.eq_def m Atom(q)]
  simp only [freeAtoms_atom]

theorem models_and_iff (m : Capability) (P Q : Formula) :
    m ⊨ (P ∧ᶜ Q) ↔ (m ⊨ P) ∧ (m ⊨ Q) := by
  rw [Models.eq_def m (P ∧ᶜ Q)]
  let r := m.restrict (P ∧ᶜ Q).freeAtoms
  constructor
  · rintro ⟨_, hP, hQ⟩
    constructor
    · apply (models_restrict_superset m P
        (X := P.freeAtoms ∪ Q.freeAtoms) Finset.subset_union_left).2
      simpa using hP
    · apply (models_restrict_superset m Q
        (X := P.freeAtoms ∪ Q.freeAtoms) Finset.subset_union_right).2
      simpa using hQ
  · rintro ⟨hP, hQ⟩
    refine ⟨?_, ?_, ?_⟩
    rw [Capability.restrict_domain, freeAtoms_and,
      Finset.inter_eq_right]
    exact Finset.union_subset (models_scope hP) (models_scope hQ)
    · simpa using (models_restrict_superset m P
        (X := P.freeAtoms ∪ Q.freeAtoms) Finset.subset_union_left).1 hP
    · simpa using (models_restrict_superset m Q
        (X := P.freeAtoms ∪ Q.freeAtoms) Finset.subset_union_right).1 hQ

theorem models_and_elim_left {m : Capability} {P Q : Formula}
    (h : m ⊨ (P ∧ᶜ Q)) : m ⊨ P :=
  (models_and_iff m P Q).1 h |>.1

theorem models_and_elim_right {m : Capability} {P Q : Formula}
    (h : m ⊨ (P ∧ᶜ Q)) : m ⊨ Q :=
  (models_and_iff m P Q).1 h |>.2

theorem models_and_intro {m : Capability} {P Q : Formula}
    (hP : m ⊨ P) (hQ : m ⊨ Q) : m ⊨ (P ∧ᶜ Q) :=
  (models_and_iff m P Q).2 ⟨hP, hQ⟩

theorem models_or_iff (m : Capability) (P Q : Formula)
    (scope : (P ∨ᶜ Q).freeAtoms ⊆ m.domain) :
    m ⊨ (P ∨ᶜ Q) ↔ (m ⊨ P) ∨ (m ⊨ Q) := by
  rw [Models.eq_def m (P ∨ᶜ Q)]
  constructor
  · rintro ⟨_, hP | hQ⟩
    · left
      apply (models_restrict_superset m P
        (X := P.freeAtoms ∪ Q.freeAtoms) Finset.subset_union_left).2
      simpa using hP
    · right
      apply (models_restrict_superset m Q
        (X := P.freeAtoms ∪ Q.freeAtoms) Finset.subset_union_right).2
      simpa using hQ
  · intro h
    refine ⟨?_, ?_⟩
    · simpa [Capability.restrict_domain, Finset.inter_eq_right] using scope
    · rcases h with hP | hQ
      · left
        simpa using (models_restrict_superset m P
          (X := P.freeAtoms ∪ Q.freeAtoms) Finset.subset_union_left).1 hP
      · right
        simpa using (models_restrict_superset m Q
          (X := P.freeAtoms ∪ Q.freeAtoms) Finset.subset_union_right).1 hQ

theorem models_or_intro_left {m : Capability} {P Q : Formula}
    (hP : m ⊨ P) (scopeQ : Q.freeAtoms ⊆ m.domain) :
    m ⊨ (P ∨ᶜ Q) := by
  apply (models_or_iff m P Q ?_).2
  · exact Or.inl hP
  · simp only [freeAtoms_or]
    exact Finset.union_subset (models_scope hP) scopeQ

theorem models_or_intro_right {m : Capability} {P Q : Formula}
    (scopeP : P.freeAtoms ⊆ m.domain) (hQ : m ⊨ Q) :
    m ⊨ (P ∨ᶜ Q) := by
  apply (models_or_iff m P Q ?_).2
  · exact Or.inr hQ
  · simp only [freeAtoms_or]
    exact Finset.union_subset scopeP (models_scope hQ)

theorem models_impl_iff (m : Capability) (P Q : Formula) :
    m ⊨ (P ⇒ᶜ Q) ↔
      let r := m.restrict (P ⇒ᶜ Q).freeAtoms
      r.domain = (P ⇒ᶜ Q).freeAtoms ∧
        ∀ n, r ⊑ n → n ⊨ P → n ⊨ Q := by
  rw [Models.eq_def m (P ⇒ᶜ Q)]

theorem models_impl_elim {m : Capability} {P Q : Formula}
    (hPQ : m ⊨ (P ⇒ᶜ Q)) (hP : m ⊨ P) : m ⊨ Q := by
  rw [models_impl_iff] at hPQ
  exact hPQ.2 m (Capability.restrict_refines _ _) hP

theorem models_impl_intro {m : Capability} {P Q : Formula}
    (scope : (P ⇒ᶜ Q).freeAtoms ⊆ m.domain)
    (h : ∀ n, m.restrict (P ⇒ᶜ Q).freeAtoms ⊑ n →
      n ⊨ P → n ⊨ Q) :
    m ⊨ (P ⇒ᶜ Q) := by
  rw [models_impl_iff]
  refine ⟨?_, h⟩
  rw [Capability.restrict_domain, Finset.inter_eq_right]
  exact scope

theorem models_star_iff (m : Capability) (P Q : Formula) :
    m ⊨ (P ∗ Q) ↔
      let r := m.restrict (P ∗ Q).freeAtoms
      r.domain = (P ∗ Q).freeAtoms ∧
        ∃ (m₁ m₂ : Capability) (h : Capability.Compatible m₁ m₂),
          Capability.product m₁ m₂ h ⊑ r ∧
            m₁ ⊨ P ∧ m₂ ⊨ Q := by
  rw [Models.eq_def m (P ∗ Q)]

theorem models_star_intro {m m₁ m₂ : Capability} {P Q : Formula}
    (h : Capability.Compatible m₁ m₂)
    (scope : (P ∗ Q).freeAtoms ⊆ m.domain)
    (product : Capability.product m₁ m₂ h ⊑
      m.restrict (P ∗ Q).freeAtoms)
    (hP : m₁ ⊨ P) (hQ : m₂ ⊨ Q) : m ⊨ (P ∗ Q) := by
  rw [models_star_iff]
  refine ⟨?_, m₁, m₂, h, product, hP, hQ⟩
  rw [Capability.restrict_domain, Finset.inter_eq_right]
  exact scope

theorem models_wand_iff (m : Capability) (d : Nat) (P Q : Formula) :
    m ⊨ (P -∗[d] Q) ↔
      let r := m.restrict (P -∗[d] Q).freeAtoms
      r.domain = (P -∗[d] Q).freeAtoms ∧
        ∃ L : Finset Atom,
          ∀ (η : Fin d → Atom), OpeningInjective η →
            Disjoint (openingAtoms η) L →
            ∀ n (h : Capability.Compatible n r),
              (Capability.product n r h).domain =
                  r.domain ∪ openingAtoms η →
              n ⊨ P.openMany d η →
              Capability.product n r h ⊨ Q.openMany d η := by
  rw [Models.eq_def m (P -∗[d] Q)]

theorem models_wand_intro {m : Capability} {d : Nat} {P Q : Formula}
    (scope : (P -∗[d] Q).freeAtoms ⊆ m.domain)
    (h : ∃ L : Finset Atom,
      ∀ (η : Fin d → Atom), OpeningInjective η →
        Disjoint (openingAtoms η) L →
        ∀ n (compatible : Capability.Compatible n
            (m.restrict (P -∗[d] Q).freeAtoms)),
          (Capability.product n (m.restrict (P -∗[d] Q).freeAtoms)
              compatible).domain =
              (m.restrict (P -∗[d] Q).freeAtoms).domain ∪
                openingAtoms η →
          n ⊨ P.openMany d η →
          Capability.product n (m.restrict (P -∗[d] Q).freeAtoms)
              compatible ⊨ Q.openMany d η) :
    m ⊨ (P -∗[d] Q) := by
  rw [models_wand_iff]
  refine ⟨?_, h⟩
  rw [Capability.restrict_domain, Finset.inter_eq_right]
  exact scope

theorem models_sum_iff (m : Capability) (P Q : Formula) :
    m ⊨ (P ⊕ Q) ↔
      let r := m.restrict (P ⊕ Q).freeAtoms
      r.domain = (P ⊕ Q).freeAtoms ∧
        ∃ (m₁ m₂ : Capability) (h : Capability.SumDefined m₁ m₂),
          Capability.sum m₁ m₂ h ⊑ r ∧
            m₁ ⊨ P ∧ m₂ ⊨ Q := by
  rw [Models.eq_def m (P ⊕ Q)]

theorem models_sum_intro {m m₁ m₂ : Capability} {P Q : Formula}
    (h : Capability.SumDefined m₁ m₂)
    (scope : (P ⊕ Q).freeAtoms ⊆ m.domain)
    (sum : Capability.sum m₁ m₂ h ⊑ m.restrict (P ⊕ Q).freeAtoms)
    (hP : m₁ ⊨ P) (hQ : m₂ ⊨ Q) : m ⊨ (P ⊕ Q) := by
  rw [models_sum_iff]
  refine ⟨?_, m₁, m₂, h, sum, hP, hQ⟩
  rw [Capability.restrict_domain, Finset.inter_eq_right]
  exact scope

theorem models_all_iff (m : Capability) (P : Formula) :
    m ⊨ Formula.all P ↔
      let r := m.restrict P.freeAtoms
      r.domain = P.freeAtoms ∧
        ∃ L : Finset Atom,
          ∀ y, y ∉ L →
            ∀ F : Capability.FiberExtension,
              F.input = P.freeAtoms → F.output = {y} →
              ∀ n, F.Extends r n → n ⊨ P.openAt 0 y := by
  rw [Models.eq_def m (Formula.all P)]
  simp only [freeAtoms_all]

theorem models_all_intro {m : Capability} {P : Formula}
    (scope : P.freeAtoms ⊆ m.domain)
    (h : ∃ L : Finset Atom,
      ∀ y, y ∉ L →
        ∀ F : Capability.FiberExtension,
          F.input = P.freeAtoms → F.output = {y} →
          ∀ n, F.Extends (m.restrict P.freeAtoms) n →
            n ⊨ P.openAt 0 y) :
    m ⊨ Formula.all P := by
  rw [models_all_iff]
  refine ⟨?_, h⟩
  rw [Capability.restrict_domain, Finset.inter_eq_right]
  exact scope

theorem models_over_iff (m : Capability) (P : Formula) :
    m ⊨ (🄾 P) ↔
      let r := m.restrict P.freeAtoms
      r.domain = P.freeAtoms ∧ ∃ n, r ⊆ n ∧ n ⊨ P := by
  rw [Models.eq_def m (🄾 P)]
  simp only [freeAtoms_over]

theorem models_over_intro {m : Capability} {P : Formula}
    (hP : m ⊨ P) : m ⊨ (🄾 P) := by
  rw [models_over_iff]
  refine ⟨?_, m.restrict P.freeAtoms, Capability.subset_refl _, ?_⟩
  · rw [Capability.restrict_domain, Finset.inter_eq_right]
    exact models_scope hP
  · exact (models_restrict_iff m P).1 hP

theorem models_under_iff (m : Capability) (P : Formula) :
    m ⊨ (🅄 P) ↔
      let r := m.restrict P.freeAtoms
      r.domain = P.freeAtoms ∧ ∃ n, n ⊆ r ∧ n ⊨ P := by
  rw [Models.eq_def m (🅄 P)]
  simp only [freeAtoms_under]

theorem models_under_intro {m : Capability} {P : Formula}
    (hP : m ⊨ P) : m ⊨ (🅄 P) := by
  rw [models_under_iff]
  refine ⟨?_, m.restrict P.freeAtoms, Capability.subset_refl _, ?_⟩
  · rw [Capability.restrict_domain, Finset.inter_eq_right]
    exact models_scope hP
  · exact (models_restrict_iff m P).1 hP

theorem models_persist_iff (m : Capability) (P : Formula) :
    m ⊨ (□ P) ↔
      ∃ σ, σ.domain = P.freeAtoms ∧
        m.restrict P.freeAtoms = Capability.singleton σ ∧
          Capability.singleton σ ⊨ P := by
  rw [Models.eq_def m (□ P)]
  simp only [freeAtoms_persist]
  constructor
  · rintro ⟨_, h⟩
    exact h
  · rintro ⟨σ, hσ, same, hP⟩
    refine ⟨?_, σ, hσ, same, hP⟩
    rw [Capability.restrict_domain, Finset.inter_eq_right]
    calc
      P.freeAtoms = σ.domain := hσ.symm
      _ = (Capability.singleton σ).domain :=
        (Capability.singleton_domain σ).symm
      _ = (m.restrict P.freeAtoms).domain := congrArg Capability.domain same |>.symm
      _ ⊆ m.domain := Finset.inter_subset_left

theorem models_persist_elim {m : Capability} {P : Formula}
    (h : m ⊨ (□ P)) : m ⊨ P := by
  obtain ⟨σ, _, same, hP⟩ := (models_persist_iff m P).1 h
  apply models_kripke (m := Capability.singleton σ) (n := m) ?_ hP
  rw [← same]
  exact Capability.restrict_refines m P.freeAtoms

theorem models_fiber_iff (m : Capability) (X : Finset LogicVar)
    (P : Formula) :
    m ⊨ Formula.fiber X P ↔
      let r := m.restrict (Formula.fiber X P).freeAtoms
      r.domain = (Formula.fiber X P).freeAtoms ∧
        LogicVar.LocallyClosed X ∧
          ∀ σ f, Capability.IsFiber f r (LogicVar.freeAtomSet X) σ →
            f ⊨ P.substituteStore σ := by
  rw [Models.eq_def m (Formula.fiber X P)]

theorem models_fiber_intro {m : Capability} {X : Finset LogicVar}
    {P : Formula} (scope : (Formula.fiber X P).freeAtoms ⊆ m.domain)
    (closed : LogicVar.LocallyClosed X)
    (h : ∀ σ f,
      Capability.IsFiber f (m.restrict (Formula.fiber X P).freeAtoms)
          (LogicVar.freeAtomSet X) σ →
        f ⊨ P.substituteStore σ) :
    m ⊨ Formula.fiber X P := by
  rw [models_fiber_iff]
  refine ⟨?_, closed, h⟩
  rw [Capability.restrict_domain, Finset.inter_eq_right]
  exact scope

theorem and_mono {P P' Q Q' : Formula} (hP : P ⊫ P')
    (hQ : Q ⊫ Q') : P ∧ᶜ Q ⊫ P' ∧ᶜ Q' := by
  intro m h
  obtain ⟨hmP, hmQ⟩ := (models_and_iff m P Q).1 h
  exact models_and_intro (hP m hmP) (hQ m hmQ)

theorem and_comm (P Q : Formula) : P ∧ᶜ Q ⊣⊢ Q ∧ᶜ P := by
  constructor <;> intro m h
  · obtain ⟨hP, hQ⟩ := (models_and_iff m P Q).1 h
    exact models_and_intro hQ hP
  · obtain ⟨hQ, hP⟩ := (models_and_iff m Q P).1 h
    exact models_and_intro hP hQ

theorem and_assoc (P Q R : Formula) :
    (P ∧ᶜ Q) ∧ᶜ R ⊣⊢ P ∧ᶜ (Q ∧ᶜ R) := by
  constructor <;> intro m h
  · obtain ⟨hPQ, hR⟩ := (models_and_iff m (P ∧ᶜ Q) R).1 h
    obtain ⟨hP, hQ⟩ := (models_and_iff m P Q).1 hPQ
    exact models_and_intro hP (models_and_intro hQ hR)
  · obtain ⟨hP, hQR⟩ := (models_and_iff m P (Q ∧ᶜ R)).1 h
    obtain ⟨hQ, hR⟩ := (models_and_iff m Q R).1 hQR
    exact models_and_intro (models_and_intro hP hQ) hR

theorem and_top (P : Formula) : P ∧ᶜ ⊤ᶜ ⊣⊢ P := by
  constructor
  · intro m h
    exact models_and_elim_left h
  · intro m hP
    exact models_and_intro hP (models_top m)

end Formula

end ContextTypes
