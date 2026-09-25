import ContextTypes.Syntax
import Mathlib.Data.Finmap
import Mathlib.Tactic

set_option autoImplicit false

namespace ContextTypes

/-!
# Supported qualifiers

Qualifiers are semantic predicates on finite assignments of locally nameless
logical variables.  Their finite support is explicit and binding operations
transport both the support and the predicate domain.
-/

/-- A finite assignment from logical variables to core values. -/
def Assignment := Finmap (fun _ : LogicVar => Value)

namespace Assignment

instance : EmptyCollection Assignment :=
  inferInstanceAs (EmptyCollection (Finmap (fun _ : LogicVar => Value)))

instance : DecidableEq Assignment :=
  inferInstanceAs (DecidableEq (Finmap (fun _ : LogicVar => Value)))

/-- The logical variables defined by an assignment. -/
def domain (ρ : Assignment) : Finset LogicVar :=
  (show Finmap (fun _ : LogicVar => Value) from ρ).keys

/-- Look up a logical variable. -/
def lookup (ρ : Assignment) (ξ : LogicVar) : Option Value :=
  (show Finmap (fun _ : LogicVar => Value) from ρ).lookup ξ

/-- Restrict an assignment to a finite logical-variable set. -/
def restrict (ρ : Assignment) (X : Finset LogicVar) : Assignment :=
  Finmap.keysLookupEquiv.symm
    ⟨(ρ.domain ∩ X, fun ξ => if ξ ∈ X then ρ.lookup ξ else none), by
      intro ξ
      by_cases hξ : ξ ∈ X
      · simp only [hξ, if_pos, Finset.mem_inter, and_true]
        exact Finmap.lookup_isSome.trans Finmap.mem_keys.symm
      · simp [hξ]⟩

/-- Left-biased union of assignments. -/
def merge (ρ σ : Assignment) : Assignment :=
  Finmap.union
    (show Finmap (fun _ : LogicVar => Value) from ρ)
    (show Finmap (fun _ : LogicVar => Value) from σ)

/-- Swap two logical-variable keys. -/
def swap (ξ₁ ξ₂ : LogicVar) (ρ : Assignment) : Assignment :=
  Finmap.keysLookupEquiv.symm
    ⟨(ρ.domain.image (LogicVar.swap ξ₁ ξ₂),
      fun ξ => ρ.lookup (LogicVar.swap ξ₁ ξ₂ ξ)), by
      intro ξ
      constructor
      · intro h
        have hdom : LogicVar.swap ξ₁ ξ₂ ξ ∈ ρ.domain := by
          apply Finmap.mem_keys.2
          apply Finmap.lookup_isSome.1
          exact h
        apply Finset.mem_image.2
        exact ⟨LogicVar.swap ξ₁ ξ₂ ξ, hdom,
          LogicVar.swap_involutive ξ₁ ξ₂ ξ⟩
      · intro h
        obtain ⟨ζ, hζ, same⟩ := Finset.mem_image.1 h
        have back : LogicVar.swap ξ₁ ξ₂ ξ = ζ := by
          rw [← same, LogicVar.swap_involutive]
        change (ρ.lookup (LogicVar.swap ξ₁ ξ₂ ξ)).isSome = true
        rw [back]
        apply Finmap.lookup_isSome.2
        exact Finmap.mem_keys.1 hζ⟩

@[simp] theorem domain_empty : domain (∅ : Assignment) = ∅ :=
  rfl

@[simp] theorem lookup_empty (ξ : LogicVar) : lookup (∅ : Assignment) ξ = none :=
  Finmap.lookup_empty ξ

theorem mem_domain_iff (ρ : Assignment) (ξ : LogicVar) :
    ξ ∈ ρ.domain ↔ ∃ v, ρ.lookup ξ = some v :=
  Finmap.mem_iff

theorem lookup_eq_none_iff (ρ : Assignment) (ξ : LogicVar) :
    ρ.lookup ξ = none ↔ ξ ∉ ρ.domain :=
  Finmap.lookup_eq_none

/-- Assignments are extensional in lookup. -/
theorem ext {ρ σ : Assignment} (h : ∀ ξ, ρ.lookup ξ = σ.lookup ξ) : ρ = σ := by
  change (∀ ξ, Finmap.lookup ξ ρ = Finmap.lookup ξ σ) at h
  exact Finmap.ext_lookup h

@[simp] theorem domain_restrict (ρ : Assignment) (X : Finset LogicVar) :
    (ρ.restrict X).domain = ρ.domain ∩ X :=
  Finmap.keysLookupEquiv_symm_apply_keys _

@[simp] theorem lookup_restrict (ρ : Assignment) (X : Finset LogicVar)
    (ξ : LogicVar) :
    (ρ.restrict X).lookup ξ = if ξ ∈ X then ρ.lookup ξ else none :=
  Finmap.keysLookupEquiv_symm_apply_lookup _ _

@[simp] theorem restrict_empty (ρ : Assignment) : ρ.restrict ∅ = ∅ := by
  apply ext
  intro ξ
  rw [lookup_restrict]
  exact (lookup_empty ξ).symm

@[simp] theorem empty_restrict (X : Finset LogicVar) :
    (∅ : Assignment).restrict X = ∅ := by
  apply ext
  intro ξ
  rw [lookup_restrict]
  by_cases hξ : ξ ∈ X <;> simp [hξ]

theorem restrict_restrict (ρ : Assignment) (X Y : Finset LogicVar) :
    (ρ.restrict X).restrict Y = ρ.restrict (X ∩ Y) := by
  apply ext
  intro ξ
  simp only [lookup_restrict, Finset.mem_inter]
  by_cases hξX : ξ ∈ X <;> by_cases hξY : ξ ∈ Y <;>
    simp [hξX, hξY]

theorem restrict_eq_self (ρ : Assignment) {X : Finset LogicVar}
    (h : ρ.domain ⊆ X) : ρ.restrict X = ρ := by
  apply ext
  intro ξ
  rw [lookup_restrict]
  by_cases hξ : ξ ∈ X
  · simp [hξ]
  · have absent : ξ ∉ ρ.domain := fun hdom => hξ (h hdom)
    simp [hξ, (lookup_eq_none_iff ρ ξ).2 absent]

theorem restrict_eq_empty_of_disjoint (ρ : Assignment) {X : Finset LogicVar}
    (h : Disjoint ρ.domain X) : ρ.restrict X = ∅ := by
  apply ext
  intro ξ
  rw [lookup_restrict, lookup_empty]
  by_cases hξX : ξ ∈ X
  · have hξρ : ξ ∉ ρ.domain := fun hξρ =>
      Finset.disjoint_left.1 h hξρ hξX
    simp [hξX, (lookup_eq_none_iff ρ ξ).2 hξρ]
  · simp [hξX]

@[simp] theorem domain_merge (ρ σ : Assignment) :
    (ρ.merge σ).domain = ρ.domain ∪ σ.domain := by
  change
    (Finmap.union
      (show Finmap (fun _ : LogicVar => Value) from ρ)
      (show Finmap (fun _ : LogicVar => Value) from σ)).keys = _
  exact Finmap.keys_union

@[simp] theorem empty_merge (ρ : Assignment) : (∅ : Assignment).merge ρ = ρ := by
  change Finmap.union ∅ ρ = ρ
  exact Finmap.empty_union

@[simp] theorem merge_empty (ρ : Assignment) : ρ.merge ∅ = ρ := by
  change Finmap.union ρ ∅ = ρ
  exact Finmap.union_empty

theorem merge_assoc (ρ σ τ : Assignment) :
    (ρ.merge σ).merge τ = ρ.merge (σ.merge τ) := by
  change Finmap.union (Finmap.union ρ σ) τ =
    Finmap.union ρ (Finmap.union σ τ)
  exact Finmap.union_assoc

@[simp] theorem domain_swap (ξ₁ ξ₂ : LogicVar) (ρ : Assignment) :
    (ρ.swap ξ₁ ξ₂).domain =
      ρ.domain.image (LogicVar.swap ξ₁ ξ₂) :=
  Finmap.keysLookupEquiv_symm_apply_keys _

@[simp] theorem lookup_swap (ξ₁ ξ₂ : LogicVar) (ρ : Assignment)
    (ξ : LogicVar) :
    (ρ.swap ξ₁ ξ₂).lookup ξ =
      ρ.lookup (LogicVar.swap ξ₁ ξ₂ ξ) :=
  Finmap.keysLookupEquiv_symm_apply_lookup _ _

@[simp] theorem swap_involutive (ξ₁ ξ₂ : LogicVar) (ρ : Assignment) :
    (ρ.swap ξ₁ ξ₂).swap ξ₁ ξ₂ = ρ := by
  apply ext
  intro ξ
  simp

theorem swap_fresh {ξ₁ ξ₂ : LogicVar} {ρ : Assignment}
    (h₁ : ξ₁ ∉ ρ.domain) (h₂ : ξ₂ ∉ ρ.domain) :
    ρ.swap ξ₁ ξ₂ = ρ := by
  apply ext
  intro ξ
  rw [lookup_swap]
  by_cases hξ₁ : ξ = ξ₁ <;> by_cases hξ₂ : ξ = ξ₂
  · subst ξ
    simp [LogicVar.swap, (lookup_eq_none_iff ρ ξ₁).2 h₁,
      (lookup_eq_none_iff ρ ξ₂).2 h₂]
  · subst ξ
    simp [LogicVar.swap, (lookup_eq_none_iff ρ ξ₁).2 h₁,
      (lookup_eq_none_iff ρ ξ₂).2 h₂]
  · subst ξ
    simp [LogicVar.swap, hξ₁, (lookup_eq_none_iff ρ ξ₁).2 h₁,
      (lookup_eq_none_iff ρ ξ₂).2 h₂]
  · simp [LogicVar.swap, hξ₁, hξ₂]

end Assignment

/-- An assignment whose domain is exactly `X`. -/
structure AssignmentOn (X : Finset LogicVar) where
  assignment : Assignment
  domain_eq : assignment.domain = X

namespace AssignmentOn

@[ext] theorem ext {X : Finset LogicVar} {ρ σ : AssignmentOn X}
    (h : ρ.assignment = σ.assignment) : ρ = σ := by
  cases ρ
  cases σ
  simp only at h
  subst h
  rfl

/-- Restrict an exact-domain assignment to a smaller exact domain. -/
def restrict {X : Finset LogicVar} (ρ : AssignmentOn X)
    (Y : Finset LogicVar) (h : Y ⊆ X) : AssignmentOn Y where
  assignment := ρ.assignment.restrict Y
  domain_eq := by
    rw [Assignment.domain_restrict, ρ.domain_eq,
      Finset.inter_eq_right.2 h]

/-- Transport an assignment back across a logical-variable swap. -/
def swapBack (ξ₁ ξ₂ : LogicVar) {X : Finset LogicVar}
    (ρ : AssignmentOn (X.image (LogicVar.swap ξ₁ ξ₂))) :
    AssignmentOn X where
  assignment := ρ.assignment.swap ξ₁ ξ₂
  domain_eq := by
    rw [Assignment.domain_swap, ρ.domain_eq]
    ext ξ
    simp

/-- Transport an assignment forward across a logical-variable swap. -/
def swapFront (ξ₁ ξ₂ : LogicVar) {X : Finset LogicVar}
    (ρ : AssignmentOn X) :
    AssignmentOn (X.image (LogicVar.swap ξ₁ ξ₂)) where
  assignment := ρ.assignment.swap ξ₁ ξ₂
  domain_eq := Assignment.domain_swap _ _ _ |>.trans
    (congrArg (fun Y => Y.image (LogicVar.swap ξ₁ ξ₂)) ρ.domain_eq)

@[simp] theorem swapBack_swapFront (ξ₁ ξ₂ : LogicVar)
    {X : Finset LogicVar} (ρ : AssignmentOn X) :
    swapBack ξ₁ ξ₂ (swapFront ξ₁ ξ₂ ρ) = ρ := by
  apply ext
  exact Assignment.swap_involutive _ _ _

@[simp] theorem swapFront_swapBack (ξ₁ ξ₂ : LogicVar)
    {X : Finset LogicVar}
    (ρ : AssignmentOn (X.image (LogicVar.swap ξ₁ ξ₂))) :
    swapFront ξ₁ ξ₂ (swapBack ξ₁ ξ₂ ρ) = ρ := by
  apply ext
  exact Assignment.swap_involutive _ _ _

/-- Reassemble a full assignment from a substitution and the variables it
does not define. -/
def substituteBack (X : Finset LogicVar) (ρ : Assignment)
    (σ : AssignmentOn (X \ ρ.domain)) : AssignmentOn X where
  assignment := σ.assignment.merge (ρ.restrict X)
  domain_eq := by
    rw [Assignment.domain_merge, σ.domain_eq, Assignment.domain_restrict]
    ext ξ
    simp only [Finset.mem_union, Finset.mem_sdiff, Finset.mem_inter]
    tauto

end AssignmentOn

/-- A semantic predicate with an explicit finite logical-variable support. -/
structure Qualifier where
  support : Finset LogicVar
  holds : AssignmentOn support → Prop

namespace Qualifier

private theorem image_swap_eq_self_of_fresh (ξ₁ ξ₂ : LogicVar)
    (X : Finset LogicVar) (h₁ : ξ₁ ∉ X) (h₂ : ξ₂ ∉ X) :
    X.image (LogicVar.swap ξ₁ ξ₂) = X := by
  apply Finset.ext
  intro ξ
  rw [Finset.mem_image]
  constructor
  · rintro ⟨ζ, hζ, rfl⟩
    have hn₁ : ζ ≠ ξ₁ := fun same => h₁ (same ▸ hζ)
    have hn₂ : ζ ≠ ξ₂ := fun same => h₂ (same ▸ hζ)
    simpa [LogicVar.swap, hn₁, hn₂] using hζ
  · intro hξ
    have hn₁ : ξ ≠ ξ₁ := fun same => h₁ (same ▸ hξ)
    have hn₂ : ξ ≠ ξ₂ := fun same => h₂ (same ▸ hξ)
    exact ⟨ξ, hξ, by simp [LogicVar.swap, hn₁, hn₂]⟩

/-- Qualifiers are extensional in their support and predicate. -/
theorem ext {q r : Qualifier} (support : q.support = r.support)
    (holds : ∀ (ρ : AssignmentOn q.support) (σ : AssignmentOn r.support),
      ρ.assignment = σ.assignment → (q.holds ρ ↔ r.holds σ)) : q = r := by
  cases q with
  | mk X P =>
      cases r with
      | mk Y Q =>
          simp only at support
          subst Y
          have same : P = Q := by
            funext ρ
            exact propext (holds ρ ρ rfl)
          subst Q
          rfl

/-- Open logical binder `k` with the fresh atom `x`. -/
def openAt (q : Qualifier) (k : Nat) (x : Atom) : Qualifier where
  support := LogicVar.openSupport k x q.support
  holds := fun ρ => q.holds (ρ.swapBack (.bound k) (.free x))

/-- Swap two free atoms throughout a qualifier. -/
def swap (q : Qualifier) (x y : Atom) : Qualifier where
  support := q.support.image (LogicVar.swap (.free x) (.free y))
  holds := fun ρ => q.holds (ρ.swapBack (.free x) (.free y))

/-- Instantiate every logical variable supplied by `ρ`. -/
def substitute (q : Qualifier) (ρ : Assignment) : Qualifier where
  support := q.support \ ρ.domain
  holds := fun σ => q.holds (σ.substituteBack q.support ρ)

/-- The always-true qualifier on exactly `X`. -/
def topOn (X : Finset LogicVar) : Qualifier where
  support := X
  holds := fun _ => True

/-- Unconstrained result qualifier.  Its support deliberately contains the
result binder rather than being empty. -/
def top : Qualifier :=
  topOn {LogicVar.bound 0}

/-- Conjunction of two qualifiers, evaluated on their respective supports. -/
def conj (q r : Qualifier) : Qualifier where
  support := q.support ∪ r.support
  holds := fun ρ =>
    q.holds (ρ.restrict q.support Finset.subset_union_left) ∧
    r.holds (ρ.restrict r.support Finset.subset_union_right)

/-- Free program atoms occurring in a qualifier support. -/
def freeAtoms (q : Qualifier) : Finset Atom :=
  q.support.biUnion LogicVar.freeAtoms

/-- All bound logical variables in the support lie below depth `d`. -/
def locallyClosedAt (q : Qualifier) (d : Nat) : Prop :=
  ∀ k, LogicVar.bound k ∈ q.support → k < d

/-- A qualifier with no dangling bound logical variables. -/
abbrev locallyClosed (q : Qualifier) : Prop :=
  q.locallyClosedAt 0

@[simp] theorem support_openAt (q : Qualifier) (k : Nat) (x : Atom) :
    (q.openAt k x).support = LogicVar.openSupport k x q.support :=
  rfl

@[simp] theorem support_swap (q : Qualifier) (x y : Atom) :
    (q.swap x y).support = q.support.image (LogicVar.swap (.free x) (.free y)) :=
  rfl

@[simp] theorem support_substitute (q : Qualifier) (ρ : Assignment) :
    (q.substitute ρ).support = q.support \ ρ.domain :=
  rfl

@[simp] theorem support_topOn (X : Finset LogicVar) :
    (topOn X).support = X :=
  rfl

@[simp] theorem support_top : top.support = {LogicVar.bound 0} :=
  rfl

@[simp] theorem bound_zero_mem_top : LogicVar.bound 0 ∈ top.support := by
  simp

@[simp] theorem support_conj (q r : Qualifier) :
    (q.conj r).support = q.support ∪ r.support :=
  rfl

theorem mem_freeAtoms_iff (q : Qualifier) (x : Atom) :
    x ∈ q.freeAtoms ↔ LogicVar.free x ∈ q.support := by
  constructor
  · intro hx
    obtain ⟨ξ, hξ, hxξ⟩ := Finset.mem_biUnion.1 hx
    cases ξ with
    | bound k => simp [LogicVar.freeAtoms] at hxξ
    | free y =>
        simp only [LogicVar.freeAtoms, Finset.mem_singleton] at hxξ
        subst y
        exact hξ
  · intro hx
    apply Finset.mem_biUnion.2
    exact ⟨.free x, hx, by simp [LogicVar.freeAtoms]⟩

theorem locallyClosedAt_mono (q : Qualifier) {d d' : Nat}
    (closed : q.locallyClosedAt d) (le : d ≤ d') : q.locallyClosedAt d' := by
  intro k hk
  exact lt_of_lt_of_le (closed k hk) le

theorem locallyClosedAt_substitute (q : Qualifier) (ρ : Assignment) (d : Nat)
    (closed : q.locallyClosedAt d) : (q.substitute ρ).locallyClosedAt d := by
  intro k hk
  exact closed k (Finset.mem_sdiff.1 hk).1

theorem locallyClosedAt_openAt (q : Qualifier) (d : Nat) (x : Atom)
    (body : q.locallyClosedAt (d + 1))
    (fresh : LogicVar.free x ∉ q.support) :
    (q.openAt d x).locallyClosedAt d := by
  intro k hk
  have hsrc : LogicVar.openBinder d x (.bound k) ∈ q.support :=
    (LogicVar.mem_openSupport d x q.support (.bound k)).1 hk
  by_cases same : k = d
  · subst k
    simp [LogicVar.openBinder] at hsrc
    exact (fresh hsrc).elim
  · have hbound : LogicVar.bound k ∈ q.support := by
      simpa [LogicVar.openBinder, LogicVar.swap, same] using hsrc
    have lt := body k hbound
    omega

theorem locallyClosedAt_top : top.locallyClosedAt 1 := by
  intro k hk
  simp only [support_top, Finset.mem_singleton, LogicVar.bound.injEq] at hk
  omega

theorem holds_topOn (X : Finset LogicVar) (ρ : AssignmentOn X) :
    (topOn X).holds ρ :=
  trivial

theorem holds_conj_iff (q r : Qualifier)
    (ρ : AssignmentOn (q.support ∪ r.support)) :
    (q.conj r).holds ρ ↔
      q.holds (ρ.restrict q.support Finset.subset_union_left) ∧
      r.holds (ρ.restrict r.support Finset.subset_union_right) :=
  Iff.rfl

@[simp] theorem openAt_involutive (q : Qualifier) (k : Nat) (x : Atom) :
    (q.openAt k x).openAt k x = q := by
  apply ext
  · exact LogicVar.openSupport_involutive k x q.support
  · intro ρ σ same
    change q.holds
      ((ρ.swapBack (.bound k) (.free x)).swapBack (.bound k) (.free x)) ↔
      q.holds σ
    have back :
        (ρ.swapBack (.bound k) (.free x)).swapBack (.bound k) (.free x) = σ := by
      apply AssignmentOn.ext
      change (ρ.assignment.swap (.bound k) (.free x)).swap
        (.bound k) (.free x) = σ.assignment
      rw [Assignment.swap_involutive, same]
    rw [back]

@[simp] theorem swap_involutive (q : Qualifier) (x y : Atom) :
    (q.swap x y).swap x y = q := by
  apply ext
  · ext ξ
    simp
  · intro ρ σ same
    change q.holds
      ((ρ.swapBack (.free x) (.free y)).swapBack (.free x) (.free y)) ↔
      q.holds σ
    have back :
        (ρ.swapBack (.free x) (.free y)).swapBack (.free x) (.free y) = σ := by
      apply AssignmentOn.ext
      change (ρ.assignment.swap (.free x) (.free y)).swap
        (.free x) (.free y) = σ.assignment
      rw [Assignment.swap_involutive, same]
    rw [back]

@[simp] theorem substitute_empty (q : Qualifier) :
    q.substitute ∅ = q := by
  apply ext
  · simp [substitute]
  · intro ρ σ same
    change q.holds (ρ.substituteBack q.support ∅) ↔ q.holds σ
    have back : ρ.substituteBack q.support ∅ = σ := by
      apply AssignmentOn.ext
      change ρ.assignment.merge ((∅ : Assignment).restrict q.support) =
        σ.assignment
      rw [Assignment.empty_restrict, Assignment.merge_empty, same]
    rw [back]

theorem swap_fresh (q : Qualifier) (x y : Atom)
    (hx : LogicVar.free x ∉ q.support) (hy : LogicVar.free y ∉ q.support) :
    q.swap x y = q := by
  apply ext
  · exact image_swap_eq_self_of_fresh (.free x) (.free y) q.support hx hy
  · intro ρ σ same
    change q.holds (ρ.swapBack (.free x) (.free y)) ↔ q.holds σ
    have back : ρ.swapBack (.free x) (.free y) = σ := by
      apply AssignmentOn.ext
      change ρ.assignment.swap (.free x) (.free y) = σ.assignment
      rw [same]
      apply Assignment.swap_fresh
      · rwa [σ.domain_eq]
      · rwa [σ.domain_eq]
    rw [back]

theorem substitute_fresh (q : Qualifier) (ρ : Assignment)
    (h : Disjoint q.support ρ.domain) : q.substitute ρ = q := by
  apply ext
  · exact Finset.sdiff_eq_self_of_disjoint h
  · intro σ τ same
    change q.holds (σ.substituteBack q.support ρ) ↔ q.holds τ
    have back : σ.substituteBack q.support ρ = τ := by
      apply AssignmentOn.ext
      change σ.assignment.merge (ρ.restrict q.support) = τ.assignment
      rw [Assignment.restrict_eq_empty_of_disjoint ρ h.symm,
        Assignment.merge_empty, same]
    rw [back]

theorem openAt_topOn (X : Finset LogicVar) (k : Nat) (x : Atom) :
    (topOn X).openAt k x = topOn (LogicVar.openSupport k x X) := by
  apply ext
  · rfl
  · intro ρ σ same
    constructor <;> intro <;> trivial

theorem openAt_top (x : Atom) :
    top.openAt 0 x = topOn {LogicVar.free x} := by
  rw [top, openAt_topOn]
  congr 2

end Qualifier

end ContextTypes
