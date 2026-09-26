import ContextTypes.Syntax
import Mathlib.Data.Finmap
import Mathlib.Tactic

set_option autoImplicit false

namespace ContextTypes

/-!
# Contextual capabilities

Finite stores and the capability algebra from the semantic model.  The
concrete finite-map representation is confined to the `Store` namespace;
later modules use only lookup, domain, restriction, compatibility, and merge.
-/

/-- A finite environment from program atoms to core values. -/
def Store := Finmap (fun _ : Atom => Value)

namespace Store

instance : EmptyCollection Store :=
  inferInstanceAs (EmptyCollection (Finmap (fun _ : Atom => Value)))

instance : DecidableEq Store :=
  inferInstanceAs (DecidableEq (Finmap (fun _ : Atom => Value)))

/-- The atoms defined by a store. -/
def domain (σ : Store) : Finset Atom :=
  (show Finmap (fun _ : Atom => Value) from σ).keys

/-- Look up an atom in a store. -/
def lookup (σ : Store) (x : Atom) : Option Value :=
  (show Finmap (fun _ : Atom => Value) from σ).lookup x

/-- Restrict a store to a finite set of atoms. -/
def restrict (σ : Store) (X : Finset Atom) : Store :=
  Finmap.keysLookupEquiv.symm
    ⟨(σ.domain ∩ X, fun x => if x ∈ X then σ.lookup x else none), by
      intro x
      by_cases hx : x ∈ X
      · simp only [hx, if_pos, Finset.mem_inter, and_true]
        exact Finmap.lookup_isSome.trans Finmap.mem_keys.symm
      · simp [hx]⟩

/-- Left-biased union of stores.  Compatibility makes the bias immaterial. -/
def merge (σ ρ : Store) : Store :=
  Finmap.union
    (show Finmap (fun _ : Atom => Value) from σ)
    (show Finmap (fun _ : Atom => Value) from ρ)

/-- Two stores agree wherever both are defined. -/
def Compatible (σ ρ : Store) : Prop :=
  ∀ x v w, σ.lookup x = some v → ρ.lookup x = some w → v = w

@[simp] theorem domain_empty : domain (∅ : Store) = ∅ := by
  rfl

@[simp] theorem lookup_empty (x : Atom) : lookup (∅ : Store) x = none := by
  exact Finmap.lookup_empty x

theorem mem_domain_iff (σ : Store) (x : Atom) :
    x ∈ σ.domain ↔ ∃ v, σ.lookup x = some v := by
  exact Finmap.mem_iff

theorem lookup_eq_none_iff (σ : Store) (x : Atom) :
    σ.lookup x = none ↔ x ∉ σ.domain := by
  exact Finmap.lookup_eq_none

/-- Two stores are equal when all lookups agree. -/
theorem ext {σ ρ : Store} (h : ∀ x, σ.lookup x = ρ.lookup x) : σ = ρ := by
  change (∀ x, Finmap.lookup x σ = Finmap.lookup x ρ) at h
  exact Finmap.ext_lookup h

theorem eq_empty_of_domain_eq_empty {σ : Store} (h : σ.domain = ∅) :
    σ = ∅ := by
  apply ext
  intro x
  rw [lookup_empty]
  apply (lookup_eq_none_iff σ x).2
  rw [h]
  exact Finset.notMem_empty x

@[simp] theorem domain_restrict (σ : Store) (X : Finset Atom) :
    (σ.restrict X).domain = σ.domain ∩ X := by
  exact Finmap.keysLookupEquiv_symm_apply_keys _

@[simp] theorem lookup_restrict (σ : Store) (X : Finset Atom) (x : Atom) :
    (σ.restrict X).lookup x = if x ∈ X then σ.lookup x else none := by
  exact Finmap.keysLookupEquiv_symm_apply_lookup _ _

@[simp] theorem restrict_empty (σ : Store) : σ.restrict ∅ = ∅ := by
  apply ext
  intro x
  rw [lookup_restrict]
  exact lookup_empty x |>.symm

@[simp] theorem empty_restrict (X : Finset Atom) :
    (∅ : Store).restrict X = ∅ := by
  apply ext
  intro x
  rw [lookup_restrict]
  by_cases hx : x ∈ X <;> simp [hx]

theorem restrict_restrict (σ : Store) (X Y : Finset Atom) :
    (σ.restrict X).restrict Y = σ.restrict (X ∩ Y) := by
  apply ext
  intro x
  simp only [lookup_restrict, Finset.mem_inter]
  by_cases hx : x ∈ X <;> by_cases hy : x ∈ Y <;> simp [hx, hy]

theorem restrict_congr (σ : Store) {X Y : Finset Atom}
    (h : ∀ x ∈ σ.domain, x ∈ X ↔ x ∈ Y) :
    σ.restrict X = σ.restrict Y := by
  apply ext
  intro x
  rw [lookup_restrict, lookup_restrict]
  by_cases hx : x ∈ σ.domain
  · have hXY := h x hx
    by_cases hxX : x ∈ X
    · have hxY : x ∈ Y := hXY.1 hxX
      simp [hxX, hxY]
    · have hxY : x ∉ Y := fun hy => hxX (hXY.2 hy)
      simp [hxX, hxY]
  · have none : σ.lookup x = none := (lookup_eq_none_iff σ x).2 hx
    by_cases hxX : x ∈ X <;> by_cases hxY : x ∈ Y <;> simp [hxX, hxY, none]

theorem restrict_eq_self (σ : Store) {X : Finset Atom}
    (h : σ.domain ⊆ X) : σ.restrict X = σ := by
  apply ext
  intro x
  rw [lookup_restrict]
  by_cases hx : x ∈ X
  · simp [hx]
  · have absent : x ∉ σ.domain := fun hdom => hx (h hdom)
    simp [hx, (lookup_eq_none_iff σ x).2 absent]

@[simp] theorem restrict_domain (σ : Store) :
    σ.restrict σ.domain = σ :=
  restrict_eq_self σ (fun _ h => h)

@[simp] theorem domain_merge (σ ρ : Store) :
    (σ.merge ρ).domain = σ.domain ∪ ρ.domain := by
  change
    (Finmap.union
      (show Finmap (fun _ : Atom => Value) from σ)
      (show Finmap (fun _ : Atom => Value) from ρ)).keys = _
  exact Finmap.keys_union

theorem lookup_merge_left (σ ρ : Store) {x : Atom}
    (h : x ∈ σ.domain) : (σ.merge ρ).lookup x = σ.lookup x := by
  change Finmap.lookup x (Finmap.union σ ρ) = Finmap.lookup x σ
  exact Finmap.lookup_union_left h

theorem lookup_merge_right (σ ρ : Store) {x : Atom}
    (h : x ∉ σ.domain) : (σ.merge ρ).lookup x = ρ.lookup x := by
  change Finmap.lookup x (Finmap.union σ ρ) = Finmap.lookup x ρ
  exact Finmap.lookup_union_right h

@[simp] theorem empty_merge (σ : Store) : (∅ : Store).merge σ = σ := by
  change Finmap.union ∅ σ = σ
  exact Finmap.empty_union

@[simp] theorem merge_empty (σ : Store) : σ.merge ∅ = σ := by
  change Finmap.union σ ∅ = σ
  exact Finmap.union_empty

theorem merge_assoc (σ ρ τ : Store) :
    (σ.merge ρ).merge τ = σ.merge (ρ.merge τ) := by
  change Finmap.union (Finmap.union σ ρ) τ =
    Finmap.union σ (Finmap.union ρ τ)
  exact Finmap.union_assoc

theorem restrict_merge (σ ρ : Store) (X : Finset Atom) :
    (σ.merge ρ).restrict X = (σ.restrict X).merge (ρ.restrict X) := by
  apply ext
  intro x
  by_cases hxX : x ∈ X
  · rw [lookup_restrict, if_pos hxX]
    by_cases hxσ : x ∈ σ.domain
    · rw [lookup_merge_left σ ρ hxσ]
      rw [lookup_merge_left]
      · rw [lookup_restrict, if_pos hxX]
      · simp [hxσ, hxX]
    · rw [lookup_merge_right σ ρ hxσ]
      rw [lookup_merge_right]
      · rw [lookup_restrict, if_pos hxX]
      · simp [hxσ]
  · rw [lookup_restrict, if_neg hxX]
    have hxσ : x ∉ (σ.restrict X).domain := by simp [hxX]
    rw [lookup_merge_right _ _ hxσ, lookup_restrict, if_neg hxX]

theorem restrict_eq_empty_of_disjoint (σ : Store) {X : Finset Atom}
    (h : Disjoint σ.domain X) : σ.restrict X = ∅ := by
  apply ext
  intro x
  rw [lookup_restrict, lookup_empty]
  by_cases hxX : x ∈ X
  · have hxσ : x ∉ σ.domain := fun hxσ => Finset.disjoint_left.1 h hxσ hxX
    simp [hxX, (lookup_eq_none_iff σ x).2 hxσ]
  · simp [hxX]

theorem restrict_merge_left {σ ρ : Store} {X : Finset Atom}
    (hσ : σ.domain ⊆ X) (hρ : Disjoint ρ.domain X) :
    (σ.merge ρ).restrict X = σ := by
  rw [restrict_merge, restrict_eq_self σ hσ,
    restrict_eq_empty_of_disjoint ρ hρ, merge_empty]

theorem restrict_merge_left_full {σ ρ : Store} {X : Finset Atom}
    (hσ : σ.domain = X) : (σ.merge ρ).restrict X = σ := by
  apply ext
  intro x
  rw [lookup_restrict]
  by_cases hx : x ∈ X
  · rw [if_pos hx, lookup_merge_left]
    simpa [hσ] using hx
  · rw [if_neg hx]
    apply Eq.symm
    apply (lookup_eq_none_iff σ x).2
    simpa [hσ] using hx

theorem restrict_restricted_domain (σ : Store) (X : Finset Atom) :
    σ.restrict (σ.restrict X).domain = σ.restrict X := by
  rw [domain_restrict]
  apply restrict_congr
  intro x hx
  simp [hx]

theorem Compatible.refl (σ : Store) : Compatible σ σ := by
  intro x v w hv hw
  rw [hv] at hw
  exact Option.some.inj hw

theorem Compatible.symm {σ ρ : Store} (h : Compatible σ ρ) :
    Compatible ρ σ := by
  intro x v w hv hw
  exact (h x w v hw hv).symm

theorem Compatible.restrict_left {σ ρ : Store} (h : Compatible σ ρ)
    (X : Finset Atom) : Compatible (σ.restrict X) ρ := by
  intro x v w hv hw
  rw [lookup_restrict] at hv
  split at hv
  · exact h x v w hv hw
  · contradiction

theorem Compatible.restrict_right {σ ρ : Store} (h : Compatible σ ρ)
    (X : Finset Atom) : Compatible σ (ρ.restrict X) :=
  (h.symm.restrict_left X).symm

theorem Compatible.of_disjoint {σ ρ : Store}
    (h : Disjoint σ.domain ρ.domain) : Compatible σ ρ := by
  intro x v w hv hw
  have hxσ : x ∈ σ.domain := (mem_domain_iff σ x).2 ⟨v, hv⟩
  have hxρ : x ∈ ρ.domain := (mem_domain_iff ρ x).2 ⟨w, hw⟩
  exact (Finset.disjoint_left.1 h hxσ hxρ).elim

theorem Compatible.merge_left {σ ρ τ : Store}
    (hσ : Compatible σ τ) (hρ : Compatible ρ τ) :
    Compatible (σ.merge ρ) τ := by
  intro x v w hv hw
  by_cases hx : x ∈ σ.domain
  · rw [lookup_merge_left σ ρ hx] at hv
    exact hσ x v w hv hw
  · rw [lookup_merge_right σ ρ hx] at hv
    exact hρ x v w hv hw

theorem Compatible.merge_right {σ ρ τ : Store}
    (hσ : Compatible σ ρ) (hτ : Compatible σ τ) :
    Compatible σ (ρ.merge τ) :=
  (hσ.symm.merge_left hτ.symm).symm

theorem Compatible.of_merge_left {σ ρ τ : Store}
    (h : Compatible (σ.merge ρ) τ) : Compatible σ τ := by
  intro x v w hv hw
  have hx : x ∈ σ.domain := (mem_domain_iff σ x).2 ⟨v, hv⟩
  apply h x v w
  · rwa [lookup_merge_left σ ρ hx]
  · exact hw

theorem Compatible.of_merge_right {σ ρ τ : Store}
    (hσρ : Compatible σ ρ) (h : Compatible (σ.merge ρ) τ) :
    Compatible ρ τ := by
  intro x v w hv hw
  by_cases hx : x ∈ σ.domain
  · obtain ⟨u, hu⟩ := (mem_domain_iff σ x).1 hx
    have huv : u = v := hσρ x u v hu hv
    subst u
    exact h x v w (by rwa [lookup_merge_left σ ρ hx]) hw
  · exact h x v w (by rwa [lookup_merge_right σ ρ hx]) hw

theorem merge_comm {σ ρ : Store} (h : Compatible σ ρ) :
    σ.merge ρ = ρ.merge σ := by
  apply ext
  intro x
  by_cases hxσ : x ∈ σ.domain
  · obtain ⟨v, hv⟩ := (mem_domain_iff σ x).1 hxσ
    rw [lookup_merge_left σ ρ hxσ, hv]
    by_cases hxρ : x ∈ ρ.domain
    · obtain ⟨w, hw⟩ := (mem_domain_iff ρ x).1 hxρ
      rw [lookup_merge_left ρ σ hxρ, hw]
      exact congrArg some (h x v w hv hw)
    · rw [lookup_merge_right ρ σ hxρ, hv]
  · rw [lookup_merge_right σ ρ hxσ]
    by_cases hxρ : x ∈ ρ.domain
    · rw [lookup_merge_left ρ σ hxρ]
    · rw [lookup_merge_right ρ σ hxρ]
      exact ((lookup_eq_none_iff ρ x).2 hxρ).trans
        ((lookup_eq_none_iff σ x).2 hxσ).symm

end Store

/-- A nonempty collection of stores with one common finite domain. -/
structure Capability where
  domain : Finset Atom
  stores : Store → Prop
  nonempty : ∃ σ, stores σ
  fixedDomain : ∀ σ, stores σ → σ.domain = domain

namespace Capability

instance : Membership Store Capability := ⟨fun m σ => m.stores σ⟩

/-- Membership in a capability determines the store domain. -/
theorem mem_domain {m : Capability} {σ : Store} (h : σ ∈ m) :
    σ.domain = m.domain :=
  m.fixedDomain σ h

/-- Extensionality by domain and store membership. -/
@[ext] theorem ext {m n : Capability} (domain : m.domain = n.domain)
    (stores : ∀ σ, σ ∈ m ↔ σ ∈ n) : m = n := by
  cases m with
  | mk Xm storesM neM domM =>
      cases n with
      | mk Xn storesN neN domN =>
          simp only at domain
          subst Xn
          have same : storesM = storesN := by
            funext σ
            exact propext (stores σ)
          subst storesN
          rfl

/-- The unit capability, containing only the empty store. -/
def unit : Capability where
  domain := ∅
  stores := fun σ => σ = ∅
  nonempty := ⟨∅, rfl⟩
  fixedDomain := by rintro σ rfl; rfl

@[simp] theorem unit_domain : unit.domain = ∅ :=
  rfl

@[simp] theorem mem_unit_iff (σ : Store) : σ ∈ unit ↔ σ = ∅ :=
  Iff.rfl

theorem eq_unit_of_domain_eq_empty {m : Capability} (h : m.domain = ∅) :
    m = unit := by
  apply ext h
  intro σ
  constructor
  · intro hσ
    exact (mem_unit_iff σ).2
      (Store.eq_empty_of_domain_eq_empty (m.mem_domain hσ |>.trans h))
  · intro hσ
    obtain rfl := (mem_unit_iff σ).1 hσ
    obtain ⟨ρ, hρ⟩ := m.nonempty
    have : ρ = ∅ :=
      Store.eq_empty_of_domain_eq_empty (m.mem_domain hρ |>.trans h)
    simpa [this] using hρ

/-- The deterministic capability containing exactly one store. -/
def singleton (σ : Store) : Capability where
  domain := σ.domain
  stores := fun ρ => ρ = σ
  nonempty := ⟨σ, rfl⟩
  fixedDomain := by rintro ρ rfl; rfl

@[simp] theorem singleton_domain (σ : Store) :
    (singleton σ).domain = σ.domain :=
  rfl

@[simp] theorem mem_singleton_iff (σ ρ : Store) :
    ρ ∈ singleton σ ↔ ρ = σ :=
  Iff.rfl

/-- Project a capability to a finite set of visible atoms. -/
def restrict (m : Capability) (X : Finset Atom) : Capability where
  domain := m.domain ∩ X
  stores := fun ρ => ∃ σ, σ ∈ m ∧ σ.restrict X = ρ
  nonempty := by
    obtain ⟨σ, hσ⟩ := m.nonempty
    exact ⟨σ.restrict X, σ, hσ, rfl⟩
  fixedDomain := by
    rintro ρ ⟨σ, hσ, rfl⟩
    rw [Store.domain_restrict, m.mem_domain hσ]

@[simp] theorem restrict_domain (m : Capability) (X : Finset Atom) :
    (m.restrict X).domain = m.domain ∩ X :=
  rfl

theorem mem_restrict_iff (m : Capability) (X : Finset Atom) (σ : Store) :
    σ ∈ m.restrict X ↔ ∃ ρ, ρ ∈ m ∧ ρ.restrict X = σ :=
  Iff.rfl

theorem restrict_restrict (m : Capability) (X Y : Finset Atom) :
    (m.restrict X).restrict Y = m.restrict (X ∩ Y) := by
  apply ext
  · simp [Finset.inter_assoc]
  · intro σ
    constructor
    · rintro ⟨ρ, ⟨τ, hτ, rfl⟩, rfl⟩
      exact ⟨τ, hτ, (Store.restrict_restrict τ X Y).symm⟩
    · rintro ⟨τ, hτ, rfl⟩
      exact ⟨τ.restrict X, ⟨τ, hτ, rfl⟩,
        Store.restrict_restrict τ X Y⟩

@[simp] theorem restrict_empty (m : Capability) : m.restrict ∅ = unit := by
  apply ext
  · simp
  · intro σ
    constructor
    · rintro ⟨ρ, hρ, rfl⟩
      exact Store.restrict_empty ρ
    · rintro rfl
      obtain ⟨ρ, hρ⟩ := m.nonempty
      exact ⟨ρ, hρ, Store.restrict_empty ρ⟩

@[simp] theorem restrict_singleton (σ : Store) (X : Finset Atom) :
    (singleton σ).restrict X = singleton (σ.restrict X) := by
  apply ext
  · simp [Store.domain_restrict]
  · intro ρ
    constructor
    · rintro ⟨τ, rfl, rfl⟩
      rfl
    · intro h
      rw [mem_singleton_iff] at h
      subst ρ
      exact ⟨σ, rfl, rfl⟩

@[simp] theorem restrict_domain_self (m : Capability) :
    m.restrict m.domain = m := by
  apply ext
  · simp
  · intro σ
    constructor
    · rintro ⟨ρ, hρ, same⟩
      have hdom : ρ.domain ⊆ m.domain := by
        rw [m.mem_domain hρ]
      rw [Store.restrict_eq_self ρ hdom] at same
      simpa [← same] using hρ
    · intro hσ
      have hdom : σ.domain ⊆ m.domain := by
        rw [m.mem_domain hσ]
      exact ⟨σ, hσ, Store.restrict_eq_self σ hdom⟩

/-- Projection/Kripke order on capabilities. -/
def Refines (m n : Capability) : Prop :=
  m = n.restrict m.domain

/-- Same-domain inclusion between the possible stores of two capabilities. -/
def Subset (m n : Capability) : Prop :=
  m.domain = n.domain ∧ ∀ σ : Store, σ ∈ m → σ ∈ n

theorem refines_refl (m : Capability) : Refines m m := by
  rw [Refines, restrict_domain_self]

theorem refines_domain_subset {m n : Capability} (h : Refines m n) :
    m.domain ⊆ n.domain := by
  rw [Refines] at h
  have hd := congrArg Capability.domain h
  simp only [restrict_domain] at hd
  intro x hx
  rw [hd] at hx
  exact (Finset.mem_inter.1 hx).1

theorem refines_trans {m n p : Capability} (hmn : Refines m n)
    (hnp : Refines n p) : Refines m p := by
  have hdom : m.domain ⊆ n.domain := refines_domain_subset hmn
  unfold Refines at hmn hnp ⊢
  calc
    m = n.restrict m.domain := hmn
    _ = (p.restrict n.domain).restrict m.domain := by rw [← hnp]
    _ = p.restrict (n.domain ∩ m.domain) := restrict_restrict _ _ _
    _ = p.restrict m.domain := by rw [Finset.inter_eq_right.2 hdom]

theorem refines_antisymm {m n : Capability} (hmn : Refines m n)
    (hnm : Refines n m) : m = n := by
  have hmnDom := refines_domain_subset hmn
  have hnmDom := refines_domain_subset hnm
  have hdom : m.domain = n.domain := Finset.Subset.antisymm hmnDom hnmDom
  rw [Refines, hdom, restrict_domain_self] at hmn
  exact hmn

theorem restrict_refines (m : Capability) (X : Finset Atom) :
    Refines (m.restrict X) m := by
  unfold Refines
  rw [restrict_domain]
  calc
    m.restrict X = (m.restrict m.domain).restrict X := by
      rw [restrict_domain_self]
    _ = m.restrict (m.domain ∩ X) := restrict_restrict _ _ _

theorem subset_refl (m : Capability) : Subset m m :=
  ⟨rfl, fun _ h => h⟩

theorem subset_trans {m n p : Capability} (hmn : Subset m n)
    (hnp : Subset n p) : Subset m p := by
  exact ⟨hmn.1.trans hnp.1, fun σ hσ => hnp.2 σ (hmn.2 σ hσ)⟩

theorem subset_antisymm {m n : Capability} (hmn : Subset m n)
    (hnm : Subset n m) : m = n := by
  apply ext hmn.1
  intro σ
  exact ⟨fun h => hmn.2 σ h, fun h => hnm.2 σ h⟩

theorem subset_restrict {m n : Capability} (h : Subset m n)
    (X : Finset Atom) : Subset (m.restrict X) (n.restrict X) := by
  constructor
  · simp [h.1]
  · rintro σ ⟨ρ, hρ, rfl⟩
    exact ⟨ρ, h.2 ρ hρ, rfl⟩

/-! ## Algebraic operations -/

/-- Every store from `m` agrees with every store from `n`. -/
def Compatible (m n : Capability) : Prop :=
  ∀ {σ ρ : Store}, σ ∈ m → ρ ∈ n → Store.Compatible σ ρ

/-- Product of compatible capabilities. -/
def product (m n : Capability) (h : Compatible m n) : Capability where
  domain := m.domain ∪ n.domain
  stores := fun τ => ∃ σ ∈ m, ∃ ρ ∈ n,
    Store.Compatible σ ρ ∧ τ = σ.merge ρ
  nonempty := by
    obtain ⟨σ, hσ⟩ := m.nonempty
    obtain ⟨ρ, hρ⟩ := n.nonempty
    exact ⟨σ.merge ρ, σ, hσ, ρ, hρ, h hσ hρ, rfl⟩
  fixedDomain := by
    rintro τ ⟨σ, hσ, ρ, hρ, compat, rfl⟩
    rw [Store.domain_merge, m.mem_domain hσ, n.mem_domain hρ]

/-- The additive sum is defined only for capabilities with the same domain. -/
def SumDefined (m n : Capability) : Prop :=
  m.domain = n.domain

/-- Additive union of two same-domain capabilities. -/
def sum (m n : Capability) (h : SumDefined m n) : Capability where
  domain := m.domain
  stores := fun σ => σ ∈ m ∨ σ ∈ n
  nonempty := by
    obtain ⟨σ, hσ⟩ := m.nonempty
    exact ⟨σ, Or.inl hσ⟩
  fixedDomain := by
    intro σ hσ
    rcases hσ with hσ | hσ
    · exact m.mem_domain hσ
    · exact (n.mem_domain hσ).trans h.symm

theorem Compatible.symm {m n : Capability} (h : Compatible m n) :
    Compatible n m := by
  intro σ ρ hσ hρ
  exact (h hρ hσ).symm

theorem compatible_unit_right (m : Capability) : Compatible m unit := by
  intro σ ρ hσ hρ
  rw [mem_unit_iff] at hρ
  subst ρ
  exact Store.Compatible.of_disjoint (by simp)

theorem compatible_unit_left (m : Capability) : Compatible unit m :=
  Capability.Compatible.symm (compatible_unit_right m)

theorem Compatible.restrict_left {m n : Capability} (h : Compatible m n)
    (X : Finset Atom) : Compatible (m.restrict X) n := by
  intro σ ρ hσ hρ
  obtain ⟨τ, hτ, rfl⟩ := hσ
  exact (h hτ hρ).restrict_left X

theorem Compatible.restrict_right {m n : Capability} (h : Compatible m n)
    (X : Finset Atom) : Compatible m (n.restrict X) :=
  Capability.Compatible.symm
    (Capability.Compatible.restrict_left (Capability.Compatible.symm h) X)

@[simp] theorem product_domain (m n : Capability) (h : Compatible m n) :
    (product m n h).domain = m.domain ∪ n.domain :=
  rfl

theorem mem_product_iff (m n : Capability) (h : Compatible m n) (τ : Store) :
    τ ∈ product m n h ↔ ∃ σ ∈ m, ∃ ρ ∈ n,
      Store.Compatible σ ρ ∧ τ = σ.merge ρ :=
  Iff.rfl

@[simp] theorem sum_domain (m n : Capability) (h : SumDefined m n) :
    (sum m n h).domain = m.domain :=
  rfl

theorem mem_sum_iff (m n : Capability) (h : SumDefined m n) (σ : Store) :
    σ ∈ sum m n h ↔ σ ∈ m ∨ σ ∈ n :=
  Iff.rfl

theorem product_unit_right (m : Capability) :
    product m unit (compatible_unit_right m) = m := by
  apply ext
  · simp
  · intro τ
    constructor
    · rintro ⟨σ, hσ, ρ, hρ, compat, rfl⟩
      rw [mem_unit_iff] at hρ
      subst ρ
      simpa using hσ
    · intro hτ
      exact ⟨τ, hτ, ∅, rfl, compatible_unit_right m hτ rfl, by simp⟩

theorem product_unit_left (m : Capability) :
    product unit m (compatible_unit_left m) = m := by
  apply ext
  · simp
  · intro τ
    constructor
    · rintro ⟨σ, hσ, ρ, hρ, compat, rfl⟩
      rw [mem_unit_iff] at hσ
      subst σ
      simpa using hρ
    · intro hτ
      exact ⟨∅, rfl, τ, hτ, compatible_unit_left m rfl hτ, by simp⟩

theorem product_comm {m n : Capability} (h : Compatible m n) :
    product m n h = product n m h.symm := by
  apply ext
  · exact Finset.union_comm _ _
  · intro τ
    constructor
    · rintro ⟨σ, hσ, ρ, hρ, compat, rfl⟩
      exact ⟨ρ, hρ, σ, hσ, compat.symm, Store.merge_comm compat⟩
    · rintro ⟨ρ, hρ, σ, hσ, compat, rfl⟩
      exact ⟨σ, hσ, ρ, hρ, compat.symm, Store.merge_comm compat⟩

theorem product_restrict_left {m n : Capability} (h : Compatible m n) :
    (product m n h).restrict m.domain = m := by
  apply ext
  · simp
  · intro τ
    constructor
    · rintro ⟨υ, ⟨σ, hσ, ρ, hρ, compat, rfl⟩, rfl⟩
      rw [Store.restrict_merge_left_full (m.mem_domain hσ)]
      exact hσ
    · intro hτ
      obtain ⟨ρ, hρ⟩ := n.nonempty
      refine ⟨τ.merge ρ, ⟨τ, hτ, ρ, hρ, h hτ hρ, rfl⟩, ?_⟩
      apply Store.ext
      intro x
      rw [Store.lookup_restrict]
      by_cases hx : x ∈ m.domain
      · rw [if_pos hx, Store.lookup_merge_left]
        simpa [m.mem_domain hτ] using hx
      · rw [if_neg hx]
        exact (Store.lookup_eq_none_iff τ x).2 (by simpa [m.mem_domain hτ] using hx) |>.symm

theorem product_refines_left {m n : Capability} (h : Compatible m n) :
    Refines m (product m n h) := by
  rw [Refines, product_restrict_left]

theorem product_refines_right {m n : Capability} (h : Compatible m n) :
    Refines n (product m n h) := by
  rw [product_comm h]
  exact product_refines_left h.symm

theorem Compatible.refines_right {m n p : Capability} (hmn : Refines m n)
    (h : Compatible p n) : Compatible p m := by
  intro σ ρ hσ hρ
  rw [Refines] at hmn
  rw [hmn] at hρ
  obtain ⟨τ, hτ, rfl⟩ := hρ
  exact (h hσ hτ).restrict_right m.domain

theorem Compatible.refines_left {m n p : Capability} (hmn : Refines m n)
    (h : Compatible n p) : Compatible m p :=
  Capability.Compatible.symm
    (Capability.Compatible.refines_right hmn (Capability.Compatible.symm h))

theorem restrict_product {m n : Capability} (h : Compatible m n)
    (X : Finset Atom) :
    (product m n h).restrict X =
      product (m.restrict X) (n.restrict X)
        (Capability.Compatible.restrict_right
          (Capability.Compatible.restrict_left h X) X) := by
  apply ext
  · simp [Finset.union_inter_distrib_right]
  · intro τ
    constructor
    · rintro ⟨υ, ⟨σ, hσ, ρ, hρ, compat, rfl⟩, rfl⟩
      exact ⟨σ.restrict X, ⟨σ, hσ, rfl⟩,
        ρ.restrict X, ⟨ρ, hρ, rfl⟩,
        (compat.restrict_left X).restrict_right X,
        Store.restrict_merge σ ρ X⟩
    · rintro ⟨σ, ⟨σ', hσ', rfl⟩, ρ, ⟨ρ', hρ', rfl⟩, compat, rfl⟩
      exact ⟨σ'.merge ρ',
        ⟨σ', hσ', ρ', hρ', h hσ' hρ', rfl⟩,
        Store.restrict_merge σ' ρ' X⟩

theorem product_assoc {m n p : Capability}
    (hmn : Compatible m n) (hmnp : Compatible (product m n hmn) p) :
    ∃ (hnp : Compatible n p)
      (hm_np : Compatible m (product n p hnp)),
      product (product m n hmn) p hmnp =
        product m (product n p hnp) hm_np := by
  have hmp : Compatible m p := by
    intro σ τ hσ hτ
    obtain ⟨ρ, hρ⟩ := n.nonempty
    have hprod : σ.merge ρ ∈ product m n hmn :=
      ⟨σ, hσ, ρ, hρ, hmn hσ hρ, rfl⟩
    exact Store.Compatible.of_merge_left (hmnp hprod hτ)
  have hnp : Compatible n p := by
    intro ρ τ hρ hτ
    obtain ⟨σ, hσ⟩ := m.nonempty
    have hσρ := hmn hσ hρ
    have hprod : σ.merge ρ ∈ product m n hmn :=
      ⟨σ, hσ, ρ, hρ, hσρ, rfl⟩
    exact Store.Compatible.of_merge_right hσρ (hmnp hprod hτ)
  have hm_np : Compatible m (product n p hnp) := by
    intro σ υ hσ hυ
    obtain ⟨ρ, hρ, τ, hτ, compat, rfl⟩ := hυ
    exact Store.Compatible.merge_right (hmn hσ hρ) (hmp hσ hτ)
  refine ⟨hnp, hm_np, ?_⟩
  apply ext
  · simp [Finset.union_assoc]
  · intro υ
    constructor
    · rintro ⟨ω, ⟨σ, hσ, ρ, hρ, hσρ, rfl⟩,
        τ, hτ, hσρτ, rfl⟩
      have hρτ := Store.Compatible.of_merge_right hσρ hσρτ
      have hστ := Store.Compatible.of_merge_left hσρτ
      refine ⟨σ, hσ, ρ.merge τ, ?_, ?_, ?_⟩
      · exact ⟨ρ, hρ, τ, hτ, hρτ, rfl⟩
      · exact Store.Compatible.merge_right hσρ hστ
      · exact Store.merge_assoc σ ρ τ
    · rintro ⟨σ, hσ, ω, ⟨ρ, hρ, τ, hτ, hρτ, rfl⟩,
        hσρτ, rfl⟩
      have hσρ := (Store.Compatible.of_merge_left hσρτ.symm).symm
      have hστ := Store.Compatible.of_merge_right hρτ hσρτ.symm |>.symm
      refine ⟨σ.merge ρ, ?_, τ, hτ, ?_, ?_⟩
      · exact ⟨σ, hσ, ρ, hρ, hσρ, rfl⟩
      · exact Store.Compatible.merge_left hστ hρτ
      · exact (Store.merge_assoc σ ρ τ).symm

theorem sum_comm {m n : Capability} (h : SumDefined m n) :
    sum m n h = sum n m h.symm := by
  apply ext
  · exact h
  · intro σ
    exact or_comm

theorem sum_assoc {m n p : Capability}
    (hmn : SumDefined m n) (hmnp : SumDefined (sum m n hmn) p) :
    sum (sum m n hmn) p hmnp =
      sum m (sum n p (hmn.symm.trans hmnp)) hmn := by
  apply ext
  · rfl
  · intro σ
    change ((σ ∈ m ∨ σ ∈ n) ∨ σ ∈ p) ↔
      (σ ∈ m ∨ σ ∈ n ∨ σ ∈ p)
    tauto

theorem subset_sum_left {m n : Capability} (h : SumDefined m n) :
    Subset m (sum m n h) :=
  ⟨rfl, fun _ hσ => Or.inl hσ⟩

theorem subset_sum_right {m n : Capability} (h : SumDefined m n) :
    Subset n (sum m n h) :=
  ⟨h.symm, fun _ hσ => Or.inr hσ⟩

theorem restrict_sum {m n : Capability} (h : SumDefined m n)
    (X : Finset Atom) :
    (sum m n h).restrict X =
      sum (m.restrict X) (n.restrict X)
        (by
          unfold SumDefined at h ⊢
          exact congrArg (fun Y => Y ∩ X) h) := by
  apply ext
  · rfl
  · intro σ
    constructor
    · rintro ⟨ρ, hρ | hρ, rfl⟩
      · exact Or.inl ⟨ρ, hρ, rfl⟩
      · exact Or.inr ⟨ρ, hρ, rfl⟩
    · rintro (⟨ρ, hρ, rfl⟩ | ⟨ρ, hρ, rfl⟩)
      · exact ⟨ρ, Or.inl hρ, rfl⟩
      · exact ⟨ρ, Or.inr hρ, rfl⟩

/-! ## Fibers -/

/-- The fiber selected by a store known to occur as a projection of `m`. -/
def fiber (m : Capability) (σ : Store)
    (hne : ∃ ρ, ρ ∈ m ∧ ρ.restrict σ.domain = σ) : Capability where
  domain := m.domain
  stores := fun ρ => ρ ∈ m ∧ ρ.restrict σ.domain = σ
  nonempty := hne
  fixedDomain := by
    intro ρ hρ
    exact m.mem_domain hρ.1

/-- `f` is the fiber of `m` selected by the `X`-projection `σ`. -/
def IsFiber (f m : Capability) (X : Finset Atom) (σ : Store) : Prop :=
  σ ∈ m.restrict X ∧
  f.domain = m.domain ∧
  ∀ ρ, ρ ∈ f ↔ ρ ∈ m ∧ ρ.restrict σ.domain = σ

/-- `f` is one of the fibers of `m` over `X`. -/
def FiberMember (f m : Capability) (X : Finset Atom) : Prop :=
  ∃ σ, IsFiber f m X σ

theorem mem_fiber_iff (m : Capability) (σ : Store)
    (hne : ∃ ρ, ρ ∈ m ∧ ρ.restrict σ.domain = σ) (ρ : Store) :
    ρ ∈ m.fiber σ hne ↔ ρ ∈ m ∧ ρ.restrict σ.domain = σ :=
  Iff.rfl

theorem fiber_from_projection (m : Capability) (X : Finset Atom) (σ : Store)
    (hσ : σ ∈ m.restrict X) :
    ∃ f, IsFiber f m X σ := by
  obtain ⟨ρ, hρ, rfl⟩ := hσ
  have hne : ∃ τ, τ ∈ m ∧
      τ.restrict (ρ.restrict X).domain = ρ.restrict X :=
    ⟨ρ, hρ, Store.restrict_restricted_domain ρ X⟩
  refine ⟨m.fiber (ρ.restrict X) hne, ?_⟩
  exact ⟨⟨ρ, hρ, rfl⟩, rfl, fun _ => Iff.rfl⟩

theorem IsFiber.projection_mem {f m : Capability} {X : Finset Atom}
    {σ : Store} (h : IsFiber f m X σ) : σ ∈ m.restrict X :=
  h.1

theorem IsFiber.domain_eq {f m : Capability} {X : Finset Atom}
    {σ : Store} (h : IsFiber f m X σ) : f.domain = m.domain :=
  h.2.1

theorem IsFiber.mem_iff {f m : Capability} {X : Finset Atom}
    {σ ρ : Store} (h : IsFiber f m X σ) :
    ρ ∈ f ↔ ρ ∈ m ∧ ρ.restrict σ.domain = σ :=
  h.2.2 ρ

theorem IsFiber.source_mem {f m : Capability} {X : Finset Atom}
    {σ ρ : Store} (h : IsFiber f m X σ) (hρ : ρ ∈ f) : ρ ∈ m :=
  (h.mem_iff.1 hρ).1

theorem IsFiber.store_restrict {f m : Capability} {X : Finset Atom}
    {σ ρ : Store} (h : IsFiber f m X σ) (hρ : ρ ∈ f) :
    ρ.restrict σ.domain = σ :=
  (h.mem_iff.1 hρ).2

theorem fiber_from_store (m : Capability) (X : Finset Atom) {σ : Store}
    (hσ : σ ∈ m) :
    ∃ f, IsFiber f m X (σ.restrict X) ∧ σ ∈ f := by
  have hproj : σ.restrict X ∈ m.restrict X := ⟨σ, hσ, rfl⟩
  obtain ⟨f, hf⟩ := fiber_from_projection m X (σ.restrict X) hproj
  refine ⟨f, hf, ?_⟩
  apply hf.mem_iff.2
  exact ⟨hσ, Store.restrict_restricted_domain σ X⟩

theorem IsFiber.restrict_input {f m : Capability} {X : Finset Atom}
    {σ ρ : Store} (h : IsFiber f m X σ) (hρ : ρ ∈ f) :
    ρ.restrict X = σ := by
  obtain ⟨τ, hτ, same⟩ := h.projection_mem
  have hρm := h.source_mem hρ
  have hσdom : σ.domain = m.domain ∩ X :=
    (m.restrict X).mem_domain h.projection_mem
  rw [← h.store_restrict hρ, hσdom]
  apply Store.restrict_congr
  intro x hx
  have hxM : x ∈ m.domain := by
    rw [← h.domain_eq, ← f.mem_domain hρ]
    exact hx
  simp [hxM]

/-! ## Fiber extensions -/

/-- A relation assigning an output capability to each store on an input
domain.  Extensionality makes the assigned capability unique as a set of
stores, without requiring the relation itself to be functional. -/
structure FiberExtension where
  input : Finset Atom
  output : Finset Atom
  disjoint : Disjoint input output
  rel : Store → Capability → Prop
  rel_domain : ∀ σ m, σ.domain = input → rel σ m → m.domain = output
  rel_nonempty : ∀ σ, σ.domain = input →
    ∃ m ρ, rel σ m ∧ ρ ∈ m
  rel_extensional : ∀ σ m n ρ, σ.domain = input →
    rel σ m → rel σ n → (ρ ∈ m ↔ ρ ∈ n)

namespace FiberExtension

/-- An extension may read its input from `m` and writes fresh output atoms. -/
def Applicable (F : FiberExtension) (m : Capability) : Prop :=
  F.input ⊆ m.domain ∧ Disjoint F.output m.domain

/-- `n` is obtained by applying `F` independently to every store of `m`. -/
def Extends (m : Capability) (F : FiberExtension) (n : Capability) : Prop :=
  F.Applicable m ∧
  n.domain = m.domain ∪ F.output ∧
  ∀ τ, τ ∈ n ↔ ∃ σ w ρ,
    σ ∈ m ∧ F.rel (σ.restrict F.input) w ∧ ρ ∈ w ∧
      τ = σ.merge ρ

/-- On `m`, each input store determines at most one output store. -/
def FunctionalOn (F : FiberExtension) (m : Capability) : Prop :=
  ∀ {σ : Store} {w : Capability} {ρ τ : Store},
    σ ∈ m → F.rel (σ.restrict F.input) w →
    ρ ∈ w → τ ∈ w → ρ = τ

theorem projection_domain {F : FiberExtension} {m : Capability}
    (h : F.Applicable m) {σ : Store} (hσ : σ ∈ m) :
    (σ.restrict F.input).domain = F.input := by
  rw [Store.domain_restrict, m.mem_domain hσ]
  exact Finset.inter_eq_right.2 h.1

theorem output_store_domain {F : FiberExtension} {σ ρ : Store}
    {w : Capability} (hσ : σ.domain = F.input) (hrel : F.rel σ w)
    (hρ : ρ ∈ w) : ρ.domain = F.output := by
  rw [w.mem_domain hρ, F.rel_domain σ w hσ hrel]

theorem output_compatible {F : FiberExtension} {m w : Capability}
    {σ ρ : Store} (happ : F.Applicable m) (hσ : σ ∈ m)
    (hrel : F.rel (σ.restrict F.input) w) (hρ : ρ ∈ w) :
    Store.Compatible σ ρ := by
  apply Store.Compatible.of_disjoint
  rw [m.mem_domain hσ,
    output_store_domain (projection_domain happ hσ) hrel hρ]
  exact happ.2.symm

theorem Extends.applicable {F : FiberExtension} {m n : Capability}
    (h : F.Extends m n) : F.Applicable m :=
  h.1

theorem Extends.domain_eq {F : FiberExtension} {m n : Capability}
    (h : F.Extends m n) : n.domain = m.domain ∪ F.output :=
  h.2.1

theorem Extends.mem_iff {F : FiberExtension} {m n : Capability}
    (h : F.Extends m n) (τ : Store) :
    τ ∈ n ↔ ∃ σ w ρ,
      σ ∈ m ∧ F.rel (σ.restrict F.input) w ∧ ρ ∈ w ∧
        τ = σ.merge ρ :=
  h.2.2 τ

theorem extends_exists (F : FiberExtension) (m : Capability)
    (happ : F.Applicable m) : ∃ n, F.Extends m n := by
  let stores : Store → Prop := fun τ => ∃ σ w ρ,
    σ ∈ m ∧ F.rel (σ.restrict F.input) w ∧ ρ ∈ w ∧
      τ = σ.merge ρ
  have ne : ∃ τ, stores τ := by
    obtain ⟨σ, hσ⟩ := m.nonempty
    obtain ⟨w, ρ, hrel, hρ⟩ := F.rel_nonempty (σ.restrict F.input)
      (projection_domain happ hσ)
    exact ⟨σ.merge ρ, σ, w, ρ, hσ, hrel, hρ, rfl⟩
  have fixed : ∀ τ, stores τ → τ.domain = m.domain ∪ F.output := by
    rintro τ ⟨σ, w, ρ, hσ, hrel, hρ, rfl⟩
    rw [Store.domain_merge, m.mem_domain hσ,
      output_store_domain (projection_domain happ hσ) hrel hρ]
  let n : Capability :=
    { domain := m.domain ∪ F.output
      stores := stores
      nonempty := ne
      fixedDomain := fixed }
  exact ⟨n, happ, rfl, fun _ => Iff.rfl⟩

theorem Extends.restrict_base {F : FiberExtension} {m n : Capability}
    (h : F.Extends m n) : n.restrict m.domain = m := by
  apply Capability.ext
  · rw [restrict_domain, h.domain_eq]
    simp
  · intro τ
    constructor
    · rintro ⟨υ, hυ, rfl⟩
      obtain ⟨σ, w, ρ, hσ, hrel, hρ, rfl⟩ := h.mem_iff υ |>.1 hυ
      have hρdom : ρ.domain = F.output :=
        output_store_domain (projection_domain h.applicable hσ) hrel hρ
      rw [Store.restrict_merge_left]
      · exact hσ
      · rw [m.mem_domain hσ]
      · rw [hρdom]
        exact h.applicable.2
    · intro hτ
      obtain ⟨w, ρ, hrel, hρ⟩ := F.rel_nonempty (τ.restrict F.input)
        (projection_domain h.applicable hτ)
      refine ⟨τ.merge ρ, ?_, ?_⟩
      · apply (h.mem_iff _).2
        exact ⟨τ, w, ρ, hτ, hrel, hρ, rfl⟩
      · apply Store.restrict_merge_left
        · rw [m.mem_domain hτ]
        · rw [output_store_domain (projection_domain h.applicable hτ) hrel hρ]
          exact h.applicable.2

theorem Extends.refines {F : FiberExtension} {m n : Capability}
    (h : F.Extends m n) : Capability.Refines m n := by
  rw [Capability.Refines, h.restrict_base]

end FiberExtension

end Capability

end ContextTypes

set_option hygiene false in
scoped[ContextTypes] infix:50 " ⊑ " => ContextTypes.Capability.Refines

set_option hygiene false in
scoped[ContextTypes] infix:50 " ⊆ " => ContextTypes.Capability.Subset
