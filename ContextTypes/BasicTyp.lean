import ContextTypes.OperSem
import ContextTypes.Subst
import ContextTypes.ContextType
import Mathlib.Tactic

set_option autoImplicit false

namespace ContextTypes

/-!
# Basic typing and formation

This module contains the erased simply typed calculus and the static formation
conditions for qualifiers, context types, and bunched contexts.
-/

namespace BasicEnv

/-- Extend an erased environment, replacing any previous binding for `x`. -/
def insert (Δ : BasicEnv) (x : Atom) (T : SimpleType) : BasicEnv :=
  Finmap.insert x T Δ

/-- Remove one binding from an erased environment. -/
def erase (Δ : BasicEnv) (x : Atom) : BasicEnv :=
  Finmap.erase x Δ

/-- Pointwise inclusion of erased typing environments. -/
def Subset (Δ Δ' : BasicEnv) : Prop :=
  ∀ x T, Δ.lookup x = some T → Δ'.lookup x = some T

@[simp] theorem domain_insert (Δ : BasicEnv) (x : Atom) (T : SimpleType) :
    (Δ.insert x T).domain = {x} ∪ Δ.domain := by
  ext y
  simp [domain, insert, Finmap.mem_keys, Finmap.mem_insert]

@[simp] theorem lookup_insert (Δ : BasicEnv) (x : Atom) (T : SimpleType) :
    (Δ.insert x T).lookup x = some T :=
  Finmap.lookup_insert Δ

theorem lookup_insert_of_ne (Δ : BasicEnv) {x y : Atom} (T : SimpleType)
    (h : y ≠ x) : (Δ.insert x T).lookup y = Δ.lookup y :=
  Finmap.lookup_insert_of_ne Δ h

@[simp] theorem lookup_erase (Δ : BasicEnv) (x : Atom) :
    (Δ.erase x).lookup x = none :=
  Finmap.lookup_erase x Δ

theorem lookup_erase_of_ne (Δ : BasicEnv) {x y : Atom} (h : y ≠ x) :
    (Δ.erase x).lookup y = Δ.lookup y :=
  Finmap.lookup_erase_ne h

theorem subset_refl (Δ : BasicEnv) : Δ.Subset Δ :=
  fun _ _ h => h

theorem Subset.trans {Δ₁ Δ₂ Δ₃ : BasicEnv}
    (h₁₂ : Δ₁.Subset Δ₂) (h₂₃ : Δ₂.Subset Δ₃) : Δ₁.Subset Δ₃ :=
  fun x T h => h₂₃ x T (h₁₂ x T h)

theorem Subset.insert {Δ Δ' : BasicEnv} (h : Δ.Subset Δ')
    (x : Atom) (T : SimpleType) :
    (Δ.insert x T).Subset (Δ'.insert x T) := by
  intro y U hy
  by_cases same : y = x
  · subst y
    rw [lookup_insert] at hy ⊢
    exact Option.some.inj hy ▸ rfl
  · rw [lookup_insert_of_ne _ T same] at hy
    rw [lookup_insert_of_ne _ T same]
    exact h y U hy

theorem insert_comm (Δ : BasicEnv) {x y : Atom} (T U : SimpleType)
    (hne : x ≠ y) :
    (Δ.insert x T).insert y U = (Δ.insert y U).insert x T := by
  apply Finmap.ext_lookup
  intro z
  change ((Δ.insert x T).insert y U).lookup z =
    ((Δ.insert y U).insert x T).lookup z
  by_cases hzx : z = x
  · subst z
    rw [lookup_insert, lookup_insert_of_ne _ U hne]
    rw [lookup_insert]
  · by_cases hzy : z = y
    · subst z
      rw [lookup_insert]
      rw [lookup_insert_of_ne _ T (Ne.symm hne), lookup_insert]
    · rw [lookup_insert_of_ne _ U hzy,
        lookup_insert_of_ne _ T hzx,
        lookup_insert_of_ne _ T hzx,
        lookup_insert_of_ne _ U hzy]

theorem subset_insert_of_fresh (Δ : BasicEnv) (y : Atom) (U : SimpleType)
    (fresh : y ∉ Δ.domain) : Δ.Subset (Δ.insert y U) := by
  intro z T hz
  have hzy : z ≠ y := by
    intro same
    subst z
    exact fresh (Finmap.mem_keys.2 (Finmap.mem_of_lookup_eq_some hz))
  rw [lookup_insert_of_ne _ U hzy]
  exact hz

end BasicEnv

namespace Primitive

/-- Erased argument and result base types of a unary primitive. -/
def signature : Primitive → BaseType × BaseType
  | .eqZero => (.nat, .bool)
  | .plusOne => (.nat, .nat)
  | .minusOne => (.nat, .nat)
  | .boolGen => (.unit, .bool)
  | .natGen => (.unit, .nat)

end Primitive

mutual

  /-- Erased typing of core values. -/
  inductive BasicValTyp : BasicEnv → Value → SimpleType → Prop where
    | const (Δ : BasicEnv) (c : Constant) :
        BasicValTyp Δ (.const c) (.base c.baseType)
    | free {Δ : BasicEnv} {x : Atom} {T : SimpleType}
        (typed : Δ.lookup x = some T) :
        BasicValTyp Δ (.free x) T
    | lam {Δ : BasicEnv} {T U : SimpleType} {e : Term} (L : Finset Atom)
        (typed : ∀ x, x ∉ L →
          BasicTermTyp (Δ.insert x T) (e.openAt 0 (.free x)) U) :
        BasicValTyp Δ (.lam T e) (.arrow T U)
    | fix {Δ : BasicEnv} {T U : SimpleType} {v : Value} (L : Finset Atom)
        (typed : ∀ x, x ∉ L →
          BasicValTyp (Δ.insert x T) (v.openAt 0 (.free x))
            (.arrow (.arrow T U) U)) :
        BasicValTyp Δ (.fix (.arrow T U) v) (.arrow T U)

  /-- Erased typing of core terms. -/
  inductive BasicTermTyp : BasicEnv → Term → SimpleType → Prop where
    | ret {Δ : BasicEnv} {v : Value} {T : SimpleType}
        (typed : BasicValTyp Δ v T) :
        BasicTermTyp Δ (.ret v) T
    | letE {Δ : BasicEnv} {T U : SimpleType} {e₁ e₂ : Term}
        (L : Finset Atom)
        (left : BasicTermTyp Δ e₁ T)
        (right : ∀ x, x ∉ L →
          BasicTermTyp (Δ.insert x T) (e₂.openAt 0 (.free x)) U) :
        BasicTermTyp Δ (.letE e₁ e₂) U
    | primitive {Δ : BasicEnv} {op : Primitive} {v : Value}
        {b₁ b₂ : BaseType}
        (signature : op.signature = (b₁, b₂))
        (typed : BasicValTyp Δ v (.base b₁)) :
        BasicTermTyp Δ (.primitive op v) (.base b₂)
    | app {Δ : BasicEnv} {T U : SimpleType} {v₁ v₂ : Value}
        (fn : BasicValTyp Δ v₁ (.arrow T U))
        (arg : BasicValTyp Δ v₂ T) :
        BasicTermTyp Δ (.app v₁ v₂) U
    | matchBool {Δ : BasicEnv} {v : Value} {e₁ e₂ : Term}
        {T : SimpleType}
        (scrutinee : BasicValTyp Δ v (.base .bool))
        (trueBranch : BasicTermTyp Δ e₁ T)
        (falseBranch : BasicTermTyp Δ e₂ T) :
        BasicTermTyp Δ (.matchBool v e₁ e₂) T

end

set_option hygiene false in
scoped[ContextTypes] notation:40 Δ:41 " ⊢ᵥ " v:41 " ⋮ " T:41 =>
  ContextTypes.BasicValTyp Δ v T

set_option hygiene false in
scoped[ContextTypes] notation:40 Δ:41 " ⊢ₑ " e:41 " ⋮ " T:41 =>
  ContextTypes.BasicTermTyp Δ e T

theorem Term.locallyClosedAt_one_of_open (e : Term) (L : Finset Atom)
    (h : ∀ x, x ∉ L → (e.openAt 0 (.free x)).locallyClosed) :
    e.locallyClosedAt 1 := by
  obtain ⟨x, hX⟩ := Finset.exists_nat_subset_range (L ∪ e.support)
  have fresh : x ∉ L ∪ e.support := by
    intro hx
    have := hX hx
    simp at this
  have fresh' : x ∉ L ∧ x ∉ e.support := by
    simpa only [Finset.mem_union, not_or] using fresh
  have closed := h x fresh'.1
  have body := Term.locallyClosedAt_closeAt
    (e.openAt 0 (.free x)) x 0 closed
  rwa [Term.closeAt_openAt e x 0 fresh'.2] at body

theorem Value.locallyClosedAt_one_of_open (v : Value) (L : Finset Atom)
    (h : ∀ x, x ∉ L → (v.openAt 0 (.free x)).locallyClosed) :
    v.locallyClosedAt 1 := by
  obtain ⟨x, hX⟩ := Finset.exists_nat_subset_range (L ∪ v.support)
  have fresh : x ∉ L ∪ v.support := by
    intro hx
    have := hX hx
    simp at this
  have fresh' : x ∉ L ∧ x ∉ v.support := by
    simpa only [Finset.mem_union, not_or] using fresh
  have closed := h x fresh'.1
  have body := Value.locallyClosedAt_closeAt
    (v.openAt 0 (.free x)) x 0 closed
  rwa [Value.closeAt_openAt v x 0 fresh'.2] at body

theorem BasicValTyp.locallyClosed {Δ : BasicEnv} {v : Value}
    {T : SimpleType} (h : BasicValTyp Δ v T) : v.locallyClosed := by
  induction h using BasicValTyp.rec
      (motive_2 := fun _ e _ _ => e.locallyClosed) with
  | const => trivial
  | free => trivial
  | lam L typed ih => exact Term.locallyClosedAt_one_of_open _ L ih
  | fix L typed ih => exact Value.locallyClosedAt_one_of_open _ L ih
  | ret typed ih => exact ih
  | letE L left right ih₁ ih₂ =>
      exact ⟨ih₁, Term.locallyClosedAt_one_of_open _ L ih₂⟩
  | primitive signature typed ih => exact ih
  | app fn arg ih₁ ih₂ => exact ⟨ih₁, ih₂⟩
  | matchBool scrutinee trueBranch falseBranch ih ih₁ ih₂ =>
      exact ⟨ih, ih₁, ih₂⟩

theorem BasicTermTyp.locallyClosed {Δ : BasicEnv} {e : Term}
    {T : SimpleType} (h : BasicTermTyp Δ e T) : e.locallyClosed := by
  induction h using BasicTermTyp.rec
      (motive_1 := fun _ v _ _ => v.locallyClosed) with
  | const => trivial
  | free => trivial
  | lam L typed ih => exact Term.locallyClosedAt_one_of_open _ L ih
  | fix L typed ih => exact Value.locallyClosedAt_one_of_open _ L ih
  | ret typed ih => exact ih
  | letE L left right ih₁ ih₂ =>
      exact ⟨ih₁, Term.locallyClosedAt_one_of_open _ L ih₂⟩
  | primitive signature typed ih => exact ih
  | app fn arg ih₁ ih₂ => exact ⟨ih₁, ih₂⟩
  | matchBool scrutinee trueBranch falseBranch ih ih₁ ih₂ =>
      exact ⟨ih, ih₁, ih₂⟩

theorem BasicValTyp.support_subset {Δ : BasicEnv} {v : Value}
    {T : SimpleType} (h : BasicValTyp Δ v T) : v.support ⊆ Δ.domain := by
  refine BasicValTyp.rec
    (motive_1 := fun Δ v _ _ => v.support ⊆ Δ.domain)
    (motive_2 := fun Δ e _ _ => e.support ⊆ Δ.domain)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ h
  · intro Δ c
    simp [Value.support]
  · intro Δ x T typed
    simp only [Value.support, Finset.singleton_subset_iff]
    exact Finmap.mem_keys.2 (Finmap.mem_of_lookup_eq_some typed)
  · intro Δ T U e L typed ih
    intro y hy
    obtain ⟨x, hx⟩ := Finset.exists_nat_subset_range (L ∪ {y})
    have fresh : x ∉ L ∪ {y} := by
      intro hmem
      have := hx hmem
      simp at this
    have fresh' : x ∉ L ∧ x ≠ y := by
      simpa only [Finset.mem_union, Finset.mem_singleton, not_or] using fresh
    have hxy : y ≠ x := Ne.symm fresh'.2
    have hopen : y ∈ (e.openAt 0 (.free x)).support :=
      Term.support_subset_openAt e 0 (.free x) hy
    have hdom := ih x fresh'.1 hopen
    simpa [BasicEnv.domain_insert, hxy] using hdom
  · intro Δ T U v L typed ih
    intro y hy
    obtain ⟨x, hx⟩ := Finset.exists_nat_subset_range (L ∪ {y})
    have fresh : x ∉ L ∪ {y} := by
      intro hmem
      have := hx hmem
      simp at this
    have fresh' : x ∉ L ∧ x ≠ y := by
      simpa only [Finset.mem_union, Finset.mem_singleton, not_or] using fresh
    have hxy : y ≠ x := Ne.symm fresh'.2
    have hopen : y ∈ (v.openAt 0 (.free x)).support :=
      Value.support_subset_openAt v 0 (.free x) hy
    have hdom := ih x fresh'.1 hopen
    simpa [BasicEnv.domain_insert, hxy] using hdom
  · intro Δ v T typed ih
    exact ih
  · intro Δ T U e₁ e₂ L left right ih₁ ih₂
    intro y hy
    rcases Finset.mem_union.1 hy with hy | hy
    · exact ih₁ hy
    · obtain ⟨x, hx⟩ := Finset.exists_nat_subset_range (L ∪ {y})
      have fresh : x ∉ L ∪ {y} := by
        intro hmem
        have := hx hmem
        simp at this
      have fresh' : x ∉ L ∧ x ≠ y := by
        simpa only [Finset.mem_union, Finset.mem_singleton, not_or] using fresh
      have hxy : y ≠ x := Ne.symm fresh'.2
      have hopen : y ∈ (e₂.openAt 0 (.free x)).support :=
        Term.support_subset_openAt e₂ 0 (.free x) hy
      have hdom := ih₂ x fresh'.1 hopen
      simpa [BasicEnv.domain_insert, hxy] using hdom
  · intro Δ op v b₁ b₂ signature typed ih
    exact ih
  · intro Δ T U v₁ v₂ fn arg ih₁ ih₂
    exact Finset.union_subset ih₁ ih₂
  · intro Δ v e₁ e₂ T scrutinee trueBranch falseBranch ih ih₁ ih₂
    exact Finset.union_subset (Finset.union_subset ih ih₁) ih₂

theorem BasicTermTyp.support_subset {Δ : BasicEnv} {e : Term}
    {T : SimpleType} (h : BasicTermTyp Δ e T) : e.support ⊆ Δ.domain := by
  refine BasicTermTyp.rec
    (motive_1 := fun Δ v _ _ => v.support ⊆ Δ.domain)
    (motive_2 := fun Δ e _ _ => e.support ⊆ Δ.domain)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ h
  · intro Δ c
    simp [Value.support]
  · intro Δ x T typed
    simp only [Value.support, Finset.singleton_subset_iff]
    exact Finmap.mem_keys.2 (Finmap.mem_of_lookup_eq_some typed)
  · intro Δ T U e L typed ih
    intro y hy
    obtain ⟨x, hx⟩ := Finset.exists_nat_subset_range (L ∪ {y})
    have fresh : x ∉ L ∪ {y} := by
      intro hmem
      have := hx hmem
      simp at this
    have fresh' : x ∉ L ∧ x ≠ y := by
      simpa only [Finset.mem_union, Finset.mem_singleton, not_or] using fresh
    have hxy : y ≠ x := Ne.symm fresh'.2
    have hopen : y ∈ (e.openAt 0 (.free x)).support :=
      Term.support_subset_openAt e 0 (.free x) hy
    have hdom := ih x fresh'.1 hopen
    simpa [BasicEnv.domain_insert, hxy] using hdom
  · intro Δ T U v L typed ih
    intro y hy
    obtain ⟨x, hx⟩ := Finset.exists_nat_subset_range (L ∪ {y})
    have fresh : x ∉ L ∪ {y} := by
      intro hmem
      have := hx hmem
      simp at this
    have fresh' : x ∉ L ∧ x ≠ y := by
      simpa only [Finset.mem_union, Finset.mem_singleton, not_or] using fresh
    have hxy : y ≠ x := Ne.symm fresh'.2
    have hopen : y ∈ (v.openAt 0 (.free x)).support :=
      Value.support_subset_openAt v 0 (.free x) hy
    have hdom := ih x fresh'.1 hopen
    simpa [BasicEnv.domain_insert, hxy] using hdom
  · intro Δ v T typed ih
    exact ih
  · intro Δ T U e₁ e₂ L left right ih₁ ih₂
    intro y hy
    rcases Finset.mem_union.1 hy with hy | hy
    · exact ih₁ hy
    · obtain ⟨x, hx⟩ := Finset.exists_nat_subset_range (L ∪ {y})
      have fresh : x ∉ L ∪ {y} := by
        intro hmem
        have := hx hmem
        simp at this
      have fresh' : x ∉ L ∧ x ≠ y := by
        simpa only [Finset.mem_union, Finset.mem_singleton, not_or] using fresh
      have hxy : y ≠ x := Ne.symm fresh'.2
      have hopen : y ∈ (e₂.openAt 0 (.free x)).support :=
        Term.support_subset_openAt e₂ 0 (.free x) hy
      have hdom := ih₂ x fresh'.1 hopen
      simpa [BasicEnv.domain_insert, hxy] using hdom
  · intro Δ op v b₁ b₂ signature typed ih
    exact ih
  · intro Δ T U v₁ v₂ fn arg ih₁ ih₂
    exact Finset.union_subset ih₁ ih₂
  · intro Δ v e₁ e₂ T scrutinee trueBranch falseBranch ih ih₁ ih₂
    exact Finset.union_subset (Finset.union_subset ih ih₁) ih₂

theorem BasicValTyp.weaken {Δ Δ' : BasicEnv} {v : Value} {T : SimpleType}
    (h : BasicValTyp Δ v T) (sub : Δ.Subset Δ') :
    BasicValTyp Δ' v T := by
  refine (BasicValTyp.rec
    (motive_1 := fun Δ v T _ => ∀ Δ', Δ.Subset Δ' → BasicValTyp Δ' v T)
    (motive_2 := fun Δ e T _ => ∀ Δ', Δ.Subset Δ' → BasicTermTyp Δ' e T)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ h) Δ' sub
  · intro Δ c Δ' sub
    exact BasicValTyp.const Δ' c
  · intro Δ x T typed Δ' sub
    exact BasicValTyp.free (sub x T typed)
  · intro Δ T U e L typed ih Δ' sub
    apply BasicValTyp.lam L
    intro x hx
    exact ih x hx (Δ'.insert x T) (sub.insert x T)
  · intro Δ T U v L typed ih Δ' sub
    apply BasicValTyp.fix L
    intro x hx
    exact ih x hx (Δ'.insert x T) (sub.insert x T)
  · intro Δ v T typed ih Δ' sub
    exact BasicTermTyp.ret (ih Δ' sub)
  · intro Δ T U e₁ e₂ L left right ih₁ ih₂ Δ' sub
    apply BasicTermTyp.letE L (ih₁ Δ' sub)
    intro x hx
    exact ih₂ x hx (Δ'.insert x T) (sub.insert x T)
  · intro Δ op v b₁ b₂ signature typed ih Δ' sub
    exact BasicTermTyp.primitive signature (ih Δ' sub)
  · intro Δ T U v₁ v₂ fn arg ih₁ ih₂ Δ' sub
    exact BasicTermTyp.app (ih₁ Δ' sub) (ih₂ Δ' sub)
  · intro Δ v e₁ e₂ T scrutinee trueBranch falseBranch ih ih₁ ih₂ Δ' sub
    exact BasicTermTyp.matchBool (ih Δ' sub) (ih₁ Δ' sub) (ih₂ Δ' sub)

theorem BasicTermTyp.weaken {Δ Δ' : BasicEnv} {e : Term} {T : SimpleType}
    (h : BasicTermTyp Δ e T) (sub : Δ.Subset Δ') :
    BasicTermTyp Δ' e T := by
  refine (BasicTermTyp.rec
    (motive_1 := fun Δ v T _ => ∀ Δ', Δ.Subset Δ' → BasicValTyp Δ' v T)
    (motive_2 := fun Δ e T _ => ∀ Δ', Δ.Subset Δ' → BasicTermTyp Δ' e T)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ h) Δ' sub
  · intro Δ c Δ' sub
    exact BasicValTyp.const Δ' c
  · intro Δ x T typed Δ' sub
    exact BasicValTyp.free (sub x T typed)
  · intro Δ T U e L typed ih Δ' sub
    apply BasicValTyp.lam L
    intro x hx
    exact ih x hx (Δ'.insert x T) (sub.insert x T)
  · intro Δ T U v L typed ih Δ' sub
    apply BasicValTyp.fix L
    intro x hx
    exact ih x hx (Δ'.insert x T) (sub.insert x T)
  · intro Δ v T typed ih Δ' sub
    exact BasicTermTyp.ret (ih Δ' sub)
  · intro Δ T U e₁ e₂ L left right ih₁ ih₂ Δ' sub
    apply BasicTermTyp.letE L (ih₁ Δ' sub)
    intro x hx
    exact ih₂ x hx (Δ'.insert x T) (sub.insert x T)
  · intro Δ op v b₁ b₂ signature typed ih Δ' sub
    exact BasicTermTyp.primitive signature (ih Δ' sub)
  · intro Δ T U v₁ v₂ fn arg ih₁ ih₂ Δ' sub
    exact BasicTermTyp.app (ih₁ Δ' sub) (ih₂ Δ' sub)
  · intro Δ v e₁ e₂ T scrutinee trueBranch falseBranch ih ih₁ ih₂ Δ' sub
    exact BasicTermTyp.matchBool (ih Δ' sub) (ih₁ Δ' sub) (ih₂ Δ' sub)

mutual

  theorem BasicValTyp.substitute {Δ : BasicEnv} {x : Atom}
      {T U : SimpleType} {v u : Value}
      (typed : BasicValTyp (Δ.insert x T) v U)
      (arg : BasicValTyp Δ u T) (fresh : x ∉ Δ.domain) :
      BasicValTyp Δ (v.substitute x u) U := by
    refine (BasicValTyp.rec
      (motive_1 := fun Δ' v U _ => ∀ Δ x T u,
        Δ' = Δ.insert x T → BasicValTyp Δ u T → x ∉ Δ.domain →
          BasicValTyp Δ (v.substitute x u) U)
      (motive_2 := fun Δ' e U _ => ∀ Δ x T u,
        Δ' = Δ.insert x T → BasicValTyp Δ u T → x ∉ Δ.domain →
          BasicTermTyp Δ (e.substitute x u) U)
      ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ typed) Δ x T u rfl arg fresh
    · intro Δ' c Δ x T u eq arg fresh
      exact BasicValTyp.const Δ c
    · intro Δ' y U hlookup Δ x T u eq arg fresh
      subst Δ'
      by_cases hyx : y = x
      · subst y
        have hUT : U = T := by
          rw [BasicEnv.lookup_insert] at hlookup
          exact (Option.some.inj hlookup).symm
        subst U
        simpa [Value.substitute] using arg
      · have hy : Δ.lookup y = some U := by
          rwa [BasicEnv.lookup_insert_of_ne Δ T hyx] at hlookup
        simpa [Value.substitute, hyx] using BasicValTyp.free hy
    · intro Δ' S V e L body ih Δ x T u eq arg fresh
      subst Δ'
      apply BasicValTyp.lam (L ∪ {x} ∪ Δ.domain)
      intro y hy
      have hy' : y ∉ L ∧ y ≠ x ∧ y ∉ Δ.domain := by
        have h := Finset.notMem_union.1 hy
        have hLx := Finset.notMem_union.1 h.1
        exact ⟨hLx.1, by simpa using hLx.2, h.2⟩
      have henv : (Δ.insert x T).insert y S =
          (Δ.insert y S).insert x T :=
        BasicEnv.insert_comm Δ T S (Ne.symm hy'.2.1)
      have hu : BasicValTyp (Δ.insert y S) u T :=
        arg.weaken (BasicEnv.subset_insert_of_fresh Δ y S hy'.2.2)
      have hx : x ∉ (Δ.insert y S).domain := by
        simpa [BasicEnv.domain_insert, Ne.symm hy'.2.1] using fresh
      have htyped := ih y hy'.1 (Δ.insert y S) x T u henv hu hx
      rw [Term.substitute_openAt e x u (.free y) arg.locallyClosed 0] at htyped
      simpa [Value.substitute, hy'.2.1] using htyped
    · intro Δ' S V v L body ih Δ x T u eq arg fresh
      subst Δ'
      apply BasicValTyp.fix (L ∪ {x} ∪ Δ.domain)
      intro y hy
      have hy' : y ∉ L ∧ y ≠ x ∧ y ∉ Δ.domain := by
        have h := Finset.notMem_union.1 hy
        have hLx := Finset.notMem_union.1 h.1
        exact ⟨hLx.1, by simpa using hLx.2, h.2⟩
      have henv : (Δ.insert x T).insert y S =
          (Δ.insert y S).insert x T :=
        BasicEnv.insert_comm Δ T S (Ne.symm hy'.2.1)
      have hu : BasicValTyp (Δ.insert y S) u T :=
        arg.weaken (BasicEnv.subset_insert_of_fresh Δ y S hy'.2.2)
      have hx : x ∉ (Δ.insert y S).domain := by
        simpa [BasicEnv.domain_insert, Ne.symm hy'.2.1] using fresh
      have htyped := ih y hy'.1 (Δ.insert y S) x T u henv hu hx
      rw [Value.substitute_openAt v x u (.free y) arg.locallyClosed 0] at htyped
      simpa [Value.substitute, hy'.2.1] using htyped
    · intro Δ' v U typed ih Δ x T u eq arg fresh
      exact BasicTermTyp.ret (ih Δ x T u eq arg fresh)
    · intro Δ' S V e₁ e₂ L left right ih₁ ih₂ Δ x T u eq arg fresh
      subst Δ'
      apply BasicTermTyp.letE (L ∪ {x} ∪ Δ.domain)
        (ih₁ Δ x T u rfl arg fresh)
      intro y hy
      have hy' : y ∉ L ∧ y ≠ x ∧ y ∉ Δ.domain := by
        have h := Finset.notMem_union.1 hy
        have hLx := Finset.notMem_union.1 h.1
        exact ⟨hLx.1, by simpa using hLx.2, h.2⟩
      have henv : (Δ.insert x T).insert y S =
          (Δ.insert y S).insert x T :=
        BasicEnv.insert_comm Δ T S (Ne.symm hy'.2.1)
      have hu : BasicValTyp (Δ.insert y S) u T :=
        arg.weaken (BasicEnv.subset_insert_of_fresh Δ y S hy'.2.2)
      have hx : x ∉ (Δ.insert y S).domain := by
        simpa [BasicEnv.domain_insert, Ne.symm hy'.2.1] using fresh
      have htyped := ih₂ y hy'.1 (Δ.insert y S) x T u henv hu hx
      rw [Term.substitute_openAt e₂ x u (.free y) arg.locallyClosed 0] at htyped
      simpa [Value.substitute, hy'.2.1] using htyped
    · intro Δ' op v b₁ b₂ signature typed ih Δ x T u eq arg fresh
      exact BasicTermTyp.primitive signature (ih Δ x T u eq arg fresh)
    · intro Δ' S V v₁ v₂ fn arg' ih₁ ih₂ Δ x T u eq arg fresh
      exact BasicTermTyp.app (ih₁ Δ x T u eq arg fresh)
        (ih₂ Δ x T u eq arg fresh)
    · intro Δ' v e₁ e₂ U scrutinee left right ih ih₁ ih₂
        Δ x T u eq arg fresh
      exact BasicTermTyp.matchBool (ih Δ x T u eq arg fresh)
        (ih₁ Δ x T u eq arg fresh) (ih₂ Δ x T u eq arg fresh)

  theorem BasicTermTyp.substitute {Δ : BasicEnv} {x : Atom}
      {T U : SimpleType} {e : Term} {u : Value}
      (typed : BasicTermTyp (Δ.insert x T) e U)
      (arg : BasicValTyp Δ u T) (fresh : x ∉ Δ.domain) :
      BasicTermTyp Δ (e.substitute x u) U := by
    refine (BasicTermTyp.rec
      (motive_1 := fun Δ' v U _ => ∀ Δ x T u,
        Δ' = Δ.insert x T → BasicValTyp Δ u T → x ∉ Δ.domain →
          BasicValTyp Δ (v.substitute x u) U)
      (motive_2 := fun Δ' e U _ => ∀ Δ x T u,
        Δ' = Δ.insert x T → BasicValTyp Δ u T → x ∉ Δ.domain →
          BasicTermTyp Δ (e.substitute x u) U)
      ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ typed) Δ x T u rfl arg fresh
    · intro Δ' c Δ x T u eq arg fresh
      subst Δ'
      exact (BasicValTyp.const (Δ.insert x T) c).substitute arg fresh
    · intro Δ' y U hlookup Δ x T u eq arg fresh
      subst Δ'
      exact (BasicValTyp.free hlookup).substitute arg fresh
    · intro Δ' S V e L body ih Δ x T u eq arg fresh
      subst Δ'
      exact (BasicValTyp.lam L body).substitute arg fresh
    · intro Δ' S V v L body ih Δ x T u eq arg fresh
      subst Δ'
      exact (BasicValTyp.fix L body).substitute arg fresh
    · intro Δ' v U typed ih Δ x T u eq arg fresh
      exact BasicTermTyp.ret (ih Δ x T u eq arg fresh)
    · intro Δ' S V e₁ e₂ L left right ih₁ ih₂ Δ x T u eq arg fresh
      subst Δ'
      apply BasicTermTyp.letE (L ∪ {x} ∪ Δ.domain)
        (ih₁ Δ x T u rfl arg fresh)
      intro y hy
      have hy' : y ∉ L ∧ y ≠ x ∧ y ∉ Δ.domain := by
        have h := Finset.notMem_union.1 hy
        have hLx := Finset.notMem_union.1 h.1
        exact ⟨hLx.1, by simpa using hLx.2, h.2⟩
      have henv : (Δ.insert x T).insert y S =
          (Δ.insert y S).insert x T :=
        BasicEnv.insert_comm Δ T S (Ne.symm hy'.2.1)
      have hu : BasicValTyp (Δ.insert y S) u T :=
        arg.weaken (BasicEnv.subset_insert_of_fresh Δ y S hy'.2.2)
      have hx : x ∉ (Δ.insert y S).domain := by
        simpa [BasicEnv.domain_insert, Ne.symm hy'.2.1] using fresh
      have htyped := ih₂ y hy'.1 (Δ.insert y S) x T u henv hu hx
      rw [Term.substitute_openAt e₂ x u (.free y) arg.locallyClosed 0] at htyped
      simpa [Value.substitute, hy'.2.1] using htyped
    · intro Δ' op v b₁ b₂ signature typed ih Δ x T u eq arg fresh
      exact BasicTermTyp.primitive signature (ih Δ x T u eq arg fresh)
    · intro Δ' S V v₁ v₂ fn arg' ih₁ ih₂ Δ x T u eq arg fresh
      exact BasicTermTyp.app (ih₁ Δ x T u eq arg fresh)
        (ih₂ Δ x T u eq arg fresh)
    · intro Δ' v e₁ e₂ U scrutinee left right ih ih₁ ih₂
        Δ x T u eq arg fresh
      exact BasicTermTyp.matchBool (ih Δ x T u eq arg fresh)
        (ih₁ Δ x T u eq arg fresh) (ih₂ Δ x T u eq arg fresh)

end

theorem BasicTermTyp.openAt_of_body {Δ : BasicEnv} {T U : SimpleType}
    {e : Term} {u : Value} (L : Finset Atom)
    (body : ∀ x, x ∉ L →
      BasicTermTyp (Δ.insert x T) (e.openAt 0 (.free x)) U)
    (arg : BasicValTyp Δ u T) : BasicTermTyp Δ (e.openAt 0 u) U := by
  obtain ⟨x, hx⟩ :=
    Finset.exists_nat_subset_range (L ∪ Δ.domain ∪ e.support)
  have fresh : x ∉ L ∪ Δ.domain ∪ e.support := by
    intro h
    have := hx h
    simp at this
  have fresh' : x ∉ L ∧ x ∉ Δ.domain ∧ x ∉ e.support := by
    simpa [and_assoc] using fresh
  have h := (body x fresh'.1).substitute arg fresh'.2.1
  rwa [Term.substitute_openVar e x u 0 fresh'.2.2 arg.locallyClosed] at h

theorem BasicValTyp.openAt_of_body {Δ : BasicEnv} {T U : SimpleType}
    {v u : Value} (L : Finset Atom)
    (body : ∀ x, x ∉ L →
      BasicValTyp (Δ.insert x T) (v.openAt 0 (.free x)) U)
    (arg : BasicValTyp Δ u T) : BasicValTyp Δ (v.openAt 0 u) U := by
  obtain ⟨x, hx⟩ :=
    Finset.exists_nat_subset_range (L ∪ Δ.domain ∪ v.support)
  have fresh : x ∉ L ∪ Δ.domain ∪ v.support := by
    intro h
    have := hx h
    simp at this
  have fresh' : x ∉ L ∧ x ∉ Δ.domain ∧ x ∉ v.support := by
    simpa [and_assoc] using fresh
  have h := (body x fresh'.1).substitute arg fresh'.2.1
  rwa [Value.substitute_openVar v x u 0 fresh'.2.2 arg.locallyClosed] at h

theorem Primitive.Step.resultBase {op : Primitive} {c c' : Constant}
    (step : Primitive.Step op c c') :
    op.signature.2 = c'.baseType := by
  cases step <;> rfl

theorem HeadStep.preserve {Δ : BasicEnv} {e e' : Term} {T : SimpleType}
    (step : HeadStep e e') (typed : BasicTermTyp Δ e T) :
    BasicTermTyp Δ e' T := by
  cases step with
  | letRet v e closed =>
      cases typed with
      | letE L left right =>
          cases left with
          | ret arg => exact BasicTermTyp.openAt_of_body L right arg
  | primitive op c c' step closed =>
      cases typed with
      | @primitive _ _ _ b₁ b₂ signature arg =>
          cases arg with
          | const =>
              have hb : c'.baseType = b₂ :=
                step.resultBase.symm.trans (congrArg Prod.snd signature)
              rw [← hb]
              exact BasicTermTyp.ret (BasicValTyp.const Δ c')
  | beta S e v closed =>
      cases typed with
      | app fn arg =>
          cases fn with
          | lam L body => exact BasicTermTyp.openAt_of_body L body arg
  | fix S vf v closed =>
      cases typed with
      | app fn arg =>
          cases fn with
          | fix L body =>
              exact BasicTermTyp.app
                (BasicValTyp.openAt_of_body L body arg)
                (BasicValTyp.fix L body)
  | matchTrue e₁ e₂ closed =>
      cases typed with
      | matchBool scrutinee left right => exact left
  | matchFalse e₁ e₂ closed =>
      cases typed with
      | matchBool scrutinee left right => exact right

theorem Step.preserve {Δ : BasicEnv} {e e' : Term} {T : SimpleType}
    (step : Step e e') (typed : BasicTermTyp Δ e T) :
    BasicTermTyp Δ e' T := by
  cases step with
  | head step => exact step.preserve typed
  | letE step closed =>
      cases typed with
      | letE L left right =>
          exact BasicTermTyp.letE L (step.preserve left) right

theorem Steps.preserve {Δ : BasicEnv} {e e' : Term} {T : SimpleType}
    (steps : Steps e e') (typed : BasicTermTyp Δ e T) :
    BasicTermTyp Δ e' T := by
  induction steps with
  | refl => exact typed
  | tail step steps ih => exact ih (step.preserve typed)

theorem BasicTermTyp.reaches {Δ : BasicEnv} {e : Term} {v : Value}
    {T : SimpleType} (typed : BasicTermTyp Δ e T) (h : e.reaches v) :
    BasicValTyp Δ v T := by
  have result := h.preserve typed
  cases result with
  | ret typed => exact typed

namespace Qualifier

/-- All bound variables in `q` are below `d`, and all free atoms lie in `X`. -/
def ScopedAt (q : Qualifier) (d : Nat) (X : Finset Atom) : Prop :=
  ∀ ξ, ξ ∈ q.support →
    match ξ with
    | .bound k => k < d
    | .free x => x ∈ X

/-- A closed qualifier scoped by the program atoms in `X`. -/
abbrev Scoped (q : Qualifier) (X : Finset Atom) : Prop :=
  q.ScopedAt 0 X

/-- A qualifier body may additionally mention its result binder. -/
abbrev BodyScoped (q : Qualifier) (X : Finset Atom) : Prop :=
  q.ScopedAt 1 X

theorem ScopedAt.mono {q : Qualifier} {d d' : Nat} {X Y : Finset Atom}
    (h : q.ScopedAt d X) (hd : d ≤ d') (hX : X ⊆ Y) :
    q.ScopedAt d' Y := by
  intro ξ hξ
  cases ξ with
  | bound k => exact lt_of_lt_of_le (h _ hξ) hd
  | free x => exact hX (h _ hξ)

theorem ScopedAt.locallyClosedAt {q : Qualifier} {d : Nat}
    {X : Finset Atom} (h : q.ScopedAt d X) : q.locallyClosedAt d := by
  intro k hk
  exact h (.bound k) hk

theorem ScopedAt.freeAtoms_subset {q : Qualifier} {d : Nat}
    {X : Finset Atom} (h : q.ScopedAt d X) : q.freeAtoms ⊆ X := by
  intro x hx
  rw [Qualifier.mem_freeAtoms_iff] at hx
  exact h (.free x) hx

theorem ScopedAt.shiftFrom {q : Qualifier} {d : Nat} {X : Finset Atom}
    (h : q.ScopedAt d X) (k : Nat) :
    (q.shiftFrom k).ScopedAt (d + 1) X := by
  intro ξ hξ
  rw [support_shiftFrom, Finset.mem_image] at hξ
  obtain ⟨ζ, hζ, rfl⟩ := hξ
  cases ζ with
  | free x => exact h (.free x) hζ
  | bound n =>
      have hn := h (.bound n) hζ
      by_cases hkn : k ≤ n
      · simp [LogicVar.shiftFrom, hkn]
        omega
      · simp [LogicVar.shiftFrom, hkn]
        omega

end Qualifier

namespace ContextType

/-- Binder scoping alone, without the erased-shape condition. -/
def LocallyClosedAt : ContextType → Nat → Prop
  | .over _ q, d | .under _ q, d => q.locallyClosedAt (d + 1)
  | .inter τ₁ τ₂, d | .union τ₁ τ₂, d | .sum τ₁ τ₂, d =>
      τ₁.LocallyClosedAt d ∧ τ₂.LocallyClosedAt d
  | .arrow τ₁ τ₂, d | .wand τ₁ τ₂, d =>
      τ₁.LocallyClosedAt d ∧ τ₂.LocallyClosedAt (d + 1)
  | .persist τ, d => τ.LocallyClosedAt d

/-- A context type with no dangling outer logical variables. -/
abbrev LocallyClosed (τ : ContextType) : Prop :=
  τ.LocallyClosedAt 0

theorem LocallyClosedAt.mono {τ : ContextType} {d d' : Nat}
    (h : τ.LocallyClosedAt d) (hdd : d ≤ d') :
    τ.LocallyClosedAt d' := by
  induction τ generalizing d d' with
  | «over» b q =>
      exact q.locallyClosedAt_mono h (Nat.add_le_add_right hdd 1)
  | under b q =>
      exact q.locallyClosedAt_mono h (Nat.add_le_add_right hdd 1)
  | inter τ₁ τ₂ ih₁ ih₂ =>
      exact ⟨ih₁ h.1 hdd, ih₂ h.2 hdd⟩
  | union τ₁ τ₂ ih₁ ih₂ =>
      exact ⟨ih₁ h.1 hdd, ih₂ h.2 hdd⟩
  | sum τ₁ τ₂ ih₁ ih₂ =>
      exact ⟨ih₁ h.1 hdd, ih₂ h.2 hdd⟩
  | arrow τ₁ τ₂ ih₁ ih₂ =>
      exact ⟨ih₁ h.1 hdd,
        ih₂ h.2 (Nat.add_le_add_right hdd 1)⟩
  | wand τ₁ τ₂ ih₁ ih₂ =>
      exact ⟨ih₁ h.1 hdd,
        ih₂ h.2 (Nat.add_le_add_right hdd 1)⟩
  | persist τ ih => exact ih h hdd

theorem shiftFrom_eq_of_locallyClosedAt (τ : ContextType) (k : Nat)
    (closed : τ.LocallyClosedAt k) : τ.shiftFrom k = τ := by
  induction τ generalizing k with
  | «over» b q =>
      simp only [shiftFrom]
      rw [q.shiftFrom_eq_of_locallyClosedAt (k + 1) closed]
  | under b q =>
      simp only [shiftFrom]
      rw [q.shiftFrom_eq_of_locallyClosedAt (k + 1) closed]
  | inter τ₁ τ₂ ih₁ ih₂ =>
      simp only [shiftFrom]
      rw [ih₁ k closed.1, ih₂ k closed.2]
  | union τ₁ τ₂ ih₁ ih₂ =>
      simp only [shiftFrom]
      rw [ih₁ k closed.1, ih₂ k closed.2]
  | sum τ₁ τ₂ ih₁ ih₂ =>
      simp only [shiftFrom]
      rw [ih₁ k closed.1, ih₂ k closed.2]
  | arrow τ₁ τ₂ ih₁ ih₂ =>
      simp only [shiftFrom]
      rw [ih₁ k closed.1, ih₂ (k + 1) closed.2]
  | wand τ₁ τ₂ ih₁ ih₂ =>
      simp only [shiftFrom]
      rw [ih₁ k closed.1, ih₂ (k + 1) closed.2]
  | persist τ ih =>
      simp only [shiftFrom]
      rw [ih k closed]

theorem openAt_shiftFrom_eq (τ : ContextType) (k : Nat) (x : Atom)
    (closed : τ.LocallyClosedAt k) (fresh : x ∉ τ.freeAtoms) :
    (τ.shiftFrom k).openAt k x = τ := by
  induction τ generalizing k with
  | «over» b q =>
      simp only [shiftFrom, openAt]
      apply congrArg (ContextType.over b)
      apply q.openAt_shiftFrom_eq
      · exact closed
      · rw [← q.mem_freeAtoms_iff]
        exact fresh
  | under b q =>
      simp only [shiftFrom, openAt]
      apply congrArg (ContextType.under b)
      apply q.openAt_shiftFrom_eq
      · exact closed
      · rw [← q.mem_freeAtoms_iff]
        exact fresh
  | inter τ₁ τ₂ ih₁ ih₂ =>
      have fresh' : x ∉ τ₁.freeAtoms ∧ x ∉ τ₂.freeAtoms := by
        simpa [freeAtoms] using fresh
      simp only [shiftFrom, openAt]
      rw [ih₁ k closed.1 fresh'.1, ih₂ k closed.2 fresh'.2]
  | union τ₁ τ₂ ih₁ ih₂ =>
      have fresh' : x ∉ τ₁.freeAtoms ∧ x ∉ τ₂.freeAtoms := by
        simpa [freeAtoms] using fresh
      simp only [shiftFrom, openAt]
      rw [ih₁ k closed.1 fresh'.1, ih₂ k closed.2 fresh'.2]
  | sum τ₁ τ₂ ih₁ ih₂ =>
      have fresh' : x ∉ τ₁.freeAtoms ∧ x ∉ τ₂.freeAtoms := by
        simpa [freeAtoms] using fresh
      simp only [shiftFrom, openAt]
      rw [ih₁ k closed.1 fresh'.1, ih₂ k closed.2 fresh'.2]
  | arrow τ₁ τ₂ ih₁ ih₂ =>
      have fresh' : x ∉ τ₁.freeAtoms ∧ x ∉ τ₂.freeAtoms := by
        simpa [freeAtoms] using fresh
      simp only [shiftFrom, openAt]
      rw [ih₁ k closed.1 fresh'.1,
        ih₂ (k + 1) closed.2 fresh'.2]
  | wand τ₁ τ₂ ih₁ ih₂ =>
      have fresh' : x ∉ τ₁.freeAtoms ∧ x ∉ τ₂.freeAtoms := by
        simpa [freeAtoms] using fresh
      simp only [shiftFrom, openAt]
      rw [ih₁ k closed.1 fresh'.1,
        ih₂ (k + 1) closed.2 fresh'.2]
  | persist τ ih =>
      simp only [shiftFrom, openAt]
      rw [ih k closed fresh]

/-- All branches of a context type have compatible erased shapes. -/
def ShapeOK : ContextType → Prop
  | .over _ _ | .under _ _ => True
  | .inter τ₁ τ₂ | .union τ₁ τ₂ | .sum τ₁ τ₂ =>
      τ₁.ShapeOK ∧ τ₂.ShapeOK ∧ τ₁.erase = τ₂.erase
  | .arrow τ₁ τ₂ | .wand τ₁ τ₂ => τ₁.ShapeOK ∧ τ₂.ShapeOK
  | .persist τ => τ.ShapeOK

/-- Formation of a context type under `d` logical binders and atoms `X`. -/
def WellFormedAt : ContextType → Nat → Finset Atom → Prop
  | .over _ q, d, X | .under _ q, d, X => q.ScopedAt (d + 1) X
  | .inter τ₁ τ₂, d, X | .union τ₁ τ₂, d, X | .sum τ₁ τ₂, d, X =>
      τ₁.WellFormedAt d X ∧ τ₂.WellFormedAt d X ∧ τ₁.erase = τ₂.erase
  | .arrow τ₁ τ₂, d, X =>
      τ₁.WellFormedAt d X ∧ τ₂.WellFormedAt (d + 1) X
  | .wand τ₁ τ₂, d, X =>
      τ₁.WellFormedAt 0 ∅ ∧ τ₂.WellFormedAt (d + 1) X
  | .persist τ, d, X => τ.WellFormedAt d X

/-- Formation of a closed context type over program atoms `X`. -/
abbrev WellFormed (τ : ContextType) (X : Finset Atom) : Prop :=
  τ.WellFormedAt 0 X

theorem WellFormedAt.mono {τ : ContextType} {d : Nat}
    {X Y : Finset Atom} (h : τ.WellFormedAt d X) (hXY : X ⊆ Y) :
    τ.WellFormedAt d Y := by
  induction τ generalizing d X Y <;> simp_all [WellFormedAt]
  all_goals
    first
    | exact Qualifier.ScopedAt.mono h (Nat.le_refl _) hXY
    | aesop

theorem WellFormedAt.locallyClosedAt {τ : ContextType} {d : Nat}
    {X : Finset Atom} (h : τ.WellFormedAt d X) : τ.LocallyClosedAt d := by
  induction τ generalizing d X with
  | «over» b q =>
      exact Qualifier.ScopedAt.locallyClosedAt h
  | under b q =>
      exact Qualifier.ScopedAt.locallyClosedAt h
  | inter τ₁ τ₂ ih₁ ih₂ =>
      exact ⟨ih₁ h.1, ih₂ h.2.1⟩
  | union τ₁ τ₂ ih₁ ih₂ =>
      exact ⟨ih₁ h.1, ih₂ h.2.1⟩
  | sum τ₁ τ₂ ih₁ ih₂ =>
      exact ⟨ih₁ h.1, ih₂ h.2.1⟩
  | arrow τ₁ τ₂ ih₁ ih₂ => exact ⟨ih₁ h.1, ih₂ h.2⟩
  | wand τ₁ τ₂ ih₁ ih₂ =>
      exact ⟨LocallyClosedAt.mono (ih₁ h.1) (Nat.zero_le d), ih₂ h.2⟩
  | persist τ ih => exact ih h

theorem WellFormedAt.shiftFrom {τ : ContextType} {d : Nat}
    {X : Finset Atom} (h : τ.WellFormedAt d X) (k : Nat) :
    (τ.shiftFrom k).WellFormedAt (d + 1) X := by
  induction τ generalizing d k X with
  | «over» b q => exact Qualifier.ScopedAt.shiftFrom h (k + 1)
  | under b q => exact Qualifier.ScopedAt.shiftFrom h (k + 1)
  | inter τ₁ τ₂ ih₁ ih₂ =>
      exact ⟨ih₁ h.1 k, ih₂ h.2.1 k, by simpa using h.2.2⟩
  | union τ₁ τ₂ ih₁ ih₂ =>
      exact ⟨ih₁ h.1 k, ih₂ h.2.1 k, by simpa using h.2.2⟩
  | sum τ₁ τ₂ ih₁ ih₂ =>
      exact ⟨ih₁ h.1 k, ih₂ h.2.1 k, by simpa using h.2.2⟩
  | arrow τ₁ τ₂ ih₁ ih₂ =>
      exact ⟨ih₁ h.1 k, ih₂ h.2 (k + 1)⟩
  | wand τ₁ τ₂ ih₁ ih₂ =>
      have closed := h.1.locallyClosedAt
      have same := τ₁.shiftFrom_eq_of_locallyClosedAt k
        (closed.mono (Nat.zero_le k))
      simp only [ContextType.shiftFrom, ContextType.WellFormedAt]
      rw [same]
      exact ⟨h.1, ih₂ h.2 (k + 1)⟩
  | persist τ ih => exact ih h k

theorem WellFormedAt.shapeOK {τ : ContextType} {d : Nat}
    {X : Finset Atom} (h : τ.WellFormedAt d X) : τ.ShapeOK := by
  induction τ generalizing d X with
  | «over» => trivial
  | under => trivial
  | inter τ₁ τ₂ ih₁ ih₂ => exact ⟨ih₁ h.1, ih₂ h.2.1, h.2.2⟩
  | union τ₁ τ₂ ih₁ ih₂ => exact ⟨ih₁ h.1, ih₂ h.2.1, h.2.2⟩
  | sum τ₁ τ₂ ih₁ ih₂ => exact ⟨ih₁ h.1, ih₂ h.2.1, h.2.2⟩
  | arrow τ₁ τ₂ ih₁ ih₂ =>
      exact ⟨ih₁ h.1, ih₂ h.2⟩
  | wand τ₁ τ₂ ih₁ ih₂ =>
      exact ⟨ih₁ h.1, ih₂ h.2⟩
  | persist τ ih => exact ih h

theorem WellFormedAt.freeAtoms_subset {τ : ContextType} {d : Nat}
    {X : Finset Atom} (h : τ.WellFormedAt d X) : τ.freeAtoms ⊆ X := by
  induction τ generalizing d X with
  | «over» b q =>
      exact Qualifier.ScopedAt.freeAtoms_subset h
  | under b q =>
      exact Qualifier.ScopedAt.freeAtoms_subset h
  | inter τ₁ τ₂ ih₁ ih₂ =>
      intro x hx
      rcases Finset.mem_union.1 hx with hx | hx
      · exact ih₁ h.1 hx
      · exact ih₂ h.2.1 hx
  | union τ₁ τ₂ ih₁ ih₂ =>
      intro x hx
      rcases Finset.mem_union.1 hx with hx | hx
      · exact ih₁ h.1 hx
      · exact ih₂ h.2.1 hx
  | sum τ₁ τ₂ ih₁ ih₂ =>
      intro x hx
      rcases Finset.mem_union.1 hx with hx | hx
      · exact ih₁ h.1 hx
      · exact ih₂ h.2.1 hx
  | arrow τ₁ τ₂ ih₁ ih₂ =>
      intro x hx
      rcases Finset.mem_union.1 hx with hx | hx
      · exact ih₁ h.1 hx
      · exact ih₂ h.2 hx
  | wand τ₁ τ₂ ih₁ ih₂ =>
      intro x hx
      rcases Finset.mem_union.1 hx with hx | hx
      · exact False.elim (by
          have : x ∈ (∅ : Finset Atom) := ih₁ h.1 hx
          exact Finset.notMem_empty x this)
      · exact ih₂ h.2 hx
  | persist τ ih => exact ih h

end ContextType

namespace Context

/-- Formation of a bunched context under already-bound atoms `X`. -/
def WellFormedUnder : Context → Finset Atom → Prop
  | .empty, _ => True
  | .bind x τ, X => x ∉ X ∧ τ.WellFormed X
  | .comma Γ₁ Γ₂, X =>
      Γ₁.WellFormedUnder X ∧
      Γ₂.WellFormedUnder (X ∪ Γ₁.domain) ∧
      Disjoint Γ₁.domain Γ₂.domain
  | .star Γ₁ Γ₂, X =>
      Γ₁.WellFormedUnder X ∧ Γ₂.WellFormedUnder X ∧
      Disjoint Γ₁.domain Γ₂.domain
  | .sum Γ₁ Γ₂, X =>
      Γ₁.WellFormedUnder X ∧ Γ₂.WellFormedUnder X ∧
      Γ₁.domain = Γ₂.domain ∧ Γ₁.erase = Γ₂.erase

/-- Formation of a closed bunched context. -/
abbrev WellFormed (Γ : Context) : Prop :=
  Γ.WellFormedUnder ∅

theorem WellFormedUnder.freeAtoms_subset {Γ : Context} {X : Finset Atom}
    (h : Γ.WellFormedUnder X) : Γ.freeAtoms ⊆ X := by
  induction Γ generalizing X with
  | empty => simp [freeAtoms]
  | bind x τ => exact ContextType.WellFormedAt.freeAtoms_subset h.2
  | comma Γ₁ Γ₂ ih₁ ih₂ =>
      intro x hx
      rcases Finset.mem_union.1 hx with hx | hx
      · exact ih₁ h.1 hx
      · have hx₂ := ih₂ h.2.1 (Finset.mem_sdiff.1 hx).1
        rcases Finset.mem_union.1 hx₂ with hx₂ | hx₂
        · exact hx₂
        · exact ((Finset.mem_sdiff.1 hx).2 hx₂).elim
  | star Γ₁ Γ₂ ih₁ ih₂ =>
      intro x hx
      rcases Finset.mem_union.1 hx with hx | hx
      · exact ih₁ h.1 hx
      · exact ih₂ h.2.1 hx
  | sum Γ₁ Γ₂ ih₁ ih₂ =>
      intro x hx
      rcases Finset.mem_union.1 hx with hx | hx
      · exact ih₁ h.1 hx
      · exact ih₂ h.2.1 hx

theorem WellFormedUnder.domain_disjoint {Γ : Context} {X : Finset Atom}
    (h : Γ.WellFormedUnder X) : Disjoint Γ.domain X := by
  rw [Finset.disjoint_left]
  intro x hx hX
  induction Γ generalizing X with
  | empty =>
      change x ∈ (∅ : Finset Atom) at hx
      exact Finset.notMem_empty x hx
  | bind y τ =>
      have : x = y := Finset.mem_singleton.1 (by simpa [domain] using hx)
      subst x
      exact h.1 hX
  | comma Γ₁ Γ₂ ih₁ ih₂ =>
      rcases Finset.mem_union.1 (by simpa [domain] using hx) with hx | hx
      · exact ih₁ h.1 hx hX
      · exact ih₂ h.2.1 hx (Finset.mem_union_left _ hX)
  | star Γ₁ Γ₂ ih₁ ih₂ =>
      rcases Finset.mem_union.1 (by simpa [domain] using hx) with hx | hx
      · exact ih₁ h.1 hx hX
      · exact ih₂ h.2.1 hx hX
  | sum Γ₁ Γ₂ ih₁ ih₂ =>
      rcases Finset.mem_union.1 (by simpa [domain] using hx) with hx | hx
      · exact ih₁ h.1 hx hX
      · exact ih₂ h.2.1 hx hX

theorem WellFormedUnder.erase_domain {Γ : Context} {X : Finset Atom}
    (h : Γ.WellFormedUnder X) : Γ.erase.domain = Γ.domain := by
  induction Γ generalizing X with
  | empty => simp [erase, domain]
  | bind x τ => simp [erase, domain]
  | comma Γ₁ Γ₂ ih₁ ih₂ =>
      simp only [erase, domain, BasicEnv.domain_merge]
      rw [ih₁ h.1, ih₂ h.2.1]
  | star Γ₁ Γ₂ ih₁ ih₂ =>
      simp only [erase, domain, BasicEnv.domain_merge]
      rw [ih₁ h.1, ih₂ h.2.1]
  | sum Γ₁ Γ₂ ih₁ ih₂ =>
      rw [erase, ih₁ h.1, domain, h.2.2.1, Finset.union_self]

end Context

end ContextTypes
