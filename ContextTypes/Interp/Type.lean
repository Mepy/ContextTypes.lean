import ContextTypes.Interp.Atoms

set_option autoImplicit false

namespace ContextTypes

/-!
# Context-type interpretation and transport laws
-/

open scoped ContextTypes

namespace ContextType

/-! ## Result-first context-type interpretation -/

def measure : ContextType → Nat
  | .over _ _ | .under _ _ => 1
  | .inter τ₁ τ₂ | .union τ₁ τ₂ | .sum τ₁ τ₂
  | .arrow τ₁ τ₂ | .wand τ₁ τ₂ =>
      1 + max τ₁.measure τ₂.measure
  | .persist τ => 1 + τ.measure

@[simp] theorem measure_shiftFrom (τ : ContextType) (k : Nat) :
    (τ.shiftFrom k).measure = τ.measure := by
  induction τ generalizing k <;> simp_all [shiftFrom, measure]

theorem measure_pos (τ : ContextType) : 0 < τ.measure := by
  cases τ <;> simp only [measure] <;> omega

def interpFuel : Nat → Nat → BasicEnv → ContextType → Term → Formula
  | 0, d, Δ, τ, e =>
      let Δ' := Interp.relevantEnv Δ τ e
      Interp.guard d Δ' τ e ∧ᶜ ⊤ᶜ
  | gas + 1, d, Δ, τ, e =>
      let Δ' := Interp.relevantEnv Δ τ e
      let G := Interp.guard d Δ' τ e
      G ∧ᶜ
        match τ with
        | .over b q =>
            .all (Interp.resultFirst Δ' τ e ⇒ᶜ
              .fiber (q.support \ {.bound 0}) (Interp.overResult b q))
        | .under b q =>
            .all (Interp.resultFirst Δ' τ e ⇒ᶜ
              .fiber (q.support \ {.bound 0}) (Interp.underResult b q))
        | .inter τ₁ τ₂ =>
            interpFuel gas d Δ τ₁ e ∧ᶜ interpFuel gas d Δ τ₂ e
        | .union τ₁ τ₂ =>
            interpFuel gas d Δ τ₁ e ∨ᶜ interpFuel gas d Δ τ₂ e
        | .sum τ₁ τ₂ =>
            .all (Interp.resultFirst Δ' τ e ⇒ᶜ
              (interpFuel gas (d + 1) Δ' (τ₁.shiftFrom 0) (.ret (.bound 0)) ⊕
               interpFuel gas (d + 1) Δ' (τ₂.shiftFrom 0) (.ret (.bound 0))))
        | .arrow τ₁ τ₂ =>
            let τ₁' := (τ₁.shiftFrom 0).shiftFrom 0
            let τ₂' := τ₂.shiftFrom 1
            .all (Interp.resultFirst Δ' τ e ⇒ᶜ
              .all (interpFuel gas (d + 2) Δ' τ₁' (.ret (.bound 0)) ⇒ᶜ
                interpFuel gas (d + 2) Δ' τ₂'
                  (.app (.bound 1) (.bound 0))))
        | .wand τ₁ τ₂ =>
            let τ₁' := (τ₁.shiftFrom 0).shiftFrom 0
            let τ₂' := τ₂.shiftFrom 1
            .all (Interp.resultFirst Δ' τ e ⇒ᶜ
              (interpFuel gas (d + 2) Δ' τ₁' (.ret (.bound 0)) -∗[1]
                interpFuel gas (d + 2) Δ' τ₂'
                  (.app (.bound 1) (.bound 0))))
        | .persist τ =>
            .all (Interp.resultFirst Δ' (.persist τ) e ⇒ᶜ
              □ interpFuel gas (d + 1) Δ' (τ.shiftFrom 0) (.ret (.bound 0)))

/-- Once enough fuel is available to visit the entire context type, the
result-first interpretation is independent of the fuel allowance. -/
theorem interpFuel_eq_of_measure_le (gas gas' d : Nat) (Δ : BasicEnv)
    (τ : ContextType) (e : Term)
    (lower : τ.measure ≤ gas) (lower' : τ.measure ≤ gas') :
    interpFuel gas d Δ τ e = interpFuel gas' d Δ τ e := by
  have aux : ∀ n (τ : ContextType), τ.measure = n →
      ∀ gas gas' d Δ e, τ.measure ≤ gas → τ.measure ≤ gas' →
      interpFuel gas d Δ τ e = interpFuel gas' d Δ τ e := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
        intro τ hmeasure gas gas' d Δ e lower lower'
        cases gas with
        | zero =>
            have := τ.measure_pos
            omega
        | succ gas =>
            cases gas' with
            | zero =>
                have := τ.measure_pos
                omega
            | succ gas' =>
                have hchild (τ' : ContextType) (d' : Nat) (Δ' : BasicEnv) (e' : Term)
                    (smaller : τ'.measure < τ.measure) :
                    interpFuel gas d' Δ' τ' e' = interpFuel gas' d' Δ' τ' e' :=
                  ih τ'.measure (by omega) τ' rfl gas gas' d' Δ' e'
                    (by omega) (by omega)
                cases τ with
                | «over» b q => rfl
                | under b q => rfl
                | inter τ₁ τ₂ =>
                    have h₁ := hchild τ₁ d Δ e (by
                      simp only [measure]
                      omega)
                    have h₂ := hchild τ₂ d Δ e (by
                      simp only [measure]
                      omega)
                    simp only [interpFuel]
                    rw [h₁, h₂]
                | union τ₁ τ₂ =>
                    have h₁ := hchild τ₁ d Δ e (by
                      simp only [measure]
                      omega)
                    have h₂ := hchild τ₂ d Δ e (by
                      simp only [measure]
                      omega)
                    simp only [interpFuel]
                    rw [h₁, h₂]
                | sum τ₁ τ₂ =>
                    have h₁ := hchild (τ₁.shiftFrom 0) (d + 1)
                      (Interp.relevantEnv Δ (.sum τ₁ τ₂) e) (.ret (.bound 0)) (by
                        simp only [measure_shiftFrom, measure]
                        omega)
                    have h₂ := hchild (τ₂.shiftFrom 0) (d + 1)
                      (Interp.relevantEnv Δ (.sum τ₁ τ₂) e) (.ret (.bound 0)) (by
                        simp only [measure_shiftFrom, measure]
                        omega)
                    simp only [interpFuel]
                    rw [h₁, h₂]
                | arrow τ₁ τ₂ =>
                    have h₁ := hchild ((τ₁.shiftFrom 0).shiftFrom 0) (d + 2)
                      (Interp.relevantEnv Δ (.arrow τ₁ τ₂) e) (.ret (.bound 0)) (by
                        simp only [measure_shiftFrom, measure]
                        omega)
                    have h₂ := hchild (τ₂.shiftFrom 1) (d + 2)
                      (Interp.relevantEnv Δ (.arrow τ₁ τ₂) e)
                      (.app (.bound 1) (.bound 0)) (by
                        simp only [measure_shiftFrom, measure]
                        omega)
                    simp only [interpFuel]
                    rw [h₁, h₂]
                | wand τ₁ τ₂ =>
                    have h₁ := hchild ((τ₁.shiftFrom 0).shiftFrom 0) (d + 2)
                      (Interp.relevantEnv Δ (.wand τ₁ τ₂) e) (.ret (.bound 0)) (by
                        simp only [measure_shiftFrom, measure]
                        omega)
                    have h₂ := hchild (τ₂.shiftFrom 1) (d + 2)
                      (Interp.relevantEnv Δ (.wand τ₁ τ₂) e)
                      (.app (.bound 1) (.bound 0)) (by
                        simp only [measure_shiftFrom, measure]
                        omega)
                    simp only [interpFuel]
                    rw [h₁, h₂]
                | persist τ =>
                    have hτ := hchild (τ.shiftFrom 0) (d + 1)
                      (Interp.relevantEnv Δ (.persist τ) e) (.ret (.bound 0)) (by
                        simp only [measure_shiftFrom, measure]
                        omega)
                    simp only [interpFuel]
                    rw [hτ]
  exact aux τ.measure τ rfl gas gas' d Δ e lower lower'

/-- Interpretation of a context type at a core term. -/
def interp (Δ : BasicEnv) (τ : ContextType) (e : Term) : Formula :=
  interpFuel τ.measure 0 Δ τ e

theorem interp_persist (Δ : BasicEnv) (τ : ContextType) (e : Term) :
    interp Δ (.persist τ) e =
      (Interp.guard 0 (Interp.relevantEnv Δ τ e) τ e ∧ᶜ
        Formula.all
          (Interp.resultFirst (Interp.relevantEnv Δ τ e) (.persist τ) e ⇒ᶜ
            □ interpFuel τ.measure 1 (Interp.relevantEnv Δ τ e)
              (τ.shiftFrom 0) (.ret (.bound 0)))) := by
  unfold interp
  rw [show (ContextType.persist τ).measure = τ.measure + 1 by
    simp [measure, Nat.add_comm]]
  simp only [interpFuel, Interp.relevantEnv_persist,
    Interp.guard_persist, Nat.zero_add]

theorem freeAtoms_interpFuel_subset (gas d : Nat) (Δ : BasicEnv)
    (τ : ContextType) (e : Term) :
    (interpFuel gas d Δ τ e).freeAtoms ⊆ τ.freeAtoms ∪ e.support := by
  induction gas generalizing d Δ τ e with
  | zero =>
      simpa [interpFuel] using
        Interp.freeAtoms_guard_relevant_subset d Δ τ e
  | succ gas ih =>
      cases τ with
      | «over» b q =>
          simp only [interpFuel, Formula.freeAtoms_and,
            Formula.freeAtoms_all, Formula.freeAtoms_impl,
            Interp.freeAtoms_overResultFiber, ContextType.freeAtoms]
          exact Finset.union_subset
            (Interp.freeAtoms_guard_relevant_subset d Δ (.over b q) e)
            (Finset.union_subset
              (Interp.freeAtoms_resultFirst_relevant_subset Δ (.over b q) e)
              Finset.subset_union_left)
      | under b q =>
          simp only [interpFuel, Formula.freeAtoms_and,
            Formula.freeAtoms_all, Formula.freeAtoms_impl,
            Interp.freeAtoms_underResultFiber, ContextType.freeAtoms]
          exact Finset.union_subset
            (Interp.freeAtoms_guard_relevant_subset d Δ (.under b q) e)
            (Finset.union_subset
              (Interp.freeAtoms_resultFirst_relevant_subset Δ (.under b q) e)
              Finset.subset_union_left)
      | inter τ₁ τ₂ =>
          simp only [interpFuel, Formula.freeAtoms_and, ContextType.freeAtoms]
          refine Finset.union_subset
            (Interp.freeAtoms_guard_relevant_subset d Δ (.inter τ₁ τ₂) e)
            (Finset.union_subset ?_ ?_)
          · intro x hx
            rcases Finset.mem_union.1 (ih d Δ τ₁ e hx) with hx | hx
            · exact Finset.mem_union_left _ (Finset.mem_union_left _ hx)
            · exact Finset.mem_union_right _ hx
          · intro x hx
            rcases Finset.mem_union.1 (ih d Δ τ₂ e hx) with hx | hx
            · exact Finset.mem_union_left _ (Finset.mem_union_right _ hx)
            · exact Finset.mem_union_right _ hx
      | union τ₁ τ₂ =>
          simp only [interpFuel, Formula.freeAtoms_and, Formula.freeAtoms_or,
            ContextType.freeAtoms]
          refine Finset.union_subset
            (Interp.freeAtoms_guard_relevant_subset d Δ (.union τ₁ τ₂) e)
            (Finset.union_subset ?_ ?_)
          · intro x hx
            rcases Finset.mem_union.1 (ih d Δ τ₁ e hx) with hx | hx
            · exact Finset.mem_union_left _ (Finset.mem_union_left _ hx)
            · exact Finset.mem_union_right _ hx
          · intro x hx
            rcases Finset.mem_union.1 (ih d Δ τ₂ e hx) with hx | hx
            · exact Finset.mem_union_left _ (Finset.mem_union_right _ hx)
            · exact Finset.mem_union_right _ hx
      | sum τ₁ τ₂ =>
          simp only [interpFuel, Formula.freeAtoms_and,
            Formula.freeAtoms_all, Formula.freeAtoms_impl,
            Formula.freeAtoms_sum, ContextType.freeAtoms]
          refine Finset.union_subset
            (Interp.freeAtoms_guard_relevant_subset d Δ (.sum τ₁ τ₂) e)
            (Finset.union_subset
              (Interp.freeAtoms_resultFirst_relevant_subset Δ (.sum τ₁ τ₂) e)
              (Finset.union_subset ?_ ?_))
          · intro x hx
            have h := ih (d + 1) (Interp.relevantEnv Δ (.sum τ₁ τ₂) e)
              (τ₁.shiftFrom 0) (.ret (.bound 0)) hx
            simp [Term.support, Value.support] at h
            exact Finset.mem_union_left _ (Finset.mem_union_left _ h)
          · intro x hx
            have h := ih (d + 1) (Interp.relevantEnv Δ (.sum τ₁ τ₂) e)
              (τ₂.shiftFrom 0) (.ret (.bound 0)) hx
            simp [Term.support, Value.support] at h
            exact Finset.mem_union_left _ (Finset.mem_union_right _ h)
      | arrow τ₁ τ₂ =>
          simp only [interpFuel, Formula.freeAtoms_and,
            Formula.freeAtoms_all, Formula.freeAtoms_impl,
            ContextType.freeAtoms]
          refine Finset.union_subset
            (Interp.freeAtoms_guard_relevant_subset d Δ (.arrow τ₁ τ₂) e)
            (Finset.union_subset
              (Interp.freeAtoms_resultFirst_relevant_subset Δ (.arrow τ₁ τ₂) e)
              (Finset.union_subset ?_ ?_))
          · intro x hx
            have h := ih (d + 2) (Interp.relevantEnv Δ (.arrow τ₁ τ₂) e)
              ((τ₁.shiftFrom 0).shiftFrom 0) (.ret (.bound 0)) hx
            simp [Term.support, Value.support] at h
            exact Finset.mem_union_left _ (Finset.mem_union_left _ h)
          · intro x hx
            have h := ih (d + 2) (Interp.relevantEnv Δ (.arrow τ₁ τ₂) e)
              (τ₂.shiftFrom 1) (.app (.bound 1) (.bound 0)) hx
            simp [Term.support, Value.support] at h
            exact Finset.mem_union_left _ (Finset.mem_union_right _ h)
      | wand τ₁ τ₂ =>
          simp only [interpFuel, Formula.freeAtoms_and,
            Formula.freeAtoms_all, Formula.freeAtoms_impl,
            Formula.freeAtoms_wand, ContextType.freeAtoms]
          refine Finset.union_subset
            (Interp.freeAtoms_guard_relevant_subset d Δ (.wand τ₁ τ₂) e)
            (Finset.union_subset
              (Interp.freeAtoms_resultFirst_relevant_subset Δ (.wand τ₁ τ₂) e)
              (Finset.union_subset ?_ ?_))
          · intro x hx
            have h := ih (d + 2) (Interp.relevantEnv Δ (.wand τ₁ τ₂) e)
              ((τ₁.shiftFrom 0).shiftFrom 0) (.ret (.bound 0)) hx
            simp [Term.support, Value.support] at h
            exact Finset.mem_union_left _ (Finset.mem_union_left _ h)
          · intro x hx
            have h := ih (d + 2) (Interp.relevantEnv Δ (.wand τ₁ τ₂) e)
              (τ₂.shiftFrom 1) (.app (.bound 1) (.bound 0)) hx
            simp [Term.support, Value.support] at h
            exact Finset.mem_union_left _ (Finset.mem_union_right _ h)
      | persist τ =>
          simp only [interpFuel, Formula.freeAtoms_and,
            Formula.freeAtoms_all, Formula.freeAtoms_impl,
            Formula.freeAtoms_persist, ContextType.freeAtoms]
          refine Finset.union_subset
            (Interp.freeAtoms_guard_relevant_subset d Δ (.persist τ) e)
            (Finset.union_subset
              (Interp.freeAtoms_resultFirst_relevant_subset Δ (.persist τ) e)
              ?_)
          intro x hx
          have h := ih (d + 1) (Interp.relevantEnv Δ (.persist τ) e)
            (τ.shiftFrom 0) (.ret (.bound 0)) hx
          simp [Term.support, Value.support] at h
          exact Finset.mem_union_left _ h

theorem freeAtoms_interp_subset (Δ : BasicEnv) (τ : ContextType)
    (e : Term) : (interp Δ τ e).freeAtoms ⊆ τ.freeAtoms ∪ e.support :=
  freeAtoms_interpFuel_subset τ.measure 0 Δ τ e

theorem interpFuel_eq_guard_and (gas d : Nat) (Δ : BasicEnv)
    (τ : ContextType) (e : Term) :
    ∃ P, interpFuel gas d Δ τ e =
      (Interp.guard d (Interp.relevantEnv Δ τ e) τ e ∧ᶜ P) := by
  cases gas with
  | zero => exact ⟨⊤ᶜ, rfl⟩
  | succ gas => exact ⟨_, rfl⟩

theorem models_interpFuel_guard {m : Capability} {gas d : Nat}
    {Δ : BasicEnv} {τ : ContextType} {e : Term}
    (h : m ⊨ interpFuel gas d Δ τ e) :
    m ⊨ Interp.guard d (Interp.relevantEnv Δ τ e) τ e := by
  obtain ⟨P, eq⟩ := interpFuel_eq_guard_and gas d Δ τ e
  rw [eq] at h
  exact Formula.models_and_elim_left h

theorem models_interp_guard {m : Capability} {Δ : BasicEnv}
    {τ : ContextType} {e : Term} (h : m ⊨ interp Δ τ e) :
    m ⊨ Interp.guard 0 (Interp.relevantEnv Δ τ e) τ e :=
  models_interpFuel_guard h

theorem models_interp_basicWorld {m : Capability} {Δ : BasicEnv}
    {τ : ContextType} {e : Term} (h : m ⊨ interp Δ τ e) :
    m ⊨ Interp.basicWorld (Interp.relevantEnv Δ τ e) := by
  have hg := models_interp_guard h
  exact Formula.models_and_elim_left (Formula.models_and_elim_right hg)

theorem models_interp_basicTyping {m : Capability} {Δ : BasicEnv}
    {τ : ContextType} {e : Term} (h : m ⊨ interp Δ τ e) :
    m ⊨ Interp.basicTyping (Interp.relevantEnv Δ τ e) e τ.erase := by
  have hg := models_interp_guard h
  exact Formula.models_and_elim_left
    (Formula.models_and_elim_right (Formula.models_and_elim_right hg))

theorem models_interp_total {m : Capability} {Δ : BasicEnv}
    {τ : ContextType} {e : Term} (h : m ⊨ interp Δ τ e) :
    m ⊨ Interp.total e := by
  have hg := models_interp_guard h
  exact Formula.models_and_elim_right
    (Formula.models_and_elim_right (Formula.models_and_elim_right hg))

theorem models_interp_restrict {m : Capability} {Δ : BasicEnv}
    {τ : ContextType} {e : Term} {X : Finset Atom}
    (hX : τ.freeAtoms ∪ e.support ⊆ X) :
    m ⊨ interp Δ τ e ↔ m.restrict X ⊨ interp Δ τ e :=
  Formula.models_restrict_superset m (interp Δ τ e)
    (Finset.Subset.trans (freeAtoms_interp_subset Δ τ e) hX)

theorem models_interp_projection {m n : Capability} {Δ : BasicEnv}
    {τ : ContextType} {e : Term} (X : Finset Atom)
    (hX : τ.freeAtoms ∪ e.support ⊆ X)
    (same : m.restrict X = n.restrict X) :
    m ⊨ interp Δ τ e ↔ n ⊨ interp Δ τ e :=
  Formula.models_projection X
    (Finset.Subset.trans (freeAtoms_interp_subset Δ τ e) hX) same

set_option hygiene false in
scoped[ContextTypes] notation:20 (name := contextTypeInterp)
    "⟦" τ "⟧[" Δ "] " e:20 =>
  ContextTypes.ContextType.interp Δ τ e

end ContextType



namespace Interp

theorem relevantEnv_eq_of_agreeOn {Δ₁ Δ₂ : BasicEnv}
    {τ : ContextType} {e : Term}
    (h : BasicEnv.AgreeOn (τ.freeAtoms ∪ e.support) Δ₁ Δ₂) :
    relevantEnv Δ₁ τ e = relevantEnv Δ₂ τ e :=
  BasicEnv.restrict_eq_of_agreeOn h

/-- Relevant source inputs and freshly named inputs agree wherever an opened
child type can observe them. -/
theorem relevantEnv_openManyAt_agreeOn {Δ : BasicEnv} {τ υ : ContextType} {e : Term}
    {d : Nat} {η : Fin d → Atom} {T : Fin d → SimpleType}
    (inj : Function.Injective η) (source : υ.freeAtoms ⊆ τ.freeAtoms)
    (target : (υ.openManyAt 0 d η).freeAtoms ⊆ (τ.openManyAt 0 d η).freeAtoms) :
    BasicEnv.AgreeOn (υ.openManyAt 0 d η).freeAtoms
      ((relevantEnv Δ τ e).insertMany d η T)
      (relevantEnv (Δ.insertMany d η T) (τ.openManyAt 0 d η) (e.openManyAt 0 d η)) := by
  have agree : BasicEnv.AgreeOn (relevantAtoms τ e) (relevantEnv Δ τ e) Δ := by
    intro x hx
    simp only [relevantEnv, BasicEnv.lookup_restrict, if_pos hx]
  have inputs := agree.insertMany d η T inj
  intro x hx
  rw [inputs x (Finset.Subset.trans (υ.freeAtoms_openManyAt_subset 0 d η)
    (Finset.union_subset_union (Finset.Subset.trans source Finset.subset_union_left)
      (Finset.Subset.refl _)) hx)]
  simp only [relevantEnv, BasicEnv.lookup_restrict,
    if_pos (Finset.mem_union_left _ (target hx)), relevantAtoms]

end Interp

namespace ContextType

theorem interpFuel_eq_of_agreeOn (gas d : Nat) {Δ₁ Δ₂ : BasicEnv}
    {τ : ContextType} {e : Term}
    (h : BasicEnv.AgreeOn (τ.freeAtoms ∪ e.support) Δ₁ Δ₂) :
    interpFuel gas d Δ₁ τ e = interpFuel gas d Δ₂ τ e := by
  induction gas generalizing d Δ₁ Δ₂ τ e with
  | zero =>
      simp only [interpFuel]
      rw [Interp.relevantEnv_eq_of_agreeOn h]
  | succ gas ih =>
      cases τ with
      | «over» b q =>
          simp only [interpFuel]
          rw [Interp.relevantEnv_eq_of_agreeOn h]
      | under b q =>
          simp only [interpFuel]
          rw [Interp.relevantEnv_eq_of_agreeOn h]
      | sum τ₁ τ₂ =>
          simp only [interpFuel]
          rw [Interp.relevantEnv_eq_of_agreeOn h]
      | arrow τ₁ τ₂ =>
          simp only [interpFuel]
          rw [Interp.relevantEnv_eq_of_agreeOn h]
      | wand τ₁ τ₂ =>
          simp only [interpFuel]
          rw [Interp.relevantEnv_eq_of_agreeOn h]
      | persist τ =>
          simp only [interpFuel]
          rw [Interp.relevantEnv_eq_of_agreeOn h]
      | inter τ₁ τ₂ =>
          have h₁ : BasicEnv.AgreeOn (τ₁.freeAtoms ∪ e.support) Δ₁ Δ₂ :=
            h.mono (by
              intro x hx
              rcases Finset.mem_union.1 hx with hx | hx
              · exact Finset.mem_union_left _ (Finset.mem_union_left _ hx)
              · exact Finset.mem_union_right _ hx)
          have h₂ : BasicEnv.AgreeOn (τ₂.freeAtoms ∪ e.support) Δ₁ Δ₂ :=
            h.mono (by
              intro x hx
              rcases Finset.mem_union.1 hx with hx | hx
              · exact Finset.mem_union_left _ (Finset.mem_union_right _ hx)
              · exact Finset.mem_union_right _ hx)
          simp only [interpFuel]
          rw [Interp.relevantEnv_eq_of_agreeOn h]
          rw [ih _ h₁]
          rw [ih _ h₂]
      | union τ₁ τ₂ =>
          have h₁ : BasicEnv.AgreeOn (τ₁.freeAtoms ∪ e.support) Δ₁ Δ₂ :=
            h.mono (by
              intro x hx
              rcases Finset.mem_union.1 hx with hx | hx
              · exact Finset.mem_union_left _ (Finset.mem_union_left _ hx)
              · exact Finset.mem_union_right _ hx)
          have h₂ : BasicEnv.AgreeOn (τ₂.freeAtoms ∪ e.support) Δ₁ Δ₂ :=
            h.mono (by
              intro x hx
              rcases Finset.mem_union.1 hx with hx | hx
              · exact Finset.mem_union_left _ (Finset.mem_union_right _ hx)
              · exact Finset.mem_union_right _ hx)
          simp only [interpFuel]
          rw [Interp.relevantEnv_eq_of_agreeOn h]
          rw [ih _ h₁]
          rw [ih _ h₂]

theorem interpFuel_eq_of_locallyClosedAt (gas : Nat) (Δ : BasicEnv)
    (τ : ContextType) (e : Term) (k d d' : Nat)
    (closed : τ.LocallyClosedAt k) (hk : k ≤ d) (hk' : k ≤ d') :
    interpFuel gas d Δ τ e = interpFuel gas d' Δ τ e := by
  induction gas generalizing Δ τ e k d d' with
  | zero =>
      simp only [interpFuel]
      rw [Interp.guard_eq_of_locallyClosedAt _ τ e k d d' closed hk hk']
  | succ gas ih =>
      have hguard := Interp.guard_eq_of_locallyClosedAt
        (Interp.relevantEnv Δ τ e) τ e k d d' closed hk hk'
      cases τ with
      | «over» b q | under b q =>
          simp only [interpFuel]
          rw [hguard]
      | inter τ₁ τ₂ | union τ₁ τ₂ =>
          simp only [interpFuel]
          rw [hguard, ih Δ τ₁ e k d d' closed.1 hk hk',
            ih Δ τ₂ e k d d' closed.2 hk hk']
      | sum τ₁ τ₂ =>
          simp only [interpFuel]
          rw [hguard,
            ih _ (τ₁.shiftFrom 0) _ (k + 1) (d + 1) (d' + 1)
              (closed.1.shiftFrom 0) (Nat.add_le_add_right hk 1) (Nat.add_le_add_right hk' 1),
            ih _ (τ₂.shiftFrom 0) _ (k + 1) (d + 1) (d' + 1)
              (closed.2.shiftFrom 0) (Nat.add_le_add_right hk 1) (Nat.add_le_add_right hk' 1)]
      | arrow τ₁ τ₂ | wand τ₁ τ₂ =>
          simp only [interpFuel]
          rw [hguard,
            ih _ ((τ₁.shiftFrom 0).shiftFrom 0) _ (k + 1 + 1) (d + 2) (d' + 2)
              ((closed.1.shiftFrom 0).shiftFrom 0) (by omega) (by omega),
            ih _ (τ₂.shiftFrom 1) _ (k + 1 + 1) (d + 2) (d' + 2)
              (closed.2.shiftFrom 1) (by omega) (by omega)]
      | persist τ =>
          simp only [interpFuel]
          rw [hguard,
            ih _ (τ.shiftFrom 0) _ (k + 1) (d + 1) (d' + 1)
              (closed.shiftFrom 0) (Nat.add_le_add_right hk 1) (Nat.add_le_add_right hk' 1)]

theorem interpFuel_openAt_fresh (gas d : Nat) (Δ : BasicEnv)
    (τ : ContextType) (e : Term) (k : Nat) (y : Atom)
    (closedτ : τ.LocallyClosedAt k) (closedE : e.locallyClosedAt k)
    (freshΔ : y ∉ Δ.domain) (freshτ : y ∉ τ.freeAtoms)
    (freshE : y ∉ e.support) :
    (interpFuel gas d Δ τ e).openAt k y = interpFuel gas d Δ τ e := by
  induction gas generalizing d Δ τ e k with
  | zero =>
      have hΔ : y ∉ (Interp.relevantEnv Δ τ e).domain := by
        rw [Interp.relevantEnv_domain]
        exact fun hy => freshΔ (Finset.mem_inter.1 hy).1
      simp only [interpFuel, Formula.openAt]
      rw [Interp.guard_openAt_eq d _ τ e k y closedE hΔ freshE]
  | succ gas ih =>
      have hΔ : y ∉ (Interp.relevantEnv Δ τ e).domain := by
        rw [Interp.relevantEnv_domain]
        exact fun hy => freshΔ (Finset.mem_inter.1 hy).1
      have hguard := Interp.guard_openAt_eq d (Interp.relevantEnv Δ τ e)
        τ e k y closedE hΔ freshE
      have hresult := Interp.resultFirst_openAt_fresh (Interp.relevantEnv Δ τ e)
        τ e k y closedτ closedE hΔ freshE
      cases τ with
      | «over» b q =>
          have hbody := Interp.overResultFiber_openAt_fresh b q k y closedτ freshτ
          simp only [Formula.openAt] at hbody
          simp only [interpFuel, Formula.openAt]
          rw [hguard, hresult, hbody]
      | under b q =>
          have hbody := Interp.underResultFiber_openAt_fresh b q k y closedτ freshτ
          simp only [Formula.openAt] at hbody
          simp only [interpFuel, Formula.openAt]
          rw [hguard, hresult, hbody]
      | inter τ₁ τ₂ =>
          have hf : y ∉ τ₁.freeAtoms ∧ y ∉ τ₂.freeAtoms := by
            simpa [freeAtoms] using freshτ
          simp only [interpFuel, Formula.openAt]
          rw [hguard, ih d Δ τ₁ e k closedτ.1 closedE freshΔ hf.1 freshE,
            ih d Δ τ₂ e k closedτ.2 closedE freshΔ hf.2 freshE]
      | union τ₁ τ₂ =>
          have hf : y ∉ τ₁.freeAtoms ∧ y ∉ τ₂.freeAtoms := by
            simpa [freeAtoms] using freshτ
          simp only [interpFuel, Formula.openAt]
          rw [hguard, ih d Δ τ₁ e k closedτ.1 closedE freshΔ hf.1 freshE,
            ih d Δ τ₂ e k closedτ.2 closedE freshΔ hf.2 freshE]
      | sum τ₁ τ₂ =>
          have hf : y ∉ τ₁.freeAtoms ∧ y ∉ τ₂.freeAtoms := by
            simpa [freeAtoms] using freshτ
          simp only [interpFuel, Formula.openAt]
          rw [hguard, hresult,
            ih (d + 1) _ (τ₁.shiftFrom 0) (.ret (.bound 0)) (k + 1)
              (closedτ.1.shiftFrom 0) (by simp [Term.locallyClosedAt, Value.locallyClosedAt])
              hΔ (by simpa using hf.1) (by simp [Term.support, Value.support]),
            ih (d + 1) _ (τ₂.shiftFrom 0) (.ret (.bound 0)) (k + 1)
              (closedτ.2.shiftFrom 0) (by simp [Term.locallyClosedAt, Value.locallyClosedAt])
              hΔ (by simpa using hf.2) (by simp [Term.support, Value.support])]
      | arrow τ₁ τ₂ =>
          have hf : y ∉ τ₁.freeAtoms ∧ y ∉ τ₂.freeAtoms := by
            simpa [freeAtoms] using freshτ
          simp only [interpFuel, Formula.openAt]
          rw [hguard, hresult,
            ih (d + 2) _ ((τ₁.shiftFrom 0).shiftFrom 0) (.ret (.bound 0)) ((k + 1) + 1)
              ((closedτ.1.shiftFrom 0).shiftFrom 0)
              (by simp [Term.locallyClosedAt, Value.locallyClosedAt])
              hΔ (by simpa using hf.1) (by simp [Term.support, Value.support]),
            ih (d + 2) _ (τ₂.shiftFrom 1) (.app (.bound 1) (.bound 0)) ((k + 1) + 1)
              (closedτ.2.shiftFrom 1)
              (by simp [Term.locallyClosedAt, Value.locallyClosedAt])
              hΔ (by simpa using hf.2) (by simp [Term.support, Value.support])]
      | wand τ₁ τ₂ =>
          have hf : y ∉ τ₁.freeAtoms ∧ y ∉ τ₂.freeAtoms := by
            simpa [freeAtoms] using freshτ
          simp only [interpFuel, Formula.openAt]
          rw [hguard, hresult,
            ih (d + 2) _ ((τ₁.shiftFrom 0).shiftFrom 0) (.ret (.bound 0)) ((k + 1) + 1)
              ((closedτ.1.shiftFrom 0).shiftFrom 0)
              (by simp [Term.locallyClosedAt, Value.locallyClosedAt])
              hΔ (by simpa using hf.1) (by simp [Term.support, Value.support]),
            ih (d + 2) _ (τ₂.shiftFrom 1) (.app (.bound 1) (.bound 0)) ((k + 1) + 1)
              (closedτ.2.shiftFrom 1)
              (by simp [Term.locallyClosedAt, Value.locallyClosedAt])
              hΔ (by simpa using hf.2) (by simp [Term.support, Value.support])]
      | persist τ =>
          simp only [interpFuel, Formula.openAt]
          rw [hguard, hresult,
            ih (d + 1) _ (τ.shiftFrom 0) (.ret (.bound 0)) (k + 1)
              (closedτ.shiftFrom 0) (by simp [Term.locallyClosedAt, Value.locallyClosedAt])
              hΔ (by simpa using freshτ) (by simp [Term.support, Value.support])]

/-- Opening a symbolic returned argument agrees semantically with inserting
its fresh name in the erased environment and returning that name. -/
theorem models_interpFuel_ret_bound_openAt_iff
    {m : Capability} {Δ : BasicEnv} {τ : ContextType} {gas d : Nat} {y : Atom}
    (wfτ : τ.WellFormed Δ.domain) (fresh : y ∉ Δ.domain) :
    m ⊨ (interpFuel gas d Δ τ (.ret (.bound 0))).openAt 0 y ↔
      m ⊨ interpFuel gas 0 (Δ.insert y τ.erase) τ (.ret (.free y)) := by
  induction gas generalizing m Δ τ d with
  | zero =>
      simp only [interpFuel, Formula.openAt]
      constructor
      · intro h
        exact Formula.models_and_intro
          ((Interp.models_guard_relevant_ret_bound_openAt_iff wfτ fresh).1
            (Formula.models_and_elim_left h)) (Formula.models_top _)
      · intro h
        exact Formula.models_and_intro
          ((Interp.models_guard_relevant_ret_bound_openAt_iff wfτ fresh).2
            (Formula.models_and_elim_left h)) (Formula.models_top _)
  | succ gas ih =>
      let Δτ := Δ.restrict τ.freeAtoms
      let Δy := Δτ.insert y τ.erase
      have freshτ : y ∉ τ.freeAtoms := fun hy => fresh (wfτ.freeAtoms_subset hy)
      have freshΔτ : y ∉ Δτ.domain := by
        simp only [Δτ, BasicEnv.domain_restrict, Finset.mem_inter]
        exact fun h => fresh h.1
      have envB : Interp.relevantEnv Δ τ (.ret (.bound 0)) = Δτ := by
        simp [Δτ, Interp.relevantEnv, Interp.relevantAtoms, Term.support, Value.support]
      have envY : Interp.relevantEnv (Δ.insert y τ.erase) τ (.ret (.free y)) = Δy :=
        Interp.relevantEnv_insert_ret_free _ _ _ _
      have envB' : Interp.relevantEnv Δτ τ (.ret (.bound 0)) = Δτ := by
        simp [Δτ, Interp.relevantEnv, Interp.relevantAtoms, Term.support, Value.support,
          BasicEnv.restrict_restrict]
      have envY' : Interp.relevantEnv Δy τ (.ret (.free y)) = Δy := by
        rw [Interp.relevantEnv_insert_ret_free]
        simp [Δτ, Δy, BasicEnv.restrict_restrict]
      have domainB : Δτ.domain = τ.freeAtoms := by
        simp only [Δτ, BasicEnv.domain_restrict]
        exact Finset.inter_eq_right.2 wfτ.freeAtoms_subset
      have hresult : (Interp.resultFirst Δτ τ (.ret (.bound 0))).openAt 1 y =
          Interp.resultFirst Δy τ (.ret (.free y)) := by
        rw [Interp.resultFirst_ret_bound_openAt _ τ y wfτ.locallyClosedAt freshΔτ,
          Interp.resultFirst_eq_of_locallyClosed _ τ (.ret (.free y)) wfτ.locallyClosedAt (by trivial),
          envB', envY']
        simp only [Δy, BasicEnv.domain_insert, Finset.singleton_union, Finset.image_insert]
      have hguard :
          m ⊨ (Interp.guard d Δτ τ (.ret (.bound 0))).openAt 0 y ↔
          m ⊨ Interp.guard 0 Δy τ (.ret (.free y)) := by
        simpa only [envB, envY] using Interp.models_guard_relevant_ret_bound_openAt_iff
          (m := m) (d := d) wfτ fresh
      have hfuel (υ : ContextType) (e : Term) (k n n' : Nat)
          (hυ : υ.LocallyClosedAt k) (he : e.locallyClosedAt k) (hefree : e.support = ∅)
          (hs : υ.freeAtoms ⊆ τ.freeAtoms) (hn : k ≤ n) (hn' : k ≤ n') :
          (interpFuel gas n' Δτ υ e).openAt k y = interpFuel gas n Δy υ e := by
        rw [interpFuel_openAt_fresh gas n' Δτ υ e k y hυ he freshΔτ
          (fun hy => freshτ (hs hy)) (by rw [hefree]; exact Finset.notMem_empty _),
          interpFuel_eq_of_locallyClosedAt gas Δτ υ e k n' n hυ hn' hn]
        apply interpFuel_eq_of_agreeOn
        intro x hx
        have hxυ : x ∈ υ.freeAtoms := by simpa [hefree] using hx
        have hxy : x ≠ y := fun h => freshτ (h ▸ hs hxυ)
        exact (BasicEnv.lookup_insert_of_ne Δτ τ.erase hxy).symm
      have scope (h : m ⊨ Interp.guard 0 Δy τ (.ret (.free y))) :
          τ.freeAtoms ∪ {y} ⊆ m.domain := by
        have hs := (Interp.models_basicWorld_iff m Δy).1
          (Formula.models_and_elim_left (Formula.models_and_elim_right h)) |>.1
        simpa only [Δy, BasicEnv.domain_insert, domainB, Finset.union_comm] using hs
      have scopeB (υ : ContextType) (hs : υ.freeAtoms ⊆ τ.freeAtoms)
          (h : m ⊨ Interp.guard 0 Δy τ (.ret (.free y))) :
          ((interpFuel gas d Δ υ (.ret (.bound 0))).openAt 0 y).freeAtoms ⊆ m.domain := by
        intro x hx
        apply scope h
        rcases Finset.mem_union.1 (Formula.freeAtoms_openAt_subset _ 0 y hx) with hx | hx
        · exact Finset.mem_union_right _ hx
        · have hxυ := freeAtoms_interpFuel_subset gas d Δ υ (.ret (.bound 0)) hx
          exact Finset.mem_union_left _ (hs (by simpa [Term.support, Value.support] using hxυ))
      have scopeY (υ : ContextType) (hs : υ.freeAtoms ⊆ τ.freeAtoms)
          (h : m ⊨ Interp.guard 0 Δy τ (.ret (.free y))) :
          (interpFuel gas 0 (Δ.insert y τ.erase) υ (.ret (.free y))).freeAtoms ⊆ m.domain :=
        Finset.Subset.trans (freeAtoms_interpFuel_subset gas 0 _ υ (.ret (.free y)))
          (Finset.Subset.trans (Finset.union_subset_union hs (Finset.Subset.refl _)) (scope h))
      cases τ with
      | inter τ₁ τ₂ =>
          simp only [interpFuel, Formula.openAt, envB, envY]
          have h₂ := ih (m := m) (d := d) wfτ.2.1 fresh
          rw [← wfτ.2.2] at h₂
          constructor
          · intro h
            apply Formula.models_and_intro (hguard.1 (Formula.models_and_elim_left h))
            exact Formula.models_and_intro
              ((ih wfτ.1 fresh).1 (Formula.models_and_elim_left (Formula.models_and_elim_right h)))
              (h₂.1 (Formula.models_and_elim_right (Formula.models_and_elim_right h)))
          · intro h
            apply Formula.models_and_intro (hguard.2 (Formula.models_and_elim_left h))
            exact Formula.models_and_intro
              ((ih wfτ.1 fresh).2 (Formula.models_and_elim_left (Formula.models_and_elim_right h)))
              (h₂.2 (Formula.models_and_elim_right (Formula.models_and_elim_right h)))
      | union τ₁ τ₂ =>
          simp only [interpFuel, Formula.openAt, envB, envY]
          constructor
          · intro h
            have hg := hguard.1 (Formula.models_and_elim_left h)
            have hb := Formula.models_and_elim_right h
            apply Formula.models_and_intro hg
            rcases (Formula.models_or_iff _ _ _ (Formula.models_scope hb)).1 hb with h₁ | h₂
            · exact Formula.models_or_intro_left ((ih wfτ.1 fresh).1 h₁)
                (scopeY τ₂ Finset.subset_union_right hg)
            · have h₂' := (ih wfτ.2.1 fresh).1 h₂
              rw [← wfτ.2.2] at h₂'
              exact Formula.models_or_intro_right (scopeY τ₁ Finset.subset_union_left hg) h₂'
          · intro h
            have hg := Formula.models_and_elim_left h
            have hb := Formula.models_and_elim_right h
            apply Formula.models_and_intro (hguard.2 hg)
            rcases (Formula.models_or_iff _ _ _ (Formula.models_scope hb)).1 hb with h₁ | h₂
            · exact Formula.models_or_intro_left ((ih wfτ.1 fresh).2 h₁)
                (scopeB τ₂ Finset.subset_union_right hg)
            · have h₂' : m ⊨ interpFuel gas 0 (Δ.insert y τ₂.erase) τ₂ (.ret (.free y)) := by
                simpa only [ContextType.erase, wfτ.2.2] using h₂
              exact Formula.models_or_intro_right (scopeB τ₁ Finset.subset_union_left hg)
                ((ih wfτ.2.1 fresh).2 h₂')
      | «over» b q =>
          have hQ := Interp.overResultFiber_openAt_fresh b q 0 y wfτ.locallyClosedAt freshτ
          simp only [Formula.openAt] at hQ
          simp only [interpFuel, Formula.openAt, envB, envY]
          rw [hresult, hQ, Formula.models_and_iff, Formula.models_and_iff, hguard]
      | under b q =>
          have hQ := Interp.underResultFiber_openAt_fresh b q 0 y wfτ.locallyClosedAt freshτ
          simp only [Formula.openAt] at hQ
          simp only [interpFuel, Formula.openAt, envB, envY]
          rw [hresult, hQ, Formula.models_and_iff, Formula.models_and_iff, hguard]
      | sum τ₁ τ₂ =>
          have hs₁ : (τ₁.shiftFrom 0).freeAtoms ⊆ (τ₁ ⊕ τ₂ : ContextType).freeAtoms := by
            simpa only [freeAtoms_shiftFrom] using
              (Finset.subset_union_left : τ₁.freeAtoms ⊆ τ₁.freeAtoms ∪ τ₂.freeAtoms)
          have hs₂ : (τ₂.shiftFrom 0).freeAtoms ⊆ (τ₁ ⊕ τ₂ : ContextType).freeAtoms := by
            simpa only [freeAtoms_shiftFrom] using
              (Finset.subset_union_right : τ₂.freeAtoms ⊆ τ₁.freeAtoms ∪ τ₂.freeAtoms)
          have h₁ := hfuel (τ₁.shiftFrom 0) (.ret (.bound 0)) 1 1 (d + 1)
            (wfτ.1.locallyClosedAt.shiftFrom 0) (by simp [Term.locallyClosedAt, Value.locallyClosedAt]) rfl hs₁ (by omega) (by omega)
          have h₂ := hfuel (τ₂.shiftFrom 0) (.ret (.bound 0)) 1 1 (d + 1)
            (wfτ.2.1.locallyClosedAt.shiftFrom 0) (by simp [Term.locallyClosedAt, Value.locallyClosedAt]) rfl hs₂ (by omega) (by omega)
          simp only [interpFuel, Formula.openAt, envB, envY, Nat.zero_add]
          rw [hresult, h₁, h₂, Formula.models_and_iff, Formula.models_and_iff, hguard]
      | arrow τ₁ τ₂ =>
          have hs₁ : ((τ₁.shiftFrom 0).shiftFrom 0).freeAtoms ⊆ (τ₁.arrow τ₂).freeAtoms := by
            simpa only [freeAtoms_shiftFrom] using
              (Finset.subset_union_left : τ₁.freeAtoms ⊆ τ₁.freeAtoms ∪ τ₂.freeAtoms)
          have hs₂ : (τ₂.shiftFrom 1).freeAtoms ⊆ (τ₁.arrow τ₂).freeAtoms := by
            simpa only [freeAtoms_shiftFrom] using
              (Finset.subset_union_right : τ₂.freeAtoms ⊆ τ₁.freeAtoms ∪ τ₂.freeAtoms)
          have h₁ := hfuel ((τ₁.shiftFrom 0).shiftFrom 0) (.ret (.bound 0)) 2 2 (d + 2)
            ((wfτ.1.locallyClosedAt.shiftFrom 0).shiftFrom 0) (by simp [Term.locallyClosedAt, Value.locallyClosedAt]) rfl hs₁ (by omega) (by omega)
          have h₂ := hfuel (τ₂.shiftFrom 1) (.app (.bound 1) (.bound 0)) 2 2 (d + 2)
            (wfτ.2.locallyClosedAt.shiftFrom 1) (by simp [Term.locallyClosedAt, Value.locallyClosedAt]) rfl hs₂ (by omega) (by omega)
          simp only [interpFuel, Formula.openAt, envB, envY, Nat.zero_add]
          rw [hresult, h₁, h₂, Formula.models_and_iff, Formula.models_and_iff, hguard]
      | wand τ₁ τ₂ =>
          have hs₁ : ((τ₁.shiftFrom 0).shiftFrom 0).freeAtoms ⊆ (τ₁.wand τ₂).freeAtoms := by
            simpa only [freeAtoms_shiftFrom] using
              (Finset.subset_union_left : τ₁.freeAtoms ⊆ τ₁.freeAtoms ∪ τ₂.freeAtoms)
          have hs₂ : (τ₂.shiftFrom 1).freeAtoms ⊆ (τ₁.wand τ₂).freeAtoms := by
            simpa only [freeAtoms_shiftFrom] using
              (Finset.subset_union_right : τ₂.freeAtoms ⊆ τ₁.freeAtoms ∪ τ₂.freeAtoms)
          have h₁ := hfuel ((τ₁.shiftFrom 0).shiftFrom 0) (.ret (.bound 0)) 2 2 (d + 2)
            ((wfτ.1.locallyClosedAt.shiftFrom 0).shiftFrom 0) (by simp [Term.locallyClosedAt, Value.locallyClosedAt]) rfl hs₁ (by omega) (by omega)
          have h₂ := hfuel (τ₂.shiftFrom 1) (.app (.bound 1) (.bound 0)) 2 2 (d + 2)
            (wfτ.2.locallyClosedAt.shiftFrom 1) (by simp [Term.locallyClosedAt, Value.locallyClosedAt]) rfl hs₂ (by omega) (by omega)
          simp only [interpFuel, Formula.openAt, envB, envY, Nat.zero_add]
          rw [hresult, h₁, h₂, Formula.models_and_iff, Formula.models_and_iff, hguard]
      | persist τ =>
          have hs : (τ.shiftFrom 0).freeAtoms ⊆ (ContextType.persist τ).freeAtoms := by
            rw [freeAtoms_shiftFrom]
            exact Finset.Subset.refl _
          have h := hfuel (τ.shiftFrom 0) (.ret (.bound 0)) 1 1 (d + 1)
            (wfτ.locallyClosedAt.shiftFrom 0) (by simp [Term.locallyClosedAt, Value.locallyClosedAt]) rfl hs (by omega) (by omega)
          simp only [interpFuel, Formula.openAt, envB, envY, Nat.zero_add]
          rw [hresult, h, Formula.models_and_iff, Formula.models_and_iff, hguard]

/-- The full argument interpretation uses the same conversion, with fuel
fixed by the context type and the outer binder shift made explicit. -/
theorem models_interp_ret_bound_openAt_iff
    {m : Capability} {Δ : BasicEnv} {τ : ContextType} {y : Atom}
    (wfτ : τ.WellFormed Δ.domain) (fresh : y ∉ Δ.domain) :
    m ⊨ (interpFuel τ.measure 1 Δ (τ.shiftFrom 0) (.ret (.bound 0))).openAt 0 y ↔
      m ⊨ interp (Δ.insert y τ.erase) τ (.ret (.free y)) := by
  rw [τ.shiftFrom_eq_of_locallyClosedAt 0 wfτ.locallyClosedAt]
  exact models_interpFuel_ret_bound_openAt_iff wfτ fresh

/-- Opening a symbolic application with an overapproximate base codomain
agrees with the actual named dependent-codomain interpretation. -/
theorem models_interp_app_bound_openAt_over_iff {m : Capability} {Δ : BasicEnv}
    {b : BaseType} {q : Qualifier} {y z : Atom} {T : SimpleType}
    (wfτ : ({ν : b | q}).WellFormedAt 1 Δ.domain)
    (freshY : y ∉ Δ.domain) (freshZ : z ∉ Δ.domain) (hne : y ≠ z)
    (world : m ⊨ Interp.basicWorld ((Δ.insert z (.arrow T (.base b))).insert y T)) :
    m ⊨ ((interpFuel 1 2 Δ (({ν : b | q}).shiftFrom 1)
      (.app (.bound 1) (.bound 0))).openAt 1 z).openAt 0 y ↔
    m ⊨ interp ((Δ.insert z (.arrow T (.base b))).insert y T)
      (({ν : b | q}).openAt 0 y) (.app (.free z) (.free y)) := by
  have shift := ({ν : b | q}).shiftFrom_eq_of_locallyClosedAt 1 wfτ.locallyClosedAt
  have freshq : z ∉ q.freeAtoms := fun h => freshZ (wfτ.freeAtoms_subset h)
  have hg := Interp.models_guard_relevant_app_bound_openAt_iff wfτ freshY freshZ hne world
  rw [shift] at hg ⊢
  have hr := Interp.resultFirst_app_bound_openAt_named_eq T (.arrow T (.base b))
    wfτ freshY freshZ hne
  rw [shift] at hr
  have hr' :
      ((Interp.resultFirst (Interp.relevantEnv Δ ({ν : b | q}) (.app (.bound 1) (.bound 0)))
        ({ν : b | q}) (.app (.bound 1) (.bound 0))).openAt 2 z).openAt 1 y =
      Interp.resultFirst (Interp.relevantEnv ((Δ.insert z (.arrow T (.base b))).insert y T)
        (({ν : b | q}).openAt 0 y) (.app (.free z) (.free y)))
        (({ν : b | q}).openAt 0 y) (.app (.free z) (.free y)) := by
    simpa only [Interp.resultFirst, Interp.relevantSupport, Interp.relevantEnv_idem] using hr
  have hb : ((Formula.fiber (q.support \ {.bound 0}) (Interp.overResult b q)).openAt 2 z).openAt 1 y =
      Formula.fiber ((q.openAt 1 y).support \ {.bound 0}) (Interp.overResult b (q.openAt 1 y)) := by
    rw [Interp.overResultFiber_openAt_fresh b q 1 z wfτ.locallyClosedAt freshq,
      Interp.overResultFiber_openAt]
  simp only [Formula.openAt] at hb
  simp only [interp, measure, ContextType.openAt, interpFuel, Formula.openAt]
  rw [hr', hb, Formula.models_and_iff, Formula.models_and_iff, hg]
  rfl

/-- Opening a symbolic application with an underapproximate base codomain
agrees with the actual named dependent-codomain interpretation. -/
theorem models_interp_app_bound_openAt_under_iff {m : Capability} {Δ : BasicEnv}
    {b : BaseType} {q : Qualifier} {y z : Atom} {T : SimpleType}
    (wfτ : ([ν : b | q]).WellFormedAt 1 Δ.domain)
    (freshY : y ∉ Δ.domain) (freshZ : z ∉ Δ.domain) (hne : y ≠ z)
    (world : m ⊨ Interp.basicWorld ((Δ.insert z (.arrow T (.base b))).insert y T)) :
    m ⊨ ((interpFuel 1 2 Δ (([ν : b | q]).shiftFrom 1)
      (.app (.bound 1) (.bound 0))).openAt 1 z).openAt 0 y ↔
    m ⊨ interp ((Δ.insert z (.arrow T (.base b))).insert y T)
      (([ν : b | q]).openAt 0 y) (.app (.free z) (.free y)) := by
  have shift := ([ν : b | q]).shiftFrom_eq_of_locallyClosedAt 1 wfτ.locallyClosedAt
  have freshq : z ∉ q.freeAtoms := fun h => freshZ (wfτ.freeAtoms_subset h)
  have hg := Interp.models_guard_relevant_app_bound_openAt_iff wfτ freshY freshZ hne world
  rw [shift] at hg ⊢
  have hr := Interp.resultFirst_app_bound_openAt_named_eq T (.arrow T (.base b))
    wfτ freshY freshZ hne
  rw [shift] at hr
  have hr' :
      ((Interp.resultFirst (Interp.relevantEnv Δ ([ν : b | q]) (.app (.bound 1) (.bound 0)))
        ([ν : b | q]) (.app (.bound 1) (.bound 0))).openAt 2 z).openAt 1 y =
      Interp.resultFirst (Interp.relevantEnv ((Δ.insert z (.arrow T (.base b))).insert y T)
        (([ν : b | q]).openAt 0 y) (.app (.free z) (.free y)))
        (([ν : b | q]).openAt 0 y) (.app (.free z) (.free y)) := by
    simpa only [Interp.resultFirst, Interp.relevantSupport, Interp.relevantEnv_idem] using hr
  have hb : ((Formula.fiber (q.support \ {.bound 0}) (Interp.underResult b q)).openAt 2 z).openAt 1 y =
      Formula.fiber ((q.openAt 1 y).support \ {.bound 0}) (Interp.underResult b (q.openAt 1 y)) := by
    rw [Interp.underResultFiber_openAt_fresh b q 1 z wfτ.locallyClosedAt freshq,
      Interp.underResultFiber_openAt]
  simp only [Formula.openAt] at hb
  simp only [interp, measure, ContextType.openAt, interpFuel, Formula.openAt]
  rw [hr', hb, Formula.models_and_iff, Formula.models_and_iff, hg]
  rfl

/-- Finite named inputs normalize the interpretation of any dependent
overapproximate base type, at any remaining binder depth and positive fuel. -/
theorem models_interpFuel_openManyAt_over_iff
    {m : Capability} {Δ : BasicEnv} {b : BaseType} {q : Qualifier} {e : Term}
    {gas n d : Nat} {η : Fin d → Atom} {T : Fin d → SimpleType}
    (wfτ : ({ν : b | q} : ContextType).WellFormedAt (n + d) Δ.domain)
    (inj : Function.Injective η) (freshΔ : ∀ i, η i ∉ Δ.domain)
    (support : e.support ⊆ Δ.domain)
    (typed : Δ.insertMany d η T ⊢ₑ e.openManyAt n d η ⋮ .base b)
    (world : m ⊨ Interp.basicWorld (Δ.insertMany d η T)) :
    m ⊨ (interpFuel (gas + 1) (n + d) Δ ({ν : b | q}) e).openManyAt n d η ↔
      m ⊨ interpFuel (gas + 1) n (Δ.insertMany d η T)
        (({ν : b | q} : ContextType).openManyAt n d η) (e.openManyAt n d η) := by
  have hg := Interp.models_guard_relevant_openManyAt_iff wfτ inj freshΔ support typed world
  have freshτ : ∀ i, η i ∉ (ContextType.over b q).freeAtoms :=
    fun i hx => freshΔ i (wfτ.freeAtoms_subset hx)
  have freshE : ∀ i, η i ∉ e.support := fun i hx => freshΔ i (support hx)
  have hr := Interp.resultFirst_openManyAt_inputs Δ (.over b q) e n d η T
    inj freshΔ freshτ freshE
  simp only [interpFuel, Formula.openManyAt_and, Formula.openManyAt_all,
    Formula.openManyAt_impl, ContextType.openManyAt_over]
  simp only [Interp.resultFirst_relevantEnv] at *
  rw [hr, Interp.overResultFiber_openManyAt,
    Formula.models_and_iff, Formula.models_and_iff]
  simpa only [ContextType.openManyAt_over] using and_congr hg Iff.rfl

/-- The finite dependent-input conversion also preserves angelic base types. -/
theorem models_interpFuel_openManyAt_under_iff
    {m : Capability} {Δ : BasicEnv} {b : BaseType} {q : Qualifier} {e : Term}
    {gas n d : Nat} {η : Fin d → Atom} {T : Fin d → SimpleType}
    (wfτ : ([ν : b | q] : ContextType).WellFormedAt (n + d) Δ.domain)
    (inj : Function.Injective η) (freshΔ : ∀ i, η i ∉ Δ.domain)
    (support : e.support ⊆ Δ.domain)
    (typed : Δ.insertMany d η T ⊢ₑ e.openManyAt n d η ⋮ .base b)
    (world : m ⊨ Interp.basicWorld (Δ.insertMany d η T)) :
    m ⊨ (interpFuel (gas + 1) (n + d) Δ ([ν : b | q]) e).openManyAt n d η ↔
      m ⊨ interpFuel (gas + 1) n (Δ.insertMany d η T)
        (([ν : b | q] : ContextType).openManyAt n d η) (e.openManyAt n d η) := by
  have hg := Interp.models_guard_relevant_openManyAt_iff wfτ inj freshΔ support typed world
  have freshτ : ∀ i, η i ∉ (ContextType.under b q).freeAtoms :=
    fun i hx => freshΔ i (wfτ.freeAtoms_subset hx)
  have freshE : ∀ i, η i ∉ e.support := fun i hx => freshΔ i (support hx)
  have hr := Interp.resultFirst_openManyAt_inputs Δ (.under b q) e n d η T
    inj freshΔ freshτ freshE
  simp only [interpFuel, Formula.openManyAt_and, Formula.openManyAt_all,
    Formula.openManyAt_impl, ContextType.openManyAt_under]
  simp only [Interp.resultFirst_relevantEnv] at *
  rw [hr, Interp.underResultFiber_openManyAt,
    Formula.models_and_iff, Formula.models_and_iff]
  simpa only [ContextType.openManyAt_under] using and_congr hg Iff.rfl

/-- Pointwise result equivalence transports the full result-first
interpretation, including the static and universal-termination guard. -/
theorem models_interpFuel_of_reaches_iff
    {m : Capability} {Δ : BasicEnv} {τ : ContextType} {e₁ e₂ : Term} {gas : Nat}
    (wfτ : τ.WellFormed Δ.domain)
    (typed₁ : Δ ⊢ₑ e₁ ⋮ τ.erase) (typed₂ : Δ ⊢ₑ e₂ ⋮ τ.erase)
    (world : m ⊨ Interp.basicWorld Δ) (terminates : m ⊨ Interp.total e₂)
    (support : e₁.support ⊆ e₂.support)
    (heval : ∀ σ, σ ∈ m → ∀ v,
      (Interp.instantiateTerm e₁ σ.toAssignment).reaches v ↔
        (Interp.instantiateTerm e₂ σ.toAssignment).reaches v)
    (h : m ⊨ interpFuel gas 0 Δ τ e₁) :
    m ⊨ interpFuel gas 0 Δ τ e₂ := by
  induction gas generalizing τ with
  | zero =>
      exact Formula.models_and_intro
        (Interp.models_guard_relevant_of_world wfτ typed₂ world terminates)
        (Formula.models_top m)
  | succ gas ih =>
      let X := τ.freeAtoms ∪ e₁.support
      let Y := τ.freeAtoms ∪ e₂.support
      let Δ₁ := Interp.relevantEnv Δ τ e₁
      let Δ₂ := Interp.relevantEnv Δ τ e₂
      have hΔ₁ : Δ₁.domain = X := by
        rw [Interp.relevantEnv_domain]
        exact Finset.inter_eq_right.2
          (Finset.union_subset wfτ.freeAtoms_subset typed₁.support_subset)
      have hΔ₂ : Δ₂.domain = Y := by
        rw [Interp.relevantEnv_domain]
        exact Finset.inter_eq_right.2
          (Finset.union_subset wfτ.freeAtoms_subset typed₂.support_subset)
      have hres : ∀ (e : Term), e.locallyClosed →
          (Interp.relevantEnv Δ τ e).domain = τ.freeAtoms ∪ e.support →
          Interp.resultFirst (Interp.relevantEnv Δ τ e) τ e =
            Interp.resultAt ((τ.freeAtoms ∪ e.support).image LogicVar.free) e (.bound 0) := by
        intro e closed hdom
        let Δ' := Interp.relevantEnv Δ τ e
        have hX : Interp.relevantSupport Δ' τ e =
            (τ.freeAtoms ∪ e.support).image LogicVar.free := by
          rw [LogicVar.eq_image_free_of_locallyClosed
            (Interp.relevantSupport_locallyClosed Δ' τ e wfτ.locallyClosedAt closed)]
          rw [Interp.freeAtomSet_relevantSupport, Interp.relevantEnv_idem, hdom]
        change Interp.resultAt ((Interp.relevantSupport Δ' τ e).image (LogicVar.shiftFrom 0))
          (Interp.shiftTerm e) (.bound 0) = _
        have hclosed : LogicVar.LocallyClosed ((τ.freeAtoms ∪ e.support).image LogicVar.free) := by
          intro k hk
          simp at hk
        rw [hX, LogicVar.image_shiftFrom_eq_of_locallyClosed _ 0 hclosed,
          Interp.shiftTerm_eq_of_locallyClosed e closed]
      have hr₁ := hres e₁ typed₁.locallyClosed hΔ₁
      have hr₂ := hres e₂ typed₂.locallyClosed hΔ₂
      have hworldScope := (Interp.models_basicWorld_iff m Δ).1 world |>.1
      have hXY : X ⊆ Y := Finset.union_subset_union (Finset.Subset.refl _) support
      have hY : Y ⊆ m.domain := Finset.Subset.trans
        (Finset.union_subset wfτ.freeAtoms_subset typed₂.support_subset) hworldScope
      have hall (Q : Formula) (hQ : Q.freeAtoms ⊆ τ.freeAtoms)
          (hq : m ⊨ Formula.all (Interp.resultFirst Δ₁ τ e₁ ⇒ᶜ Q)) :
          m ⊨ Formula.all (Interp.resultFirst Δ₂ τ e₂ ⇒ᶜ Q) := by
        rw [hr₁] at hq
        rw [hr₂]
        exact Interp.models_all_resultAt_of_reaches_iff typed₁.locallyClosed typed₂.locallyClosed
          Finset.subset_union_right Finset.subset_union_right hXY
          (Finset.Subset.trans hQ Finset.subset_union_left) hY heval hq
      have hagree : BasicEnv.AgreeOn τ.freeAtoms Δ₁ Δ₂ := by
        intro x hx
        simp only [Δ₁, Δ₂, Interp.relevantEnv, BasicEnv.lookup_restrict,
          Interp.relevantAtoms, if_pos (Finset.mem_union_left _ hx)]
      have hfuel (τ' : ContextType) (e : Term) (d : Nat)
          (hs : τ'.freeAtoms ∪ e.support ⊆ τ.freeAtoms) :
          interpFuel gas d Δ₁ τ' e = interpFuel gas d Δ₂ τ' e :=
        interpFuel_eq_of_agreeOn gas d (hagree.mono hs)
      have hfree (τ' : ContextType) (e : Term) (d : Nat)
          (hs : τ'.freeAtoms ∪ e.support ⊆ τ.freeAtoms) :
          (interpFuel gas d Δ₁ τ' e).freeAtoms ⊆ τ.freeAtoms :=
        Finset.Subset.trans (freeAtoms_interpFuel_subset gas d Δ₁ τ' e) hs
      have hscope (τ' : ContextType) (hs : τ'.freeAtoms ⊆ τ.freeAtoms) :
          (interpFuel gas 0 Δ τ' e₂).freeAtoms ⊆ m.domain :=
        Finset.Subset.trans (freeAtoms_interpFuel_subset gas 0 Δ τ' e₂)
          (Finset.Subset.trans (Finset.union_subset_union hs (Finset.Subset.refl _)) hY)
      have hguard := Interp.models_guard_relevant_of_world wfτ typed₂ world terminates
      have hbody := Formula.models_and_elim_right h
      cases τ with
      | «over» b q =>
          dsimp only at hbody ⊢
          apply Formula.models_and_intro hguard
          exact hall _ (by rw [Interp.freeAtoms_overResultFiber]; exact Finset.Subset.refl _) hbody
      | under b q =>
          dsimp only at hbody ⊢
          apply Formula.models_and_intro hguard
          exact hall _ (by rw [Interp.freeAtoms_underResultFiber]; exact Finset.Subset.refl _) hbody
      | inter τ₁ τ₂ =>
          dsimp only at hbody ⊢
          apply Formula.models_and_intro hguard
          apply Formula.models_and_intro
          · exact ih wfτ.1 typed₁ typed₂ (Formula.models_and_elim_left hbody)
          · have ht₁ : Δ ⊢ₑ e₁ ⋮ τ₂.erase := by simpa only [ContextType.erase, wfτ.2.2] using typed₁
            have ht₂ : Δ ⊢ₑ e₂ ⋮ τ₂.erase := by simpa only [ContextType.erase, wfτ.2.2] using typed₂
            exact ih wfτ.2.1 ht₁ ht₂ (Formula.models_and_elim_right hbody)
      | union τ₁ τ₂ =>
          dsimp only at hbody ⊢
          apply Formula.models_and_intro hguard
          have hs := (Formula.models_or_iff m _ _ (Formula.models_scope hbody)).1 hbody
          rcases hs with hs | hs
          · exact Formula.models_or_intro_left (ih wfτ.1 typed₁ typed₂ hs)
              (hscope τ₂ Finset.subset_union_right)
          · have ht₁ : Δ ⊢ₑ e₁ ⋮ τ₂.erase := by simpa only [ContextType.erase, wfτ.2.2] using typed₁
            have ht₂ : Δ ⊢ₑ e₂ ⋮ τ₂.erase := by simpa only [ContextType.erase, wfτ.2.2] using typed₂
            exact Formula.models_or_intro_right (hscope τ₁ Finset.subset_union_left)
              (ih wfτ.2.1 ht₁ ht₂ hs)
      | sum τ₁ τ₂ =>
          dsimp only at hbody ⊢
          have hs₁ : (τ₁.shiftFrom 0).freeAtoms ∪ (.ret (.bound 0) : Term).support ⊆
              (τ₁ ⊕ τ₂ : ContextType).freeAtoms := by
            simpa only [freeAtoms_shiftFrom, Term.support, Value.support, Finset.union_empty] using
              (Finset.subset_union_left : τ₁.freeAtoms ⊆ τ₁.freeAtoms ∪ τ₂.freeAtoms)
          have hs₂ : (τ₂.shiftFrom 0).freeAtoms ∪ (.ret (.bound 0) : Term).support ⊆
              (τ₁ ⊕ τ₂ : ContextType).freeAtoms := by
            simpa only [freeAtoms_shiftFrom, Term.support, Value.support, Finset.union_empty] using
              (Finset.subset_union_right : τ₂.freeAtoms ⊆ τ₁.freeAtoms ∪ τ₂.freeAtoms)
          apply Formula.models_and_intro hguard
          dsimp only
          rw [← hfuel _ _ 1 hs₁, ← hfuel _ _ 1 hs₂]
          apply hall _ _ hbody
          simp only [Formula.freeAtoms_sum]
          exact Finset.union_subset (hfree _ _ 1 hs₁) (hfree _ _ 1 hs₂)
      | arrow τ₁ τ₂ =>
          dsimp only at hbody ⊢
          have hs₁ : ((τ₁.shiftFrom 0).shiftFrom 0).freeAtoms ∪
              (.ret (.bound 0) : Term).support ⊆ (ContextType.arrow τ₁ τ₂).freeAtoms := by
            simpa only [freeAtoms_shiftFrom, Term.support, Value.support, Finset.union_empty] using
              (Finset.subset_union_left : τ₁.freeAtoms ⊆ τ₁.freeAtoms ∪ τ₂.freeAtoms)
          have hs₂ : (τ₂.shiftFrom 1).freeAtoms ∪
              (.app (.bound 1) (.bound 0) : Term).support ⊆ (ContextType.arrow τ₁ τ₂).freeAtoms := by
            simpa only [freeAtoms_shiftFrom, Term.support, Value.support, Finset.union_empty] using
              (Finset.subset_union_right : τ₂.freeAtoms ⊆ τ₁.freeAtoms ∪ τ₂.freeAtoms)
          apply Formula.models_and_intro hguard
          dsimp only
          rw [← hfuel _ _ 2 hs₁, ← hfuel _ _ 2 hs₂]
          apply hall _ _ hbody
          simp only [Formula.freeAtoms_all, Formula.freeAtoms_impl]
          exact Finset.union_subset (hfree _ _ 2 hs₁) (hfree _ _ 2 hs₂)
      | wand τ₁ τ₂ =>
          dsimp only at hbody ⊢
          have hs₁ : ((τ₁.shiftFrom 0).shiftFrom 0).freeAtoms ∪
              (.ret (.bound 0) : Term).support ⊆ (ContextType.wand τ₁ τ₂).freeAtoms := by
            simpa only [freeAtoms_shiftFrom, Term.support, Value.support, Finset.union_empty] using
              (Finset.subset_union_left : τ₁.freeAtoms ⊆ τ₁.freeAtoms ∪ τ₂.freeAtoms)
          have hs₂ : (τ₂.shiftFrom 1).freeAtoms ∪
              (.app (.bound 1) (.bound 0) : Term).support ⊆ (ContextType.wand τ₁ τ₂).freeAtoms := by
            simpa only [freeAtoms_shiftFrom, Term.support, Value.support, Finset.union_empty] using
              (Finset.subset_union_right : τ₂.freeAtoms ⊆ τ₁.freeAtoms ∪ τ₂.freeAtoms)
          apply Formula.models_and_intro hguard
          dsimp only
          rw [← hfuel _ _ 2 hs₁, ← hfuel _ _ 2 hs₂]
          apply hall _ _ hbody
          simp only [Formula.freeAtoms_wand]
          exact Finset.union_subset (hfree _ _ 2 hs₁) (hfree _ _ 2 hs₂)
      | persist τ =>
          dsimp only at hbody ⊢
          have hs : (τ.shiftFrom 0).freeAtoms ∪ (.ret (.bound 0) : Term).support ⊆
              (ContextType.persist τ).freeAtoms := by
            simpa only [freeAtoms_shiftFrom, Term.support, Value.support, Finset.union_empty] using
              (Finset.Subset.refl τ.freeAtoms)
          apply Formula.models_and_intro hguard
          dsimp only
          rw [← hfuel _ _ 1 hs]
          apply hall _ _ hbody
          simp only [Formula.freeAtoms_persist]
          exact hfree _ _ 1 hs

/-- Pointwise result equivalence transports a well-formed context-type
interpretation when the target's totality obligation is established. -/
theorem models_interp_of_reaches_iff
    {m : Capability} {Δ : BasicEnv} {τ : ContextType} {e₁ e₂ : Term}
    (wfτ : τ.WellFormed Δ.domain)
    (typed₁ : Δ ⊢ₑ e₁ ⋮ τ.erase) (typed₂ : Δ ⊢ₑ e₂ ⋮ τ.erase)
    (world : m ⊨ Interp.basicWorld Δ) (terminates : m ⊨ Interp.total e₂)
    (support : e₁.support ⊆ e₂.support)
    (heval : ∀ σ, σ ∈ m → ∀ v,
      (Interp.instantiateTerm e₁ σ.toAssignment).reaches v ↔
        (Interp.instantiateTerm e₂ σ.toAssignment).reaches v)
    (h : m ⊨ interp Δ τ e₁) : m ⊨ interp Δ τ e₂ :=
  models_interpFuel_of_reaches_iff wfτ typed₁ typed₂ world terminates support heval h


/-- Correlated equality of reachable results transports the entire type
interpretation across input capabilities and erased environments. -/
theorem models_interpFuel_of_resultsEquivOn
    {m n : Capability} {Δ₁ Δ₂ : BasicEnv} {τ : ContextType} {e₁ e₂ : Term} {gas : Nat}
    (wf₁ : τ.WellFormed Δ₁.domain) (wf₂ : τ.WellFormed Δ₂.domain)
    (typed₁ : Δ₁ ⊢ₑ e₁ ⋮ τ.erase) (typed₂ : Δ₂ ⊢ₑ e₂ ⋮ τ.erase)
    (world : n ⊨ Interp.basicWorld Δ₂) (terminates : n ⊨ Interp.total e₂)
    (env : BasicEnv.AgreeOn τ.freeAtoms Δ₁ Δ₂)
    (results : Interp.ResultsEquivOn τ.freeAtoms m n e₁ e₂)
    (h : m ⊨ interpFuel gas 0 Δ₁ τ e₁) :
    n ⊨ interpFuel gas 0 Δ₂ τ e₂ := by
  induction gas generalizing τ with
  | zero =>
      exact Formula.models_and_intro
        (Interp.models_guard_relevant_of_world wf₂ typed₂ world terminates)
        (Formula.models_top n)
  | succ gas ih =>
      let X := τ.freeAtoms ∪ e₁.support
      let Y := τ.freeAtoms ∪ e₂.support
      let Θ₁ := Interp.relevantEnv Δ₁ τ e₁
      let Θ₂ := Interp.relevantEnv Δ₂ τ e₂
      have hΘ₁ : Θ₁.domain = X := by
        rw [Interp.relevantEnv_domain]
        exact Finset.inter_eq_right.2
          (Finset.union_subset wf₁.freeAtoms_subset typed₁.support_subset)
      have hΘ₂ : Θ₂.domain = Y := by
        rw [Interp.relevantEnv_domain]
        exact Finset.inter_eq_right.2
          (Finset.union_subset wf₂.freeAtoms_subset typed₂.support_subset)
      have hres : ∀ (Δ : BasicEnv) (e : Term), τ.WellFormed Δ.domain → e.locallyClosed →
          (Interp.relevantEnv Δ τ e).domain = τ.freeAtoms ∪ e.support →
          Interp.resultFirst (Interp.relevantEnv Δ τ e) τ e =
            Interp.resultAt ((τ.freeAtoms ∪ e.support).image LogicVar.free) e (.bound 0) := by
        intro Δ e wf closed hdom
        let Δ' := Interp.relevantEnv Δ τ e
        have hX : Interp.relevantSupport Δ' τ e =
            (τ.freeAtoms ∪ e.support).image LogicVar.free := by
          rw [LogicVar.eq_image_free_of_locallyClosed
            (Interp.relevantSupport_locallyClosed Δ' τ e wf.locallyClosedAt closed)]
          rw [Interp.freeAtomSet_relevantSupport, Interp.relevantEnv_idem, hdom]
        change Interp.resultAt ((Interp.relevantSupport Δ' τ e).image (LogicVar.shiftFrom 0))
          (Interp.shiftTerm e) (.bound 0) = _
        have hclosed : LogicVar.LocallyClosed ((τ.freeAtoms ∪ e.support).image LogicVar.free) := by
          intro k hk
          simp at hk
        rw [hX, LogicVar.image_shiftFrom_eq_of_locallyClosed _ 0 hclosed,
          Interp.shiftTerm_eq_of_locallyClosed e closed]
      have hr₁ := hres Δ₁ e₁ wf₁ typed₁.locallyClosed hΘ₁
      have hr₂ := hres Δ₂ e₂ wf₂ typed₂.locallyClosed hΘ₂
      have hguard₁ := models_interpFuel_guard h
      have hwf := (Interp.models_wellFormed_iff m 0 Θ₁ τ).1
        (Formula.models_and_elim_left hguard₁)
      have hX : X ⊆ m.domain := by simpa only [hΘ₁] using hwf.1
      have hY : Y ⊆ n.domain := Finset.Subset.trans
        (Finset.union_subset wf₂.freeAtoms_subset typed₂.support_subset)
        ((Interp.models_basicWorld_iff n Δ₂).1 world).1
      have total₁ : m ⊨ Interp.total e₁ := Formula.models_and_elim_right
        (Formula.models_and_elim_right (Formula.models_and_elim_right hguard₁))
      have returns₁ : ∀ σ, σ ∈ m → ∃ v, (Interp.instantiateTerm e₁ σ.toAssignment).reaches v :=
        fun σ hσ => (Interp.models_total_term typed₁.locallyClosed total₁ hσ).reaches_result
      have returns₂ : ∀ ρ, ρ ∈ n → ∃ v, (Interp.instantiateTerm e₂ ρ.toAssignment).reaches v :=
        fun ρ hρ => (Interp.models_total_term typed₂.locallyClosed terminates hρ).reaches_result
      have hall (Q : Formula) (hQ : Q.freeAtoms ⊆ τ.freeAtoms)
          (hq : m ⊨ Formula.all (Interp.resultFirst Θ₁ τ e₁ ⇒ᶜ Q)) :
          n ⊨ Formula.all (Interp.resultFirst Θ₂ τ e₂ ⇒ᶜ Q) := by
        rw [hr₁] at hq
        rw [hr₂]
        exact Interp.models_all_resultAt_of_resultsEquivOn hX hY returns₁ returns₂
          typed₁.locallyClosed typed₂.locallyClosed Finset.subset_union_right Finset.subset_union_right
          Finset.subset_union_left Finset.subset_union_left hQ results hq
      have hagree : BasicEnv.AgreeOn τ.freeAtoms Θ₁ Θ₂ := by
        intro x hx
        simp only [Θ₁, Θ₂, Interp.relevantEnv, BasicEnv.lookup_restrict,
          Interp.relevantAtoms, if_pos (Finset.mem_union_left _ hx)]
        exact env x hx
      have hfuel (τ' : ContextType) (e : Term) (d : Nat)
          (hs : τ'.freeAtoms ∪ e.support ⊆ τ.freeAtoms) :
          interpFuel gas d Θ₁ τ' e = interpFuel gas d Θ₂ τ' e :=
        interpFuel_eq_of_agreeOn gas d (hagree.mono hs)
      have hfree (τ' : ContextType) (e : Term) (d : Nat)
          (hs : τ'.freeAtoms ∪ e.support ⊆ τ.freeAtoms) :
          (interpFuel gas d Θ₁ τ' e).freeAtoms ⊆ τ.freeAtoms :=
        Finset.Subset.trans (freeAtoms_interpFuel_subset gas d Θ₁ τ' e) hs
      have hscope (τ' : ContextType) (hs : τ'.freeAtoms ⊆ τ.freeAtoms) :
          (interpFuel gas 0 Δ₂ τ' e₂).freeAtoms ⊆ n.domain :=
        Finset.Subset.trans (freeAtoms_interpFuel_subset gas 0 Δ₂ τ' e₂)
          (Finset.Subset.trans (Finset.union_subset_union hs (Finset.Subset.refl _)) hY)
      have hguard := Interp.models_guard_relevant_of_world wf₂ typed₂ world terminates
      have hbody := Formula.models_and_elim_right h
      cases τ with
      | «over» b q =>
          dsimp only at hbody ⊢
          apply Formula.models_and_intro hguard
          exact hall _ (by rw [Interp.freeAtoms_overResultFiber]; exact Finset.Subset.refl _) hbody
      | under b q =>
          dsimp only at hbody ⊢
          apply Formula.models_and_intro hguard
          exact hall _ (by rw [Interp.freeAtoms_underResultFiber]; exact Finset.Subset.refl _) hbody
      | inter τ₁ τ₂ =>
          dsimp only at hbody ⊢
          apply Formula.models_and_intro hguard
          apply Formula.models_and_intro
          · exact ih wf₁.1 wf₂.1 typed₁ typed₂
              (env.mono Finset.subset_union_left) (results.mono Finset.subset_union_left) (Formula.models_and_elim_left hbody)
          · have ht₁ : Δ₁ ⊢ₑ e₁ ⋮ τ₂.erase := by simpa only [ContextType.erase, wf₁.2.2] using typed₁
            have ht₂ : Δ₂ ⊢ₑ e₂ ⋮ τ₂.erase := by simpa only [ContextType.erase, wf₂.2.2] using typed₂
            exact ih wf₁.2.1 wf₂.2.1 ht₁ ht₂
              (env.mono Finset.subset_union_right) (results.mono Finset.subset_union_right) (Formula.models_and_elim_right hbody)
      | union τ₁ τ₂ =>
          dsimp only at hbody ⊢
          apply Formula.models_and_intro hguard
          have hs := (Formula.models_or_iff m _ _ (Formula.models_scope hbody)).1 hbody
          rcases hs with hs | hs
          · exact Formula.models_or_intro_left (ih wf₁.1 wf₂.1 typed₁ typed₂
              (env.mono Finset.subset_union_left) (results.mono Finset.subset_union_left) hs)
              (hscope τ₂ Finset.subset_union_right)
          · have ht₁ : Δ₁ ⊢ₑ e₁ ⋮ τ₂.erase := by simpa only [ContextType.erase, wf₁.2.2] using typed₁
            have ht₂ : Δ₂ ⊢ₑ e₂ ⋮ τ₂.erase := by simpa only [ContextType.erase, wf₂.2.2] using typed₂
            exact Formula.models_or_intro_right (hscope τ₁ Finset.subset_union_left)
              (ih wf₁.2.1 wf₂.2.1 ht₁ ht₂
              (env.mono Finset.subset_union_right) (results.mono Finset.subset_union_right) hs)
      | sum τ₁ τ₂ =>
          dsimp only at hbody ⊢
          have hs₁ : (τ₁.shiftFrom 0).freeAtoms ∪ (.ret (.bound 0) : Term).support ⊆
              (τ₁ ⊕ τ₂ : ContextType).freeAtoms := by
            simpa only [freeAtoms_shiftFrom, Term.support, Value.support, Finset.union_empty] using
              (Finset.subset_union_left : τ₁.freeAtoms ⊆ τ₁.freeAtoms ∪ τ₂.freeAtoms)
          have hs₂ : (τ₂.shiftFrom 0).freeAtoms ∪ (.ret (.bound 0) : Term).support ⊆
              (τ₁ ⊕ τ₂ : ContextType).freeAtoms := by
            simpa only [freeAtoms_shiftFrom, Term.support, Value.support, Finset.union_empty] using
              (Finset.subset_union_right : τ₂.freeAtoms ⊆ τ₁.freeAtoms ∪ τ₂.freeAtoms)
          apply Formula.models_and_intro hguard
          dsimp only
          rw [← hfuel _ _ 1 hs₁, ← hfuel _ _ 1 hs₂]
          apply hall _ _ hbody
          simp only [Formula.freeAtoms_sum]
          exact Finset.union_subset (hfree _ _ 1 hs₁) (hfree _ _ 1 hs₂)
      | arrow τ₁ τ₂ =>
          dsimp only at hbody ⊢
          have hs₁ : ((τ₁.shiftFrom 0).shiftFrom 0).freeAtoms ∪
              (.ret (.bound 0) : Term).support ⊆ (ContextType.arrow τ₁ τ₂).freeAtoms := by
            simpa only [freeAtoms_shiftFrom, Term.support, Value.support, Finset.union_empty] using
              (Finset.subset_union_left : τ₁.freeAtoms ⊆ τ₁.freeAtoms ∪ τ₂.freeAtoms)
          have hs₂ : (τ₂.shiftFrom 1).freeAtoms ∪
              (.app (.bound 1) (.bound 0) : Term).support ⊆ (ContextType.arrow τ₁ τ₂).freeAtoms := by
            simpa only [freeAtoms_shiftFrom, Term.support, Value.support, Finset.union_empty] using
              (Finset.subset_union_right : τ₂.freeAtoms ⊆ τ₁.freeAtoms ∪ τ₂.freeAtoms)
          apply Formula.models_and_intro hguard
          dsimp only
          rw [← hfuel _ _ 2 hs₁, ← hfuel _ _ 2 hs₂]
          apply hall _ _ hbody
          simp only [Formula.freeAtoms_all, Formula.freeAtoms_impl]
          exact Finset.union_subset (hfree _ _ 2 hs₁) (hfree _ _ 2 hs₂)
      | wand τ₁ τ₂ =>
          dsimp only at hbody ⊢
          have hs₁ : ((τ₁.shiftFrom 0).shiftFrom 0).freeAtoms ∪
              (.ret (.bound 0) : Term).support ⊆ (ContextType.wand τ₁ τ₂).freeAtoms := by
            simpa only [freeAtoms_shiftFrom, Term.support, Value.support, Finset.union_empty] using
              (Finset.subset_union_left : τ₁.freeAtoms ⊆ τ₁.freeAtoms ∪ τ₂.freeAtoms)
          have hs₂ : (τ₂.shiftFrom 1).freeAtoms ∪
              (.app (.bound 1) (.bound 0) : Term).support ⊆ (ContextType.wand τ₁ τ₂).freeAtoms := by
            simpa only [freeAtoms_shiftFrom, Term.support, Value.support, Finset.union_empty] using
              (Finset.subset_union_right : τ₂.freeAtoms ⊆ τ₁.freeAtoms ∪ τ₂.freeAtoms)
          apply Formula.models_and_intro hguard
          dsimp only
          rw [← hfuel _ _ 2 hs₁, ← hfuel _ _ 2 hs₂]
          apply hall _ _ hbody
          simp only [Formula.freeAtoms_wand]
          exact Finset.union_subset (hfree _ _ 2 hs₁) (hfree _ _ 2 hs₂)
      | persist τ =>
          dsimp only at hbody ⊢
          have hs : (τ.shiftFrom 0).freeAtoms ∪ (.ret (.bound 0) : Term).support ⊆
              (ContextType.persist τ).freeAtoms := by
            simpa only [freeAtoms_shiftFrom, Term.support, Value.support, Finset.union_empty] using
              (Finset.Subset.refl τ.freeAtoms)
          apply Formula.models_and_intro hguard
          dsimp only
          rw [← hfuel _ _ 1 hs]
          apply hall _ _ hbody
          simp only [Formula.freeAtoms_persist]
          exact hfree _ _ 1 hs

/-- Equality of the complete result graphs observed by a type transports its
interpretation, even when intermediate input variables are forgotten. -/
theorem models_interp_of_resultsEquivOn
    {m n : Capability} {Δ₁ Δ₂ : BasicEnv} {τ : ContextType} {e₁ e₂ : Term}
    (wf₁ : τ.WellFormed Δ₁.domain) (wf₂ : τ.WellFormed Δ₂.domain)
    (typed₁ : Δ₁ ⊢ₑ e₁ ⋮ τ.erase) (typed₂ : Δ₂ ⊢ₑ e₂ ⋮ τ.erase)
    (world : n ⊨ Interp.basicWorld Δ₂) (terminates : n ⊨ Interp.total e₂)
    (env : BasicEnv.AgreeOn τ.freeAtoms Δ₁ Δ₂)
    (results : Interp.ResultsEquivOn τ.freeAtoms m n e₁ e₂)
    (h : m ⊨ interp Δ₁ τ e₁) : n ⊨ interp Δ₂ τ e₂ :=
  models_interpFuel_of_resultsEquivOn wf₁ wf₂ typed₁ typed₂ world terminates env results h

/-- A well-typed lambda application has exactly the interpretation of its
beta reduct, including universal termination and nondeterministic results. -/
theorem models_interp_beta_iff {m : Capability} {Δ : BasicEnv}
    {τ : ContextType} {T : SimpleType} {e : Term} {u : Value}
    (wfτ : τ.WellFormed Δ.domain)
    (typed : Δ ⊢ₑ (.app (.lam T e) u) ⋮ τ.erase)
    (world : m ⊨ Interp.basicWorld Δ) :
    m ⊨ interp Δ τ (.app (.lam T e) u) ↔ m ⊨ interp Δ τ (e.openAt 0 u) := by
  have closed := typed.locallyClosed
  have step : HeadStep (.app (.lam T e) u) (e.openAt 0 u) :=
    .beta T e u closed
  have typed' := step.preserve typed
  have inputs : ∀ σ, σ ∈ m → ∀ x, x ∈ e.support →
      ∀ v, σ.lookup x = some v → v.locallyClosed := by
    intro σ hσ x hx v hv
    have hxΔ : x ∈ Δ.domain := typed.support_subset (Finset.mem_union_left _ hx)
    obtain ⟨U, hU⟩ := (BasicEnv.mem_domain_iff Δ x).1 hxΔ
    obtain ⟨w, hw, hwT⟩ := (Interp.models_basicWorld_iff m Δ).1 world |>.2 σ hσ x U hU
    have same : w = v := Option.some.inj (hw.symm.trans hv)
    exact same ▸ hwT.locallyClosed
  have normalize (σ : Store) (hσ : σ ∈ m) :
      Interp.instantiateTerm (e.openAt 0 u) σ.toAssignment =
        (Interp.instantiateTermAt e 1 σ.toAssignment).openAt 0
          (Interp.instantiateValueAt u 0 σ.toAssignment) := by
    rw [Interp.instantiateTerm, Interp.instantiateTermAt_store_openAt e u σ 0 0 (inputs σ hσ),
      Interp.instantiateTermAt_store_depth e σ 0 1]
  have eval (σ : Store) (hσ : σ ∈ m) (v : Value) :
      (Interp.instantiateTerm (.app (.lam T e) u) σ.toAssignment).reaches v ↔
        (Interp.instantiateTerm (e.openAt 0 u) σ.toAssignment).reaches v := by
    have hc := (Interp.instantiateTerm_typed typed
      ((Interp.models_basicWorld_iff m Δ).1 world |>.2 σ hσ)).locallyClosed
    rw [normalize σ hσ]
    simp only [Interp.instantiateTerm, Interp.instantiateTermAt, Interp.instantiateValueAt] at hc ⊢
    exact Term.beta_reaches_iff hc.1 hc.2
  have term (σ : Store) (hσ : σ ∈ m) :
      (Interp.instantiateTerm (.app (.lam T e) u) σ.toAssignment).MustTerminate ↔
        (Interp.instantiateTerm (e.openAt 0 u) σ.toAssignment).MustTerminate := by
    have hc := (Interp.instantiateTerm_typed typed
      ((Interp.models_basicWorld_iff m Δ).1 world |>.2 σ hσ)).locallyClosed
    rw [normalize σ hσ]
    simp only [Interp.instantiateTerm, Interp.instantiateTermAt, Interp.instantiateValueAt] at hc ⊢
    exact Term.beta_mustTerminate_iff hc.1 hc.2
  have scope : (.app (.lam T e) u : Term).support ⊆ m.domain :=
    Finset.Subset.trans typed.support_subset ((Interp.models_basicWorld_iff m Δ).1 world).1
  have scope' := Finset.Subset.trans step.support_subset scope
  have total : m ⊨ Interp.total (.app (.lam T e) u) ↔ m ⊨ Interp.total (e.openAt 0 u) := by
    rw [Interp.models_total_iff closed, Interp.models_total_iff typed'.locallyClosed]
    constructor
    · rintro ⟨_, h⟩
      exact ⟨scope', fun σ hσ => (term σ hσ).1 (h σ hσ)⟩
    · rintro ⟨_, h⟩
      exact ⟨scope, fun σ hσ => (term σ hσ).2 (h σ hσ)⟩
  constructor
  · intro h
    apply models_interp_of_resultsEquivOn wfτ wfτ typed typed' world
      (total.1 (models_interp_total h)) (fun _ _ => rfl) ?_ h
    intro s v
    constructor
    · rintro ⟨σ, hσ, same, hv⟩
      exact ⟨σ, hσ, same, (eval σ hσ v).1 hv⟩
    · rintro ⟨σ, hσ, same, hv⟩
      exact ⟨σ, hσ, same, (eval σ hσ v).2 hv⟩
  · intro h
    exact models_interp_of_reaches_iff wfτ typed' typed world
      (total.2 (models_interp_total h)) step.support_subset
      (fun σ hσ v => (eval σ hσ v).symm) h

/-- A well-typed fixed-point application has exactly the interpretation of
its unfolding, including universal termination and nondeterministic results. -/
theorem models_interp_fix_iff {m : Capability} {Δ : BasicEnv}
    {τ : ContextType} {T : SimpleType} {vf u : Value}
    (wfτ : τ.WellFormed Δ.domain)
    (typed : Δ ⊢ₑ (.app (.fix T vf) u) ⋮ τ.erase)
    (world : m ⊨ Interp.basicWorld Δ) :
    m ⊨ interp Δ τ (.app (.fix T vf) u) ↔
      m ⊨ interp Δ τ (.app (vf.openAt 0 u) (.fix T vf)) := by
  have closed := typed.locallyClosed
  have step : HeadStep (.app (.fix T vf) u) (.app (vf.openAt 0 u) (.fix T vf)) :=
    .fix T vf u closed
  have typed' := step.preserve typed
  have inputs : ∀ σ, σ ∈ m → ∀ x, x ∈ vf.support →
      ∀ v, σ.lookup x = some v → v.locallyClosed := by
    intro σ hσ x hx v hv
    have hxΔ : x ∈ Δ.domain := typed.support_subset (Finset.mem_union_left _ hx)
    obtain ⟨U, hU⟩ := (BasicEnv.mem_domain_iff Δ x).1 hxΔ
    obtain ⟨w, hw, hwT⟩ := (Interp.models_basicWorld_iff m Δ).1 world |>.2 σ hσ x U hU
    have same : w = v := Option.some.inj (hw.symm.trans hv)
    exact same ▸ hwT.locallyClosed
  have normalize (σ : Store) (hσ : σ ∈ m) :
      Interp.instantiateTerm (.app (vf.openAt 0 u) (.fix T vf)) σ.toAssignment =
        .app ((Interp.instantiateValueAt vf 1 σ.toAssignment).openAt 0
          (Interp.instantiateValueAt u 0 σ.toAssignment))
          (.fix T (Interp.instantiateValueAt vf 1 σ.toAssignment)) := by
    simp only [Interp.instantiateTerm, Interp.instantiateTermAt, Interp.instantiateValueAt]
    rw [Interp.instantiateValueAt_store_openAt vf u σ 0 0 (inputs σ hσ),
      Interp.instantiateValueAt_store_depth vf σ 0 1]
  have eval (σ : Store) (hσ : σ ∈ m) (v : Value) :
      (Interp.instantiateTerm (.app (.fix T vf) u) σ.toAssignment).reaches v ↔
        (Interp.instantiateTerm (.app (vf.openAt 0 u) (.fix T vf)) σ.toAssignment).reaches v := by
    have hc := (Interp.instantiateTerm_typed typed
      ((Interp.models_basicWorld_iff m Δ).1 world |>.2 σ hσ)).locallyClosed
    rw [normalize σ hσ]
    simp only [Interp.instantiateTerm, Interp.instantiateTermAt, Interp.instantiateValueAt] at hc ⊢
    exact Term.fix_reaches_iff hc.1 hc.2
  have term (σ : Store) (hσ : σ ∈ m) :
      (Interp.instantiateTerm (.app (.fix T vf) u) σ.toAssignment).MustTerminate ↔
        (Interp.instantiateTerm (.app (vf.openAt 0 u) (.fix T vf)) σ.toAssignment).MustTerminate := by
    have hc := (Interp.instantiateTerm_typed typed
      ((Interp.models_basicWorld_iff m Δ).1 world |>.2 σ hσ)).locallyClosed
    rw [normalize σ hσ]
    simp only [Interp.instantiateTerm, Interp.instantiateTermAt, Interp.instantiateValueAt] at hc ⊢
    exact Term.fix_mustTerminate_iff hc.1 hc.2
  have scope : (.app (.fix T vf) u : Term).support ⊆ m.domain :=
    Finset.Subset.trans typed.support_subset ((Interp.models_basicWorld_iff m Δ).1 world).1
  have scope' := Finset.Subset.trans step.support_subset scope
  have total : m ⊨ Interp.total (.app (.fix T vf) u) ↔
      m ⊨ Interp.total (.app (vf.openAt 0 u) (.fix T vf)) := by
    rw [Interp.models_total_iff closed, Interp.models_total_iff typed'.locallyClosed]
    constructor
    · rintro ⟨_, h⟩
      exact ⟨scope', fun σ hσ => (term σ hσ).1 (h σ hσ)⟩
    · rintro ⟨_, h⟩
      exact ⟨scope, fun σ hσ => (term σ hσ).2 (h σ hσ)⟩
  constructor
  · intro h
    apply models_interp_of_resultsEquivOn wfτ wfτ typed typed' world
      (total.1 (models_interp_total h)) (fun _ _ => rfl) ?_ h
    intro s v
    constructor
    · rintro ⟨σ, hσ, same, hv⟩
      exact ⟨σ, hσ, same, (eval σ hσ v).1 hv⟩
    · rintro ⟨σ, hσ, same, hv⟩
      exact ⟨σ, hσ, same, (eval σ hσ v).2 hv⟩
  · intro h
    exact models_interp_of_reaches_iff wfτ typed' typed world
      (total.2 (models_interp_total h)) step.support_subset
      (fun σ hσ v => (eval σ hσ v).symm) h

/-- Every result of a term may be named in the erased environment while
preserving the complete result-first context-type interpretation. -/
theorem models_interpFuel_named_result
    {m : Capability} {Δ : BasicEnv} {τ : ContextType} {e : Term}
    {gas : Nat} {y : Atom} {X : Finset LogicVar}
    (wfτ : τ.WellFormed Δ.domain) (typed : Δ ⊢ₑ e ⋮ τ.erase)
    (world : m ⊨ Interp.basicWorld Δ)
    (closedX : LogicVar.LocallyClosed X) (supportX : e.logicSupport ⊆ X)
    (typeSupport : τ.freeAtoms.image LogicVar.free ⊆ X)
    (freshX : LogicVar.free y ∉ X) (freshΔ : y ∉ Δ.domain)
    (hres : m ⊨ Interp.resultAt X e (.free y))
    (hsource : m ⊨ interpFuel gas 0 Δ τ e) :
    m ⊨ interpFuel gas 0 (Δ.insert y τ.erase) τ (.ret (.free y)) := by
  have hy : y ∈ m.domain := by
    apply Formula.models_scope hres
    rw [Interp.freeAtoms_resultAt]
    simp [LogicVar.freeAtoms]
  have htyped := Formula.models_and_elim_left
    (Formula.models_and_elim_right (Formula.models_and_elim_right (models_interpFuel_guard hsource)))
  have world' := Interp.models_basicWorld_insert world hy
    (Interp.models_resultAt_typed closedX typed.locallyClosed supportX freshX hres htyped)
  have lookup := BasicEnv.lookup_insert Δ y τ.erase
  apply models_interpFuel_of_resultsEquivOn wfτ
    (wfτ.mono (by simp [BasicEnv.domain_insert])) typed
    (BasicTermTyp.ret (BasicValTyp.free lookup)) world'
    (Interp.models_total_ret_free world' lookup)
    ?_ ?_ hsource
  · intro x hx
    rw [BasicEnv.lookup_insert_of_ne _ τ.erase]
    intro hxy
    subst x
    exact freshΔ (wfτ.freeAtoms_subset hx)
  · apply Interp.resultsEquivOn_result_alias closedX supportX freshX ?_ hres
    intro x hx
    exact (LogicVar.mem_freeAtomSet_iff X x).2 (typeSupport (Finset.mem_image.2 ⟨x, hx, rfl⟩))

/-- Naming every result also preserves the full type interpretation. -/
theorem models_interp_named_result
    {m : Capability} {Δ : BasicEnv} {τ : ContextType} {e : Term}
    {y : Atom} {X : Finset LogicVar}
    (wfτ : τ.WellFormed Δ.domain) (typed : Δ ⊢ₑ e ⋮ τ.erase)
    (world : m ⊨ Interp.basicWorld Δ)
    (closedX : LogicVar.LocallyClosed X) (supportX : e.logicSupport ⊆ X)
    (typeSupport : τ.freeAtoms.image LogicVar.free ⊆ X)
    (freshX : LogicVar.free y ∉ X) (freshΔ : y ∉ Δ.domain)
    (hres : m ⊨ Interp.resultAt X e (.free y))
    (hsource : m ⊨ interp Δ τ e) :
    m ⊨ interp (Δ.insert y τ.erase) τ (.ret (.free y)) :=
  models_interpFuel_named_result wfτ typed world closedX supportX typeSupport freshX freshΔ hres hsource

/-- Name every result of a nondeterministic term beneath a fresh binder,
preserving the whole context-type interpretation. -/
theorem models_interpFuel_result_alias
    {m : Capability} {Δ : BasicEnv} {τ : ContextType}
    {gas d : Nat} {e : Term} {y : Atom} {X : Finset LogicVar}
    (closedX : LogicVar.LocallyClosed X) (closedE : e.locallyClosed)
    (supportX : e.logicSupport ⊆ X)
    (freshX : LogicVar.free y ∉ X) (freshΔ : y ∉ Δ.domain)
    (wfτ : τ.WellFormed Δ.domain) (supportE : e.support ⊆ Δ.domain)
    (typeSupport : τ.freeAtoms.image LogicVar.free ⊆ X)
    (hres : m ⊨ Interp.resultAt X e (.free y))
    (hsource : m ⊨ interpFuel gas d Δ τ e) :
    m ⊨ (interpFuel gas (d + 1) Δ (τ.shiftFrom 0)
      (.ret (.bound 0))).openAt 0 y := by
  induction gas generalizing d Δ τ with
  | zero =>
      simp only [interpFuel, Formula.openAt]
      apply Formula.models_and_intro
      · exact Interp.models_guard_relevant_shift_openAt_result_alias (e := e) closedX closedE
          supportX freshX freshΔ hres (models_interpFuel_guard hsource)
      · exact Formula.models_top _
  | succ gas ih =>
      have hguard := models_interpFuel_guard hsource
      have hbody := Formula.models_and_elim_right hsource
      have hclosed := wfτ.locallyClosedAt
      have hshift := τ.shiftFrom_eq_of_locallyClosedAt 0 hclosed
      let Δe := Interp.relevantEnv Δ τ e
      let Δτ := Interp.relevantEnv Δ τ (.ret (.bound 0))
      have hΔτ : y ∉ Δτ.domain := by
        rw [Interp.relevantEnv_domain]
        exact fun hy => freshΔ (Finset.mem_inter.1 hy).1
      have hall : ∀ Q : Formula, Q.freeAtoms ⊆ τ.freeAtoms →
          m ⊨ Formula.all
            (Interp.resultFirst Δe τ e ⇒ᶜ Q) →
          m ⊨ Formula.all
            ((Interp.resultFirst Δτ τ (.ret (.bound 0))).openAt 1 y ⇒ᶜ Q) := by
        intro Q hQ h
        exact Interp.models_resultFirst_result_alias wfτ closedE supportE
          closedX supportX typeSupport freshX freshΔ hQ hres h
      have hfuel : ∀ (υ : ContextType) (e : Term) (k n n' : Nat),
          υ.LocallyClosedAt k → e.locallyClosedAt k → e.support = ∅ →
          υ.freeAtoms ⊆ τ.freeAtoms → k ≤ n → k ≤ n' →
          (interpFuel gas n' Δτ υ e).openAt k y = interpFuel gas n Δe υ e := by
        intro υ e k n n' hυ he hefree hυτ hkn hkn'
        have hfree : y ∉ υ.freeAtoms := fun hy => freshΔ (wfτ.freeAtoms_subset (hυτ hy))
        rw [interpFuel_openAt_fresh gas n' Δτ υ e k y hυ he hΔτ hfree
          (by rw [hefree]; exact Finset.notMem_empty _),
          interpFuel_eq_of_locallyClosedAt gas Δτ υ e k n' n hυ hkn' hkn]
        apply interpFuel_eq_of_agreeOn
        intro x hx
        have hxυ : x ∈ υ.freeAtoms := by simpa [hefree] using hx
        have hxτ := hυτ hxυ
        simp [Δτ, Δe, Interp.relevantEnv, Interp.relevantAtoms,
          BasicEnv.lookup_restrict, hxτ, Term.support, Value.support]
      have hscopeInner : ∀ (υ : ContextType) (e : Term) (n : Nat),
          e.support = ∅ → υ.freeAtoms ⊆ τ.freeAtoms →
          (interpFuel gas n Δe υ e).freeAtoms ⊆ τ.freeAtoms := by
        intro υ e n he hυ
        have hs := freeAtoms_interpFuel_subset gas n Δe υ e
        rw [he, Finset.union_empty] at hs
        exact Finset.Subset.trans hs hυ
      have hTypeSupport (υ : ContextType) (hυ : υ.freeAtoms ⊆ τ.freeAtoms) :
          υ.freeAtoms.image LogicVar.free ⊆ X :=
        Finset.Subset.trans (Finset.image_subset_image hυ) typeSupport
      have htargetGuard : m ⊨
          (Interp.guard (d + 1) Δτ τ (.ret (.bound 0))).openAt 0 y := by
        simpa only [hshift] using
          Interp.models_guard_relevant_shift_openAt_result_alias (e := e) closedX closedE
            supportX freshX freshΔ hres hguard
      have hτScope : τ.freeAtoms ⊆ m.domain := by
        have hwf := (Interp.models_wellFormed_iff m d Δe τ).1
          (Formula.models_and_elim_left hguard)
        exact Finset.Subset.trans hwf.2.freeAtoms_subset hwf.1
      have hyScope : y ∈ m.domain := by
        apply Formula.models_scope hres
        rw [Interp.freeAtoms_resultAt]
        simp [LogicVar.freeAtoms]
      have scopeOpened : ∀ υ : ContextType, υ.freeAtoms ⊆ τ.freeAtoms →
          ((interpFuel gas (d + 1) Δ υ (.ret (.bound 0))).openAt 0 y).freeAtoms ⊆ m.domain := by
        intro υ hυ x hx
        rcases Finset.mem_union.1
          (Formula.freeAtoms_openAt_subset _ 0 y hx) with hx | hx
        · have hxy := Finset.mem_singleton.1 hx
          subst x
          exact hyScope
        · apply hτScope
          apply hυ
          have hs := freeAtoms_interpFuel_subset gas (d + 1) Δ υ (.ret (.bound 0)) hx
          simpa [Term.support, Value.support] using hs
      rw [hshift]
      cases τ with
      | inter τ₁ τ₂ =>
          have hshift₁ := τ₁.shiftFrom_eq_of_locallyClosedAt 0 wfτ.1.locallyClosedAt
          have hshift₂ := τ₂.shiftFrom_eq_of_locallyClosedAt 0 wfτ.2.1.locallyClosedAt
          simp only [interpFuel, Formula.openAt]
          apply Formula.models_and_intro htargetGuard
          apply Formula.models_and_intro
          · simpa only [hshift₁] using ih freshΔ wfτ.1 supportE (hTypeSupport τ₁ Finset.subset_union_left)
              (Formula.models_and_elim_left hbody)
          · simpa only [hshift₂] using ih freshΔ wfτ.2.1 supportE (hTypeSupport τ₂ Finset.subset_union_right)
              (Formula.models_and_elim_right hbody)
      | union τ₁ τ₂ =>
          have hshift₁ := τ₁.shiftFrom_eq_of_locallyClosedAt 0 wfτ.1.locallyClosedAt
          have hshift₂ := τ₂.shiftFrom_eq_of_locallyClosedAt 0 wfτ.2.1.locallyClosedAt
          simp only [interpFuel, Formula.openAt]
          apply Formula.models_and_intro htargetGuard
          rcases (Formula.models_or_iff _ _ _ (Formula.models_scope hbody)).1 hbody with h₁ | h₂
          · apply Formula.models_or_intro_left
            · simpa only [hshift₁] using ih freshΔ wfτ.1 supportE (hTypeSupport τ₁ Finset.subset_union_left) h₁
            · exact scopeOpened τ₂ Finset.subset_union_right
          · apply Formula.models_or_intro_right
            · exact scopeOpened τ₁ Finset.subset_union_left
            · simpa only [hshift₂] using ih freshΔ wfτ.2.1 supportE (hTypeSupport τ₂ Finset.subset_union_right) h₂
      | «over» b q =>
          have hQ := Interp.overResultFiber_openAt_fresh b q 0 y hclosed
            (fun hy => freshΔ (wfτ.freeAtoms_subset hy))
          simp only [Formula.openAt] at hQ
          simp only [interpFuel, Formula.openAt]
          apply Formula.models_and_intro htargetGuard
          rw [hQ]
          exact hall _ (by rw [Interp.freeAtoms_overResultFiber]; exact Finset.Subset.refl _) hbody
      | under b q =>
          have hQ := Interp.underResultFiber_openAt_fresh b q 0 y hclosed
            (fun hy => freshΔ (wfτ.freeAtoms_subset hy))
          simp only [Formula.openAt] at hQ
          simp only [interpFuel, Formula.openAt]
          apply Formula.models_and_intro htargetGuard
          rw [hQ]
          exact hall _ (by rw [Interp.freeAtoms_underResultFiber]; exact Finset.Subset.refl _) hbody
      | sum τ₁ τ₂ =>
          have hs₁ : (τ₁.shiftFrom 0).freeAtoms ⊆ (τ₁.sum τ₂).freeAtoms := by
            simpa only [freeAtoms_shiftFrom] using
              (Finset.subset_union_left : τ₁.freeAtoms ⊆ τ₁.freeAtoms ∪ τ₂.freeAtoms)
          have hs₂ : (τ₂.shiftFrom 0).freeAtoms ⊆ (τ₁.sum τ₂).freeAtoms := by
            simpa only [freeAtoms_shiftFrom] using
              (Finset.subset_union_right : τ₂.freeAtoms ⊆ τ₁.freeAtoms ∪ τ₂.freeAtoms)
          have h₁ := hfuel (τ₁.shiftFrom 0) (.ret (.bound 0)) 1 (d + 1) (d + 1 + 1)
            (wfτ.1.locallyClosedAt.shiftFrom 0)
            (by simp [Term.locallyClosedAt, Value.locallyClosedAt]) rfl hs₁ (by omega) (by omega)
          have h₂ := hfuel (τ₂.shiftFrom 0) (.ret (.bound 0)) 1 (d + 1) (d + 1 + 1)
            (wfτ.2.1.locallyClosedAt.shiftFrom 0)
            (by simp [Term.locallyClosedAt, Value.locallyClosedAt]) rfl hs₂ (by omega) (by omega)
          simp only [interpFuel, Formula.openAt]
          apply Formula.models_and_intro htargetGuard
          rw [h₁, h₂]
          apply hall _ ?_ hbody
          simp only [Formula.freeAtoms_sum]
          exact Finset.union_subset (hscopeInner _ _ _ rfl hs₁) (hscopeInner _ _ _ rfl hs₂)
      | arrow τ₁ τ₂ =>
          have hs₁ : ((τ₁.shiftFrom 0).shiftFrom 0).freeAtoms ⊆ (τ₁.arrow τ₂).freeAtoms := by
            simpa only [freeAtoms_shiftFrom] using
              (Finset.subset_union_left : τ₁.freeAtoms ⊆ τ₁.freeAtoms ∪ τ₂.freeAtoms)
          have hs₂ : (τ₂.shiftFrom 1).freeAtoms ⊆ (τ₁.arrow τ₂).freeAtoms := by
            simpa only [freeAtoms_shiftFrom] using
              (Finset.subset_union_right : τ₂.freeAtoms ⊆ τ₁.freeAtoms ∪ τ₂.freeAtoms)
          have h₁ := hfuel ((τ₁.shiftFrom 0).shiftFrom 0) (.ret (.bound 0)) 2 (d + 2) (d + 1 + 2)
            ((wfτ.1.locallyClosedAt.shiftFrom 0).shiftFrom 0)
            (by simp [Term.locallyClosedAt, Value.locallyClosedAt]) rfl hs₁ (by omega) (by omega)
          have h₂ := hfuel (τ₂.shiftFrom 1) (.app (.bound 1) (.bound 0)) 2 (d + 2) (d + 1 + 2)
            (wfτ.2.locallyClosedAt.shiftFrom 1)
            (by simp [Term.locallyClosedAt, Value.locallyClosedAt]) rfl hs₂ (by omega) (by omega)
          simp only [interpFuel, Formula.openAt]
          apply Formula.models_and_intro htargetGuard
          rw [h₁, h₂]
          apply hall _ ?_ hbody
          simp only [Formula.freeAtoms_all, Formula.freeAtoms_impl]
          exact Finset.union_subset (hscopeInner _ _ _ rfl hs₁) (hscopeInner _ _ _ rfl hs₂)
      | wand τ₁ τ₂ =>
          have hs₁ : ((τ₁.shiftFrom 0).shiftFrom 0).freeAtoms ⊆ (τ₁.wand τ₂).freeAtoms := by
            simpa only [freeAtoms_shiftFrom] using
              (Finset.subset_union_left : τ₁.freeAtoms ⊆ τ₁.freeAtoms ∪ τ₂.freeAtoms)
          have hs₂ : (τ₂.shiftFrom 1).freeAtoms ⊆ (τ₁.wand τ₂).freeAtoms := by
            simpa only [freeAtoms_shiftFrom] using
              (Finset.subset_union_right : τ₂.freeAtoms ⊆ τ₁.freeAtoms ∪ τ₂.freeAtoms)
          have h₁ := hfuel ((τ₁.shiftFrom 0).shiftFrom 0) (.ret (.bound 0)) 2 (d + 2) (d + 1 + 2)
            ((wfτ.1.locallyClosedAt.shiftFrom 0).shiftFrom 0)
            (by simp [Term.locallyClosedAt, Value.locallyClosedAt]) rfl hs₁ (by omega) (by omega)
          have h₂ := hfuel (τ₂.shiftFrom 1) (.app (.bound 1) (.bound 0)) 2 (d + 2) (d + 1 + 2)
            (wfτ.2.locallyClosedAt.shiftFrom 1)
            (by simp [Term.locallyClosedAt, Value.locallyClosedAt]) rfl hs₂ (by omega) (by omega)
          simp only [interpFuel, Formula.openAt]
          apply Formula.models_and_intro htargetGuard
          rw [h₁, h₂]
          apply hall _ ?_ hbody
          simp only [Formula.freeAtoms_wand]
          exact Finset.union_subset (hscopeInner _ _ _ rfl hs₁) (hscopeInner _ _ _ rfl hs₂)
      | persist τ =>
          have hs : (τ.shiftFrom 0).freeAtoms ⊆ (ContextType.persist τ).freeAtoms := by
            rw [freeAtoms_shiftFrom]
            exact Finset.Subset.refl _
          have h := hfuel (τ.shiftFrom 0) (.ret (.bound 0)) 1 (d + 1) (d + 1 + 1)
            (wfτ.locallyClosedAt.shiftFrom 0)
            (by simp [Term.locallyClosedAt, Value.locallyClosedAt]) rfl hs (by omega) (by omega)
          simp only [interpFuel, Formula.openAt]
          apply Formula.models_and_intro htargetGuard
          rw [h]
          apply hall _ ?_ hbody
          simp only [Formula.freeAtoms_persist]
          exact hscopeInner _ _ _ rfl hs

/-- Name a returned value beneath a fresh result binder without changing its
type interpretation on a singleton capability. -/
theorem models_interpFuel_ret_alias_singleton
    {m : Capability} {ρ : Store} {Δ : BasicEnv} {τ : ContextType}
    {gas d : Nat} {v : Value} {y : Atom} {X : Finset LogicVar}
    (closedX : LogicVar.LocallyClosed X) (closedV : v.locallyClosed)
    (supportX : (.ret v : Term).logicSupport ⊆ X)
    (freshX : LogicVar.free y ∉ X) (freshΔ : y ∉ Δ.domain)
    (wfτ : τ.WellFormed Δ.domain) (supportV : v.support ⊆ Δ.domain)
    (single : m = Capability.singleton ρ)
    (hres : m ⊨ Interp.resultAt X (.ret v) (.free y))
    (hsource : m ⊨ interpFuel gas d Δ τ (.ret v)) :
    m ⊨ (interpFuel gas (d + 1) Δ (τ.shiftFrom 0)
      (.ret (.bound 0))).openAt 0 y := by
  subst m
  induction gas generalizing d Δ τ with
  | zero =>
      simp only [interpFuel, Formula.openAt]
      apply Formula.models_and_intro
      · exact Interp.models_guard_relevant_shift_openAt_result_alias (e := .ret v) closedX closedV
          supportX freshX freshΔ hres (models_interpFuel_guard hsource)
      · exact Formula.models_top _
  | succ gas ih =>
      have hguard := models_interpFuel_guard hsource
      have hbody := Formula.models_and_elim_right hsource
      have hclosed := wfτ.locallyClosedAt
      have hshift := τ.shiftFrom_eq_of_locallyClosedAt 0 hclosed
      let Δe := Interp.relevantEnv Δ τ (.ret v)
      let Δτ := Interp.relevantEnv Δ τ (.ret (.bound 0))
      have hΔτ : y ∉ Δτ.domain := by
        rw [Interp.relevantEnv_domain]
        exact fun hy => freshΔ (Finset.mem_inter.1 hy).1
      have hall : ∀ Q : Formula, Q.freeAtoms ⊆ τ.freeAtoms →
          Capability.singleton ρ ⊨ Formula.all
            (Interp.resultFirst Δe τ (.ret v) ⇒ᶜ Q) →
          Capability.singleton ρ ⊨ Formula.all
            ((Interp.resultFirst Δτ τ (.ret (.bound 0))).openAt 1 y ⇒ᶜ Q) := by
        intro Q hQ h
        exact Interp.models_resultFirst_ret_alias_singleton wfτ closedV supportV
          closedX supportX freshX freshΔ hQ hres h
      have hfuel : ∀ (υ : ContextType) (e : Term) (k n n' : Nat),
          υ.LocallyClosedAt k → e.locallyClosedAt k → e.support = ∅ →
          υ.freeAtoms ⊆ τ.freeAtoms → k ≤ n → k ≤ n' →
          (interpFuel gas n' Δτ υ e).openAt k y = interpFuel gas n Δe υ e := by
        intro υ e k n n' hυ he hefree hυτ hkn hkn'
        have hfree : y ∉ υ.freeAtoms := fun hy => freshΔ (wfτ.freeAtoms_subset (hυτ hy))
        rw [interpFuel_openAt_fresh gas n' Δτ υ e k y hυ he hΔτ hfree
          (by rw [hefree]; exact Finset.notMem_empty _),
          interpFuel_eq_of_locallyClosedAt gas Δτ υ e k n' n hυ hkn' hkn]
        apply interpFuel_eq_of_agreeOn
        intro x hx
        have hxυ : x ∈ υ.freeAtoms := by simpa [hefree] using hx
        have hxτ := hυτ hxυ
        simp [Δτ, Δe, Interp.relevantEnv, Interp.relevantAtoms,
          BasicEnv.lookup_restrict, hxτ, Term.support, Value.support]
      have hscopeInner : ∀ (υ : ContextType) (e : Term) (n : Nat),
          e.support = ∅ → υ.freeAtoms ⊆ τ.freeAtoms →
          (interpFuel gas n Δe υ e).freeAtoms ⊆ τ.freeAtoms := by
        intro υ e n he hυ
        have hs := freeAtoms_interpFuel_subset gas n Δe υ e
        rw [he, Finset.union_empty] at hs
        exact Finset.Subset.trans hs hυ
      have htargetGuard : Capability.singleton ρ ⊨
          (Interp.guard (d + 1) Δτ τ (.ret (.bound 0))).openAt 0 y := by
        simpa only [hshift] using
          Interp.models_guard_relevant_shift_openAt_result_alias (e := .ret v) closedX closedV
            supportX freshX freshΔ hres hguard
      have hτScope : τ.freeAtoms ⊆ ρ.domain := by
        have hwf := (Interp.models_wellFormed_iff (Capability.singleton ρ) d Δe τ).1
          (Formula.models_and_elim_left hguard)
        exact Finset.Subset.trans hwf.2.freeAtoms_subset hwf.1
      have hyScope : y ∈ ρ.domain := by
        apply Formula.models_scope hres
        rw [Interp.freeAtoms_resultAt]
        simp [LogicVar.freeAtoms]
      have scopeOpened : ∀ υ : ContextType, υ.freeAtoms ⊆ τ.freeAtoms →
          ((interpFuel gas (d + 1) Δ υ (.ret (.bound 0))).openAt 0 y).freeAtoms ⊆ ρ.domain := by
        intro υ hυ x hx
        rcases Finset.mem_union.1
          (Formula.freeAtoms_openAt_subset _ 0 y hx) with hx | hx
        · have hxy := Finset.mem_singleton.1 hx
          subst x
          exact hyScope
        · apply hτScope
          apply hυ
          have hs := freeAtoms_interpFuel_subset gas (d + 1) Δ υ (.ret (.bound 0)) hx
          simpa [Term.support, Value.support] using hs
      rw [hshift]
      cases τ with
      | inter τ₁ τ₂ =>
          have hshift₁ := τ₁.shiftFrom_eq_of_locallyClosedAt 0 wfτ.1.locallyClosedAt
          have hshift₂ := τ₂.shiftFrom_eq_of_locallyClosedAt 0 wfτ.2.1.locallyClosedAt
          simp only [interpFuel, Formula.openAt]
          apply Formula.models_and_intro htargetGuard
          apply Formula.models_and_intro
          · simpa only [hshift₁] using ih freshΔ wfτ.1 supportV
              (Formula.models_and_elim_left hbody)
          · simpa only [hshift₂] using ih freshΔ wfτ.2.1 supportV
              (Formula.models_and_elim_right hbody)
      | union τ₁ τ₂ =>
          have hshift₁ := τ₁.shiftFrom_eq_of_locallyClosedAt 0 wfτ.1.locallyClosedAt
          have hshift₂ := τ₂.shiftFrom_eq_of_locallyClosedAt 0 wfτ.2.1.locallyClosedAt
          simp only [interpFuel, Formula.openAt]
          apply Formula.models_and_intro htargetGuard
          rcases (Formula.models_or_iff _ _ _ (Formula.models_scope hbody)).1 hbody with h₁ | h₂
          · apply Formula.models_or_intro_left
            · simpa only [hshift₁] using ih freshΔ wfτ.1 supportV h₁
            · exact scopeOpened τ₂ Finset.subset_union_right
          · apply Formula.models_or_intro_right
            · exact scopeOpened τ₁ Finset.subset_union_left
            · simpa only [hshift₂] using ih freshΔ wfτ.2.1 supportV h₂
      | «over» b q =>
          have hQ := Interp.overResultFiber_openAt_fresh b q 0 y hclosed
            (fun hy => freshΔ (wfτ.freeAtoms_subset hy))
          simp only [Formula.openAt] at hQ
          simp only [interpFuel, Formula.openAt]
          apply Formula.models_and_intro htargetGuard
          rw [hQ]
          exact hall _ (by rw [Interp.freeAtoms_overResultFiber]; exact Finset.Subset.refl _) hbody
      | under b q =>
          have hQ := Interp.underResultFiber_openAt_fresh b q 0 y hclosed
            (fun hy => freshΔ (wfτ.freeAtoms_subset hy))
          simp only [Formula.openAt] at hQ
          simp only [interpFuel, Formula.openAt]
          apply Formula.models_and_intro htargetGuard
          rw [hQ]
          exact hall _ (by rw [Interp.freeAtoms_underResultFiber]; exact Finset.Subset.refl _) hbody
      | sum τ₁ τ₂ =>
          have hs₁ : (τ₁.shiftFrom 0).freeAtoms ⊆ (τ₁.sum τ₂).freeAtoms := by
            simpa only [freeAtoms_shiftFrom] using
              (Finset.subset_union_left : τ₁.freeAtoms ⊆ τ₁.freeAtoms ∪ τ₂.freeAtoms)
          have hs₂ : (τ₂.shiftFrom 0).freeAtoms ⊆ (τ₁.sum τ₂).freeAtoms := by
            simpa only [freeAtoms_shiftFrom] using
              (Finset.subset_union_right : τ₂.freeAtoms ⊆ τ₁.freeAtoms ∪ τ₂.freeAtoms)
          have h₁ := hfuel (τ₁.shiftFrom 0) (.ret (.bound 0)) 1 (d + 1) (d + 1 + 1)
            (wfτ.1.locallyClosedAt.shiftFrom 0)
            (by simp [Term.locallyClosedAt, Value.locallyClosedAt]) rfl hs₁ (by omega) (by omega)
          have h₂ := hfuel (τ₂.shiftFrom 0) (.ret (.bound 0)) 1 (d + 1) (d + 1 + 1)
            (wfτ.2.1.locallyClosedAt.shiftFrom 0)
            (by simp [Term.locallyClosedAt, Value.locallyClosedAt]) rfl hs₂ (by omega) (by omega)
          simp only [interpFuel, Formula.openAt]
          apply Formula.models_and_intro htargetGuard
          rw [h₁, h₂]
          apply hall _ ?_ hbody
          simp only [Formula.freeAtoms_sum]
          exact Finset.union_subset (hscopeInner _ _ _ rfl hs₁) (hscopeInner _ _ _ rfl hs₂)
      | arrow τ₁ τ₂ =>
          have hs₁ : ((τ₁.shiftFrom 0).shiftFrom 0).freeAtoms ⊆ (τ₁.arrow τ₂).freeAtoms := by
            simpa only [freeAtoms_shiftFrom] using
              (Finset.subset_union_left : τ₁.freeAtoms ⊆ τ₁.freeAtoms ∪ τ₂.freeAtoms)
          have hs₂ : (τ₂.shiftFrom 1).freeAtoms ⊆ (τ₁.arrow τ₂).freeAtoms := by
            simpa only [freeAtoms_shiftFrom] using
              (Finset.subset_union_right : τ₂.freeAtoms ⊆ τ₁.freeAtoms ∪ τ₂.freeAtoms)
          have h₁ := hfuel ((τ₁.shiftFrom 0).shiftFrom 0) (.ret (.bound 0)) 2 (d + 2) (d + 1 + 2)
            ((wfτ.1.locallyClosedAt.shiftFrom 0).shiftFrom 0)
            (by simp [Term.locallyClosedAt, Value.locallyClosedAt]) rfl hs₁ (by omega) (by omega)
          have h₂ := hfuel (τ₂.shiftFrom 1) (.app (.bound 1) (.bound 0)) 2 (d + 2) (d + 1 + 2)
            (wfτ.2.locallyClosedAt.shiftFrom 1)
            (by simp [Term.locallyClosedAt, Value.locallyClosedAt]) rfl hs₂ (by omega) (by omega)
          simp only [interpFuel, Formula.openAt]
          apply Formula.models_and_intro htargetGuard
          rw [h₁, h₂]
          apply hall _ ?_ hbody
          simp only [Formula.freeAtoms_all, Formula.freeAtoms_impl]
          exact Finset.union_subset (hscopeInner _ _ _ rfl hs₁) (hscopeInner _ _ _ rfl hs₂)
      | wand τ₁ τ₂ =>
          have hs₁ : ((τ₁.shiftFrom 0).shiftFrom 0).freeAtoms ⊆ (τ₁.wand τ₂).freeAtoms := by
            simpa only [freeAtoms_shiftFrom] using
              (Finset.subset_union_left : τ₁.freeAtoms ⊆ τ₁.freeAtoms ∪ τ₂.freeAtoms)
          have hs₂ : (τ₂.shiftFrom 1).freeAtoms ⊆ (τ₁.wand τ₂).freeAtoms := by
            simpa only [freeAtoms_shiftFrom] using
              (Finset.subset_union_right : τ₂.freeAtoms ⊆ τ₁.freeAtoms ∪ τ₂.freeAtoms)
          have h₁ := hfuel ((τ₁.shiftFrom 0).shiftFrom 0) (.ret (.bound 0)) 2 (d + 2) (d + 1 + 2)
            ((wfτ.1.locallyClosedAt.shiftFrom 0).shiftFrom 0)
            (by simp [Term.locallyClosedAt, Value.locallyClosedAt]) rfl hs₁ (by omega) (by omega)
          have h₂ := hfuel (τ₂.shiftFrom 1) (.app (.bound 1) (.bound 0)) 2 (d + 2) (d + 1 + 2)
            (wfτ.2.locallyClosedAt.shiftFrom 1)
            (by simp [Term.locallyClosedAt, Value.locallyClosedAt]) rfl hs₂ (by omega) (by omega)
          simp only [interpFuel, Formula.openAt]
          apply Formula.models_and_intro htargetGuard
          rw [h₁, h₂]
          apply hall _ ?_ hbody
          simp only [Formula.freeAtoms_wand]
          exact Finset.union_subset (hscopeInner _ _ _ rfl hs₁) (hscopeInner _ _ _ rfl hs₂)
      | persist τ =>
          have hs : (τ.shiftFrom 0).freeAtoms ⊆ (ContextType.persist τ).freeAtoms := by
            rw [freeAtoms_shiftFrom]
            exact Finset.Subset.refl _
          have h := hfuel (τ.shiftFrom 0) (.ret (.bound 0)) 1 (d + 1) (d + 1 + 1)
            (wfτ.locallyClosedAt.shiftFrom 0)
            (by simp [Term.locallyClosedAt, Value.locallyClosedAt]) rfl hs (by omega) (by omega)
          simp only [interpFuel, Formula.openAt]
          apply Formula.models_and_intro htargetGuard
          rw [h]
          apply hall _ ?_ hbody
          simp only [Formula.freeAtoms_persist]
          exact hscopeInner _ _ _ rfl hs

/-- Additive input splitting and branch interpretations establish the
result-first sum type, retaining the complete result graph in each branch. -/
theorem models_interp_sum_intro {m m₁ m₂ : Capability} {Δ : BasicEnv}
    {τ₁ τ₂ : ContextType} {e : Term}
    (defined : Capability.SumDefined m₁ m₂) (same : Capability.sum m₁ m₂ defined = m)
    (wfτ : (τ₁.sum τ₂).WellFormed Δ.domain)
    (typed : Δ ⊢ₑ e ⋮ (τ₁.sum τ₂).erase)
    (world : m ⊨ Interp.basicWorld Δ)
    (h₁ : m₁ ⊨ interp Δ τ₁ e) (h₂ : m₂ ⊨ interp Δ τ₂ e) :
    m ⊨ interp Δ (τ₁.sum τ₂) e := by
  let τ := τ₁.sum τ₂
  let A := τ.freeAtoms ∪ e.support
  let Δ' := Interp.relevantEnv Δ τ e
  let gas := max τ₁.measure τ₂.measure
  let Q := interpFuel gas 1 Δ' (τ₁.shiftFrom 0) (.ret (.bound 0)) ⊕
    interpFuel gas 1 Δ' (τ₂.shiftFrom 0) (.ret (.bound 0))
  let P := Interp.resultAt (A.image LogicVar.free) e (.bound 0) ⇒ᶜ Q
  have hAΔ : A ⊆ Δ.domain := Finset.union_subset wfτ.freeAtoms_subset typed.support_subset
  have scope : A ⊆ m.domain := Finset.Subset.trans hAΔ
    ((Interp.models_basicWorld_iff m Δ).1 world).1
  have domain₁ : m₁.domain = m.domain := by
    rw [← same]
    rfl
  have domain₂ : m₂.domain = m.domain := by
    rw [← same]
    exact defined.symm
  have scope₁ : A ⊆ m₁.domain := by rwa [domain₁]
  have scope₂ : A ⊆ m₂.domain := by rwa [domain₂]
  have support₁ : τ₁.freeAtoms ∪ e.support ⊆ A :=
    Finset.union_subset
      (Finset.Subset.trans Finset.subset_union_left Finset.subset_union_left)
      Finset.subset_union_right
  have support₂ : τ₂.freeAtoms ∪ e.support ⊆ A :=
    Finset.union_subset
      (Finset.Subset.trans Finset.subset_union_right Finset.subset_union_left)
      Finset.subset_union_right
  have supportE : e.support ⊆ A := Finset.subset_union_right
  have closedA : LogicVar.LocallyClosed (A.image LogicVar.free) := by
    intro j hj
    simp at hj
  have logicA : e.logicSupport ⊆ A.image LogicVar.free := by
    rw [LogicVar.eq_image_free_of_locallyClosed
      (Interp.termLogicSupport_locallyClosed e typed.locallyClosed),
      Interp.freeAtomSet_term_logicSupport]
    exact Finset.image_subset_image Finset.subset_union_right
  have hQfree : Q.freeAtoms ⊆ τ.freeAtoms := by
    simp only [Q, Formula.freeAtoms_sum]
    apply Finset.union_subset
    · have hs := freeAtoms_interpFuel_subset gas 1 Δ' (τ₁.shiftFrom 0) (.ret (.bound 0))
      simp only [freeAtoms_shiftFrom, Term.support, Value.support, Finset.union_empty] at hs
      exact Finset.Subset.trans hs Finset.subset_union_left
    · have hs := freeAtoms_interpFuel_subset gas 1 Δ' (τ₂.shiftFrom 0) (.ret (.bound 0))
      simp only [freeAtoms_shiftFrom, Term.support, Value.support, Finset.union_empty] at hs
      exact Finset.Subset.trans hs Finset.subset_union_right
  have hPfree : P.freeAtoms = A := by
    simp only [P, Formula.freeAtoms_impl, Interp.freeAtoms_resultAt,
      Formula.LogicVar.freeAtomSet_image_free, LogicVar.freeAtoms, Finset.union_empty]
    rw [Finset.union_eq_left.2 Finset.subset_union_right,
      Finset.union_eq_left.2 (Finset.Subset.trans hQfree Finset.subset_union_left)]
  have resultFirst : Interp.resultFirst Δ' τ e =
      Interp.resultAt (A.image LogicVar.free) e (.bound 0) := by
    have henv : Δ'.domain = A := by
      rw [Interp.relevantEnv_domain]
      change Δ.domain ∩ A = A
      exact Finset.inter_eq_right.2 hAΔ
    have hclosed := Interp.relevantSupport_locallyClosed Δ' τ e
      wfτ.locallyClosedAt typed.locallyClosed
    have hsupport : Interp.relevantSupport Δ' τ e = A.image LogicVar.free := by
      rw [LogicVar.eq_image_free_of_locallyClosed hclosed, Interp.freeAtomSet_relevantSupport,
        Interp.relevantEnv_idem, henv]
    rw [Interp.resultFirst, hsupport,
      LogicVar.image_shiftFrom_eq_of_locallyClosed _ 0 closedA,
      Interp.shiftTerm_eq_of_locallyClosed e typed.locallyClosed]
  have terminates : m ⊨ Interp.total e := by
    rw [← same]
    exact Interp.models_total_sum defined typed.locallyClosed
      (models_interp_total h₁) (models_interp_total h₂)
  unfold interp
  rw [show (τ₁.sum τ₂).measure = gas + 1 by simp [measure, gas, Nat.add_comm]]
  simp only [interpFuel, Nat.zero_add]
  apply Formula.models_and_intro
    (Interp.models_guard_relevant_of_world wfτ typed world terminates)
  change m ⊨ Formula.all (Interp.resultFirst Δ' τ e ⇒ᶜ Q)
  rw [resultFirst]
  apply (Formula.models_all_iff_refines m P).2
  refine ⟨by rw [hPfree]; exact scope, Δ.domain, ?_⟩
  intro y hy _ n href hndom
  have freshA : y ∉ A := fun hm => hy (hAΔ hm)
  have hQopen : (Q.openAt 0 y).freeAtoms ⊆ A ∪ {y} := by
    intro x hx
    rcases Finset.mem_union.1 (Formula.freeAtoms_openAt_subset Q 0 y hx) with hx | hx
    · exact Finset.mem_union_right _ hx
    · exact Finset.mem_union_left _ (Finset.subset_union_left (hQfree hx))
  have hopen : (Interp.resultAt (A.image LogicVar.free) e (.bound 0)).openAt 0 y =
      Interp.resultAt (A.image LogicVar.free) e (.free y) := by
    have hi := Interp.resultAt_shift_openAt (A.image LogicVar.free) e y closedA
      typed.locallyClosed logicA (by simpa using freshA)
    rw [LogicVar.image_shiftFrom_eq_of_locallyClosed _ 0 closedA,
      Interp.shiftTerm_eq_of_locallyClosed e typed.locallyClosed] at hi
    exact hi
  have hRfree : (Interp.resultAt (A.image LogicVar.free) e (.free y)).freeAtoms = A ∪ {y} := by
    simp only [Interp.freeAtoms_resultAt, Formula.LogicVar.freeAtomSet_image_free,
      Finset.union_eq_left.2 supportE, LogicVar.freeAtoms]
  have hn : n.domain = A ∪ {y} := by rwa [hPfree] at hndom
  change n ⊨ ((Interp.resultAt (A.image LogicVar.free) e (.bound 0)).openAt 0 y ⇒ᶜ
    Q.openAt 0 y)
  rw [hopen]
  apply Formula.models_impl_intro
  · simp only [Formula.freeAtoms_impl, hRfree]
    rw [hn]
    exact Finset.union_subset (Finset.Subset.refl _) hQopen
  · intro k hnk hres
    have hnk' : n ⊑ k := by
      simp only [Formula.freeAtoms_impl, hRfree, Finset.union_eq_left.2 hQopen] at hnk
      rwa [← hn, Capability.restrict_domain_self] at hnk
    have hmk : m.restrict A ⊑ k := Capability.refines_trans
      (by rwa [hPfree] at href) hnk'
    have defA : Capability.SumDefined (m₁.restrict A) (m₂.restrict A) := by
      simp only [Capability.SumDefined, Capability.restrict_domain, domain₁, domain₂]
    have sumA : Capability.sum (m₁.restrict A) (m₂.restrict A) defA = m.restrict A := by
      rw [← same, Capability.restrict_sum]
    obtain ⟨sub₁, sub₂, split⟩ := Capability.sum_pullback defA (by rwa [sumA])
    let k₁ := Capability.pullback k (m₁.restrict A) sub₁
    let k₂ := Capability.pullback k (m₂.restrict A) sub₂
    have hsource₁ : k₁ ⊨ interp Δ τ₁ e := by
      apply Formula.models_kripke
        (m := m₁.restrict A) (n := k₁)
        (Capability.restrict_pullback k (m₁.restrict A) sub₁).symm
      exact (models_interp_restrict support₁).1 h₁
    have hsource₂ : k₂ ⊨ interp Δ τ₂ e := by
      apply Formula.models_kripke
        (m := m₂.restrict A) (n := k₂)
        (Capability.restrict_pullback k (m₂.restrict A) sub₂).symm
      exact (models_interp_restrict support₂).1 h₂
    have hres₁ : k₁ ⊨ Interp.resultAt (A.image LogicVar.free) e (.free y) :=
      Interp.models_resultAt_pullback closedA logicA (by simpa using freshA)
        (by simp [Finset.inter_eq_right.2 scope₁]) sub₁ hres
    have hres₂ : k₂ ⊨ Interp.resultAt (A.image LogicVar.free) e (.free y) :=
      Interp.models_resultAt_pullback closedA logicA (by simpa using freshA)
        (by simp [Finset.inter_eq_right.2 scope₂]) sub₂ hres
    have child (υ : ContextType) (wfυ : υ.WellFormed Δ.domain)
        (supportυ : υ.freeAtoms ⊆ τ.freeAtoms) (measureυ : υ.measure ≤ gas)
        (r : Capability) (hsource : r ⊨ interp Δ υ e)
        (result : r ⊨ Interp.resultAt (A.image LogicVar.free) e (.free y)) :
        r ⊨ (interpFuel gas 1 Δ' (υ.shiftFrom 0) (.ret (.bound 0))).openAt 0 y := by
      have h := models_interpFuel_result_alias closedA typed.locallyClosed logicA
        (by simpa using freshA) hy wfυ typed.support_subset
        (Finset.image_subset_image (Finset.Subset.trans supportυ Finset.subset_union_left))
        result hsource
      have heq : interpFuel gas 1 Δ' (υ.shiftFrom 0) (.ret (.bound 0)) =
          interpFuel υ.measure 1 Δ (υ.shiftFrom 0) (.ret (.bound 0)) := by
        rw [interpFuel_eq_of_measure_le gas υ.measure 1 Δ' (υ.shiftFrom 0)
          (.ret (.bound 0)) (by simpa only [measure_shiftFrom] using measureυ)
          (by simpa only [measure_shiftFrom] using Nat.le_refl υ.measure)]
        apply interpFuel_eq_of_agreeOn
        intro x hx
        have hxυ : x ∈ υ.freeAtoms := by
          simpa only [freeAtoms_shiftFrom, Term.support, Value.support, Finset.union_empty] using hx
        have hxA : x ∈ A := Finset.subset_union_left (supportυ hxυ)
        change (Δ.restrict A).lookup x = Δ.lookup x
        rw [BasicEnv.lookup_restrict, if_pos hxA]
      rw [heq]
      exact h
    apply (Formula.models_sum_iff_eq _ _ _).2
    refine ⟨k₁, k₂, rfl, split, ?_, ?_⟩
    · exact child τ₁ wfτ.1 Finset.subset_union_left (Nat.le_max_left _ _) k₁ hsource₁ hres₁
    · exact child τ₂ wfτ.2.1 Finset.subset_union_right (Nat.le_max_right _ _) k₂ hsource₂ hres₂

theorem interp_eq_of_agreeOn {Δ₁ Δ₂ : BasicEnv} {τ : ContextType}
    {e : Term}
    (h : BasicEnv.AgreeOn (τ.freeAtoms ∪ e.support) Δ₁ Δ₂) :
    interp Δ₁ τ e = interp Δ₂ τ e :=
  interpFuel_eq_of_agreeOn τ.measure 0 h

/-- An overapproximate constant refinement fixes the value of a returned
variable in every possible store. -/
theorem models_over_constant_ret_free_lookup
    {m : Capability} {Δ : BasicEnv} {x : Atom} {c : Constant}
    (typed : Δ ⊢ᵥ (.free x) ⋮ (.base c.baseType))
    (h : m ⊨ interp Δ
      (.over c.baseType (Qualifier.equal (.bound 0) (.const c)))
      (.ret (.free x))) :
    ∀ σ, σ ∈ m → σ.lookup x = some (.const c) := by
  let q := Qualifier.equal (.bound 0) (.const c)
  let τ := ContextType.over c.baseType q
  let e := Term.ret (.free x)
  let Δ' := Interp.relevantEnv Δ τ e
  let P := Interp.resultFirst Δ' τ e ⇒ᶜ
    Formula.fiber (q.support \ {.bound 0}) (Interp.overResult c.baseType q)
  have hxΔ : x ∈ Δ.domain := typed.support_subset (by simp [Value.support])
  have hx : Δ.lookup x = some (.base c.baseType) := by
    cases typed with
    | free hx => exact hx
  have hΔ' : Δ'.domain = {x} := by
    simp [Δ', Interp.relevantEnv_domain, Interp.relevantAtoms, τ, q, e,
      ContextType.freeAtoms, Qualifier.equal, Qualifier.freeAtoms,
      Value.logicalSupport, Term.support, Value.support, LogicVar.freeAtoms,
      hxΔ]
  have hrel : Interp.relevantEnv Δ' τ e = Δ' :=
    Interp.relevantEnv_idem Δ τ e
  have hX : Interp.relevantSupport Δ' τ e = {LogicVar.free x} := by
    simp only [Interp.relevantSupport, hrel, hΔ']
    simp [τ, q, e,
      ContextType.support, ContextType.supportAt, Qualifier.equal,
      Value.logicalSupport, LogicVar.supportAtDepth, LogicVar.atDepth,
      Term.logicSupportAt, Value.logicSupportAt]
  have hP : P.freeAtoms = {x} := by
    simp only [P, Formula.freeAtoms_impl, Interp.freeAtoms_resultFirst,
      Interp.freeAtoms_overResultFiber, hrel, hΔ']
    simp [q, e, Qualifier.equal, Qualifier.freeAtoms,
      Value.logicalSupport, Term.support, Value.support, LogicVar.freeAtoms]
  have hall : m ⊨ Formula.all P := Formula.models_and_elim_right h
  obtain ⟨hdom, L, hall⟩ := (Formula.models_all_iff m P).1 hall
  obtain ⟨y, hy⟩ := Finset.exists_nat_subset_range (L ∪ {x})
  have hyfresh : y ∉ L ∪ {x} := by
    intro hmem
    have := hy hmem
    simp at this
  have hyL : y ∉ L := fun hy => hyfresh (Finset.mem_union_left _ hy)
  have hxy : y ≠ x := by simpa using fun hy => hyfresh (Finset.mem_union_right L hy)
  let r := m.restrict P.freeAtoms
  have hrdom : r.domain = {x} := hdom.trans hP
  have hworld : r ⊨ Interp.basicWorld Δ' := by
    have hw := (Formula.models_restrict_iff m (Interp.basicWorld Δ')).1
      (models_interp_basicWorld h)
    simpa [Interp.freeAtoms_basicWorld, hΔ', r, hP] using hw
  have hvalues : ∀ σ, σ ∈ r → ∃ v,
      σ.lookup x = some v ∧ v.locallyClosed := by
    intro σ hσ
    obtain ⟨v, hv, hvT⟩ := (Interp.models_basicWorld_iff r Δ').1 hworld
      |>.2 σ hσ x (.base c.baseType) (by
        simp [Δ', Interp.relevantEnv, Interp.relevantAtoms, τ, q, e,
          ContextType.freeAtoms, Qualifier.equal, Qualifier.freeAtoms,
          Value.logicalSupport, Term.support, Value.support, LogicVar.freeAtoms, hx])
    exact ⟨v, hv, hvT.locallyClosed⟩
  let F := Capability.FiberExtension.ofMap {x} {y}
    (fun σ => Store.singleton y ((σ.lookup x).getD (.const .unit)))
    (by simp [Ne.symm hxy])
    (by
      intro σ _
      simp)
  have hFin : F.input = P.freeAtoms := by simp [F, Capability.FiberExtension.ofMap, hP]
  have hFout : F.output = {y} := rfl
  have happ : F.Applicable r := by
    constructor
    · simp [F, Capability.FiberExtension.ofMap, hrdom]
    · simp [F, Capability.FiberExtension.ofMap, hrdom, hxy]
  obtain ⟨n, hExt⟩ := F.extends_exists r happ
  have hnvalues : ∀ ρ, ρ ∈ n → ∃ v,
      ρ.lookup x = some v ∧ ρ.lookup y = some v ∧ v.locallyClosed := by
    intro ρ hρ
    obtain ⟨σ, w, o, hσ, hw, ho, rfl⟩ := (hExt.mem_iff ρ).1 hρ
    change w = Capability.singleton
      (Store.singleton y (((σ.restrict {x}).lookup x).getD (.const .unit))) at hw
    subst w
    rw [Capability.mem_singleton_iff] at ho
    subst o
    obtain ⟨v, hv, hclosed⟩ := hvalues σ hσ
    have hxσ : x ∈ σ.domain := by
      rw [r.mem_domain hσ, hrdom]
      simp
    have hyσ : y ∉ σ.domain := by
      rw [r.mem_domain hσ, hrdom]
      simpa using hxy
    refine ⟨v, ?_, ?_, hclosed⟩
    · rwa [Store.lookup_merge_left _ _ hxσ]
    · rw [Store.lookup_merge_right _ _ hyσ]
      simp [hv]
  have hres : n ⊨ Interp.resultAt {LogicVar.free x} e (.free y) := by
    apply Interp.models_resultAt_intro
    · intro k hk
      simp at hk
    · simp [e, Term.logicSupportAt, Value.logicSupportAt]
    · simpa using hxy
    · simp [hExt.domain_eq, hrdom, hFout, LogicVar.freeAtomSet, LogicVar.freeAtoms]
    · intro ρ hρ
      obtain ⟨v, hxv, hyv, hclosed⟩ := hnvalues ρ hρ
      refine ⟨v, hyv, ?_⟩
      simpa [e, Interp.instantiateTerm, Interp.instantiateTermAt,
        Interp.instantiateValueAt, Store.toAssignment_lookup_free, hxv] using
        Steps.refl (.ret v) hclosed
    · intro ρ hρ v heval
      obtain ⟨u, hxu, hyu, _⟩ := hnvalues ρ hρ
      have hvu : v = u := by
        have : (Term.ret u).reaches v := by
          simpa [e, Interp.instantiateTerm, Interp.instantiateTermAt,
            Interp.instantiateValueAt, Store.toAssignment_lookup_free, hxu] using heval
        exact Term.ret.inj this.ret_eq
      exact ⟨ρ, hρ, rfl, by simpa [hvu] using hyu⟩
  have hsource := hall y hyL F hFin hFout n hExt
  have hopen : (Interp.resultFirst Δ' τ e).openAt 0 y =
      Interp.resultAt {LogicVar.free x} e (.free y) := by
    rw [Interp.resultFirst_openAt]
    · rw [hX]
    · rw [hX]
      intro k hk
      simp at hk
    · trivial
    · simp [hX, e, Term.logicSupportAt, Value.logicSupportAt]
    · simpa [hX] using hxy
  have hbody : n ⊨ (Interp.overResult c.baseType q).openAt 0 y := by
    change n ⊨ ((Interp.resultFirst Δ' τ e).openAt 0 y ⇒ᶜ
      (Formula.fiber (q.support \ {.bound 0})
        (Interp.overResult c.baseType q)).openAt 0 y) at hsource
    rw [hopen] at hsource
    have hb := Formula.models_impl_elim hsource hres
    simpa [Formula.openAt, q, Qualifier.equal, Value.logicalSupport, LogicVar.openSupport,
      Formula.models_fiber_empty_iff] using hb
  have hnconstant : ∀ ρ, ρ ∈ n → ρ.lookup x = some (.const c) := by
    intro ρ hρ
    obtain ⟨_, a, ha, hlook⟩ :=
      Formula.models_over_and_atom_holdsStore hbody hρ
    have hyc : ρ.lookup y = some (.const c) := by
      have hafree : (q.openAt 0 y).freeAtoms = {y} := by
        simp [q, Qualifier.equal, Qualifier.freeAtoms, LogicVar.openSupport,
          LogicVar.openBinder, LogicVar.swap, Value.logicalSupport, LogicVar.freeAtoms]
      have halook : a.assignment.lookup (.free y) = some (.const c) := by
        simpa [q, Qualifier.openAt, Qualifier.equal, Value.denoteAssignment,
          AssignmentOn.swapBack, Assignment.lookup_swap, LogicVar.swap] using ha
      rw [hlook y, hafree, Store.lookup_restrict, if_pos (by simp)] at halook
      exact halook
    obtain ⟨v, hxv, hyv, _⟩ := hnvalues ρ hρ
    exact hxv.trans (hyv.symm.trans hyc)
  intro σ hσ
  have hσr : σ.restrict {x} ∈ r := by
    change σ.restrict {x} ∈ m.restrict P.freeAtoms
    rw [hP]
    exact ⟨σ, hσ, rfl⟩
  have hσn : σ.restrict {x} ∈ n.restrict r.domain := by
    rw [hExt.restrict_base]
    exact hσr
  obtain ⟨ρ, hρ, hproj⟩ := hσn
  have hlook := congrArg (fun s : Store => s.lookup x) hproj
  change (ρ.restrict r.domain).lookup x = (σ.restrict {x}).lookup x at hlook
  rw [Store.lookup_restrict, if_pos (by simp [hrdom]),
    Store.lookup_restrict, if_pos (by simp)] at hlook
  exact hlook.symm.trans (hnconstant ρ hρ)

/-- A precise constant type fixes its returned variable pointwise. -/
theorem models_constantPrecise_ret_free_lookup
    {m : Capability} {Δ : BasicEnv} {x : Atom} {c : Constant}
    (typed : Δ ⊢ᵥ (.free x) ⋮ (.base c.baseType))
    (h : m ⊨ interp Δ (constantPrecise c) (.ret (.free x))) :
    ∀ σ, σ ∈ m → σ.lookup x = some (.const c) := by
  have hover : m ⊨ interp Δ
      (.over c.baseType (Qualifier.equal (.bound 0) (.const c)))
      (.ret (.free x)) :=
    Formula.models_and_elim_left (Formula.models_and_elim_right h)
  exact models_over_constant_ret_free_lookup typed hover

end ContextType


namespace Formula

theorem supportSetAtDepth_eq (d : Nat) (X : Finset LogicVar) :
    supportSetAtDepth d X = LogicVar.supportAtDepth d X := by
  unfold supportSetAtDepth LogicVar.supportAtDepth
  apply Finset.biUnion_congr rfl
  intro ξ _
  cases ξ with
  | free x => rfl
  | bound k => by_cases h : d ≤ k <;> simp [LogicVar.atDepth, h]

theorem supportAt_eq (P : Formula) (n : Nat) :
    P.supportAt n = LogicVar.supportAtDepth n P.support := by
  induction P generalizing n with
  | top | bot => simp [supportAt, support]
  | atom q =>
      simp [supportAt, support, supportSetAtDepth_eq]
  | and P Q ihP ihQ | or P Q ihP ihQ | impl P Q ihP ihQ
  | star P Q ihP ihQ | sum P Q ihP ihQ =>
      simp only [supportAt, support, LogicVar.supportAtDepth_union]
      rw [ihP n, ihQ n]
  | wand d P Q ihP ihQ =>
      simp only [supportAt, support, Nat.zero_add, LogicVar.supportAtDepth_union]
      rw [ihP (n + d), ihQ (n + d), ihP d, ihQ d,
        LogicVar.supportAtDepth_add, LogicVar.supportAtDepth_add]
  | all P ih =>
      simp only [supportAt, support, Nat.zero_add]
      rw [ih (n + 1), ih 1, LogicVar.supportAtDepth_add]
  | «over» P ih | under P ih | persist P ih => exact ih n
  | fiber X P ih =>
      simp only [supportAt, support, supportSetAtDepth_zero, LogicVar.supportAtDepth_union]
      rw [supportSetAtDepth_eq, ih]

theorem supportAt_fiberAtom (q : Qualifier) (n : Nat) :
    (fiberAtom q).supportAt n = LogicVar.supportAtDepth n q.support := by
  simp [fiberAtom, supportAt, supportSetAtDepth_eq]

end Formula

mutual
  theorem Value.logicSupportAt_eq (v : Value) (n : Nat) :
      v.logicSupportAt n = LogicVar.supportAtDepth n v.logicSupport := by
    cases v with
    | const c => simp [Value.logicSupportAt, Value.logicSupport]
    | free x => simp [Value.logicSupportAt, Value.logicSupport, LogicVar.supportAtDepth, LogicVar.atDepth]
    | bound k =>
        by_cases h : n ≤ k
        simp [Value.logicSupportAt, Value.logicSupport, boundLogicSupportAt,
          LogicVar.supportAtDepth, LogicVar.atDepth, h]
        simp [Value.logicSupportAt, Value.logicSupport, boundLogicSupportAt,
          LogicVar.supportAtDepth, LogicVar.atDepth, h]
    | lam T e =>
        simp only [Value.logicSupportAt, Value.logicSupport, Nat.zero_add]
        rw [Term.logicSupportAt_eq e (n + 1), Term.logicSupportAt_eq e 1,
          LogicVar.supportAtDepth_add]
    | fix T v =>
        simp only [Value.logicSupportAt, Value.logicSupport, Nat.zero_add]
        rw [Value.logicSupportAt_eq v (n + 1), Value.logicSupportAt_eq v 1,
          LogicVar.supportAtDepth_add]

  theorem Term.logicSupportAt_eq (e : Term) (n : Nat) :
      e.logicSupportAt n = LogicVar.supportAtDepth n e.logicSupport := by
    cases e with
    | ret v | primitive _ v => exact Value.logicSupportAt_eq v n
    | app v₁ v₂ =>
        simp only [Term.logicSupportAt, Term.logicSupport, LogicVar.supportAtDepth_union]
        rw [Value.logicSupportAt_eq v₁ n, Value.logicSupportAt_eq v₂ n]
    | letE e₁ e₂ =>
        simp only [Term.logicSupportAt, Term.logicSupport, Nat.zero_add,
          LogicVar.supportAtDepth_union]
        rw [Term.logicSupportAt_eq e₁ n, Term.logicSupportAt_eq e₂ (n + 1),
          Term.logicSupportAt_eq e₂ 1, LogicVar.supportAtDepth_add]
    | matchBool v e₁ e₂ =>
        simp only [Term.logicSupportAt, Term.logicSupport, LogicVar.supportAtDepth_union]
        rw [Value.logicSupportAt_eq v n, Term.logicSupportAt_eq e₁ n, Term.logicSupportAt_eq e₂ n]
end

namespace Interp

theorem supportAt_guard (d n : Nat) (Δ : BasicEnv) (τ : ContextType) (e : Term) :
    (guard d Δ τ e).supportAt n = Δ.domain.image LogicVar.free ∪ e.logicSupportAt n := by
  have hΔ : LogicVar.supportAtDepth n (Δ.domain.image LogicVar.free) =
      Δ.domain.image LogicVar.free := by
    simp [LogicVar.supportAtDepth, Finset.image_biUnion, LogicVar.atDepth,
      Finset.biUnion_singleton]
  simp only [guard, Formula.supportAt, wellFormed, basicWorld, basicTyping, total,
    Formula.supportAt_fiberAtom, wellFormedQualifier, basicWorldQualifier,
    basicTypingQualifier, totalQualifier, LogicVar.supportAtDepth_union, hΔ,
    ← Term.logicSupportAt_eq]
  simp [Finset.union_assoc]

theorem relevantSupport_eq {Δ : BasicEnv} {τ : ContextType} {e : Term}
    (scopeτ : τ.freeAtoms ⊆ Δ.domain) (scopeE : e.support ⊆ Δ.domain) :
    relevantSupport Δ τ e = τ.support ∪ e.logicSupport := by
  ext ξ
  cases ξ with
  | bound k => exact bound_mem_relevantSupport_iff Δ τ e k
  | free x =>
      simp only [free_mem_relevantSupport_iff, Finset.mem_union, ContextType.free_mem_support_iff]
      rw [← LogicVar.mem_freeAtomSet_iff, freeAtomSet_term_logicSupport]
      exact ⟨And.right, fun h => ⟨h.elim (fun hx => scopeτ hx) (fun hx => scopeE hx), h⟩⟩

theorem supportAt_resultFirst {Δ : BasicEnv} {τ : ContextType} {e : Term}
    (scopeτ : τ.freeAtoms ⊆ Δ.domain) (scopeE : e.support ⊆ Δ.domain) (n : Nat) :
    (resultFirst Δ τ e).supportAt (n + 1) = τ.supportAt n ∪ e.logicSupportAt n := by
  simp only [resultFirst, resultAt, Formula.supportAt, Formula.supportSetAtDepth_eq,
    resultQualifier, LogicVar.supportAtDepth_union, shiftTerm_logicSupport,
    LogicVar.supportAtDepth_shiftFrom n 0 _ (Nat.zero_le n),
    relevantSupport_eq scopeτ scopeE, LogicVar.supportAtDepth_union,
    ← ContextType.supportAt_eq, ← Term.logicSupportAt_eq]
  have hb : LogicVar.supportAtDepth (n + 1) ({.bound 0} : Finset LogicVar) = ∅ := by
    simp [LogicVar.supportAtDepth, LogicVar.atDepth]
  rw [hb]
  simp [Finset.union_assoc]

theorem scope_relevantEnv {Δ : BasicEnv} {τ : ContextType} {e : Term}
    (scopeτ : τ.freeAtoms ⊆ Δ.domain) (scopeE : e.support ⊆ Δ.domain) :
    τ.freeAtoms ⊆ (relevantEnv Δ τ e).domain ∧ e.support ⊆ (relevantEnv Δ τ e).domain := by
  rw [relevantEnv_domain]
  exact ⟨Finset.subset_inter scopeτ Finset.subset_union_left,
    Finset.subset_inter scopeE Finset.subset_union_right⟩

theorem supportAt_guard_relevant_subset (d n : Nat) (Δ : BasicEnv) (τ : ContextType) (e : Term) :
    (guard d (relevantEnv Δ τ e) τ e).supportAt n ⊆ τ.supportAt n ∪ e.logicSupportAt n := by
  rw [supportAt_guard]
  apply Finset.union_subset _ Finset.subset_union_right
  rintro ξ hξ
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hξ
  rw [relevantEnv_domain] at hx
  rcases Finset.mem_union.1 (Finset.mem_inter.1 hx).2 with hx | hx
  · exact Finset.mem_union_left _ ((ContextType.free_mem_supportAt_iff τ n x).2 hx)
  · apply Finset.mem_union_right
    rw [Term.logicSupportAt_eq, LogicVar.free_mem_supportAtDepth_iff,
      ← LogicVar.mem_freeAtomSet_iff, freeAtomSet_term_logicSupport]
    exact hx

end Interp

namespace ContextType

open scoped ContextTypes

/-- Interpretation never observes logical inputs outside the type and term. -/
theorem supportAt_interpFuel_subset (gas d : Nat) (Δ : BasicEnv) (τ : ContextType) (e : Term)
    (scopeτ : τ.freeAtoms ⊆ Δ.domain) (scopeE : e.support ⊆ Δ.domain) (n : Nat) :
    (interpFuel gas d Δ τ e).supportAt n ⊆ τ.supportAt n ∪ e.logicSupportAt n := by
  induction gas generalizing d Δ τ e n with
  | zero =>
      simpa only [interpFuel, Formula.supportAt, Finset.union_empty] using
        Interp.supportAt_guard_relevant_subset d n Δ τ e
  | succ gas ih =>
      have hr := Interp.scope_relevantEnv scopeτ scopeE
      have graph := Interp.supportAt_resultFirst hr.1 hr.2 n
      have guard := Interp.supportAt_guard_relevant_subset d n Δ τ e
      have ret (n : Nat) : (Term.ret (.bound 0)).logicSupportAt (n + 1) = ∅ := by
        simp [Term.logicSupportAt, Value.logicSupportAt, boundLogicSupportAt]
      have app (n : Nat) : (Term.app (.bound 1) (.bound 0)).logicSupportAt (n + 2) = ∅ := by
        simp [Term.logicSupportAt, Value.logicSupportAt, boundLogicSupportAt]
      have child (υ : ContextType) (d' n' : Nat) (t : Term)
          (hs : υ.freeAtoms ⊆ (Interp.relevantEnv Δ τ e).domain) (empty : t.support = ∅) :=
        ih d' (Interp.relevantEnv Δ τ e) υ t hs (by rw [empty]; exact Finset.empty_subset _) n'
      cases τ with
      | «over» b q | under b q =>
          simp only [interpFuel, Formula.supportAt]
          apply Finset.union_subset guard
          rw [graph]
          apply Finset.union_subset (Finset.Subset.refl _)
          simp only [Interp.overResult, Interp.underResult, Formula.supportAt,
            Formula.supportSetAtDepth_eq, Interp.resultBasicTyping, Interp.basicTyping,
            Formula.supportAt_fiberAtom, Interp.basicTypingQualifier, BasicEnv.domain_empty,
            Finset.image_empty, Finset.empty_union,
            Term.logicSupportAt, Value.logicSupportAt, boundLogicSupportAt,
            Nat.zero_le, if_true, Nat.sub_zero, LogicVar.supportAtDepth]
          have hb : ¬n + 1 ≤ 0 := by omega
          simp only [Finset.singleton_biUnion, LogicVar.atDepth, if_neg hb, Finset.union_empty]
          apply Finset.union_subset
          · apply Finset.Subset.trans _ Finset.subset_union_left
            change LogicVar.supportAtDepth (n + 1) (q.support \ {.bound 0}) ⊆
              LogicVar.supportAtDepth (n + 1) q.support
            exact Finset.biUnion_subset_biUnion_of_subset_left _ Finset.sdiff_subset
          · exact Finset.subset_union_left
      | inter τ₁ τ₂ | union τ₁ τ₂ =>
          have h₁ := ih d Δ τ₁ e (Finset.Subset.trans Finset.subset_union_left scopeτ) scopeE n
          have h₂ := ih d Δ τ₂ e (Finset.Subset.trans Finset.subset_union_right scopeτ) scopeE n
          simp only [interpFuel, Formula.supportAt]
          apply Finset.union_subset guard
          apply Finset.union_subset
          · exact Finset.Subset.trans h₁ (by simp only [supportAt]; intro ξ hx; grind)
          · exact Finset.Subset.trans h₂ (by simp only [supportAt]; intro ξ hx; grind)
      | sum τ₁ τ₂ =>
          have h₁ := child (τ₁.shiftFrom 0) (d + 1) (n + 1) (.ret (.bound 0))
            (by simpa only [freeAtoms_shiftFrom] using Finset.Subset.trans Finset.subset_union_left hr.1)
            (by simp [Term.support, Value.support])
          have h₂ := child (τ₂.shiftFrom 0) (d + 1) (n + 1) (.ret (.bound 0))
            (by simpa only [freeAtoms_shiftFrom] using Finset.Subset.trans Finset.subset_union_right hr.1)
            (by simp [Term.support, Value.support])
          rw [ret, Finset.union_empty, supportAt_shiftFrom _ n 0 (Nat.zero_le n)] at h₁ h₂
          simp only [interpFuel, Formula.supportAt]
          apply Finset.union_subset guard
          rw [graph]
          apply Finset.union_subset (Finset.Subset.refl _)
          exact Finset.Subset.trans (Finset.union_subset_union h₁ h₂) Finset.subset_union_left
      | arrow τ₁ τ₂ | wand τ₁ τ₂ =>
          have h₁ := child ((τ₁.shiftFrom 0).shiftFrom 0) (d + 2) (n + 2) (.ret (.bound 0))
            (by simpa only [freeAtoms_shiftFrom] using Finset.Subset.trans Finset.subset_union_left hr.1)
            (by simp [Term.support, Value.support])
          have h₂ := child (τ₂.shiftFrom 1) (d + 2) (n + 2) (.app (.bound 1) (.bound 0))
            (by simpa only [freeAtoms_shiftFrom] using Finset.Subset.trans Finset.subset_union_right hr.1)
            (by simp [Term.support, Value.support])
          rw [show n + 2 = (n + 1) + 1 by omega, ret, Finset.union_empty,
            supportAt_shiftFrom _ (n + 1) 0 (by omega), supportAt_shiftFrom _ n 0 (by omega)] at h₁
          rw [app, Finset.union_empty, show n + 2 = (n + 1) + 1 by omega,
            supportAt_shiftFrom _ (n + 1) 1 (by omega)] at h₂
          simp only [interpFuel, Formula.supportAt]
          apply Finset.union_subset guard
          rw [graph]
          apply Finset.union_subset (Finset.Subset.refl _)
          exact Finset.Subset.trans (Finset.union_subset_union h₁ h₂) Finset.subset_union_left
      | persist τ =>
          have h := child (τ.shiftFrom 0) (d + 1) (n + 1) (.ret (.bound 0))
            (by simpa only [freeAtoms_shiftFrom] using hr.1) (by simp [Term.support, Value.support])
          rw [ret, Finset.union_empty, supportAt_shiftFrom _ n 0 (Nat.zero_le n)] at h
          simp only [interpFuel, Formula.supportAt]
          apply Finset.union_subset guard
          rw [graph]
          exact Finset.union_subset (Finset.Subset.refl _) (Finset.Subset.trans h Finset.subset_union_left)

/-- With enough fuel, every external input of the type and term is observed.
This exact support is needed when transporting persistence and magic wand. -/
theorem supportAt_interpFuel (gas d : Nat) (Δ : BasicEnv) (τ : ContextType) (e : Term)
    (lower : τ.measure ≤ gas) (scopeτ : τ.freeAtoms ⊆ Δ.domain)
    (scopeE : e.support ⊆ Δ.domain) (n : Nat) :
    (interpFuel gas d Δ τ e).supportAt n = τ.supportAt n ∪ e.logicSupportAt n := by
  apply Finset.Subset.antisymm (supportAt_interpFuel_subset gas d Δ τ e scopeτ scopeE n)
  induction gas generalizing d Δ τ e n with
  | zero =>
      have := τ.measure_pos
      omega
  | succ gas ih =>
      have hr := Interp.scope_relevantEnv scopeτ scopeE
      have graph := Interp.supportAt_resultFirst hr.1 hr.2 n
      cases τ with
      | «over» b q | under b q | sum τ₁ τ₂ | arrow τ₁ τ₂ | wand τ₁ τ₂ | persist τ =>
          simp only [interpFuel, Formula.supportAt]
          rw [graph]
          exact Finset.Subset.trans Finset.subset_union_left Finset.subset_union_right
      | inter τ₁ τ₂ | union τ₁ τ₂ =>
          have lower₁ : τ₁.measure ≤ gas := by simp only [measure] at lower; omega
          have lower₂ : τ₂.measure ≤ gas := by simp only [measure] at lower; omega
          have h₁ := ih d Δ τ₁ e lower₁ (Finset.Subset.trans Finset.subset_union_left scopeτ) scopeE n
          have h₂ := ih d Δ τ₂ e lower₂ (Finset.Subset.trans Finset.subset_union_right scopeτ) scopeE n
          simp only [interpFuel, Formula.supportAt, supportAt]
          intro ξ hx
          apply Finset.mem_union_right
          rcases Finset.mem_union.1 hx with hx | hx
          · rcases Finset.mem_union.1 hx with hx | hx
            · exact Finset.mem_union_left _ (h₁ (Finset.mem_union_left _ hx))
            · exact Finset.mem_union_right _ (h₂ (Finset.mem_union_left _ hx))
          · exact Finset.mem_union_left _ (h₁ (Finset.mem_union_right _ hx))

theorem support_interpFuel (gas d : Nat) (Δ : BasicEnv) (τ : ContextType) (e : Term)
    (lower : τ.measure ≤ gas) (scopeτ : τ.freeAtoms ⊆ Δ.domain)
    (scopeE : e.support ⊆ Δ.domain) :
    (interpFuel gas d Δ τ e).support = τ.support ∪ e.logicSupport :=
  supportAt_interpFuel gas d Δ τ e lower scopeτ scopeE 0

end ContextType

/-- Finite opening preserves the exact observed support, independently of
the two static guard depths. -/
theorem ContextType.support_interpFuel_openManyAt_eq
    {gas n n' k d : Nat} {Δ Δ' : BasicEnv} {τ : ContextType} {e : Term}
    {η : Fin d → Atom}
    (lower : τ.measure ≤ gas) (lower' : (τ.openManyAt k d η).measure ≤ gas)
    (scopeτ : τ.freeAtoms ⊆ Δ.domain)
    (scopeE : e.support ⊆ Δ.domain)
    (scopeτ' : (τ.openManyAt k d η).freeAtoms ⊆ Δ'.domain)
    (scopeE' : (e.openManyAt k d η).support ⊆ Δ'.domain)
    (inj : Function.Injective η) (freshE : ∀ i, η i ∉ e.support) :
    ((ContextType.interpFuel gas n Δ τ e).openManyAt k d η).support =
      (ContextType.interpFuel gas n' Δ' (τ.openManyAt k d η) (e.openManyAt k d η)).support := by
  have hs := Formula.supportAt_openManyAt (ContextType.interpFuel gas n Δ τ e) 0 k d η
  have hτ := ContextType.supportAt_openManyAt τ 0 k d η
  have he := Term.logicSupportAt_openManyAt e 0 k d η inj freshE
  simp only [Nat.add_zero] at hs hτ he
  change ((ContextType.interpFuel gas n Δ τ e).openManyAt k d η).support =
    (ContextType.interpFuel gas n Δ τ e).support.image (LogicVar.openManyAt k d η) at hs
  change (τ.openManyAt k d η).support = τ.support.image (LogicVar.openManyAt k d η) at hτ
  change (e.openManyAt k d η).logicSupport = e.logicSupport.image (LogicVar.openManyAt k d η) at he
  rw [ContextType.support_interpFuel gas n' Δ' _ _ lower' scopeτ' scopeE']
  change _ = (τ.openManyAt k d η).support ∪ (e.openManyAt k d η).logicSupport
  rw [hτ, he]
  rw [hs, ContextType.support_interpFuel gas n Δ τ e lower scopeτ scopeE, Finset.image_union]



namespace ContextType

@[simp] theorem measure_openAt (τ : ContextType) (k : Nat) (y : Atom) :
    (τ.openAt k y).measure = τ.measure := by
  induction τ generalizing k <;> simp_all [ContextType.openAt, measure]

@[simp] theorem measure_openManyAt (τ : ContextType) (k d : Nat) (η : Fin d → Atom) :
    (τ.openManyAt k d η).measure = τ.measure := by
  induction d with
  | zero => rfl
  | succ d ih => rw [ContextType.openManyAt, measure_openAt, ih]

end ContextType

end ContextTypes
