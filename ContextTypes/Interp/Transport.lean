import ContextTypes.Interp.Type

set_option autoImplicit false

/-!
# Finite-input interpretation conversion

Opening external input binders agrees with interpreting their fresh names.
The conversion retains complete nondeterministic result graphs and the observed
projections used by sum, separating functions, and persistence.
-/

namespace ContextTypes.Interp

/-- An opened dependent child may retain more inner binders than its parent,
while observing the same named ambient inputs after finite opening. -/
theorem relevantEnv_openManyAt_agreeOn_at {Δ : BasicEnv} {τ υ : ContextType} {e : Term}
    {k d : Nat} {η : Fin d → Atom} {T : Fin d → SimpleType}
    (inj : Function.Injective η) (source : υ.freeAtoms ⊆ τ.freeAtoms)
    (target : (υ.openManyAt k d η).freeAtoms ⊆ (τ.openManyAt 0 d η).freeAtoms) :
    BasicEnv.AgreeOn (υ.openManyAt k d η).freeAtoms
      ((relevantEnv Δ τ e).insertMany d η T)
      (relevantEnv (Δ.insertMany d η T) (τ.openManyAt 0 d η) (e.openManyAt 0 d η)) := by
  have agree : BasicEnv.AgreeOn (relevantAtoms τ e) (relevantEnv Δ τ e) Δ := by
    intro x hx
    simp only [relevantEnv, BasicEnv.lookup_restrict, if_pos hx]
  have inputs := agree.insertMany d η T inj
  intro x hx
  rw [inputs x (Finset.Subset.trans (υ.freeAtoms_openManyAt_subset k d η)
    (Finset.union_subset_union (Finset.Subset.trans source Finset.subset_union_left)
      (Finset.Subset.refl _)) hx)]
  simp only [relevantEnv, BasicEnv.lookup_restrict,
    if_pos (Finset.mem_union_left _ (target hx)), relevantAtoms]

end ContextTypes.Interp

namespace ContextTypes.ContextType

open scoped ContextTypes

/-- Opening an external family preserves an interpretation with no binders
or free names at those positions. -/
theorem interpFuel_openManyAt_fresh (gas n : Nat) (Δ : BasicEnv) (τ : ContextType) (e : Term)
    (k d : Nat) (η : Fin d → Atom) (closedτ : τ.LocallyClosedAt k)
    (closedE : e.locallyClosedAt k) (freshΔ : ∀ i, η i ∉ Δ.domain)
    (freshτ : ∀ i, η i ∉ τ.freeAtoms) (freshE : ∀ i, η i ∉ e.support) :
    (interpFuel gas n Δ τ e).openManyAt k d η = interpFuel gas n Δ τ e := by
  induction d with
  | zero => rfl
  | succ d ih =>
      rw [Formula.openManyAt, ih _ (fun i => freshΔ i.castSucc)
        (fun i => freshτ i.castSucc) (fun i => freshE i.castSucc)]
      exact interpFuel_openAt_fresh gas n Δ τ e (k + d) _
        (closedτ.mono (by omega)) (Term.locallyClosedAt_mono e closedE (by omega))
        (freshΔ (Fin.last d)) (freshτ (Fin.last d)) (freshE (Fin.last d))

/-- Induction predicate for complete finite-input interpretation conversion.
Fuel must cover the type: truncated children can omit type-only observations,
which would change what a surrounding persistent modality observes. -/
private def OpensInputs (gas : Nat) (τ : ContextType) : Prop :=
  τ.measure ≤ gas →
  ∀ (m : Capability) (Δ : BasicEnv) (e : Term) (d : Nat)
    (η : Fin d → Atom) (T : Fin d → SimpleType),
    τ.WellFormedAt d Δ.domain → Function.Injective η →
    (∀ i, η i ∉ Δ.domain) → e.support ⊆ Δ.domain →
    (Δ.insertMany d η T ⊢ₑ e.openManyAt 0 d η ⋮ τ.erase) →
    (m ⊨ Interp.basicWorld (Δ.insertMany d η T)) →
    (m ⊨ (interpFuel gas d Δ τ e).openManyAt 0 d η ↔
      m ⊨ interpFuel gas 0 (Δ.insertMany d η T) (τ.openManyAt 0 d η) (e.openManyAt 0 d η))

/-- The shifted result child normalizes after its result and external inputs
are named together. The target retains the symbolic result until the last step. -/
private theorem OpensInputs.resultChild {gas d : Nat} {υ : ContextType}
    (ih : OpensInputs gas (υ.shiftFrom 0)) (lower : υ.measure ≤ gas)
    {m : Capability} {Δ : BasicEnv} {η : Fin d → Atom} {T : Fin d → SimpleType}
    {z : Atom} (wf : υ.WellFormedAt d Δ.domain) (inj : Function.Injective η)
    (fresh : ∀ i, η i ∉ Δ.domain) (freshZ : z ∉ (Δ.insertMany d η T).domain)
    (world : m ⊨ Interp.basicWorld ((Δ.insertMany d η T).insert z υ.erase)) :
    m ⊨ ((interpFuel gas (d + 1) Δ (υ.shiftFrom 0) (.ret (.bound 0))).openManyAt 1 d η).openAt 0 z ↔
    m ⊨ (interpFuel gas 1 (Δ.insertMany d η T)
      ((υ.openManyAt 0 d η).shiftFrom 0) (.ret (.bound 0))).openAt 0 z := by
  have apart : ∀ i, z ≠ η i := by
    intro i hi
    apply freshZ
    rw [BasicEnv.domain_insertMany]
    exact Finset.mem_union_right _ (Finset.mem_image.2 ⟨i, Finset.mem_univ _, hi.symm⟩)
  have freshΔ : z ∉ Δ.domain := by
    intro hz
    exact freshZ (by rw [BasicEnv.domain_insertMany]; exact Finset.mem_union_left _ hz)
  have inj' : Function.Injective (Fin.cons z η) :=
    Fin.cons_injective_of_injective (by rintro ⟨i, hi⟩; exact apart i hi.symm) inj
  have fresh' : ∀ i, Fin.cons (α := fun _ => Atom) z η i ∉ Δ.domain := by
    intro i
    cases i using Fin.cases
    · simpa using freshΔ
    · simpa using fresh _
  have env : Δ.insertMany (d + 1) (Fin.cons z η) (Fin.cons υ.erase T) =
      (Δ.insertMany d η T).insert z υ.erase := by
    rw [BasicEnv.insertMany_cons, BasicEnv.insertMany_insert_comm _ _ _ _ _ _ apart]
  have term : (Term.ret (.bound 0)).openManyAt 0 (d + 1) (Fin.cons z η) = .ret (.free z) := by
    rw [Term.openManyAt_cons]
    simp [Term.openAt, Value.openAt, Term.openManyAt_ret, Value.openManyAt_free]
  have typed : Δ.insertMany (d + 1) (Fin.cons z η) (Fin.cons υ.erase T) ⊢ₑ
      (Term.ret (.bound 0)).openManyAt 0 (d + 1) (Fin.cons z η) ⋮ (υ.shiftFrom 0).erase := by
    rw [env, term, erase_shiftFrom]
    exact BasicTermTyp.ret (BasicValTyp.free (BasicEnv.lookup_insert _ _ _))
  have wf' : υ.WellFormedAt (0 + d) Δ.domain := by simpa only [Nat.zero_add] using wf
  have wfOpen : (υ.openManyAt 0 d η).WellFormed (Δ.insertMany d η T).domain := by
    simpa only [BasicEnv.domain_insertMany] using wf'.openManyAt η inj fresh
  have same := shift_openManyAt_cons_eq wf inj fresh
    (by simpa only [BasicEnv.domain_insertMany] using freshZ)
  rw [Formula.openManyAt_openAt_comm _ 1 d η 0 z
    (fun i => by omega) (fun i => Ne.symm (apart i)), ← Formula.openManyAt_cons]
  have h := ih (by simpa only [measure_shiftFrom] using lower) m Δ (.ret (.bound 0))
    (d + 1) (Fin.cons z η) (Fin.cons υ.erase T) (wf.shiftFrom 0) inj' fresh'
    (by simp [Term.support, Value.support]) typed (by rwa [env])
  rw [env, term, same] at h
  rw [h, shiftFrom_eq_of_locallyClosedAt _ 0 wfOpen.locallyClosedAt]
  simpa only [erase_openManyAt] using
    (models_interpFuel_ret_bound_openAt_iff (gas := gas) (d := 1) (m := m) wfOpen freshZ).symm

/-- A dependent application child opens all old inputs, its function result,
and its argument to the same named interpretation. -/
private theorem OpensInputs.applicationChild {gas d : Nat} {τ : ContextType}
    (ih : ∀ υ, OpensInputs gas υ) (lower : τ.measure ≤ gas)
    {m : Capability} {Δ : BasicEnv} {η : Fin d → Atom} {T : Fin d → SimpleType}
    {U : SimpleType} {y z : Atom} (wf : τ.WellFormedAt (1 + d) Δ.domain)
    (inj : Function.Injective η) (fresh : ∀ i, η i ∉ Δ.domain)
    (freshZ : z ∉ (Δ.insertMany d η T).domain)
    (freshY : y ∉ (Δ.insertMany d η T).domain ∪ {z})
    (world : m ⊨ Interp.basicWorld (((Δ.insertMany d η T).insert z (.arrow U τ.erase)).insert y U)) :
    m ⊨ (((interpFuel gas (d + 2) Δ (τ.shiftFrom 1) (.app (.bound 1) (.bound 0))).openManyAt 2 d η).openAt 1 z).openAt 0 y ↔
    m ⊨ ((interpFuel gas 2 (Δ.insertMany d η T) ((τ.openManyAt 1 d η).shiftFrom 1)
      (.app (.bound 1) (.bound 0))).openAt 1 z).openAt 0 y := by
  have apart : y ≠ z := fun hi => freshY (Finset.mem_union_right _ (by simpa using hi))
  have apartZ : ∀ i, z ≠ η i := by
    intro i hi
    exact freshZ (by
      rw [BasicEnv.domain_insertMany]
      exact Finset.mem_union_right _ (Finset.mem_image.2 ⟨i, Finset.mem_univ _, hi.symm⟩))
  have apartY : ∀ i, y ≠ η i := by
    intro i hi
    apply freshY
    apply Finset.mem_union_left
    rw [BasicEnv.domain_insertMany]
    exact Finset.mem_union_right _ (Finset.mem_image.2 ⟨i, Finset.mem_univ _, hi.symm⟩)
  have freshZΔ : z ∉ Δ.domain := fun hz => freshZ (by
    rw [BasicEnv.domain_insertMany]
    exact Finset.mem_union_left _ hz)
  have freshYΔ : y ∉ Δ.domain := fun hy => freshY (Finset.mem_union_left _ (by
    rw [BasicEnv.domain_insertMany]
    exact Finset.mem_union_left _ hy))
  have injZ : Function.Injective (Fin.cons z η) :=
    Fin.cons_injective_of_injective (by rintro ⟨i, hi⟩; exact apartZ i hi.symm) inj
  have injYZ : Function.Injective (Fin.cons y (Fin.cons z η)) :=
    Fin.cons_injective_of_injective (by
      rintro ⟨i, hi⟩
      cases i using Fin.cases
      · exact apart hi.symm
      · exact apartY _ hi.symm) injZ
  have freshYZ : ∀ i, Fin.cons (α := fun _ => Atom) y (Fin.cons z η) i ∉ Δ.domain := by
    intro i
    cases i using Fin.cases
    · exact freshYΔ
    · rename_i i
      cases i using Fin.cases
      · exact freshZΔ
      · exact fresh _
  have env := BasicEnv.insertMany_two Δ d η T y z U (.arrow U τ.erase) apart apartY apartZ
  have typeEq := shift_openManyAt_two_eq (Δ := Δ) wf inj fresh
    (by simpa only [BasicEnv.domain_insertMany] using freshZ) apart apartY
  have typed : Δ.insertMany (d + 2) (Fin.cons y (Fin.cons z η))
      (Fin.cons U (Fin.cons (.arrow U τ.erase) T)) ⊢ₑ
      (Term.app (.bound 1) (.bound 0)).openManyAt 0 (d + 2) (Fin.cons y (Fin.cons z η)) ⋮
        (τ.shiftFrom 1).erase := by
    rw [env, Term.openManyAt_two_app, erase_shiftFrom]
    apply BasicTermTyp.app
    · exact BasicValTyp.free (by rw [BasicEnv.lookup_insert_of_ne _ _ apart.symm,
        BasicEnv.lookup_insert])
    · exact BasicValTyp.free (BasicEnv.lookup_insert _ _ _)
  have wfShift : (τ.shiftFrom 1).WellFormedAt (d + 2) Δ.domain := by
    simpa only [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using wf.shiftFrom 1
  have raw := ih (τ.shiftFrom 1) (by simpa only [measure_shiftFrom] using lower)
    m Δ (.app (.bound 1) (.bound 0)) (d + 2) (Fin.cons y (Fin.cons z η))
    (Fin.cons U (Fin.cons (.arrow U τ.erase) T)) wfShift injYZ freshYZ
    (by simp [Term.support, Value.support]) typed (by rwa [env])
  rw [env, Term.openManyAt_two_app, typeEq] at raw
  have wfOpen : (τ.openManyAt 1 d η).WellFormedAt 1 (Δ.insertMany d η T).domain := by
    simpa only [BasicEnv.domain_insertMany] using wf.openManyAt η inj fresh
  have injNamed : Function.Injective (Fin.cons y (Fin.cons z Fin.elim0)) := by
    intro i j hi
    fin_cases i <;> fin_cases j <;> simp_all
  have freshNamed : ∀ i, Fin.cons (α := fun _ => Atom) y (Fin.cons z Fin.elim0) i ∉
      (Δ.insertMany d η T).domain := by
    intro i
    fin_cases i
    · exact fun hy => freshY (Finset.mem_union_left _ hy)
    · exact freshZ
  have envNamed : (Δ.insertMany d η T).insertMany 2 (Fin.cons y (Fin.cons z Fin.elim0))
      (Fin.cons U (Fin.cons (.arrow U τ.erase) Fin.elim0)) =
      ((Δ.insertMany d η T).insert z (.arrow U τ.erase)).insert y U := by
    simpa only [BasicEnv.insertMany] using BasicEnv.insertMany_two (Δ.insertMany d η T)
      0 Fin.elim0 Fin.elim0 y z U (.arrow U τ.erase) apart
      (fun i => Fin.elim0 i) (fun i => Fin.elim0 i)
  have typedNamed : (Δ.insertMany d η T).insertMany 2 (Fin.cons y (Fin.cons z Fin.elim0))
      (Fin.cons U (Fin.cons (.arrow U τ.erase) Fin.elim0)) ⊢ₑ
      (Term.app (.bound 1) (.bound 0)).openManyAt 0 2 (Fin.cons y (Fin.cons z Fin.elim0)) ⋮
        ((τ.openManyAt 1 d η).shiftFrom 1).erase := by
    rw [envNamed, Term.openManyAt_two_app 0, erase_shiftFrom, erase_openManyAt]
    apply BasicTermTyp.app
    · exact BasicValTyp.free (by rw [BasicEnv.lookup_insert_of_ne _ _ apart.symm,
        BasicEnv.lookup_insert])
    · exact BasicValTyp.free (BasicEnv.lookup_insert _ _ _)
  have named := ih ((τ.openManyAt 1 d η).shiftFrom 1)
    (by simpa only [measure_shiftFrom, measure_openManyAt] using lower)
    m (Δ.insertMany d η T) (.app (.bound 1) (.bound 0)) 2
    (Fin.cons y (Fin.cons z Fin.elim0)) (Fin.cons U (Fin.cons (.arrow U τ.erase) Fin.elim0))
    (wfOpen.shiftFrom 1) injNamed freshNamed (by simp [Term.support, Value.support])
    typedNamed (by rwa [envNamed])
  have typeNamed := shift_openManyAt_two_eq (d := 0) (η := Fin.elim0)
    (Δ := Δ.insertMany d η T) (by simpa only [Nat.add_zero] using wfOpen)
    (by intro i; exact Fin.elim0 i) (by intro i; exact Fin.elim0 i)
    (by simpa using freshZ) apart (fun i => Fin.elim0 i)
  change ((τ.openManyAt 1 d η).shiftFrom 1).openManyAt 0 2
    (Fin.cons y (Fin.cons z Fin.elim0)) = (τ.openManyAt 1 d η).openAt 0 y at typeNamed
  rw [envNamed, Term.openManyAt_two_app 0, typeNamed] at named
  rw [Formula.openManyAt_two _ d η y z apart (fun i => Ne.symm (apartY i))
    (fun i => Ne.symm (apartZ i))]
  have opening := Formula.openManyAt_two
    (interpFuel gas 2 (Δ.insertMany d η T) ((τ.openManyAt 1 d η).shiftFrom 1)
      (.app (.bound 1) (.bound 0))) 0 Fin.elim0 y z apart
        (fun i => Fin.elim0 i) (fun i => Fin.elim0 i)
  rw [show (interpFuel gas 2 (Δ.insertMany d η T) ((τ.openManyAt 1 d η).shiftFrom 1)
    (.app (.bound 1) (.bound 0))).openManyAt 2 0 Fin.elim0 =
      interpFuel gas 2 (Δ.insertMany d η T) ((τ.openManyAt 1 d η).shiftFrom 1)
        (.app (.bound 1) (.bound 0)) from rfl] at opening
  rw [opening, raw, named]

/-- A returned argument opens its two inserted binders and external inputs
without introducing observations of the function result's erased type. -/
private theorem OpensInputs.argumentChild {gas d : Nat} {τ : ContextType}
    (ih : ∀ υ, OpensInputs gas υ) (lower : τ.measure ≤ gas)
    {m : Capability} {Δ : BasicEnv} {η : Fin d → Atom} {T : Fin d → SimpleType}
    {V : SimpleType} {y z : Atom} (wf : τ.WellFormedAt d Δ.domain)
    (inj : Function.Injective η) (fresh : ∀ i, η i ∉ Δ.domain)
    (freshZ : z ∉ (Δ.insertMany d η T).domain)
    (freshY : y ∉ (Δ.insertMany d η T).domain ∪ {z})
    (world : m ⊨ Interp.basicWorld (((Δ.insertMany d η T).insert z V).insert y τ.erase)) :
    m ⊨ (((interpFuel gas (d + 2) Δ ((τ.shiftFrom 0).shiftFrom 0) (.ret (.bound 0))).openManyAt 2 d η).openAt 1 z).openAt 0 y ↔
    m ⊨ ((interpFuel gas 2 (Δ.insertMany d η T) (((τ.openManyAt 0 d η).shiftFrom 0).shiftFrom 0)
      (.ret (.bound 0))).openAt 1 z).openAt 0 y := by
  have apart : y ≠ z := fun hi => freshY (Finset.mem_union_right _ (by simpa using hi))
  have apartZ : ∀ i, z ≠ η i := by
    intro i hi
    exact freshZ (by
      rw [BasicEnv.domain_insertMany]
      exact Finset.mem_union_right _ (Finset.mem_image.2 ⟨i, Finset.mem_univ _, hi.symm⟩))
  have apartY : ∀ i, y ≠ η i := by
    intro i hi
    apply freshY
    apply Finset.mem_union_left
    rw [BasicEnv.domain_insertMany]
    exact Finset.mem_union_right _ (Finset.mem_image.2 ⟨i, Finset.mem_univ _, hi.symm⟩)
  have freshZΔ : z ∉ Δ.domain := fun hz => freshZ (by
    rw [BasicEnv.domain_insertMany]
    exact Finset.mem_union_left _ hz)
  have freshYΔ : y ∉ Δ.domain := fun hy => freshY (Finset.mem_union_left _ (by
    rw [BasicEnv.domain_insertMany]
    exact Finset.mem_union_left _ hy))
  have injZ : Function.Injective (Fin.cons z η) :=
    Fin.cons_injective_of_injective (by rintro ⟨i, hi⟩; exact apartZ i hi.symm) inj
  have injYZ : Function.Injective (Fin.cons y (Fin.cons z η)) :=
    Fin.cons_injective_of_injective (by
      rintro ⟨i, hi⟩
      cases i using Fin.cases
      · exact apart hi.symm
      · exact apartY _ hi.symm) injZ
  have freshYZ : ∀ i, Fin.cons (α := fun _ => Atom) y (Fin.cons z η) i ∉ Δ.domain := by
    intro i
    cases i using Fin.cases
    · exact freshYΔ
    · rename_i i
      cases i using Fin.cases
      · exact freshZΔ
      · exact fresh _
  have env := BasicEnv.insertMany_two Δ d η T y z τ.erase V apart apartY apartZ
  have typeEq := shift_twice_openManyAt_two_eq (Δ := Δ) wf inj fresh
    (by simpa only [BasicEnv.domain_insertMany] using freshZ)
    (by simpa only [BasicEnv.domain_insertMany] using freshY)
  have typed : Δ.insertMany (d + 2) (Fin.cons y (Fin.cons z η))
      (Fin.cons τ.erase (Fin.cons V T)) ⊢ₑ
      (Term.ret (.bound 0)).openManyAt 0 (d + 2) (Fin.cons y (Fin.cons z η)) ⋮
        ((τ.shiftFrom 0).shiftFrom 0).erase := by
    rw [env, Term.openManyAt_two_ret]
    simp only [erase_shiftFrom]
    exact BasicTermTyp.ret (BasicValTyp.free (BasicEnv.lookup_insert _ _ _))
  have wfShift : ((τ.shiftFrom 0).shiftFrom 0).WellFormedAt (d + 2) Δ.domain := by
    simpa only [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using (wf.shiftFrom 0).shiftFrom 0
  have raw := ih ((τ.shiftFrom 0).shiftFrom 0) (by simpa only [measure_shiftFrom] using lower)
    m Δ (.ret (.bound 0)) (d + 2) (Fin.cons y (Fin.cons z η))
    (Fin.cons τ.erase (Fin.cons V T)) wfShift injYZ freshYZ
    (by simp [Term.support, Value.support]) typed (by rwa [env])
  rw [env, Term.openManyAt_two_ret, typeEq] at raw
  have wf' : τ.WellFormedAt (0 + d) Δ.domain := by simpa only [Nat.zero_add] using wf
  have wfOpen : (τ.openManyAt 0 d η).WellFormed (Δ.insertMany d η T).domain := by
    simpa only [BasicEnv.domain_insertMany] using wf'.openManyAt η inj fresh
  have injNamed : Function.Injective (Fin.cons y (Fin.cons z Fin.elim0)) := by
    intro i j hi
    fin_cases i <;> fin_cases j <;> simp_all
  have freshNamed : ∀ i, Fin.cons (α := fun _ => Atom) y (Fin.cons z Fin.elim0) i ∉
      (Δ.insertMany d η T).domain := by
    intro i
    fin_cases i
    · exact fun hy => freshY (Finset.mem_union_left _ hy)
    · exact freshZ
  have envNamed : (Δ.insertMany d η T).insertMany 2 (Fin.cons y (Fin.cons z Fin.elim0))
      (Fin.cons τ.erase (Fin.cons V Fin.elim0)) =
      ((Δ.insertMany d η T).insert z V).insert y τ.erase := by
    simpa only [BasicEnv.insertMany] using BasicEnv.insertMany_two (Δ.insertMany d η T)
      0 Fin.elim0 Fin.elim0 y z τ.erase V apart
      (fun i => Fin.elim0 i) (fun i => Fin.elim0 i)
  have typedNamed : (Δ.insertMany d η T).insertMany 2 (Fin.cons y (Fin.cons z Fin.elim0))
      (Fin.cons τ.erase (Fin.cons V Fin.elim0)) ⊢ₑ
      (Term.ret (.bound 0)).openManyAt 0 2 (Fin.cons y (Fin.cons z Fin.elim0)) ⋮
        (((τ.openManyAt 0 d η).shiftFrom 0).shiftFrom 0).erase := by
    rw [envNamed, Term.openManyAt_two_ret 0]
    simp only [erase_shiftFrom, erase_openManyAt]
    exact BasicTermTyp.ret (BasicValTyp.free (BasicEnv.lookup_insert _ _ _))
  have named := ih (((τ.openManyAt 0 d η).shiftFrom 0).shiftFrom 0)
    (by simpa only [measure_shiftFrom, measure_openManyAt] using lower)
    m (Δ.insertMany d η T) (.ret (.bound 0)) 2
    (Fin.cons y (Fin.cons z Fin.elim0)) (Fin.cons τ.erase (Fin.cons V Fin.elim0))
    ((wfOpen.shiftFrom 0).shiftFrom 0) injNamed freshNamed (by simp [Term.support, Value.support])
    typedNamed (by rwa [envNamed])
  have typeNamed := shift_twice_openManyAt_two_eq (d := 0) (η := Fin.elim0)
    (Δ := Δ.insertMany d η T) wfOpen
    (by intro i; exact Fin.elim0 i) (by intro i; exact Fin.elim0 i)
    (by simpa using freshZ) (by simpa using freshY)
  change (((τ.openManyAt 0 d η).shiftFrom 0).shiftFrom 0).openManyAt 0 2
    (Fin.cons y (Fin.cons z Fin.elim0)) = τ.openManyAt 0 d η at typeNamed
  rw [envNamed, Term.openManyAt_two_ret 0, typeNamed] at named
  rw [Formula.openManyAt_two _ d η y z apart (fun i => Ne.symm (apartY i))
    (fun i => Ne.symm (apartZ i))]
  have opening := Formula.openManyAt_two
    (interpFuel gas 2 (Δ.insertMany d η T) (((τ.openManyAt 0 d η).shiftFrom 0).shiftFrom 0)
      (.ret (.bound 0))) 0 Fin.elim0 y z apart
        (fun i => Fin.elim0 i) (fun i => Fin.elim0 i)
  rw [show (interpFuel gas 2 (Δ.insertMany d η T) (((τ.openManyAt 0 d η).shiftFrom 0).shiftFrom 0)
    (.ret (.bound 0))).openManyAt 2 0 Fin.elim0 =
      interpFuel gas 2 (Δ.insertMany d η T) (((τ.openManyAt 0 d η).shiftFrom 0).shiftFrom 0)
        (.ret (.bound 0)) from rfl] at opening
  rw [opening, raw, named]

/-- An opened symbolic return supplies its named value's basic type even
before a recursive interpretation conversion can assume that typed world. -/
theorem models_basicWorld_insert_of_opened_ret {m : Capability} {τ : ContextType}
    {Δ Δ' : BasicEnv} {gas n d : Nat} {η : Fin d → Atom} {y z : Atom}
    (world : m ⊨ Interp.basicWorld Δ') (fresh : ∀ i, η i ∉ Δ.domain)
    (freshZ : z ∉ Δ.domain) (freshY : y ∉ Δ.domain)
    (h : m ⊨ (((interpFuel gas n Δ τ (.ret (.bound 0))).openManyAt 2 d η).openAt 1 z).openAt 0 y) :
    m ⊨ Interp.basicWorld (Δ'.insert y τ.erase) := by
  let Δτ := Interp.relevantEnv Δ τ (.ret (.bound 0))
  have hdom : Δτ.domain ⊆ Δ.domain := by
    simp only [Δτ, Interp.relevantEnv_domain]
    exact Finset.inter_subset_left
  obtain ⟨P, eq⟩ := interpFuel_eq_guard_and gas n Δ τ (.ret (.bound 0))
  rw [eq, Formula.openManyAt_and] at h
  simp only [Formula.openAt] at h
  have hg := Formula.models_and_elim_left h
  rw [Interp.guard_openManyAt_eq n Δτ τ (.ret (.bound 0)) 2 d η
    (by simp [Term.locallyClosedAt, Value.locallyClosedAt])
    (fun i hi => fresh i (hdom hi)) (by simp [Term.support, Value.support]),
    Interp.guard_openAt_eq n Δτ τ (.ret (.bound 0)) 1 z
      (by simp [Term.locallyClosedAt, Value.locallyClosedAt])
      (fun hz => freshZ (hdom hz)) (by simp [Term.support, Value.support])] at hg
  simp only [Interp.guard, Formula.openAt] at hg
  have basic := Formula.models_and_elim_left
    (Formula.models_and_elim_right (Formula.models_and_elim_right hg))
  rw [Interp.basicTyping_ret_bound_openAt_eq Δτ τ.erase y (fun hy => freshY (hdom hy))] at basic
  have info := (Interp.models_basicWorld_iff m (Δτ.insert y τ.erase)).1 basic
  apply Interp.models_basicWorld_insert world
  · exact info.1 (by simp)
  · intro σ hσ
    exact info.2 σ hσ y τ.erase (BasicEnv.lookup_insert _ _ _)

private theorem OpensInputs.over (gas : Nat) (b : BaseType) (q : Qualifier) :
    OpensInputs gas ({ν : b | q}) := by
  intro lower m Δ e d η T wf inj fresh support typed world
  cases gas with
  | zero => simp [ContextType.measure] at lower
  | succ gas =>
      simpa only [Nat.zero_add] using models_interpFuel_openManyAt_over_iff (n := 0)
        (by simpa only [Nat.zero_add] using wf) inj fresh support typed world

private theorem OpensInputs.under (gas : Nat) (b : BaseType) (q : Qualifier) :
    OpensInputs gas ([ν : b | q]) := by
  intro lower m Δ e d η T wf inj fresh support typed world
  cases gas with
  | zero => simp [ContextType.measure] at lower
  | succ gas =>
      simpa only [Nat.zero_add] using models_interpFuel_openManyAt_under_iff (n := 0)
        (by simpa only [Nat.zero_add] using wf) inj fresh support typed world

/-- The intersection branch of the finite-input fuel induction. -/
private theorem OpensInputs.inter {gas : Nat} {τ₁ τ₂ : ContextType}
    (h₁ : OpensInputs gas τ₁) (h₂ : OpensInputs gas τ₂) :
    OpensInputs (gas + 1) (τ₁ ⊓ τ₂) := by
  intro lower m Δ e d η T wf inj fresh support typed world
  have lower₁ : τ₁.measure ≤ gas := by simp only [measure] at lower; omega
  have lower₂ : τ₂.measure ≤ gas := by simp only [measure] at lower; omega
  have typed₂ : Δ.insertMany d η T ⊢ₑ e.openManyAt 0 d η ⋮ τ₂.erase := by
    rw [← wf.2.2]
    exact typed
  have ih₁ := h₁ lower₁ m Δ e d η T wf.1 inj fresh support typed world
  have ih₂ := h₂ lower₂ m Δ e d η T wf.2.1 inj fresh support typed₂ world
  have hg := Interp.models_guard_relevant_openManyAt_iff (n := 0) (τ := τ₁ ⊓ τ₂)
    (by simpa only [Nat.zero_add] using wf) inj fresh support typed world
  simp only [ContextType.openManyAt_inter, Nat.zero_add] at hg
  simp only [interpFuel, Formula.openManyAt_and, ContextType.openManyAt_inter]
  rw [Formula.models_and_iff, Formula.models_and_iff, hg,
    Formula.models_and_iff, Formula.models_and_iff, ih₁, ih₂]

/-- The union branch additionally checks both disjuncts' observed scopes. -/
private theorem OpensInputs.union {gas : Nat} {τ₁ τ₂ : ContextType}
    (h₁ : OpensInputs gas τ₁) (h₂ : OpensInputs gas τ₂) :
    OpensInputs (gas + 1) (τ₁ ⊔ τ₂) := by
  intro lower m Δ e d η T wf inj fresh support typed world
  have lower₁ : τ₁.measure ≤ gas := by simp only [measure] at lower; omega
  have lower₂ : τ₂.measure ≤ gas := by simp only [measure] at lower; omega
  have typed₂ : Δ.insertMany d η T ⊢ₑ e.openManyAt 0 d η ⋮ τ₂.erase := by
    rw [← wf.2.2]
    exact typed
  have ih₁ := h₁ lower₁ m Δ e d η T wf.1 inj fresh support typed world
  have ih₂ := h₂ lower₂ m Δ e d η T wf.2.1 inj fresh support typed₂ world
  have hg := Interp.models_guard_relevant_openManyAt_iff (n := 0) (τ := τ₁ ⊔ τ₂)
    (by simpa only [Nat.zero_add] using wf) inj fresh support typed world
  have scopeWorld := (Interp.models_basicWorld_iff m _).1 world |>.1
  have rawScope (υ : ContextType) (observed : υ.freeAtoms ⊆ Δ.domain) :
      ((interpFuel gas d Δ υ e).openManyAt 0 d η).freeAtoms ⊆ m.domain := by
    apply Finset.Subset.trans (Formula.freeAtoms_openManyAt_subset _ _ _ _)
    apply Finset.Subset.trans _ scopeWorld
    apply Finset.Subset.trans (Finset.union_subset_union
      (Finset.Subset.trans (freeAtoms_interpFuel_subset gas d Δ υ e)
        (Finset.union_subset observed support)) (Finset.Subset.refl _))
    rw [BasicEnv.domain_insertMany]
  have wfOpen : ((τ₁ ⊔ τ₂ : ContextType).openManyAt 0 d η).WellFormed
      (Δ.insertMany d η T).domain := by
    have wf' : (τ₁ ⊔ τ₂ : ContextType).WellFormedAt (0 + d) Δ.domain := by
      simpa only [Nat.zero_add] using wf
    simpa only [BasicEnv.domain_insertMany] using wf'.openManyAt η inj fresh
  rw [ContextType.openManyAt_union] at wfOpen
  have namedScope (υ : ContextType) (observed : υ.freeAtoms ⊆ (Δ.insertMany d η T).domain) :
      (interpFuel gas 0 (Δ.insertMany d η T) υ (e.openManyAt 0 d η)).freeAtoms ⊆ m.domain :=
    Finset.Subset.trans (freeAtoms_interpFuel_subset _ _ _ _ _)
      (Finset.Subset.trans (Finset.union_subset observed typed.support_subset) scopeWorld)
  have raw :
      (((interpFuel gas d Δ τ₁ e).openManyAt 0 d η) ∨ᶜ
        ((interpFuel gas d Δ τ₂ e).openManyAt 0 d η)).freeAtoms ⊆ m.domain := by
    rw [Formula.freeAtoms_or]
    exact Finset.union_subset (rawScope τ₁ wf.1.freeAtoms_subset) (rawScope τ₂ wf.2.1.freeAtoms_subset)
  have named :
      ((interpFuel gas 0 (Δ.insertMany d η T) (τ₁.openManyAt 0 d η) (e.openManyAt 0 d η)) ∨ᶜ
        (interpFuel gas 0 (Δ.insertMany d η T) (τ₂.openManyAt 0 d η) (e.openManyAt 0 d η))).freeAtoms ⊆
        m.domain := by
    rw [Formula.freeAtoms_or]
    exact Finset.union_subset (namedScope _ wfOpen.1.freeAtoms_subset) (namedScope _ wfOpen.2.1.freeAtoms_subset)
  simp only [ContextType.openManyAt_union, Nat.zero_add] at hg
  simp only [interpFuel, Formula.openManyAt_and, Formula.openManyAt_or, ContextType.openManyAt_union]
  rw [Formula.models_and_iff, Formula.models_and_iff, hg,
    Formula.models_or_iff m _ _ raw, Formula.models_or_iff m _ _ named, ih₁, ih₂]

/-- Finite opening preserves sum's splitting of the complete result capability. -/
private theorem OpensInputs.sum {gas : Nat} {τ₁ τ₂ : ContextType}
    (h₁ : OpensInputs gas (τ₁.shiftFrom 0)) (h₂ : OpensInputs gas (τ₂.shiftFrom 0)) :
    OpensInputs (gas + 1) (τ₁ ⊕ τ₂) := by
  intro lower m Δ e d η T wf inj fresh support typed world
  have lower₁ : τ₁.measure ≤ gas := by simp only [measure] at lower; omega
  have lower₂ : τ₂.measure ≤ gas := by simp only [measure] at lower; omega
  let τ : ContextType := τ₁ ⊕ τ₂
  let Δr := Interp.relevantEnv Δ τ e
  let Δ' := Δ.insertMany d η T
  let υ₁ := τ₁.openManyAt 0 d η
  let υ₂ := τ₂.openManyAt 0 d η
  let e' := e.openManyAt 0 d η
  let Δr' := Interp.relevantEnv Δ' (υ₁ ⊕ υ₂) e'
  let A := Interp.resultFirst Δ' (υ₁ ⊕ υ₂) e'
  let R := ((interpFuel gas (d + 1) Δr (τ₁.shiftFrom 0) (.ret (.bound 0))).openManyAt 1 d η) ⊕
    ((interpFuel gas (d + 1) Δr (τ₂.shiftFrom 0) (.ret (.bound 0))).openManyAt 1 d η)
  let S := (interpFuel gas 1 Δr' (υ₁.shiftFrom 0) (.ret (.bound 0))) ⊕
    (interpFuel gas 1 Δr' (υ₂.shiftFrom 0) (.ret (.bound 0)))
  have scopeΔ := (Interp.models_basicWorld_iff m Δ').1 world |>.1
  have wf' : τ.WellFormedAt (0 + d) Δ.domain := by simpa only [τ, Nat.zero_add] using wf
  have wfOpen : (υ₁ ⊕ υ₂ : ContextType).WellFormed Δ'.domain := by
    simpa only [τ, Δ', υ₁, υ₂, ContextType.openManyAt_sum, BasicEnv.domain_insertMany]
      using wf'.openManyAt η inj fresh
  have typedOpen : Δ' ⊢ₑ e' ⋮ (υ₁ ⊕ υ₂ : ContextType).erase := by
    simpa only [Δ', e', υ₁, ContextType.erase, erase_openManyAt] using typed
  have hg := Interp.models_guard_relevant_openManyAt_iff (n := 0) (τ := τ)
    wf' inj fresh support typed world
  have graph : (Interp.resultFirst Δr τ e).openManyAt 1 d η = A := by
    simp only [Δr, Interp.resultFirst_relevantEnv]
    simpa only [A, Δ', e', υ₁, υ₂, τ, ContextType.openManyAt_sum] using
      Interp.resultFirst_openManyAt_inputs Δ τ e 0 d η T inj fresh
        (fun i hx => fresh i (wf.freeAtoms_subset hx)) (fun i hx => fresh i (support hx))
  have scopeA : A.freeAtoms ⊆ m.domain := by
    have hs := Interp.freeAtoms_resultFirst_relevant_subset Δ' (υ₁ ⊕ υ₂) e'
    rw [Interp.resultFirst_relevantEnv] at hs
    exact Finset.Subset.trans hs
      (Finset.Subset.trans (Finset.union_subset wfOpen.freeAtoms_subset typedOpen.support_subset) scopeΔ)
  have rawScope (υ : ContextType) (hs : υ.freeAtoms ⊆ Δ.domain) :
      ((interpFuel gas (d + 1) Δr (υ.shiftFrom 0) (.ret (.bound 0))).openManyAt 1 d η).freeAtoms ⊆ m.domain := by
    apply Finset.Subset.trans (Formula.freeAtoms_openManyAt_subset _ _ _ _)
    apply Finset.Subset.trans _ scopeΔ
    rw [BasicEnv.domain_insertMany]
    apply Finset.union_subset_union _ (Finset.Subset.refl _)
    exact Finset.Subset.trans (freeAtoms_interpFuel_subset _ _ _ _ _)
      (by simpa [Term.support, Value.support] using hs)
  have namedScope (υ : ContextType) (hs : υ.freeAtoms ⊆ Δ'.domain) :
      (interpFuel gas 1 Δr' (υ.shiftFrom 0) (.ret (.bound 0))).freeAtoms ⊆ m.domain := by
    apply Finset.Subset.trans (freeAtoms_interpFuel_subset _ _ _ _ _)
    simpa [Term.support, Value.support] using Finset.Subset.trans hs scopeΔ
  have scopeR : R.freeAtoms ⊆ m.domain := by
    rw [Formula.freeAtoms_sum]
    exact Finset.union_subset (rawScope τ₁ wf.1.freeAtoms_subset) (rawScope τ₂ wf.2.1.freeAtoms_subset)
  have scopeS : S.freeAtoms ⊆ m.domain := by
    rw [Formula.freeAtoms_sum]
    exact Finset.union_subset (namedScope υ₁ wfOpen.1.freeAtoms_subset)
      (namedScope υ₂ wfOpen.2.1.freeAtoms_subset)
  have quantified : m ⊨ Formula.all (A ⇒ᶜ R) ↔ m ⊨ Formula.all (A ⇒ᶜ S) := by
    apply Formula.models_all_impl_congr
      (by rw [Formula.freeAtoms_impl]; exact Finset.union_subset scopeA scopeR)
      (by rw [Formula.freeAtoms_impl]; exact Finset.union_subset scopeA scopeS)
    refine ⟨∅, ?_⟩
    intro z _ freshZ n href hdom hA
    have freshΔ' : z ∉ Δ'.domain := fun hz => freshZ (scopeΔ hz)
    have worldN := Interp.models_basicWorld_resultFirst_openAt wfOpen typedOpen
      (Formula.models_kripke href world) freshΔ' hA
    have embedR : Δr.Subset Δ := by
      intro x U hx
      change (Δ.restrict (Interp.relevantAtoms τ e)).lookup x = some U at hx
      rw [BasicEnv.lookup_restrict] at hx
      split_ifs at hx
      · exact hx
    have freshR : ∀ i, η i ∉ Δr.domain := by
      intro i hi
      exact fresh i (Finset.inter_subset_left (by simpa only [Δr, Interp.relevantEnv_domain] using hi))
    have child (υ : ContextType) (hυ : υ.WellFormedAt d Δ.domain)
        (ih : OpensInputs gas (υ.shiftFrom 0)) (lo : υ.measure ≤ gas)
        (hs : υ.freeAtoms ⊆ τ.freeAtoms)
        (hs' : (υ.openManyAt 0 d η).freeAtoms ⊆ (υ₁ ⊕ υ₂ : ContextType).freeAtoms)
        (erased : υ.erase = τ₁.erase) (p : Capability) (hp : p ⊆ n) :
        p ⊨ ((interpFuel gas (d + 1) Δr (υ.shiftFrom 0) (.ret (.bound 0))).openManyAt 1 d η).openAt 0 z ↔
        p ⊨ (interpFuel gas 1 Δr' ((υ.openManyAt 0 d η).shiftFrom 0) (.ret (.bound 0))).openAt 0 z := by
      have hυR : υ.WellFormedAt d Δr.domain := hυ.regularize (by
        intro x hx
        simp only [Δr, Interp.relevantEnv_domain, Finset.mem_inter, Interp.relevantAtoms]
        exact ⟨hυ.freeAtoms_subset hx, Finset.mem_union_left _ (hs hx)⟩)
      have wz : p ⊨ Interp.basicWorld ((Δr.insertMany d η T).insert z υ.erase) := by
        apply Interp.models_basicWorld_of_subset ((embedR.insertMany d η T).insert z υ.erase)
        have wn := Interp.models_basicWorld_of_capability_subset hp worldN
        simpa only [ContextType.erase, υ₁, erase_openManyAt, erased] using wn
      have eq := ih.resultChild (gas := gas) (d := d) (m := p) (Δ := Δr)
        (η := η) (T := T) (z := z) lo hυR inj freshR
        (fun hz => freshΔ' (by
          simp only [Δ', BasicEnv.domain_insertMany] at hz ⊢
          rcases Finset.mem_union.1 hz with hz | hz
          · simp only [Δr, Interp.relevantEnv_domain] at hz
            exact Finset.mem_union_left _ (Finset.mem_inter.1 hz).1
          · exact Finset.mem_union_right _ hz)) wz
      have agree := Interp.relevantEnv_openManyAt_agreeOn (Δ := Δ) (τ := τ) (υ := υ)
        (e := e) (T := T) inj hs (by simpa only [τ, ContextType.openManyAt_sum] using hs')
      have envEq : interpFuel gas 1 (Δr.insertMany d η T) ((υ.openManyAt 0 d η).shiftFrom 0) (.ret (.bound 0)) =
          interpFuel gas 1 Δr' ((υ.openManyAt 0 d η).shiftFrom 0) (.ret (.bound 0)) := by
        apply interpFuel_eq_of_agreeOn
        simpa only [freeAtoms_shiftFrom, Term.support, Value.support, Finset.union_empty,
          Δr, Δr', Δ', υ₁, υ₂, e', τ, ContextType.openManyAt_sum] using agree
      rwa [envEq] at eq
    change n ⊨ (R.openAt 0 z) ↔ n ⊨ (S.openAt 0 z)
    simp only [R, S, Formula.openAt]
    rw [Formula.models_sum_iff_eq, Formula.models_sum_iff_eq]
    constructor <;> rintro ⟨p₁, p₂, defined, same, hP, hQ⟩
    · refine ⟨p₁, p₂, defined, same, ?_, ?_⟩
      · exact (child τ₁ wf.1 h₁ lower₁ Finset.subset_union_left Finset.subset_union_left rfl
          p₁ (same ▸ Capability.subset_sum_left defined)).1 hP
      · exact (child τ₂ wf.2.1 h₂ lower₂ Finset.subset_union_right Finset.subset_union_right wf.2.2.symm
          p₂ (same ▸ Capability.subset_sum_right defined)).1 hQ
    · refine ⟨p₁, p₂, defined, same, ?_, ?_⟩
      · exact (child τ₁ wf.1 h₁ lower₁ Finset.subset_union_left Finset.subset_union_left rfl
          p₁ (same ▸ Capability.subset_sum_left defined)).2 hP
      · exact (child τ₂ wf.2.1 h₂ lower₂ Finset.subset_union_right Finset.subset_union_right wf.2.2.symm
          p₂ (same ▸ Capability.subset_sum_right defined)).2 hQ
  simp only [interpFuel, Formula.openManyAt_and, Formula.openManyAt_all,
    Formula.openManyAt_impl, Formula.openManyAt_sum, ContextType.openManyAt_sum, Nat.zero_add]
  simp only [Interp.resultFirst_relevantEnv]
  have graph' : (Interp.resultFirst Δ (τ₁ ⊕ τ₂) e).openManyAt 1 d η = A := by
    simpa only [Δr, τ, Interp.resultFirst_relevantEnv] using graph
  rw [graph']
  rw [Formula.models_and_iff, Formula.models_and_iff]
  have hg' : m ⊨ (Interp.guard d Δr τ e).openManyAt 0 d η ↔
      m ⊨ Interp.guard 0 Δr' (υ₁ ⊕ υ₂) e' := by
    simpa only [τ, Δr, Δr', Δ', υ₁, υ₂, e', ContextType.openManyAt_sum, Nat.zero_add] using hg
  change (m ⊨ (Interp.guard d Δr τ e).openManyAt 0 d η ∧
    m ⊨ Formula.all (A ⇒ᶜ R)) ↔
    (m ⊨ Interp.guard 0 Δr' (υ₁ ⊕ υ₂) e' ∧ m ⊨ Formula.all (A ⇒ᶜ S))
  rw [hg', quantified]

/-- The arrow branch preserves both universally quantified binders and derives
argument typing from each antecedent rather than assuming it for all inputs. -/
private theorem OpensInputs.arrow {gas : Nat} {τ₁ τ₂ : ContextType}
    (ih : ∀ υ, OpensInputs gas υ) : OpensInputs (gas + 1) (.arrow τ₁ τ₂) := by
  intro lower m Δ e d η T wf inj fresh support typed world
  have lower₁ : τ₁.measure ≤ gas := by simp only [measure] at lower; omega
  have lower₂ : τ₂.measure ≤ gas := by simp only [measure] at lower; omega
  let τ := ContextType.arrow τ₁ τ₂
  let Δr := Interp.relevantEnv Δ τ e
  let Δ' := Δ.insertMany d η T
  let υ₁ := τ₁.openManyAt 0 d η
  let υ₂ := τ₂.openManyAt 1 d η
  let e' := e.openManyAt 0 d η
  let Δr' := Interp.relevantEnv Δ' (.arrow υ₁ υ₂) e'
  let A := Interp.resultFirst Δ' (.arrow υ₁ υ₂) e'
  let B := (interpFuel gas (d + 2) Δr ((τ₁.shiftFrom 0).shiftFrom 0)
    (.ret (.bound 0))).openManyAt 2 d η
  let C := (interpFuel gas (d + 2) Δr (τ₂.shiftFrom 1)
    (.app (.bound 1) (.bound 0))).openManyAt 2 d η
  let B' := interpFuel gas 2 Δr' ((υ₁.shiftFrom 0).shiftFrom 0) (.ret (.bound 0))
  let C' := interpFuel gas 2 Δr' (υ₂.shiftFrom 1) (.app (.bound 1) (.bound 0))
  let R := Formula.all (B ⇒ᶜ C)
  let S := Formula.all (B' ⇒ᶜ C')
  have scopeΔ := (Interp.models_basicWorld_iff m Δ').1 world |>.1
  have wf' : τ.WellFormedAt (0 + d) Δ.domain := by simpa only [τ, Nat.zero_add] using wf
  have wfOpen : (ContextType.arrow υ₁ υ₂).WellFormed Δ'.domain := by
    simpa only [τ, Δ', υ₁, υ₂, ContextType.openManyAt_arrow, BasicEnv.domain_insertMany]
      using wf'.openManyAt η inj fresh
  have typedOpen : Δ' ⊢ₑ e' ⋮ (ContextType.arrow υ₁ υ₂).erase := by
    simpa only [Δ', e', υ₁, υ₂, ContextType.erase, erase_openManyAt] using typed
  have hg := Interp.models_guard_relevant_openManyAt_iff (n := 0) (τ := τ)
    wf' inj fresh support typed world
  have graph : (Interp.resultFirst Δ τ e).openManyAt 1 d η = A := by
    simpa only [A, Δ', e', υ₁, υ₂, τ, ContextType.openManyAt_arrow] using
      Interp.resultFirst_openManyAt_inputs Δ τ e 0 d η T inj fresh
        (fun i hx => fresh i (wf.freeAtoms_subset hx)) (fun i hx => fresh i (support hx))
  have scopeA : A.freeAtoms ⊆ m.domain := by
    have hs := Interp.freeAtoms_resultFirst_relevant_subset Δ' (.arrow υ₁ υ₂) e'
    rw [Interp.resultFirst_relevantEnv] at hs
    exact Finset.Subset.trans hs
      (Finset.Subset.trans (Finset.union_subset wfOpen.freeAtoms_subset typedOpen.support_subset) scopeΔ)
  have rawScope (υ : ContextType) (t : Term) (hs : υ.freeAtoms ⊆ Δ.domain) (empty : t.support = ∅) :
      ((interpFuel gas (d + 2) Δr υ t).openManyAt 2 d η).freeAtoms ⊆ m.domain := by
    apply Finset.Subset.trans (Formula.freeAtoms_openManyAt_subset _ _ _ _)
    apply Finset.Subset.trans _ scopeΔ
    rw [BasicEnv.domain_insertMany]
    apply Finset.union_subset_union _ (Finset.Subset.refl _)
    exact Finset.Subset.trans (freeAtoms_interpFuel_subset _ _ _ _ _)
      (by simpa only [empty, Finset.union_empty] using hs)
  have namedScope (υ : ContextType) (t : Term) (hs : υ.freeAtoms ⊆ Δ'.domain) (empty : t.support = ∅) :
      (interpFuel gas 2 Δr' υ t).freeAtoms ⊆ m.domain := by
    apply Finset.Subset.trans (freeAtoms_interpFuel_subset _ _ _ _ _)
    simpa only [empty, Finset.union_empty] using Finset.Subset.trans hs scopeΔ
  have scopeR : R.freeAtoms ⊆ m.domain := by
    simp only [R, Formula.freeAtoms_all, Formula.freeAtoms_impl]
    exact Finset.union_subset
      (rawScope _ _ (by simpa only [freeAtoms_shiftFrom] using wf.1.freeAtoms_subset) (by simp [Term.support, Value.support]))
      (rawScope _ _ (by simpa only [freeAtoms_shiftFrom] using wf.2.freeAtoms_subset) (by simp [Term.support, Value.support]))
  have scopeS : S.freeAtoms ⊆ m.domain := by
    simp only [S, Formula.freeAtoms_all, Formula.freeAtoms_impl]
    exact Finset.union_subset
      (namedScope _ _ (by simpa only [freeAtoms_shiftFrom] using wfOpen.1.freeAtoms_subset) (by simp [Term.support, Value.support]))
      (namedScope _ _ (by simpa only [freeAtoms_shiftFrom] using wfOpen.2.freeAtoms_subset) (by simp [Term.support, Value.support]))
  have openedScope {r s : Capability} (P : Formula) (hs : P.freeAtoms ⊆ r.domain)
      (x : Atom) (hd : s.domain = r.domain ∪ {x}) : (P.openAt 0 x).freeAtoms ⊆ s.domain := by
    apply Finset.Subset.trans (Formula.freeAtoms_openAt_subset P 0 x)
    rw [hd]
    exact Finset.union_subset (by simp) (Finset.Subset.trans hs Finset.subset_union_left)
  have embedR : Δr.Subset Δ := by
    intro x U hx
    change (Δ.restrict (Interp.relevantAtoms τ e)).lookup x = some U at hx
    rw [BasicEnv.lookup_restrict] at hx
    split_ifs at hx
    exact hx
  have scopeRΔ : Δr.domain ⊆ Δ.domain := by
    simp only [Δr, Interp.relevantEnv_domain]
    exact Finset.inter_subset_left
  have scopeRΔ' : Δr'.domain ⊆ Δ'.domain := by
    simp only [Δr', Interp.relevantEnv_domain]
    exact Finset.inter_subset_left
  have freshR : ∀ i, η i ∉ Δr.domain := fun i hi => fresh i (scopeRΔ hi)
  have wfArgR : τ₁.WellFormedAt d Δr.domain := wf.1.regularize (by
    intro x hx
    simp only [Δr, Interp.relevantEnv_domain, Finset.mem_inter, Interp.relevantAtoms, τ, ContextType.freeAtoms]
    exact ⟨wf.1.freeAtoms_subset hx, Finset.mem_union_left _ (Finset.mem_union_left _ hx)⟩)
  have wfCodR : τ₂.WellFormedAt (1 + d) Δr.domain := by
    have h := wf.2.regularize (Y := Δr.domain) (by
      intro x hx
      simp only [Δr, Interp.relevantEnv_domain, Finset.mem_inter, Interp.relevantAtoms, τ, ContextType.freeAtoms]
      exact ⟨wf.2.freeAtoms_subset hx, Finset.mem_union_left _ (Finset.mem_union_right _ hx)⟩)
    simpa only [Nat.add_comm] using h
  have argEq : interpFuel gas 2 (Δr.insertMany d η T) ((υ₁.shiftFrom 0).shiftFrom 0) (.ret (.bound 0)) = B' := by
    apply interpFuel_eq_of_agreeOn
    have h := Interp.relevantEnv_openManyAt_agreeOn_at (Δ := Δ) (τ := τ) (υ := τ₁)
      (e := e) (k := 0) (T := T) inj Finset.subset_union_left
      (by simp only [τ, ContextType.openManyAt_arrow, ContextType.freeAtoms]; exact Finset.subset_union_left)
    simpa only [freeAtoms_shiftFrom, Term.support, Value.support, Finset.union_empty,
      Δr, Δr', Δ', υ₁, υ₂, e', τ, ContextType.openManyAt_arrow] using h
  have codEq : interpFuel gas 2 (Δr.insertMany d η T) (υ₂.shiftFrom 1) (.app (.bound 1) (.bound 0)) = C' := by
    apply interpFuel_eq_of_agreeOn
    have h := Interp.relevantEnv_openManyAt_agreeOn_at (Δ := Δ) (τ := τ) (υ := τ₂)
      (e := e) (k := 1) (T := T) inj Finset.subset_union_right
      (by simp only [τ, ContextType.openManyAt_arrow, ContextType.freeAtoms]; exact Finset.subset_union_right)
    simpa only [freeAtoms_shiftFrom, Term.support, Value.support, Finset.union_empty,
      Δr, Δr', Δ', υ₁, υ₂, e', τ, ContextType.openManyAt_arrow] using h
  have quantified : m ⊨ Formula.all (A ⇒ᶜ R) ↔ m ⊨ Formula.all (A ⇒ᶜ S) := by
    apply Formula.models_all_impl_congr
      (by rw [Formula.freeAtoms_impl]; exact Finset.union_subset scopeA scopeR)
      (by rw [Formula.freeAtoms_impl]; exact Finset.union_subset scopeA scopeS)
    refine ⟨∅, ?_⟩
    intro z _ freshZ n href hdom hA
    have freshZΔ' : z ∉ Δ'.domain := fun hz => freshZ (scopeΔ hz)
    have worldZ : n ⊨ Interp.basicWorld (Δ'.insert z (.arrow τ₁.erase τ₂.erase)) := by
      have h := Interp.models_basicWorld_resultFirst_openAt wfOpen typedOpen
        (Formula.models_kripke href world) freshZΔ' hA
      simpa only [ContextType.erase, υ₁, υ₂, erase_openManyAt] using h
    have scopeRN : ((B.openAt 1 z) ⇒ᶜ (C.openAt 1 z)).freeAtoms ⊆ n.domain := by
      simpa only [R, Formula.openAt, Formula.freeAtoms_all] using openedScope R scopeR z hdom
    have scopeSN : ((B'.openAt 1 z) ⇒ᶜ (C'.openAt 1 z)).freeAtoms ⊆ n.domain := by
      simpa only [S, Formula.openAt, Formula.freeAtoms_all] using openedScope S scopeS z hdom
    change n ⊨ Formula.all (B.openAt 1 z ⇒ᶜ C.openAt 1 z) ↔
      n ⊨ Formula.all (B'.openAt 1 z ⇒ᶜ C'.openAt 1 z)
    apply Formula.models_all_congr_full scopeRN scopeSN
    refine ⟨∅, ?_⟩
    intro y _ freshY p refp pdom
    have freshYΔ' : y ∉ Δ'.domain ∪ {z} := by
      intro hy
      apply freshY
      rw [hdom]
      rcases Finset.mem_union.1 hy with hy | hy
      · exact Finset.mem_union_left _ (scopeΔ hy)
      · exact Finset.mem_union_right _ hy
    have worldP := Formula.models_kripke refp worldZ
    have worldRaw (hB : p ⊨ (B.openAt 1 z).openAt 0 y) :
        p ⊨ Interp.basicWorld ((Δ'.insert z (.arrow τ₁.erase τ₂.erase)).insert y τ₁.erase) := by
      have h := models_basicWorld_insert_of_opened_ret (τ := (τ₁.shiftFrom 0).shiftFrom 0)
        (Δ := Δr) (Δ' := Δ'.insert z (.arrow τ₁.erase τ₂.erase))
        (gas := gas) (n := d + 2) (d := d) (η := η)
        worldP freshR (fun hz => freshZΔ' (by
          simp only [Δ', BasicEnv.domain_insertMany]
          exact Finset.mem_union_left _ (scopeRΔ hz)))
        (fun hy => freshYΔ' (Finset.mem_union_left _ (by
          simp only [Δ', BasicEnv.domain_insertMany]
          exact Finset.mem_union_left _ (scopeRΔ hy)))) hB
      simpa only [erase_shiftFrom] using h
    have worldNamed (hB : p ⊨ (B'.openAt 1 z).openAt 0 y) :
        p ⊨ Interp.basicWorld ((Δ'.insert z (.arrow τ₁.erase τ₂.erase)).insert y τ₁.erase) := by
      have h := models_basicWorld_insert_of_opened_ret (τ := (υ₁.shiftFrom 0).shiftFrom 0)
        (Δ := Δr') (Δ' := Δ'.insert z (.arrow τ₁.erase τ₂.erase)) (d := 0) (η := Fin.elim0)
        worldP (fun i => Fin.elim0 i) (fun hz => freshZΔ' (scopeRΔ' hz))
        (fun hy => freshYΔ' (Finset.mem_union_left _ (scopeRΔ' hy))) hB
      simpa only [erase_shiftFrom, υ₁, erase_openManyAt] using h
    have freshZR : z ∉ (Δr.insertMany d η T).domain := by
      intro hz
      apply freshZΔ'
      simp only [Δ', BasicEnv.domain_insertMany] at hz ⊢
      exact Finset.union_subset_union scopeRΔ (Finset.Subset.refl _) hz
    have freshYR : y ∉ (Δr.insertMany d η T).domain ∪ {z} := by
      intro hy
      apply freshYΔ'
      simp only [Δ', BasicEnv.domain_insertMany] at hy ⊢
      exact Finset.union_subset_union (Finset.union_subset_union scopeRΔ (Finset.Subset.refl _))
        (Finset.Subset.refl _) hy
    have transport (w : p ⊨ Interp.basicWorld ((Δ'.insert z (.arrow τ₁.erase τ₂.erase)).insert y τ₁.erase)) :
        (p ⊨ (B.openAt 1 z).openAt 0 y ↔ p ⊨ (B'.openAt 1 z).openAt 0 y) ∧
        (p ⊨ (C.openAt 1 z).openAt 0 y ↔ p ⊨ (C'.openAt 1 z).openAt 0 y) := by
      have wR : p ⊨ Interp.basicWorld (((Δr.insertMany d η T).insert z (.arrow τ₁.erase τ₂.erase)).insert y τ₁.erase) :=
        Interp.models_basicWorld_of_subset (((embedR.insertMany d η T).insert z _).insert y _) w
      have h₁ := OpensInputs.argumentChild (gas := gas) (d := d) (m := p) (Δ := Δr)
        (τ := τ₁) (η := η) (T := T) (V := .arrow τ₁.erase τ₂.erase)
        ih lower₁ wfArgR inj freshR freshZR freshYR wR
      have h₂ := OpensInputs.applicationChild (gas := gas) (d := d) (m := p) (Δ := Δr)
        (τ := τ₂) (η := η) (T := T) (U := τ₁.erase)
        ih lower₂ wfCodR inj freshR freshZR freshYR wR
      rw [argEq] at h₁
      rw [codEq] at h₂
      exact ⟨h₁, h₂⟩
    simp only [Formula.openAt]
    rw [Formula.models_impl_iff_of_scope p _ _ (openedScope _ scopeRN y pdom),
      Formula.models_impl_iff_of_scope p _ _ (openedScope _ scopeSN y pdom)]
    constructor
    · intro h hB
      have ht := transport (worldNamed hB)
      exact ht.2.1 (h (ht.1.2 hB))
    · intro h hB
      have ht := transport (worldRaw hB)
      exact ht.2.2 (h (ht.1.1 hB))
  simp only [interpFuel, Formula.openManyAt_and, Formula.openManyAt_all,
    Formula.openManyAt_impl, ContextType.openManyAt_arrow, Nat.zero_add]
  simp only [Interp.resultFirst_relevantEnv]
  rw [graph, Formula.models_and_iff, Formula.models_and_iff]
  have hg' : m ⊨ (Interp.guard d Δr τ e).openManyAt 0 d η ↔
      m ⊨ Interp.guard 0 Δr' (.arrow υ₁ υ₂) e' := by
    simpa only [τ, Δr, Δr', Δ', υ₁, υ₂, e', ContextType.openManyAt_arrow, Nat.zero_add] using hg
  change (m ⊨ (Interp.guard d Δr τ e).openManyAt 0 d η ∧ m ⊨ Formula.all (A ⇒ᶜ R)) ↔
    (m ⊨ Interp.guard 0 Δr' (.arrow υ₁ υ₂) e' ∧ m ⊨ Formula.all (A ⇒ᶜ S))
  rw [hg', quantified]

/-- Separating-function conversion preserves the separate argument capability
while retaining all ambient input bindings for the recursive application. -/
private theorem OpensInputs.wand {gas : Nat} {τ₁ τ₂ : ContextType}
    (ih : ∀ υ, OpensInputs gas υ) : OpensInputs (gas + 1) (.wand τ₁ τ₂) := by
  intro lower m Δ e d η T wf inj fresh support typed world
  have lower₂ : τ₂.measure ≤ gas := by simp only [measure] at lower; omega
  let τ := ContextType.wand τ₁ τ₂
  let Δr := Interp.relevantEnv Δ τ e
  let Δ' := Δ.insertMany d η T
  let υ₁ := τ₁.openManyAt 0 d η
  let υ₂ := τ₂.openManyAt 1 d η
  let e' := e.openManyAt 0 d η
  let Δr' := Interp.relevantEnv Δ' (.wand υ₁ υ₂) e'
  let A := Interp.resultFirst Δ' (.wand υ₁ υ₂) e'
  let B := (interpFuel gas (d + 2) Δr ((τ₁.shiftFrom 0).shiftFrom 0)
    (.ret (.bound 0))).openManyAt 2 d η
  let C := (interpFuel gas (d + 2) Δr (τ₂.shiftFrom 1)
    (.app (.bound 1) (.bound 0))).openManyAt 2 d η
  let B' := interpFuel gas 2 Δr' ((υ₁.shiftFrom 0).shiftFrom 0) (.ret (.bound 0))
  let C' := interpFuel gas 2 Δr' (υ₂.shiftFrom 1) (.app (.bound 1) (.bound 0))
  let R := B -∗[1] C
  let S := B' -∗[1] C'
  have scopeΔ := (Interp.models_basicWorld_iff m Δ').1 world |>.1
  have wf' : τ.WellFormedAt (0 + d) Δ.domain := by simpa only [τ, Nat.zero_add] using wf
  have wfOpen : (ContextType.wand υ₁ υ₂).WellFormed Δ'.domain := by
    simpa only [τ, Δ', υ₁, υ₂, ContextType.openManyAt_wand, BasicEnv.domain_insertMany]
      using wf'.openManyAt η inj fresh
  have typedOpen : Δ' ⊢ₑ e' ⋮ (ContextType.wand υ₁ υ₂).erase := by
    simpa only [Δ', e', υ₁, υ₂, ContextType.erase, erase_openManyAt] using typed
  have hg := Interp.models_guard_relevant_openManyAt_iff (n := 0) (τ := τ)
    wf' inj fresh support typed world
  have graph : (Interp.resultFirst Δ τ e).openManyAt 1 d η = A := by
    simpa only [A, Δ', e', υ₁, υ₂, τ, ContextType.openManyAt_wand] using
      Interp.resultFirst_openManyAt_inputs Δ τ e 0 d η T inj fresh
        (fun i hx => fresh i (wf.freeAtoms_subset hx)) (fun i hx => fresh i (support hx))
  have scopeA : A.freeAtoms ⊆ m.domain := by
    have hs := Interp.freeAtoms_resultFirst_relevant_subset Δ' (.wand υ₁ υ₂) e'
    rw [Interp.resultFirst_relevantEnv] at hs
    exact Finset.Subset.trans hs
      (Finset.Subset.trans (Finset.union_subset wfOpen.freeAtoms_subset typedOpen.support_subset) scopeΔ)
  have rawScope (υ : ContextType) (t : Term) (hs : υ.freeAtoms ⊆ Δ.domain) (empty : t.support = ∅) :
      ((interpFuel gas (d + 2) Δr υ t).openManyAt 2 d η).freeAtoms ⊆ m.domain := by
    apply Finset.Subset.trans (Formula.freeAtoms_openManyAt_subset _ _ _ _)
    apply Finset.Subset.trans _ scopeΔ
    rw [BasicEnv.domain_insertMany]
    apply Finset.union_subset_union _ (Finset.Subset.refl _)
    exact Finset.Subset.trans (freeAtoms_interpFuel_subset _ _ _ _ _)
      (by simpa only [empty, Finset.union_empty] using hs)
  have namedScope (υ : ContextType) (t : Term) (hs : υ.freeAtoms ⊆ Δ'.domain) (empty : t.support = ∅) :
      (interpFuel gas 2 Δr' υ t).freeAtoms ⊆ m.domain := by
    apply Finset.Subset.trans (freeAtoms_interpFuel_subset _ _ _ _ _)
    simpa only [empty, Finset.union_empty] using Finset.Subset.trans hs scopeΔ
  have scopeR : R.freeAtoms ⊆ m.domain := by
    simp only [R, Formula.freeAtoms_wand]
    exact Finset.union_subset
      (rawScope _ _ (by simpa only [freeAtoms_shiftFrom] using (Finset.Subset.trans wf.1.freeAtoms_subset (Finset.empty_subset Δ.domain))) (by simp [Term.support, Value.support]))
      (rawScope _ _ (by simpa only [freeAtoms_shiftFrom] using wf.2.freeAtoms_subset) (by simp [Term.support, Value.support]))
  have scopeS : S.freeAtoms ⊆ m.domain := by
    simp only [S, Formula.freeAtoms_wand]
    exact Finset.union_subset
      (namedScope _ _ (by simpa only [freeAtoms_shiftFrom] using (Finset.Subset.trans wfOpen.1.freeAtoms_subset (Finset.empty_subset Δ'.domain))) (by simp [Term.support, Value.support]))
      (namedScope _ _ (by simpa only [freeAtoms_shiftFrom] using wfOpen.2.freeAtoms_subset) (by simp [Term.support, Value.support]))
  have openedScope {r s : Capability} (P : Formula) (hs : P.freeAtoms ⊆ r.domain)
      (x : Atom) (hd : s.domain = r.domain ∪ {x}) : (P.openAt 0 x).freeAtoms ⊆ s.domain := by
    apply Finset.Subset.trans (Formula.freeAtoms_openAt_subset P 0 x)
    rw [hd]
    exact Finset.union_subset (by simp) (Finset.Subset.trans hs Finset.subset_union_left)
  have embedR : Δr.Subset Δ := by
    intro x U hx
    change (Δ.restrict (Interp.relevantAtoms τ e)).lookup x = some U at hx
    rw [BasicEnv.lookup_restrict] at hx
    split_ifs at hx
    exact hx
  have scopeRΔ : Δr.domain ⊆ Δ.domain := by
    simp only [Δr, Interp.relevantEnv_domain]
    exact Finset.inter_subset_left
  have scopeRΔ' : Δr'.domain ⊆ Δ'.domain := by
    simp only [Δr', Interp.relevantEnv_domain]
    exact Finset.inter_subset_left
  have freshR : ∀ i, η i ∉ Δr.domain := fun i hi => fresh i (scopeRΔ hi)
  have wfCodR : τ₂.WellFormedAt (1 + d) Δr.domain := by
    have h := wf.2.regularize (Y := Δr.domain) (by
      intro x hx
      simp only [Δr, Interp.relevantEnv_domain, Finset.mem_inter, Interp.relevantAtoms, τ, ContextType.freeAtoms]
      exact ⟨wf.2.freeAtoms_subset hx, Finset.mem_union_left _ (Finset.mem_union_right _ hx)⟩)
    simpa only [Nat.add_comm] using h
  have codEq : interpFuel gas 2 (Δr.insertMany d η T) (υ₂.shiftFrom 1) (.app (.bound 1) (.bound 0)) = C' := by
    apply interpFuel_eq_of_agreeOn
    have h := Interp.relevantEnv_openManyAt_agreeOn_at (Δ := Δ) (τ := τ) (υ := τ₂)
      (e := e) (k := 1) (T := T) inj Finset.subset_union_right
      (by simp only [τ, ContextType.openManyAt_wand, ContextType.freeAtoms]; exact Finset.subset_union_right)
    simpa only [freeAtoms_shiftFrom, Term.support, Value.support, Finset.union_empty,
      Δr, Δr', Δ', υ₁, υ₂, e', τ, ContextType.openManyAt_wand] using h
  have closedτ₁ := wf.1.locallyClosedAt
  have emptyτ₁ : τ₁.freeAtoms = ∅ := Finset.Subset.antisymm wf.1.freeAtoms_subset (Finset.empty_subset _)
  have shiftτ₁ : τ₁.shiftFrom 0 = τ₁ := shiftFrom_eq_of_locallyClosedAt τ₁ 0 closedτ₁
  have openτ₁ : υ₁ = τ₁ := openManyAt_eq_of_locallyClosedAt τ₁ 0 d η closedτ₁
    (by intro i; rw [emptyτ₁]; exact Finset.notMem_empty _)
  have argBase : B = interpFuel gas 2 Δr τ₁ (.ret (.bound 0)) := by
    simp only [B, shiftτ₁]
    rw [interpFuel_openManyAt_fresh gas (d + 2) Δr τ₁ (.ret (.bound 0)) 2 d η
      (closedτ₁.mono (by omega)) (by simp [Term.locallyClosedAt, Value.locallyClosedAt])
      freshR (by intro i; rw [emptyτ₁]; exact Finset.notMem_empty _) (by simp [Term.support, Value.support])]
    exact interpFuel_eq_of_locallyClosedAt gas Δr τ₁ (.ret (.bound 0)) 0 (d + 2) 2 closedτ₁
      (by omega) (by omega)
  have argEq : B = B' := by
    rw [argBase]
    simp only [B', openτ₁, shiftτ₁]
    apply interpFuel_eq_of_agreeOn
    intro x hx
    simp only [emptyτ₁, Term.support, Value.support, Finset.union_empty, Finset.notMem_empty] at hx
  have quantified : m ⊨ Formula.all (A ⇒ᶜ R) ↔ m ⊨ Formula.all (A ⇒ᶜ S) := by
    apply Formula.models_all_impl_congr
      (by rw [Formula.freeAtoms_impl]; exact Finset.union_subset scopeA scopeR)
      (by rw [Formula.freeAtoms_impl]; exact Finset.union_subset scopeA scopeS)
    refine ⟨∅, ?_⟩
    intro z _ freshZ n href hdom hA
    have freshZΔ' : z ∉ Δ'.domain := fun hz => freshZ (scopeΔ hz)
    have worldZ : n ⊨ Interp.basicWorld (Δ'.insert z (.arrow τ₁.erase τ₂.erase)) := by
      have h := Interp.models_basicWorld_resultFirst_openAt wfOpen typedOpen
        (Formula.models_kripke href world) freshZΔ' hA
      simpa only [ContextType.erase, υ₁, υ₂, erase_openManyAt] using h
    have scopeRN : ((B.openAt 1 z) -∗[1] (C.openAt 1 z)).freeAtoms ⊆ n.domain := by
      simpa only [R, Formula.openAt] using openedScope R scopeR z hdom
    have scopeSN : ((B'.openAt 1 z) -∗[1] (C'.openAt 1 z)).freeAtoms ⊆ n.domain := by
      simpa only [S, Formula.openAt] using openedScope S scopeS z hdom
    have freshZR : z ∉ (Δr.insertMany d η T).domain := by
      intro hz
      apply freshZΔ'
      simp only [Δ', BasicEnv.domain_insertMany] at hz ⊢
      exact Finset.union_subset_union scopeRΔ (Finset.Subset.refl _) hz
    have freshZΔr : z ∉ Δr.domain := by
      intro hz
      exact freshZR (by rw [BasicEnv.domain_insertMany]; exact Finset.mem_union_left _ hz)
    have closedB : (B.openAt 1 z).freeAtoms = ∅ := by
      rw [argBase, interpFuel_openAt_fresh gas 2 Δr τ₁ (.ret (.bound 0)) 1 z
        (closedτ₁.mono (by omega)) (by simp [Term.locallyClosedAt, Value.locallyClosedAt])
        freshZΔr (by rw [emptyτ₁]; exact Finset.notMem_empty _) (by simp [Term.support, Value.support])]
      apply Finset.Subset.antisymm _ (Finset.empty_subset _)
      simpa only [emptyτ₁, Term.support, Value.support, Finset.union_empty] using
        freeAtoms_interpFuel_subset gas 2 Δr τ₁ (.ret (.bound 0))
    change n ⊨ ((B.openAt 1 z) -∗[1] (C.openAt 1 z)) ↔
      n ⊨ ((B'.openAt 1 z) -∗[1] (C'.openAt 1 z))
    rw [← argEq]
    apply Formula.models_wand_congr_full closedB
      (Finset.Subset.trans (by rw [Formula.freeAtoms_wand]; exact Finset.subset_union_right) scopeRN)
      (Finset.Subset.trans (by rw [Formula.freeAtoms_wand]; exact Finset.subset_union_right) scopeSN)
    refine ⟨∅, ?_⟩
    intro ι _ _ freshN a compat adom hB
    let y := ι 0
    have opening (P : Formula) : P.openMany 1 ι = P.openAt 0 y := by rfl
    rw [opening] at hB ⊢
    let p := Capability.product a n compat
    have freshY : y ∉ n.domain := by
      intro hy
      exact Finset.disjoint_left.1 freshN
        (Finset.mem_image.2 ⟨0, Finset.mem_univ _, rfl⟩) hy
    have freshYΔ' : y ∉ Δ'.domain ∪ {z} := by
      intro hy
      apply freshY
      rw [hdom]
      exact Finset.union_subset_union scopeΔ (Finset.Subset.refl _) hy
    have freshYR : y ∉ (Δr.insertMany d η T).domain ∪ {z} := by
      intro hy
      apply freshYΔ'
      simp only [Δ', BasicEnv.domain_insertMany] at hy ⊢
      exact Finset.union_subset_union (Finset.union_subset_union scopeRΔ (Finset.Subset.refl _))
        (Finset.Subset.refl _) hy
    have worldP := Formula.models_kripke (Capability.product_refines_right compat) worldZ
    have hRaw : p ⊨ (B.openAt 1 z).openAt 0 y :=
      Formula.models_kripke (Capability.product_refines_left compat) hB
    have w := models_basicWorld_insert_of_opened_ret (τ := (τ₁.shiftFrom 0).shiftFrom 0)
      (Δ := Δr) (Δ' := Δ'.insert z (.arrow τ₁.erase τ₂.erase)) (gas := gas) (n := d + 2)
      (d := d) (η := η) worldP freshR freshZΔr
      (fun hy => freshYR (Finset.mem_union_left _ (by
        rw [BasicEnv.domain_insertMany]; exact Finset.mem_union_left _ hy))) hRaw
    have wR : p ⊨ Interp.basicWorld (((Δr.insertMany d η T).insert z
        (.arrow τ₁.erase τ₂.erase)).insert y τ₁.erase) := by
      apply Interp.models_basicWorld_of_subset (((embedR.insertMany d η T).insert z _).insert y _)
      simpa only [erase_shiftFrom] using w
    have eq := OpensInputs.applicationChild (gas := gas) (d := d) (m := p) (Δ := Δr)
      (τ := τ₂) (η := η) (T := T) (U := τ₁.erase)
      ih lower₂ wfCodR inj freshR freshZR freshYR wR
    rwa [codEq] at eq
  simp only [interpFuel, Formula.openManyAt_and, Formula.openManyAt_all,
    Formula.openManyAt_impl, Formula.openManyAt_wand, ContextType.openManyAt_wand, Nat.zero_add]
  simp only [Interp.resultFirst_relevantEnv]
  rw [graph, Formula.models_and_iff, Formula.models_and_iff]
  have hg' : m ⊨ (Interp.guard d Δr τ e).openManyAt 0 d η ↔
      m ⊨ Interp.guard 0 Δr' (.wand υ₁ υ₂) e' := by
    simpa only [τ, Δr, Δr', Δ', υ₁, υ₂, e', ContextType.openManyAt_wand, Nat.zero_add] using hg
  change (m ⊨ (Interp.guard d Δr τ e).openManyAt 0 d η ∧ m ⊨ Formula.all (A ⇒ᶜ R)) ↔
    (m ⊨ Interp.guard 0 Δr' (.wand υ₁ υ₂) e' ∧ m ⊨ Formula.all (A ⇒ᶜ S))
  rw [hg', quantified]

/-- Persistence conversion retains the same observed projection, in addition
to the returned-result child's semantic equivalence. -/
private theorem OpensInputs.persist {gas : Nat} {τ : ContextType}
    (ih : OpensInputs gas (τ.shiftFrom 0)) : OpensInputs (gas + 1) (□ τ) := by
  intro lower m Δ e d η T wf inj fresh support typed world
  have lo : τ.measure ≤ gas := by simp only [measure] at lower; omega
  let Δr := Interp.relevantEnv Δ (.persist τ) e
  let Δ' := Δ.insertMany d η T
  let υ := τ.openManyAt 0 d η
  let e' := e.openManyAt 0 d η
  let Δr' := Interp.relevantEnv Δ' (.persist υ) e'
  let A := Interp.resultFirst Δ' (.persist υ) e'
  let P := (interpFuel gas (d + 1) Δr (τ.shiftFrom 0) (.ret (.bound 0))).openManyAt 1 d η
  let Q := interpFuel gas 1 Δr' (υ.shiftFrom 0) (.ret (.bound 0))
  have scopeΔ := (Interp.models_basicWorld_iff m Δ').1 world |>.1
  have wf' : (ContextType.persist τ).WellFormedAt (0 + d) Δ.domain := by
    simpa only [Nat.zero_add] using wf
  have wfOpen : (ContextType.persist υ).WellFormed Δ'.domain := by
    simpa only [Δ', υ, ContextType.openManyAt_persist, BasicEnv.domain_insertMany]
      using wf'.openManyAt η inj fresh
  have typedOpen : Δ' ⊢ₑ e' ⋮ (ContextType.persist υ).erase := by
    simpa only [Δ', e', υ, ContextType.erase, erase_openManyAt] using typed
  have hg := Interp.models_guard_relevant_openManyAt_iff (n := 0)
    wf' inj fresh support typed world
  have graph : (Interp.resultFirst Δ (.persist τ) e).openManyAt 1 d η = A := by
    simpa only [A, Δ', e', υ, ContextType.openManyAt_persist] using
      Interp.resultFirst_openManyAt_inputs Δ (.persist τ) e 0 d η T inj fresh
        (fun i hx => fresh i (wf.freeAtoms_subset hx)) (fun i hx => fresh i (support hx))
  have scopeA : A.freeAtoms ⊆ m.domain := by
    have hs := Interp.freeAtoms_resultFirst_relevant_subset Δ' (.persist υ) e'
    rw [Interp.resultFirst_relevantEnv] at hs
    exact Finset.Subset.trans hs
      (Finset.Subset.trans (Finset.union_subset wfOpen.freeAtoms_subset typedOpen.support_subset) scopeΔ)
  have scopeP : P.freeAtoms ⊆ m.domain := by
    apply Finset.Subset.trans (Formula.freeAtoms_openManyAt_subset _ _ _ _)
    apply Finset.Subset.trans _ scopeΔ
    rw [BasicEnv.domain_insertMany]
    apply Finset.union_subset_union _ (Finset.Subset.refl _)
    exact Finset.Subset.trans (freeAtoms_interpFuel_subset _ _ _ _ _)
      (by simpa [Term.support, Value.support] using wf.freeAtoms_subset)
  have scopeQ : Q.freeAtoms ⊆ m.domain := by
    apply Finset.Subset.trans (freeAtoms_interpFuel_subset _ _ _ _ _)
    simpa [Term.support, Value.support] using Finset.Subset.trans wfOpen.freeAtoms_subset scopeΔ
  have scopesR := Interp.scope_relevantEnv wf.freeAtoms_subset support
  have scopesR' := Interp.scope_relevantEnv wfOpen.freeAtoms_subset typedOpen.support_subset
  have wfR : τ.WellFormedAt d Δr.domain := wf.regularize scopesR.1
  have sameτ : (τ.shiftFrom 0).openManyAt 1 d η = υ.shiftFrom 0 :=
    openManyAt_shiftFrom_of_le τ 0 0 d η (Nat.zero_le 0)
  have sameE : (Term.ret (.bound 0)).openManyAt 1 d η = .ret (.bound 0) := by
    have aux : ∀ d (η : Fin d → Atom),
        (Term.ret (.bound 0)).openManyAt 1 d η = .ret (.bound 0) := by
      intro d η
      induction d with
      | zero => rfl
      | succ d ih =>
          rw [Term.openManyAt, ih]
          simp [Term.openAt, Value.openAt, show (0 : Nat) ≠ 1 + d by omega]
    exact aux d η
  have sameSupport : P.support = Q.support := by
    have hs := support_interpFuel_openManyAt_eq (gas := gas) (n := d + 1) (n' := 1)
      (Δ := Δr) (Δ' := Δr') (τ := τ.shiftFrom 0) (e := .ret (.bound 0))
      (η := η) (k := 1)
      (by simpa only [measure_shiftFrom] using lo)
      (by simpa only [measure_openManyAt, measure_shiftFrom] using lo)
      (by simpa only [freeAtoms_shiftFrom] using scopesR.1)
      (by simp [Term.support, Value.support])
      (by simpa only [sameτ, freeAtoms_shiftFrom] using scopesR'.1)
      (by simp only [sameE, Term.support, Value.support]; exact Finset.empty_subset _)
      inj (by simp [Term.support, Value.support])
    simpa only [sameτ, sameE] using hs
  have embedR : Δr.Subset Δ := by
    intro x U hx
    change (Δ.restrict (Interp.relevantAtoms (.persist τ) e)).lookup x = some U at hx
    rw [BasicEnv.lookup_restrict] at hx
    split_ifs at hx
    exact hx
  have freshR : ∀ i, η i ∉ Δr.domain := by
    intro i hi
    exact fresh i (Finset.inter_subset_left (by simpa only [Δr, Interp.relevantEnv_domain] using hi))
  have envEq : interpFuel gas 1 (Δr.insertMany d η T) (υ.shiftFrom 0) (.ret (.bound 0)) = Q := by
    apply interpFuel_eq_of_agreeOn
    have agree := Interp.relevantEnv_openManyAt_agreeOn (Δ := Δ) (τ := .persist τ) (υ := τ)
      (e := e) (T := T) inj (Finset.Subset.refl _)
      (by rw [ContextType.openManyAt_persist]; exact Finset.Subset.refl _)
    simpa only [freeAtoms_shiftFrom, Term.support, Value.support, Finset.union_empty,
      Δr, Δr', Δ', υ, e', ContextType.openManyAt_persist] using agree
  have quantified : m ⊨ Formula.all (A ⇒ᶜ □ P) ↔ m ⊨ Formula.all (A ⇒ᶜ □ Q) := by
    apply Formula.models_all_impl_congr
      (by rw [Formula.freeAtoms_impl, Formula.freeAtoms_persist]; exact Finset.union_subset scopeA scopeP)
      (by rw [Formula.freeAtoms_impl, Formula.freeAtoms_persist]; exact Finset.union_subset scopeA scopeQ)
    refine ⟨∅, ?_⟩
    intro z _ freshZ n href hdom hA
    have freshΔ' : z ∉ Δ'.domain := fun hz => freshZ (scopeΔ hz)
    have worldN := Interp.models_basicWorld_resultFirst_openAt wfOpen typedOpen
      (Formula.models_kripke href world) freshΔ' hA
    have worldR : n ⊨ Interp.basicWorld ((Δr.insertMany d η T).insert z τ.erase) := by
      apply Interp.models_basicWorld_of_subset ((embedR.insertMany d η T).insert z τ.erase)
      simpa only [ContextType.erase, υ, erase_openManyAt] using worldN
    have freshZR : z ∉ (Δr.insertMany d η T).domain := by
      intro hz
      apply freshΔ'
      simp only [Δ', BasicEnv.domain_insertMany] at hz ⊢
      exact Finset.union_subset_union
        (by simp only [Δr, Interp.relevantEnv_domain]; exact Finset.inter_subset_left)
        (Finset.Subset.refl _) hz
    have equiv := ih.resultChild lo wfR inj freshR freshZR worldR
    rw [envEq] at equiv
    change n ⊨ (□ (P.openAt 0 z)) ↔ n ⊨ (□ (Q.openAt 0 z))
    apply Formula.models_persist_congr _ equiv
    apply congrArg LogicVar.freeAtomSet
    change (P.openAt 0 z).support = (Q.openAt 0 z).support
    have hsP := Formula.supportAt_openAt P 0 0 z
    have hsQ := Formula.supportAt_openAt Q 0 0 z
    change (P.openAt 0 z).support = LogicVar.openSupport 0 z P.support at hsP
    change (Q.openAt 0 z).support = LogicVar.openSupport 0 z Q.support at hsQ
    rw [hsP, hsQ, sameSupport]
  simp only [interpFuel, Formula.openManyAt_and, Formula.openManyAt_all,
    Formula.openManyAt_impl, Formula.openManyAt_persist, ContextType.openManyAt_persist, Nat.zero_add]
  simp only [Interp.resultFirst_relevantEnv]
  rw [graph, Formula.models_and_iff, Formula.models_and_iff]
  have hg' : m ⊨ (Interp.guard d Δr (.persist τ) e).openManyAt 0 d η ↔
      m ⊨ Interp.guard 0 Δr' (.persist υ) e' := by
    simpa only [Δr, Δr', Δ', υ, e', ContextType.openManyAt_persist, Nat.zero_add] using hg
  change (m ⊨ (Interp.guard d Δr (.persist τ) e).openManyAt 0 d η ∧ m ⊨ Formula.all (A ⇒ᶜ □ P)) ↔
    (m ⊨ Interp.guard 0 Δr' (.persist υ) e' ∧ m ⊨ Formula.all (A ⇒ᶜ □ Q))
  rw [hg', quantified]

/-- Open all external inputs at once, retaining the named input world's
typing and the complete nondeterministic result graph. -/
theorem models_interpFuel_openManyAt_iff
    {m : Capability} {Δ : BasicEnv} {τ : ContextType} {e : Term}
    {gas d : Nat} {η : Fin d → Atom} {T : Fin d → SimpleType}
    (lower : τ.measure ≤ gas) (wf : τ.WellFormedAt d Δ.domain)
    (inj : Function.Injective η) (fresh : ∀ i, η i ∉ Δ.domain)
    (support : e.support ⊆ Δ.domain)
    (typed : Δ.insertMany d η T ⊢ₑ e.openManyAt 0 d η ⋮ τ.erase)
    (world : m ⊨ Interp.basicWorld (Δ.insertMany d η T)) :
    m ⊨ (interpFuel gas d Δ τ e).openManyAt 0 d η ↔
      m ⊨ interpFuel gas 0 (Δ.insertMany d η T) (τ.openManyAt 0 d η) (e.openManyAt 0 d η) := by
  have all : ∀ gas τ, OpensInputs gas τ := by
    intro gas
    induction gas with
    | zero =>
        intro τ lower
        have := τ.measure_pos
        omega
    | succ gas ih =>
        intro τ
        cases τ with
        | «over» b q => exact OpensInputs.over (gas + 1) b q
        | under b q => exact OpensInputs.under (gas + 1) b q
        | inter τ₁ τ₂ => exact OpensInputs.inter (ih τ₁) (ih τ₂)
        | union τ₁ τ₂ => exact OpensInputs.union (ih τ₁) (ih τ₂)
        | sum τ₁ τ₂ => exact OpensInputs.sum (ih _) (ih _)
        | arrow τ₁ τ₂ => exact OpensInputs.arrow ih
        | wand τ₁ τ₂ => exact OpensInputs.wand ih
        | persist τ => exact OpensInputs.persist (ih _)
  exact all gas τ lower m Δ e d η T wf inj fresh support typed world

/-- The function result and argument binders normalize to a named
application of the opened dependent codomain. -/
theorem models_interpFuel_app_bound_openAt_iff
    {m : Capability} {Δ : BasicEnv} {τ : ContextType} {gas : Nat}
    {y z : Atom} {U : SimpleType} (lower : τ.measure ≤ gas)
    (wf : τ.WellFormedAt 1 Δ.domain) (freshY : y ∉ Δ.domain)
    (freshZ : z ∉ Δ.domain) (apart : y ≠ z)
    (world : m ⊨ Interp.basicWorld ((Δ.insert z (.arrow U τ.erase)).insert y U)) :
    m ⊨ ((interpFuel gas 2 Δ (τ.shiftFrom 1) (.app (.bound 1) (.bound 0))).openAt 1 z).openAt 0 y ↔
      m ⊨ interpFuel gas 0 ((Δ.insert z (.arrow U τ.erase)).insert y U)
        (τ.openAt 0 y) (.app (.free z) (.free y)) := by
  let η : Fin 2 → Atom := Fin.cons y (Fin.cons z Fin.elim0)
  let T : Fin 2 → SimpleType := Fin.cons U (Fin.cons (.arrow U τ.erase) Fin.elim0)
  have inj : Function.Injective η := by
    intro i j h
    fin_cases i <;> fin_cases j <;> simp_all [η]
  have fresh : ∀ i, η i ∉ Δ.domain := by
    intro i
    fin_cases i
    · exact freshY
    · exact freshZ
  have env : Δ.insertMany 2 η T = (Δ.insert z (.arrow U τ.erase)).insert y U := by
    simpa only [BasicEnv.insertMany] using BasicEnv.insertMany_two Δ 0 Fin.elim0 Fin.elim0
      y z U (.arrow U τ.erase) apart (fun i => Fin.elim0 i) (fun i => Fin.elim0 i)
  have typeEq : (τ.shiftFrom 1).openManyAt 0 2 η = τ.openAt 0 y := by
    have h := shift_openManyAt_two_eq (d := 0) (η := Fin.elim0) (Δ := Δ)
      (by simpa only [Nat.add_zero] using wf)
      (fun i => Fin.elim0 i) (fun i => Fin.elim0 i)
      (by simpa using freshZ) apart (fun i => Fin.elim0 i)
    exact h
  have typed : Δ.insertMany 2 η T ⊢ₑ
      (Term.app (.bound 1) (.bound 0)).openManyAt 0 2 η ⋮ (τ.shiftFrom 1).erase := by
    rw [env, Term.openManyAt_two_app 0, erase_shiftFrom]
    exact BasicTermTyp.app
      (BasicValTyp.free (by rw [BasicEnv.lookup_insert_of_ne _ _ apart.symm, BasicEnv.lookup_insert]))
      (BasicValTyp.free (BasicEnv.lookup_insert _ _ _))
  have h := models_interpFuel_openManyAt_iff (gas := gas) (d := 2) (T := T)
    (by simpa only [measure_shiftFrom] using lower) (wf.shiftFrom 1) inj fresh
    (by simp [Term.support, Value.support]) typed (by rwa [env])
  rw [env, typeEq, Term.openManyAt_two_app 0] at h
  have opening := Formula.openManyAt_two
    (interpFuel gas 2 Δ (τ.shiftFrom 1) (.app (.bound 1) (.bound 0)))
    0 Fin.elim0 y z apart (fun i => Fin.elim0 i) (fun i => Fin.elim0 i)
  change ((interpFuel gas 2 Δ (τ.shiftFrom 1) (.app (.bound 1) (.bound 0))).openAt 1 z).openAt 0 y =
    (interpFuel gas 2 Δ (τ.shiftFrom 1) (.app (.bound 1) (.bound 0))).openManyAt 0 2 η at opening
  rwa [← opening] at h

/-- The complete codomain interpretation uses fuel fixed by the type. -/
theorem models_interp_app_bound_openAt_iff
    {m : Capability} {Δ : BasicEnv} {τ : ContextType} {y z : Atom} {U : SimpleType}
    (wf : τ.WellFormedAt 1 Δ.domain) (freshY : y ∉ Δ.domain)
    (freshZ : z ∉ Δ.domain) (apart : y ≠ z)
    (world : m ⊨ Interp.basicWorld ((Δ.insert z (.arrow U τ.erase)).insert y U)) :
    m ⊨ ((interpFuel τ.measure 2 Δ (τ.shiftFrom 1) (.app (.bound 1) (.bound 0))).openAt 1 z).openAt 0 y ↔
      m ⊨ interp ((Δ.insert z (.arrow U τ.erase)).insert y U)
        (τ.openAt 0 y) (.app (.free z) (.free y)) := by
  simpa only [interp, measure_openAt] using
    models_interpFuel_app_bound_openAt_iff (Nat.le_refl τ.measure) wf freshY freshZ apart world

/-- Pointwise equality of instantiated terms preserves their entire type
interpretation, even when their syntactic free supports differ. -/
theorem models_interp_of_instantiate_eq_iff
    {m : Capability} {Δ : BasicEnv} {τ : ContextType} {e₁ e₂ : Term}
    (wf : τ.WellFormed Δ.domain) (typed₁ : Δ ⊢ₑ e₁ ⋮ τ.erase)
    (typed₂ : Δ ⊢ₑ e₂ ⋮ τ.erase) (world : m ⊨ Interp.basicWorld Δ)
    (same : ∀ σ, σ ∈ m →
      Interp.instantiateTerm e₁ σ.toAssignment = Interp.instantiateTerm e₂ σ.toAssignment) :
    m ⊨ interp Δ τ e₁ ↔ m ⊨ interp Δ τ e₂ := by
  have scope := (Interp.models_basicWorld_iff m Δ).1 world |>.1
  have total : m ⊨ Interp.total e₁ ↔ m ⊨ Interp.total e₂ := by
    rw [Interp.models_total_iff typed₁.locallyClosed, Interp.models_total_iff typed₂.locallyClosed]
    constructor
    · rintro ⟨_, h⟩
      exact ⟨Finset.Subset.trans typed₂.support_subset scope,
        fun σ hσ => same σ hσ ▸ h σ hσ⟩
    · rintro ⟨_, h⟩
      exact ⟨Finset.Subset.trans typed₁.support_subset scope,
        fun σ hσ => (same σ hσ).symm ▸ h σ hσ⟩
  have results : Interp.ResultsEquivOn τ.freeAtoms m m e₁ e₂ := by
    intro s v
    constructor
    · rintro ⟨σ, hσ, hs, hv⟩
      exact ⟨σ, hσ, hs, same σ hσ ▸ hv⟩
    · rintro ⟨σ, hσ, hs, hv⟩
      exact ⟨σ, hσ, hs, (same σ hσ).symm ▸ hv⟩
  constructor
  · intro h
    exact models_interp_of_resultsEquivOn wf wf typed₁ typed₂ world
      (total.1 (models_interp_total h)) (fun _ _ => rfl) results h
  · intro h
    exact models_interp_of_resultsEquivOn wf wf typed₂ typed₁ world
      (total.2 (models_interp_total h)) (fun _ _ => rfl) results.symm h

/-- A function argument does not observe the fresh function-result binder.
Its opened interpretation is the ordinary interpretation of its fresh name. -/
theorem models_interp_arg_bound_openAt_iff
    {m : Capability} {Δ : BasicEnv} {τ : ContextType} {gas : Nat} {y z : Atom}
    (lower : τ.measure ≤ gas) (wf : τ.WellFormed Δ.domain)
    (freshY : y ∉ Δ.domain) (freshZ : z ∉ Δ.domain) :
    m ⊨ ((interpFuel gas 2 Δ ((τ.shiftFrom 0).shiftFrom 0) (.ret (.bound 0))).openAt 1 z).openAt 0 y ↔
      m ⊨ interp (Δ.insert y τ.erase) τ (.ret (.free y)) := by
  simp only [shiftFrom_eq_of_locallyClosedAt τ 0 wf.locallyClosedAt]
  rw [interpFuel_openAt_fresh gas 2 Δ τ (.ret (.bound 0)) 1 z
    (wf.locallyClosedAt.mono (by omega)) (by simp [Term.locallyClosedAt, Value.locallyClosedAt])
    freshZ (fun hz => freshZ (wf.freeAtoms_subset hz)) (by simp [Term.support, Value.support])]
  rw [models_interpFuel_ret_bound_openAt_iff wf freshY]
  rw [interpFuel_eq_of_measure_le gas τ.measure 0 (Δ.insert y τ.erase) τ (.ret (.free y)) lower
    (Nat.le_refl _)]
  rfl

end ContextTypes.ContextType
