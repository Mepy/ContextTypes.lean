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

/-- Apply an ordinary function denotation to an existing argument binding. -/
theorem models_arrow_app_named
    {m : Capability} {Δ : BasicEnv} {τₓ τ : ContextType} {v : Value} {x : Atom}
    (wf : (τ.openAt 0 x).WellFormed Δ.domain ∧ Δ ⊢ₑ (.app v (.free x)) ⋮ (τ.openAt 0 x).erase)
    (wf₁ : (.arrow τₓ τ : ContextType).WellFormed Δ.domain ∧ Δ ⊢ₑ (.ret v) ⋮ (.arrow τₓ τ : ContextType).erase)
    (wf₂ : τₓ.WellFormed Δ.domain ∧ Δ ⊢ₑ (.ret (.free x)) ⋮ τₓ.erase)
    (fresh : x ∉ v.support ∪ τₓ.freeAtoms ∪ τ.freeAtoms)
    (world : m ⊨ Interp.basicWorld Δ)
    (fnM : m ⊨ ContextType.interp Δ (.arrow τₓ τ) (.ret v))
    (argM : m ⊨ ContextType.interp Δ τₓ (.ret (.free x))) :
    m ⊨ ContextType.interp Δ (τ.openAt 0 x) (.app v (.free x)) := by
  let Δ₀ := Δ.erase x
  let gas := max τₓ.measure τ.measure
  let Δr := Interp.relevantEnv Δ₀ (.arrow τₓ τ) (.ret v)
  let A := Interp.resultFirst Δ₀ (.arrow τₓ τ) (.ret v)
  let B := ContextType.interpFuel gas 2 Δ₀ ((τₓ.shiftFrom 0).shiftFrom 0) (.ret (.bound 0))
  let C := ContextType.interpFuel gas 2 Δ₀ (τ.shiftFrom 1) (.app (.bound 1) (.bound 0))
  have fresh' : (x ∉ v.support ∧ x ∉ τₓ.freeAtoms) ∧ x ∉ τ.freeAtoms := by
    simpa only [Finset.mem_union, not_or] using fresh
  have scopeΔ : Δ.domain ⊆ m.domain := (Interp.models_basicWorld_iff m Δ).1 world |>.1
  have lookupX : Δ.lookup x = some τₓ.erase := by
    cases wf₂.2 with
    | ret h => cases h with | free h => exact h
  have presentX : x ∈ m.domain := scopeΔ ((BasicEnv.mem_domain_iff Δ x).2 ⟨_, lookupX⟩)
  have envX : Δ₀.insert x τₓ.erase = Δ := BasicEnv.insert_erase_of_lookup lookupX
  have freshX : x ∉ Δ₀.domain := by simp [Δ₀, BasicEnv.domain_erase]
  have typed₀ : Δ₀ ⊢ₑ (.ret v) ⋮ (.arrow τₓ τ : ContextType).erase := by
    apply wf₁.2.of_agreeOn
    intro y hy
    apply (BasicEnv.lookup_erase_of_ne Δ _).symm
    intro h
    subst y
    exact fresh'.1.1 hy
  have wf₀ : (.arrow τₓ τ : ContextType).WellFormed Δ₀.domain := by
    apply wf₁.1.regularize
    intro y hy
    rw [BasicEnv.domain_erase, Finset.mem_erase]
    refine ⟨?_, wf₁.1.freeAtoms_subset hy⟩
    intro h
    subst y
    have hy' : x ∈ τₓ.freeAtoms ∨ x ∈ τ.freeAtoms := by
      simpa only [ContextType.freeAtoms, Finset.mem_union] using hy
    exact hy'.elim fresh'.1.2 fresh'.2
  have embed₀ : Δ₀.Subset Δ := by
    intro y T hy
    by_cases h : y = x
    · subst y; simp [Δ₀] at hy
    · rwa [BasicEnv.lookup_erase_of_ne Δ h] at hy
  have world₀ := Interp.models_basicWorld_of_subset embed₀ world
  have same₀ : BasicEnv.AgreeOn ((.arrow τₓ τ : ContextType).freeAtoms ∪ (.ret v : Term).support) Δ₀ Δ := by
    intro y hy
    rw [BasicEnv.lookup_erase_of_ne Δ]
    intro h
    subst y
    have hy' : (x ∈ τₓ.freeAtoms ∨ x ∈ τ.freeAtoms) ∨ x ∈ v.support := by
      simpa only [ContextType.freeAtoms, Term.support, Finset.mem_union] using hy
    exact hy'.elim (fun h => h.elim fresh'.1.2 fresh'.2) fresh'.1.1
  have fn₀ : m ⊨ ContextType.interp Δ₀ (.arrow τₓ τ) (.ret v) := by
    rw [ContextType.interp_eq_of_agreeOn same₀]
    exact fnM
  have agree (υ : ContextType) (e : Term)
      (hs : υ.freeAtoms ∪ e.support ⊆ (.arrow τₓ τ : ContextType).freeAtoms ∪ (.ret v : Term).support) :
      BasicEnv.AgreeOn (υ.freeAtoms ∪ e.support) Δr Δ₀ := by
    intro y hy
    simp only [Δr, Interp.relevantEnv, BasicEnv.lookup_restrict, Interp.relevantAtoms, if_pos (hs hy)]
  have envB : ContextType.interpFuel gas 2 Δr ((τₓ.shiftFrom 0).shiftFrom 0) (.ret (.bound 0)) = B := by
    apply ContextType.interpFuel_eq_of_agreeOn
    apply agree
    simp [ContextType.freeAtoms, Term.support, Value.support]
  have envC : ContextType.interpFuel gas 2 Δr (τ.shiftFrom 1) (.app (.bound 1) (.bound 0)) = C := by
    apply ContextType.interpFuel_eq_of_agreeOn
    apply agree
    simp only [ContextType.freeAtoms_shiftFrom, Term.support, Value.support, Finset.union_empty, ContextType.freeAtoms]
    exact Finset.Subset.trans Finset.subset_union_right Finset.subset_union_left
  have universal : m ⊨ Formula.all (A ⇒ᶜ Formula.all (B ⇒ᶜ C)) := by
    simp only [ContextType.interp, ContextType.measure, Nat.add_comm 1] at fn₀
    change m ⊨ ContextType.interpFuel (gas + 1) 0 Δ₀ (.arrow τₓ τ) (.ret v) at fn₀
    simp only [ContextType.interpFuel, Nat.zero_add, Interp.resultFirst_relevantEnv] at fn₀
    rw [envB, envC] at fn₀
    exact Formula.models_and_elim_right fn₀
  obtain ⟨z, hz⟩ := Finset.exists_nat_subset_range m.domain
  have freshZ : z ∉ m.domain := by
    intro h
    have := hz h
    simp at this
  have freshZΔ : z ∉ Δ.domain := fun h => freshZ (scopeΔ h)
  have freshZ₀ : z ∉ Δ₀.domain := by
    intro h
    apply freshZΔ
    rw [BasicEnv.domain_erase] at h
    exact (Finset.mem_erase.1 h).2
  have apart : x ≠ z := fun h => freshZ (h ▸ presentX)
  have total := ContextType.models_interp_total fnM
  have returns : ∀ σ, σ ∈ m → ∃ u, (Interp.instantiateTerm (.ret v) σ.toAssignment).reaches u :=
    fun σ hσ => (Interp.models_total_term wf₁.2.locallyClosed total hσ).reaches_result
  let g := Interp.resultCapability m m.domain (.ret v) z (Finset.Subset.refl _) returns
  have base : g.restrict m.domain = m := by
    rw [Interp.resultCapability_restrict, Capability.restrict_domain_self]
  have href : m ⊑ g := base.symm
  have graphFull := Interp.models_resultCapability m m.domain (.ret v) z
    (Finset.Subset.refl _) returns wf₁.2.locallyClosed
    (Finset.Subset.trans wf₁.2.support_subset scopeΔ) freshZ
  let X := Interp.relevantSupport Δ₀ (.arrow τₓ τ) (.ret v)
  have closedX : LogicVar.LocallyClosed X :=
    Interp.relevantSupport_locallyClosed _ _ _ wf₀.locallyClosedAt typed₀.locallyClosed
  have logicX : (.ret v : Term).logicSupport ⊆ X :=
    Interp.logicSupport_subset_relevantSupport _ _ _ typed₀.support_subset
  have scopeX : X ⊆ m.domain.image LogicVar.free := by
    rw [LogicVar.eq_image_free_of_locallyClosed closedX, Interp.freeAtomSet_relevantSupport]
    apply Finset.image_subset_image
    intro y hy
    apply scopeΔ
    have h := Finset.mem_inter.1 (by simpa only [Interp.relevantEnv_domain] using hy)
    rw [BasicEnv.domain_erase] at h
    exact (Finset.mem_erase.1 h.1).2
  have freshXZ : LogicVar.free z ∉ X := fun h => freshZ (by simpa using scopeX h)
  have graph : g ⊨ A.openAt 0 z := by
    rw [Interp.resultFirst_openAt _ _ _ z closedX typed₀.locallyClosed logicX freshXZ]
    exact Formula.models_kripke (Capability.restrict_refines g _)
      (Interp.models_resultAt_restrict_support (by intro k hk; simp at hk) scopeX logicX
        (by simpa using freshZ) graphFull)
  have outer := Formula.models_all_openAt_of_refines universal freshZ href (by rfl)
  have inner := Formula.models_impl_elim outer graph
  change g ⊨ Formula.all ((B ⇒ᶜ C).openAt 1 z) at inner
  have freshInner : x ∉ ((B ⇒ᶜ C).openAt 1 z).freeAtoms := by
    intro hx
    rcases Finset.mem_union.1 (Formula.freeAtoms_openAt_subset _ _ _ hx) with hx | hx
    · exact apart (Finset.mem_singleton.1 hx)
    · rw [Formula.freeAtoms_impl] at hx
      rcases Finset.mem_union.1 hx with hx | hx
      · have h := ContextType.freeAtoms_interpFuel_subset gas 2 Δ₀ _ _ hx
        exact fresh'.1.2 (by simpa [Term.support, Value.support] using h)
      · have h := ContextType.freeAtoms_interpFuel_subset gas 2 Δ₀ _ _ hx
        exact fresh'.2 (by simpa [Term.support, Value.support] using h)
  have opened := Formula.models_all_elim_named inner freshInner (Capability.refines_domain_subset href presentX)
  have argG : g ⊨ ContextType.interp (Δ₀.insert x τₓ.erase) τₓ (.ret (.free x)) := by
    rw [envX]
    exact Formula.models_kripke href argM
  have argBound := (ContextType.models_interp_arg_bound_openAt_iff
    (gas := gas) (z := z)
    (Nat.le_max_left τₓ.measure τ.measure) wf₀.1 freshX freshZ₀).2 argG
  have result := Formula.models_impl_elim opened argBound
  have worldZ := Interp.models_basicWorld_resultFirst_openAt wf₀ typed₀
    (Formula.models_kripke href world₀) freshZ₀ graph
  let Δ' := (Δ₀.insert z (.arrow τₓ.erase τ.erase)).insert x τₓ.erase
  have fullEq : Δ' = Δ.insert z (.arrow τₓ.erase τ.erase) := by
    dsimp only [Δ']
    rw [BasicEnv.insert_comm Δ₀ _ _ apart.symm, envX]
  have worldG := Formula.models_kripke href world
  have worldFull : g ⊨ Interp.basicWorld Δ' := by
    apply Interp.models_basicWorld_insert worldZ (Capability.refines_domain_subset href presentX)
    exact fun σ hσ => ((Interp.models_basicWorld_iff g Δ).1 worldG).2 σ hσ x τₓ.erase lookupX
  have namedFuel := (ContextType.models_interpFuel_app_bound_openAt_iff
    (gas := gas)
    (Nat.le_max_right τₓ.measure τ.measure) wf₀.2 freshX freshZ₀ apart worldFull).1 result
  have named : g ⊨ ContextType.interp Δ' (τ.openAt 0 x) (.app (.free z) (.free x)) := by
    rw [ContextType.interp]
    rw [← ContextType.interpFuel_eq_of_measure_le gas (τ.openAt 0 x).measure 0 Δ' _ _
      (by simpa only [ContextType.measure_openAt] using Nat.le_max_right τₓ.measure τ.measure) (Nat.le_refl _)]
    exact namedFuel
  have embed : Δ.Subset Δ' := by
    rw [fullEq]
    exact BasicEnv.subset_insert_of_fresh Δ z _ freshZΔ
  have typedActual : Δ' ⊢ₑ (.app v (.free x)) ⋮ (τ.openAt 0 x).erase := wf.2.weaken embed
  have typedNamed : Δ' ⊢ₑ (.app (.free z) (.free x)) ⋮ (τ.openAt 0 x).erase := by
    rw [ContextType.erase_openAt]
    exact BasicTermTyp.app
      (BasicValTyp.free (by rw [BasicEnv.lookup_insert_of_ne _ _ apart.symm, BasicEnv.lookup_insert]))
      (BasicValTyp.free (BasicEnv.lookup_insert _ _ _))
  have formed : (τ.openAt 0 x).WellFormed Δ'.domain := wf.1.mono (by
    rw [fullEq, BasicEnv.domain_insert]
    exact Finset.subset_union_right)
  have actual := (ContextType.models_interp_of_instantiate_eq_iff formed typedActual typedNamed worldFull
    (by
      intro σ hσ
      obtain ⟨u, hu, heval⟩ := Interp.models_resultAt_lookup
        (by intro k hk; simp at hk)
        (by
          rw [LogicVar.eq_image_free_of_locallyClosed (Interp.termLogicSupport_locallyClosed _ wf₁.2.locallyClosed),
            Interp.freeAtomSet_term_logicSupport]
          exact Finset.image_subset_image (Finset.Subset.trans wf₁.2.support_subset scopeΔ))
        (by simpa using freshZ) graphFull σ hσ
      have hv : u = Interp.instantiateValueAt v 0 σ.toAssignment := Term.ret.inj heval.ret_eq
      simp only [Interp.instantiateTerm, Interp.instantiateTermAt, Interp.instantiateValueAt,
        Store.toAssignment_lookup_free, hu, Option.getD_some]
      rw [hv])).2 named
  have sameEnv : BasicEnv.AgreeOn ((τ.openAt 0 x).freeAtoms ∪ (.app v (.free x) : Term).support) Δ' Δ := by
    intro y hy
    rw [fullEq, BasicEnv.lookup_insert_of_ne _ _]
    intro h
    subst y
    exact freshZΔ (Finset.union_subset wf.1.freeAtoms_subset wf.2.support_subset hy)
  rw [ContextType.interp_eq_of_agreeOn sameEnv] at actual
  apply (Formula.models_projection (m := m) (n := g) m.domain
    (Finset.Subset.trans (ContextType.freeAtoms_interp_subset _ _ _) (Finset.Subset.trans (Finset.union_subset wf.1.freeAtoms_subset wf.2.support_subset) scopeΔ))
    (by rw [Capability.restrict_domain_self, base])).2
  exact actual


/-- Construct an ordinary function denotation by checking its applications
at each fresh argument name, retaining any additional input observations. -/
theorem models_arrow_of_app_named
    {m : Capability} {Δ : BasicEnv} {τₓ τ : ContextType} {v : Value}
    (L : Finset Atom)
    (wf : (.arrow τₓ τ : ContextType).WellFormed Δ.domain)
    (typed : Δ ⊢ₑ (.ret v) ⋮ (.arrow τₓ τ : ContextType).erase)
    (world : m ⊨ Interp.basicWorld Δ)
    (app : ∀ y, y ∉ L → y ∉ Δ.domain → ∀ n, m ⊑ n →
      n ⊨ ContextType.interp (Δ.insert y τₓ.erase) τₓ (.ret (.free y)) →
      n ⊨ ContextType.interp (Δ.insert y τₓ.erase) (τ.openAt 0 y) (.app v (.free y))) :
    m ⊨ ContextType.interp Δ (.arrow τₓ τ) (.ret v) := by
  let gas := max τₓ.measure τ.measure
  let Δr := Interp.relevantEnv Δ (.arrow τₓ τ) (.ret v)
  let A := Interp.resultFirst Δ (.arrow τₓ τ) (.ret v)
  let B := ContextType.interpFuel gas 2 Δ ((τₓ.shiftFrom 0).shiftFrom 0) (.ret (.bound 0))
  let C := ContextType.interpFuel gas 2 Δ (τ.shiftFrom 1) (.app (.bound 1) (.bound 0))
  have scopeΔ : Δ.domain ⊆ m.domain := (Interp.models_basicWorld_iff m Δ).1 world |>.1
  have typedV : Δ ⊢ᵥ v ⋮ (.arrow τₓ.erase τ.erase) := by
    cases typed with
    | ret h => exact h
  have total : m ⊨ Interp.total (.ret v) := by
    apply (Interp.models_total_iff typed.locallyClosed).2
    refine ⟨Finset.Subset.trans typed.support_subset scopeΔ, ?_⟩
    intro σ hσ
    exact Term.MustTerminate.ret _
      (Interp.instantiateTerm_typed typed ((Interp.models_basicWorld_iff m Δ).1 world |>.2 σ hσ)).locallyClosed
  have guard := Interp.models_guard_relevant_of_world wf typed world total
  have agree (υ : ContextType) (u : Term)
      (hs : υ.freeAtoms ∪ u.support ⊆ (.arrow τₓ τ : ContextType).freeAtoms ∪ (.ret v : Term).support) :
      BasicEnv.AgreeOn (υ.freeAtoms ∪ u.support) Δr Δ := by
    intro x hx
    simp only [Δr, Interp.relevantEnv, BasicEnv.lookup_restrict,
      Interp.relevantAtoms, if_pos (hs hx)]
  have envB : ContextType.interpFuel gas 2 Δr ((τₓ.shiftFrom 0).shiftFrom 0)
      (.ret (.bound 0)) = B := by
    apply ContextType.interpFuel_eq_of_agreeOn
    apply agree
    simp [ContextType.freeAtoms, Term.support, Value.support]
  have envC : ContextType.interpFuel gas 2 Δr (τ.shiftFrom 1)
      (.app (.bound 1) (.bound 0)) = C := by
    apply ContextType.interpFuel_eq_of_agreeOn
    apply agree
    simp only [ContextType.freeAtoms_shiftFrom, Term.support, Value.support,
      Finset.union_empty, ContextType.freeAtoms]
    exact Finset.Subset.trans Finset.subset_union_right Finset.subset_union_left
  simp only [ContextType.interp, ContextType.measure, Nat.add_comm 1]
  change m ⊨ ContextType.interpFuel (gas + 1) 0 Δ (.arrow τₓ τ) (.ret v)
  simp only [ContextType.interpFuel, Nat.zero_add, Interp.resultFirst_relevantEnv]
  rw [envB, envC, Formula.models_and_iff]
  refine ⟨guard, ?_⟩
  have scopeA : A.freeAtoms ⊆ Δ.domain := by
    simp only [A, Interp.freeAtoms_resultFirst]
    exact Finset.union_subset
      (by rw [Interp.relevantEnv_domain]; exact Finset.inter_subset_left)
      typed.support_subset
  have scopeB : B.freeAtoms ⊆ Δ.domain := by
    apply Finset.Subset.trans (ContextType.freeAtoms_interpFuel_subset _ _ _ _ _)
    simpa [ContextType.freeAtoms_shiftFrom, Term.support, Value.support] using wf.1.freeAtoms_subset
  have scopeC : C.freeAtoms ⊆ Δ.domain := by
    apply Finset.Subset.trans (ContextType.freeAtoms_interpFuel_subset _ _ _ _ _)
    simpa [ContextType.freeAtoms_shiftFrom, Term.support, Value.support] using wf.2.freeAtoms_subset
  have scopeP : (A ⇒ᶜ Formula.all (B ⇒ᶜ C)).freeAtoms ⊆ m.domain := by
    simp only [Formula.freeAtoms_impl, Formula.freeAtoms_all]
    exact Finset.Subset.trans (Finset.union_subset scopeA (Finset.union_subset scopeB scopeC)) scopeΔ
  apply (Formula.models_all_iff_full m _).2
  refine ⟨scopeP, ∅, ?_⟩
  intro z _ freshZ n href hdom
  have scopeN : ((A ⇒ᶜ Formula.all (B ⇒ᶜ C)).openAt 0 z).freeAtoms ⊆ n.domain := by
    apply Finset.Subset.trans (Formula.freeAtoms_openAt_subset _ _ _)
    rw [hdom]
    exact Finset.union_subset (by simp) (Finset.Subset.trans scopeP Finset.subset_union_left)
  simp only [Formula.openAt]
  apply (Formula.models_impl_iff_of_scope n _ _ scopeN).2
  intro graph
  have freshZΔ : z ∉ Δ.domain := fun hz => freshZ (scopeΔ hz)
  have worldN := Interp.models_basicWorld_resultFirst_openAt wf typed
    (Formula.models_kripke href world) freshZΔ graph
  have scopeInner : ((B ⇒ᶜ C).openAt 1 z).freeAtoms ⊆ n.domain := by
    apply Finset.Subset.trans (Formula.freeAtoms_openAt_subset _ _ _)
    rw [hdom]
    exact Finset.union_subset (by simp)
      (Finset.Subset.trans (by simpa only [Formula.freeAtoms_impl] using Finset.union_subset scopeB scopeC)
        (Finset.Subset.trans scopeΔ Finset.subset_union_left))
  apply (Formula.models_all_iff_full n _).2
  refine ⟨scopeInner, L, ?_⟩
  intro y freshL freshY p hrefP hdomP
  have scopeP' : (((B ⇒ᶜ C).openAt 1 z).openAt 0 y).freeAtoms ⊆ p.domain := by
    apply Finset.Subset.trans (Formula.freeAtoms_openAt_subset _ _ _)
    rw [hdomP]
    exact Finset.union_subset (by simp) (Finset.Subset.trans scopeInner Finset.subset_union_left)
  simp only [Formula.openAt]
  apply (Formula.models_impl_iff_of_scope p _ _ scopeP').2
  intro arg
  have hrefMP := Capability.refines_trans href hrefP
  have freshYΔ : y ∉ Δ.domain := fun hy => freshY
    (Capability.refines_domain_subset href (scopeΔ hy))
  have apart : y ≠ z := by
    intro h
    subst y
    exact freshY (by rw [hdom]; simp)
  have named := (ContextType.models_interp_arg_bound_openAt_iff
    (Nat.le_max_left _ _) wf.1 freshYΔ freshZΔ).1 arg
  have hbody := app y freshL freshYΔ p hrefMP named
  have formedBody : (τ.openAt 0 y).WellFormed (Δ.insert y τₓ.erase).domain := by
    simpa only [BasicEnv.domain_insert, Finset.union_comm] using
      wf.2.openAt (fun h => freshYΔ (wf.2.freeAtoms_subset h))
  have typedBody : Δ.insert y τₓ.erase ⊢ₑ (.app v (.free y)) ⋮ (τ.openAt 0 y).erase := by
    rw [ContextType.erase_openAt]
    exact BasicTermTyp.app (typedV.weaken (BasicEnv.subset_insert_of_fresh Δ y _ freshYΔ))
      (BasicValTyp.free (BasicEnv.lookup_insert _ _ _))
  let Δ' := (Δ.insert z (.arrow τₓ.erase τ.erase)).insert y τₓ.erase
  have embed : (Δ.insert y τₓ.erase).Subset Δ' :=
    (BasicEnv.subset_insert_of_fresh Δ z _ freshZΔ).insert y τₓ.erase
  have typedApp : Δ' ⊢ₑ (.app v (.free y)) ⋮ (τ.openAt 0 y).erase := by
    rw [ContextType.erase_openAt]
    exact BasicTermTyp.app (typedV.weaken
      ((BasicEnv.subset_insert_of_fresh Δ z _ freshZΔ).trans
        (BasicEnv.subset_insert_of_fresh _ y _ (by simp [BasicEnv.domain_insert, freshYΔ, apart]))))
      (BasicValTyp.free (BasicEnv.lookup_insert _ _ _))
  have formed : (τ.openAt 0 y).WellFormed Δ'.domain :=
    formedBody.mono (by
      intro x hx
      obtain ⟨T, hT⟩ := (BasicEnv.mem_domain_iff _ x).1 hx
      exact (BasicEnv.mem_domain_iff _ x).2 ⟨T, embed x T hT⟩)
  have worldP := Formula.models_kripke hrefP worldN
  have worldArg := ContextType.models_interp_basicWorld named
  have worldFull : p ⊨ Interp.basicWorld Δ' := by
    apply Interp.models_basicWorld_insert worldP
      (by rw [hdomP]; simp)
    intro σ hσ
    apply ((Interp.models_basicWorld_iff p _).1 worldArg).2 σ hσ y τₓ.erase
    simp [Interp.relevantEnv, Interp.relevantAtoms, Term.support, Value.support]
  have sameEnv : BasicEnv.AgreeOn
      ((τ.openAt 0 y).freeAtoms ∪ (Term.app v (.free y)).support) (Δ.insert y τₓ.erase) Δ' := by
    intro x hx
    by_cases hxy : x = y
    · subst x; simp [Δ']
    · simp only [Δ', BasicEnv.lookup_insert_of_ne _ _ hxy]
      rw [BasicEnv.lookup_insert_of_ne _ _]
      intro hxz
      subst x
      have hs := Finset.union_subset formedBody.freeAtoms_subset typedBody.support_subset hx
      simp only [BasicEnv.domain_insert, Finset.mem_union, Finset.mem_singleton] at hs
      exact hs.elim (fun h => apart h.symm) freshZΔ
  have bodyFull : p ⊨ ContextType.interp Δ' (τ.openAt 0 y) (.app v (.free y)) := by
    rw [← ContextType.interp_eq_of_agreeOn sameEnv]
    exact hbody
  have graphP := Formula.models_kripke hrefP graph
  have lookup := Interp.models_resultFirst_openAt_lookup
    (Interp.relevantSupport_locallyClosed Δ (.arrow τₓ τ) (.ret v) wf.locallyClosedAt typed.locallyClosed)
    typed.locallyClosed (Interp.logicSupport_subset_relevantSupport Δ _ _ typed.support_subset)
    (by rw [Interp.free_mem_relevantSupport_iff]; exact fun hz => freshZΔ hz.1) graphP
  have typedNamed : Δ' ⊢ₑ (.app (.free z) (.free y)) ⋮ (τ.openAt 0 y).erase := by
    rw [ContextType.erase_openAt]
    exact BasicTermTyp.app
      (BasicValTyp.free (by rw [BasicEnv.lookup_insert_of_ne _ _ apart.symm, BasicEnv.lookup_insert]))
      (BasicValTyp.free (BasicEnv.lookup_insert _ _ _))
  have namedApp := (ContextType.models_interp_of_instantiate_eq_iff formed typedApp typedNamed worldFull
    (by
      intro σ hσ
      obtain ⟨u, hu, heval⟩ := lookup σ hσ
      have hv : u = Interp.instantiateValueAt v 0 σ.toAssignment := Term.ret.inj heval.ret_eq
      simp only [Interp.instantiateTerm, Interp.instantiateTermAt, Interp.instantiateValueAt,
        Store.toAssignment_lookup_free, hu, Option.getD_some]
      rw [hv])).1 bodyFull
  have opened := (ContextType.models_interpFuel_app_bound_openAt_iff
    (Nat.le_max_right _ _) wf.2 freshYΔ freshZΔ apart worldFull).2
    (by
      rw [ContextType.interpFuel_eq_of_measure_le gas (τ.openAt 0 y).measure 0 Δ'
        (τ.openAt 0 y) (.app (.free z) (.free y))
        (by simpa only [ContextType.measure_openAt] using Nat.le_max_right τₓ.measure τ.measure) (Nat.le_refl _)]
      exact namedApp)
  exact opened



/-- Apply an ordinary function to a value when its codomain is independent
of the argument binder.  A fresh argument alias preserves all input choices. -/
theorem models_arrow_app
    {m : Capability} {Δ : BasicEnv} {τₓ τ : ContextType} {v u : Value}
    (wf : (.arrow τₓ τ : ContextType).WellFormed Δ.domain)
    (closed : τ.LocallyClosed)
    (typedV : Δ ⊢ᵥ v ⋮ (.arrow τₓ.erase τ.erase))
    (typedU : Δ ⊢ᵥ u ⋮ τₓ.erase)
    (world : m ⊨ Interp.basicWorld Δ)
    (fn : m ⊨ ContextType.interp Δ (.arrow τₓ τ) (.ret v))
    (arg : m ⊨ ContextType.interp Δ τₓ (.ret u)) :
    m ⊨ ContextType.interp Δ τ (.app v u) := by
  have scopeΔ := (Interp.models_basicWorld_iff m Δ).1 world |>.1
  obtain ⟨x, hx⟩ := Finset.exists_nat_subset_range m.domain
  have freshX : x ∉ m.domain := by
    intro h
    have := hx h
    simp at this
  have freshΔ : x ∉ Δ.domain := fun h => freshX (scopeΔ h)
  have freshτ : x ∉ τ.freeAtoms := fun h => freshΔ (wf.2.freeAtoms_subset h)
  have sameτ : τ.openAt 0 x = τ := by
    have h := ContextType.openAt_shiftFrom_eq τ 0 x closed freshτ
    rwa [ContextType.shiftFrom_eq_of_locallyClosedAt τ 0 closed] at h
  have formed : τ.WellFormed Δ.domain :=
    (ContextType.wellFormedAt_iff_of_locallyClosedAt closed (Nat.zero_le 1) (Nat.le_refl 0)).1 wf.2
  have total := ContextType.models_interp_total arg
  have typedE := BasicTermTyp.ret typedU
  have returns : ∀ σ, σ ∈ m → ∃ w, (Interp.instantiateTerm (.ret u) σ.toAssignment).reaches w :=
    fun σ hσ => (Interp.models_total_term typedE.locallyClosed total hσ).reaches_result
  let g := Interp.resultCapability m m.domain (.ret u) x (Finset.Subset.refl _) returns
  let Δ' := Δ.insert x τₓ.erase
  have base : g.restrict m.domain = m := by
    rw [Interp.resultCapability_restrict, Capability.restrict_domain_self]
  have href : m ⊑ g := base.symm
  have worldG := Formula.models_kripke href world
  have graph := Interp.models_resultCapability m m.domain (.ret u) x
    (Finset.Subset.refl _) returns typedE.locallyClosed
    (Finset.Subset.trans typedE.support_subset scopeΔ) freshX
  have logic : (.ret u : Term).logicSupport ⊆ m.domain.image LogicVar.free := by
    rw [LogicVar.eq_image_free_of_locallyClosed (Interp.termLogicSupport_locallyClosed _ typedE.locallyClosed),
      Interp.freeAtomSet_term_logicSupport]
    exact Finset.image_subset_image (Finset.Subset.trans typedE.support_subset scopeΔ)
  have lookup := Interp.models_resultAt_lookup (by intro k hk; simp at hk) logic
    (by simpa using freshX) graph
  have worldFull : g ⊨ Interp.basicWorld Δ' := Interp.models_basicWorld_insert worldG
    (by simp [g])
    (Interp.models_resultAt_typed (by intro k hk; simp at hk) typedE.locallyClosed logic
      (by simpa using freshX) graph (Interp.models_basicTyping_of_world typedE worldG))
  have embed := BasicEnv.subset_insert_of_fresh Δ x τₓ.erase freshΔ
  have argActual : Δ' ⊢ₑ (.ret u) ⋮ τₓ.erase := typedE.weaken embed
  have argNamed : Δ' ⊢ₑ (.ret (.free x)) ⋮ τₓ.erase :=
    BasicTermTyp.ret (BasicValTyp.free (BasicEnv.lookup_insert _ _ _))
  have sameValue : ∀ σ, σ ∈ g →
      Interp.instantiateValueAt u 0 σ.toAssignment =
        Interp.instantiateValueAt (.free x) 0 σ.toAssignment := by
    intro σ hσ
    obtain ⟨w, hw, eval⟩ := lookup σ hσ
    have eq : w = Interp.instantiateValueAt u 0 σ.toAssignment := Term.ret.inj eval.ret_eq
    simp [Interp.instantiateValueAt, Store.toAssignment_lookup_free, hw, eq]
  have argG : g ⊨ ContextType.interp Δ' τₓ (.ret u) := by
    rw [ContextType.interp_eq_of_agreeOn (Δ₂ := Δ) (by
      intro y hy
      apply BasicEnv.lookup_insert_of_ne
      intro h
      subst y
      exact freshΔ (Finset.union_subset wf.1.freeAtoms_subset typedE.support_subset hy))]
    exact Formula.models_kripke href arg
  have argG' := (ContextType.models_interp_of_instantiate_eq_iff
    (wf.1.mono (by simp [Δ', BasicEnv.domain_insert])) argActual argNamed worldFull
    (fun σ hσ => by
      change Term.ret (Interp.instantiateValueAt u 0 σ.toAssignment) =
        Term.ret (Interp.instantiateValueAt (.free x) 0 σ.toAssignment)
      exact congrArg Term.ret (sameValue σ hσ))).1 argG
  have fnG : g ⊨ ContextType.interp Δ' (.arrow τₓ τ) (.ret v) := by
    rw [ContextType.interp_eq_of_agreeOn (Δ₂ := Δ) (by
      intro y hy
      apply BasicEnv.lookup_insert_of_ne
      intro h
      subst y
      exact freshΔ (Finset.union_subset wf.freeAtoms_subset (BasicTermTyp.ret typedV).support_subset hy))]
    exact Formula.models_kripke href fn
  have wfNamed : (τ.openAt 0 x).WellFormed Δ'.domain := by
    rw [sameτ]
    exact formed.mono (by simp [Δ', BasicEnv.domain_insert])
  have typedNamed : Δ' ⊢ₑ (.app v (.free x)) ⋮ (τ.openAt 0 x).erase := by
    rw [sameτ]
    exact BasicTermTyp.app (typedV.weaken embed) (BasicValTyp.free (BasicEnv.lookup_insert _ _ _))
  have named := ContextType.models_arrow_app_named ⟨wfNamed, typedNamed⟩
    ⟨wf.mono (by simp [Δ', BasicEnv.domain_insert]), BasicTermTyp.ret (typedV.weaken embed)⟩
    ⟨wf.1.mono (by simp [Δ', BasicEnv.domain_insert]), argNamed⟩
    (fun hy => freshΔ (Finset.union_subset
      (Finset.union_subset typedV.support_subset wf.1.freeAtoms_subset) wf.2.freeAtoms_subset hy))
    worldFull fnG argG'
  rw [sameτ] at named
  have actual := (ContextType.models_interp_of_instantiate_eq_iff
    (formed.mono (by simp [BasicEnv.domain_insert]))
    (BasicTermTyp.app (typedV.weaken embed) (typedU.weaken embed))
    (by simpa [sameτ] using typedNamed) worldFull
    (fun σ hσ => by
      simp only [Interp.instantiateTerm, Interp.instantiateTermAt]
      rw [sameValue σ hσ])).2 named
  rw [ContextType.interp_eq_of_agreeOn (Δ₂ := Δ) (by
    intro y hy
    apply BasicEnv.lookup_insert_of_ne
    intro h
    subst y
    exact freshΔ (Finset.union_subset formed.freeAtoms_subset
      (BasicTermTyp.app typedV typedU).support_subset hy))] at actual
  exact (Formula.models_projection (m := m) (n := g) m.domain
    (Finset.Subset.trans (ContextType.freeAtoms_interp_subset _ _ _)
      (Finset.Subset.trans (Finset.union_subset formed.freeAtoms_subset
        (BasicTermTyp.app typedV typedU).support_subset) scopeΔ))
    (by rw [Capability.restrict_domain_self, base])).2 actual

end ContextTypes.ContextType
