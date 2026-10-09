import ContextTypes.SemTyp.Core
import Mathlib.Tactic

set_option autoImplicit false
namespace ContextTypes.SemTyp
open scoped ContextTypes

/-- Minimum argument measure across all stores, as used by the recursive
call induction.  The minimum is attained by one possible input. -/
private def ArgMin (b : BaseType) (x : Atom) (m : Capability) (k : Nat) : Prop :=
  (∃ σ c, σ ∈ m ∧ σ.lookup x = some (.const c) ∧ Qualifier.constantMeasure b c = k) ∧
  ∀ σ c, σ ∈ m → σ.lookup x = some (.const c) → k ≤ Qualifier.constantMeasure b c

private theorem argMin_exists {b : BaseType} {x : Atom} {m : Capability}
    (values : ∀ σ, σ ∈ m → ∃ c, σ.lookup x = some (.const c)) :
    ∃ k, ArgMin b x m k := by
  classical
  let P := fun k => ∃ σ c, σ ∈ m ∧ σ.lookup x = some (.const c) ∧
    Qualifier.constantMeasure b c = k
  obtain ⟨σ, hσ⟩ := m.nonempty
  obtain ⟨c, hc⟩ := values σ hσ
  have inhabited : ∃ k, P k := ⟨_, σ, c, hσ, hc, rfl⟩
  refine ⟨Nat.find inhabited, Nat.find_spec inhabited, ?_⟩
  intro ρ d hρ hd
  exact Nat.find_min' inhabited ⟨ρ, d, hρ, hd, rfl⟩

private theorem argMin_decreases {b : BaseType} {x y : Atom} {m n : Capability} {k : Nat}
    (href : m ⊑ n) (min : ArgMin b x m k)
    (less : ∀ σ, σ ∈ n → ∃ c₁ c₂,
      σ.lookup y = some (.const c₁) ∧ σ.lookup x = some (.const c₂) ∧
      Qualifier.constantMeasure b c₁ < Qualifier.constantMeasure b c₂) :
    ∃ j, j < k ∧ ArgMin b y n j := by
  obtain ⟨j, minY⟩ := argMin_exists (b := b) (x := y)
    (fun σ hσ => by
      obtain ⟨c₁, c₂, hy, _, _⟩ := less σ hσ
      exact ⟨c₁, hy⟩)
  obtain ⟨σ, c, hσ, hx, measure⟩ := min.1
  have hxDom : x ∈ m.domain := by
    rw [← m.mem_domain hσ]
    exact (Store.mem_domain_iff σ x).2 ⟨_, hx⟩
  have lift : σ ∈ n.restrict m.domain := by rw [← href]; exact hσ
  obtain ⟨ρ, hρ, same⟩ := lift
  obtain ⟨c₁, c₂, hy, hx', lt⟩ := less ρ hρ
  have eq : c₂ = c := by
    have lookup := congrArg (fun s : Store => s.lookup x) same
    change (ρ.restrict m.domain).lookup x = σ.lookup x at lookup
    rw [Store.lookup_restrict, if_pos hxDom, hx, hx'] at lookup
    exact Value.const.inj (Option.some.inj lookup)
  subst c₂
  refine ⟨j, ?_, minY⟩
  rw [← measure]
  exact lt_of_le_of_lt (minY.2 ρ c₁ hρ hy) lt

private theorem argMin_of_interp {b : BaseType} {q : Qualifier} {x : Atom}
    {m : Capability} {Δ : BasicEnv}
    (h : m ⊨ ContextType.interp Δ (.over b q) (.ret (.free x))) :
    ∃ k, ArgMin b x m k := by
  have total := ContextType.models_interp_total h
  have scope := (Interp.models_total_iff (by trivial)).1 total |>.1
  have presentX : x ∈ m.domain := scope (by simp [Term.support, Value.support])
  apply argMin_exists
  intro σ hσ
  obtain ⟨v, hv⟩ := (Store.mem_domain_iff σ x).1 (by rwa [m.mem_domain hσ])
  have basic := Interp.models_basicTyping_term (by trivial)
    (ContextType.models_interp_basicTyping h) hσ
  have returned : ∅ ⊢ₑ (.ret v) ⋮ (.base b) := by
    simpa [Interp.instantiateTerm, Interp.instantiateTermAt, Interp.instantiateValueAt,
      Store.toAssignment_lookup_free, hv] using basic
  cases returned with
  | ret typed =>
    cases typed with
    | const _ c => exact ⟨c, hv⟩
    | free hx => simp at hx


/-- Apply the opened body to the recursive function and fold its operational
unfolding back into a fixed-point application. -/
private theorem fix_app_of_self
    {«Σ» : BasicEnv} {Γ : Context} {q : Qualifier} {τ : ContextType}
    {v : Value} {b : BaseType} {T : SimpleType} {m : Capability} {y : Atom}
    (wf : SynTyp.WellFormed «Σ» Γ (.ret (.fix (.arrow (.base b) T) v))
      (.arrow (.over b q) τ))
    (wf₂ : SynTyp.WellFormed «Σ» (Γ ,, (y ∷ (.over b q)))
      (.ret (v.openAt 0 (.free y)))
      (.arrow (ContextType.recursiveCall b y (.over b q) τ) (τ.openAt 0 y)))
    (fresh : y ∉ Γ.erase.domain) (freshτ : y ∉ τ.freeAtoms)
    (ctx : m ⊨ Context.interpUnder «Σ» (Γ ,, (y ∷ (.over b q))))
    (body : m ⊨ ContextType.interp (Γ.erase.insert y (.base b))
      (.arrow (ContextType.recursiveCall b y (.over b q) τ) (τ.openAt 0 y))
      (.ret (v.openAt 0 (.free y))))
    (self : m ⊨ ContextType.interp (Γ.erase.insert y (.base b))
      (ContextType.recursiveCall b y (.over b q) τ)
      (.ret (.fix (.arrow (.base b) T) v))) :
    m ⊨ ContextType.interp (Γ.erase.insert y (.base b)) (τ.openAt 0 y)
      (.app (.fix (.arrow (.base b) T) v) (.free y)) := by
  let Δ := Γ.erase.insert y (.base b)
  have env : (Γ ,, (y ∷ (.over b q)) : Context).erase = Δ := by
    simp only [Context.erase, ContextType.erase]
    exact BasicEnv.merge_singleton_eq_insert fresh
  have world : m ⊨ Interp.basicWorld Δ := by
    simpa only [env] using Context.models_interpUnder_erase_basicWorld wf₂.1 ctx
  have wfBody : (.arrow (ContextType.recursiveCall b y (.over b q) τ)
      (τ.openAt 0 y) : ContextType).WellFormed Δ.domain := by
    simpa only [env] using wf₂.2.1
  have typedBody : Δ ⊢ᵥ v.openAt 0 (.free y) ⋮
      (.arrow (ContextType.recursiveCall b y (.over b q) τ).erase (τ.openAt 0 y).erase) := by
    have typed : Δ ⊢ₑ (.ret (v.openAt 0 (.free y))) ⋮
        (.arrow (ContextType.recursiveCall b y (.over b q) τ) (τ.openAt 0 y) : ContextType).erase := by
      simpa only [env] using wf₂.2.2
    cases typed with
    | ret h => exact h
  have typedSelf : Δ ⊢ᵥ (.fix (.arrow (.base b) T) v) ⋮
      (ContextType.recursiveCall b y (.over b q) τ).erase := by
    have typed := wf.2.2.weaken (BasicEnv.subset_insert_of_fresh Γ.erase y (.base b) fresh)
    cases typed with
    | ret h => exact h
  have closed : (τ.openAt 0 y).LocallyClosed := (wf.2.1.2.openAt freshτ).locallyClosedAt
  have unfolded := ContextType.models_arrow_app wfBody closed typedBody typedSelf world body self
  have formed : (τ.openAt 0 y).WellFormed Δ.domain := by
    simpa only [Δ, BasicEnv.domain_insert, Finset.union_comm] using wf.2.1.2.openAt freshτ
  have typedApp : Δ ⊢ₑ (.app (.fix (.arrow (.base b) T) v) (.free y)) ⋮ (τ.openAt 0 y).erase := by
    rw [ContextType.erase_openAt]
    exact BasicTermTyp.app typedSelf (BasicValTyp.free (BasicEnv.lookup_insert _ _ _))
  exact (ContextType.models_interp_fix_iff formed typedApp world).2 unfolded


/-- Recursive-call compatibility is proved by the minimum argument measure
of the full parent capability, just as in the reference proof. -/
private theorem fix_self
    {Φ : PrimitiveContext} {«Σ» : BasicEnv} {Γ : Context} {q : Qualifier} {τ : ContextType}
    {v : Value} {b : BaseType} {T : SimpleType} (L : Finset Atom)
    (wf : SynTyp.WellFormed «Σ» Γ (.ret (.fix (.arrow (.base b) T) v))
      (.arrow (.over b q) τ))
    (wf₂ : ∀ y, y ∉ L → SynTyp.WellFormed «Σ» (Γ ,, (y ∷ (.over b q)))
      (.ret (v.openAt 0 (.free y)))
      (.arrow (ContextType.recursiveCall b y (.over b q) τ) (τ.openAt 0 y)))
    (body : ∀ y, y ∉ L → Φ ; «Σ» ; (Γ ,, (y ∷ (.over b q))) ⊨
      (.ret (v.openAt 0 (.free y))) ⋮
      (.arrow (ContextType.recursiveCall b y (.over b q) τ) (τ.openAt 0 y))) :
    let X := (L ∪ (Context.erasureUnder «Σ» Γ).domain) ∪
      (v.support ∪ (.over b q : ContextType).freeAtoms ∪ τ.freeAtoms)
    ∀ k m x, x ∉ X → ArgMin b x m k → m ⊨ Context.interpUnder «Σ» Γ →
      m ⊨ ContextType.interp (Γ.erase.insert x (.base b)) (.over b q) (.ret (.free x)) →
      m ⊨ ContextType.interp (Γ.erase.insert x (.base b))
        (ContextType.recursiveCall b x (.over b q) τ) (.ret (.fix (.arrow (.base b) T) v)) := by
  intro X k
  induction k using Nat.strong_induction_on with
  | h k ih =>
    intro m x fresh min ctx arg
    have fresh' : (x ∉ L ∧ x ∉ (Context.erasureUnder «Σ» Γ).domain) ∧
        ((x ∉ v.support ∧ x ∉ (.over b q : ContextType).freeAtoms) ∧ x ∉ τ.freeAtoms) := by
      simpa only [X, Finset.mem_union, not_or] using fresh
    have freshΔ : x ∉ Γ.erase.domain := fun h => fresh'.1.2
      (by simp only [Context.erasureUnder, BasicEnv.domain_merge]; exact Finset.mem_union_right _ h)
    let Δ := Γ.erase
    let Δx := Δ.insert x (.base b)
    let υ := ContextType.recursiveCall b x (.over b q) τ
    have ctxX := Context.models_interpUnder_comma_bind wf.1 wf.2.1.1 fresh'.1.2 ctx arg
    have wfX := wf₂ x fresh'.1.1
    have envX : (Γ ,, (x ∷ (.over b q)) : Context).erase = Δx := by
      simp only [Context.erase, ContextType.erase]
      exact BasicEnv.merge_singleton_eq_insert freshΔ
    have wfSelf : υ.WellFormed Δx.domain := by simpa only [envX] using wfX.2.1.1
    have typedSelf : Δx ⊢ₑ (.ret (.fix (.arrow (.base b) T) v)) ⋮ υ.erase :=
      wf.2.2.weaken (BasicEnv.subset_insert_of_fresh Δ x (.base b) freshΔ)
    have world : m ⊨ Interp.basicWorld Δx := by
      simpa only [envX] using Context.models_interpUnder_erase_basicWorld wfX.1 ctxX
    apply ContextType.models_arrow_of_app_named X wfSelf typedSelf world
    intro y freshY freshYΔ n href argY
    have freshY' : (y ∉ L ∧ y ∉ (Context.erasureUnder «Σ» Γ).domain) ∧
        ((y ∉ v.support ∧ y ∉ (.over b q : ContextType).freeAtoms) ∧ y ∉ τ.freeAtoms) := by
      simpa only [X, Finset.mem_union, not_or] using freshY
    have freshY₀ : y ∉ Δ.domain := fun h => freshYΔ (by simp [Δx, BasicEnv.domain_insert, h])
    have apart : y ≠ x := fun h => freshYΔ (by simp [Δx, BasicEnv.domain_insert, h])
    let Δxy := Δx.insert y (.base b)
    let Δy := Δ.insert y (.base b)
    have argQ : n ⊨ ContextType.interp Δxy (.over b q) (.ret (.free y)) :=
      Formula.models_and_elim_left (Formula.models_and_elim_right argY)
    have argLt : n ⊨ ContextType.interp Δxy
        (.over b (Qualifier.lessThanBase b (.bound 0) (.free x))) (.ret (.free y)) :=
      Formula.models_and_elim_right (Formula.models_and_elim_right argY)
    have wfLt : (.over b (Qualifier.lessThanBase b (.bound 0) (.free x)) : ContextType).WellFormed Δxy.domain :=
      wfSelf.1.2.1.mono (by simp [Δxy, BasicEnv.domain_insert])
    have less := ContextType.models_over_less_ret_free_lookup wfLt
      (BasicValTyp.free (BasicEnv.lookup_insert _ _ _)) argLt
    obtain ⟨j, lt, minY⟩ := argMin_decreases href min less
    have agree (υ : ContextType) (e : Term) (notX : x ∉ υ.freeAtoms ∪ e.support) :
        BasicEnv.AgreeOn (υ.freeAtoms ∪ e.support) Δxy Δy := by
      apply ((show BasicEnv.AgreeOn (υ.freeAtoms ∪ e.support) Δx Δ from by
        intro z hz
        apply BasicEnv.lookup_insert_of_ne
        intro eq
        subst z
        exact notX hz).insert y (.base b)).mono Finset.subset_union_left
    have argChild : n ⊨ ContextType.interp Δy (.over b q) (.ret (.free y)) := by
      rw [← ContextType.interp_eq_of_agreeOn (agree _ _ (by
        simpa only [Term.support, Value.support, Finset.mem_union, Finset.mem_singleton, not_or]
          using ⟨fresh'.2.1.2, apart.symm⟩))]
      exact argQ
    have ctxN := Formula.models_kripke href ctx
    have selfChild := ih j lt n y freshY minY ctxN argChild
    have ctxY := Context.models_interpUnder_comma_bind wf.1 wf.2.1.1 freshY'.1.2 ctxN argChild
    have envY : (Γ ,, (y ∷ (.over b q)) : Context).erase = Δy := by
      simp only [Context.erase, ContextType.erase]
      exact BasicEnv.merge_singleton_eq_insert freshY₀
    have bodyY := body y freshY'.1.1 n ctxY
    rw [envY] at bodyY
    have actual := fix_app_of_self wf (wf₂ y freshY'.1.1) freshY₀ freshY'.2.2 ctxY bodyY selfChild
    rw [← ContextType.interp_eq_of_agreeOn (agree _ _ (by
      intro h
      rcases Finset.mem_union.1 h with h | h
      · rcases Finset.mem_union.1 (ContextType.freeAtoms_openAt_subset τ 0 y h) with h | h
        · exact apart (Finset.mem_singleton.1 h).symm
        · exact fresh'.2.2 h
      · have h' : x ∈ v.support ∨ x = y := by simpa [Term.support, Value.support, or_comm] using h
        exact h'.elim fresh'.2.1.1 apart.symm))] at actual
    exact actual

/-- Fixed-point compatibility uses strict decrease of the recursive-call
argument and the semantic typing of the opened body. -/
theorem fixpoint
    {Φ : PrimitiveContext} {«Σ» : BasicEnv} {Γ : Context} {q : Qualifier} {τ : ContextType}
    {v : Value} {b : BaseType} {T : SimpleType} (L : Finset Atom)
    (erasure : τ.erase = T)
    (wf : SynTyp.WellFormed «Σ» Γ (.ret (.fix (.arrow (.base b) T) v))
      (.arrow (.over b q) τ))
    (wf₂ : ∀ y, y ∉ L → SynTyp.WellFormed «Σ» (Γ ,, (y ∷ (.over b q)))
      (.ret (v.openAt 0 (.free y)))
      (.arrow (ContextType.recursiveCall b y (.over b q) τ) (τ.openAt 0 y)))
    (body : ∀ y, y ∉ L → Φ ; «Σ» ; (Γ ,, (y ∷ (.over b q))) ⊨
      (.ret (v.openAt 0 (.free y))) ⋮
      (.arrow (ContextType.recursiveCall b y (.over b q) τ) (τ.openAt 0 y))) :
    Φ ; «Σ» ; Γ ⊨ (.ret (.fix (.arrow (.base b) T) v)) ⋮ (.arrow (.over b q) τ) := by
  subst T
  intro m ctx
  let X := (L ∪ (Context.erasureUnder «Σ» Γ).domain) ∪
    (v.support ∪ (.over b q : ContextType).freeAtoms ∪ τ.freeAtoms)
  have world := Context.models_interpUnder_erase_basicWorld wf.1 ctx
  apply ContextType.models_arrow_of_app_named X wf.2.1 wf.2.2 world
  intro y freshY freshΔ n href arg
  have fresh' : (y ∉ L ∧ y ∉ (Context.erasureUnder «Σ» Γ).domain) ∧
      ((y ∉ v.support ∧ y ∉ (.over b q : ContextType).freeAtoms) ∧ y ∉ τ.freeAtoms) := by
    simpa only [X, Finset.mem_union, not_or] using freshY
  have ctxN := Formula.models_kripke href ctx
  obtain ⟨k, min⟩ := argMin_of_interp arg
  have self := fix_self L wf wf₂ body k n y freshY min ctxN arg
  have ctxY := Context.models_interpUnder_comma_bind wf.1 wf.2.1.1 fresh'.1.2 ctxN arg
  have env : (Γ ,, (y ∷ (.over b q)) : Context).erase = Γ.erase.insert y (.base b) := by
    simp only [Context.erase, ContextType.erase]
    exact BasicEnv.merge_singleton_eq_insert freshΔ
  have bodyY := body y fresh'.1.1 n ctxY
  rw [env] at bodyY
  exact fix_app_of_self wf (wf₂ y fresh'.1.1) freshΔ fresh'.2.2 ctxY bodyY self

end ContextTypes.SemTyp
