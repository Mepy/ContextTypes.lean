import ContextTypes.SemTyp.Core
import Mathlib.Tactic

set_option autoImplicit false

namespace ContextTypes

/-! # Primitive semantic-typing compatibility -/

open scoped ContextTypes

namespace SemTyp

/-- A well-formed primitive signature transports its argument denotation to
its exact result denotation. -/
theorem primitive {Φ : PrimitiveContext} {«Σ» : BasicEnv} {Γ : Context}
    {op : Primitive} {x : Atom}
    (wfΦ : Φ.WellFormed)
    (wf : SynTyp.WellFormed «Σ» Γ (.primitive op (.free x))
      ((Φ op).resultType.openAt 0 x))
    (arg : Φ ; «Σ» ; Γ ⊨ (.ret (.free x)) ⋮ (Φ op).argType) :
    Φ ; «Σ» ; Γ ⊨ (.primitive op (.free x)) ⋮
      ((Φ op).resultType.openAt 0 x) := by
  intro m hΓ
  let s := Φ op
  have hs : s.WellFormed op := wfΦ op
  have hbasic := wf.2.2
  have hlookup : Γ.erase.lookup x = some (.base s.argBase) := by
    cases hbasic with
    | @primitive _ _ _ b₁ _ hop hv =>
        cases hv with
        | free hx =>
            have hb : b₁ = s.argBase :=
              congrArg Prod.fst (hop.symm.trans hs.erasure)
            rw [hb] at hx
            exact hx
  have hfree : s.argType.freeAtoms = ∅ :=
    Finset.Subset.antisymm hs.arg.freeAtoms_subset (Finset.empty_subset _)
  have ha := arg m hΓ
  have hagreeArg : BasicEnv.AgreeOn
      (s.argType.freeAtoms ∪ (.ret (.free x) : Term).support)
      Γ.erase (BasicEnv.singleton x (.base s.argBase)) := by
    intro y hy
    have hyx : y = x := by
      simpa [hfree, Term.support, Value.support] using hy
    subst y
    simpa using hlookup
  have harg : m ⊨ ContextType.interp
      (BasicEnv.singleton x (.base s.argBase)) s.argType
      (.ret (.free x)) := by
    rw [← ContextType.interp_eq_of_agreeOn hagreeArg]
    exact ha
  have hworld := ContextType.models_interp_basicWorld harg
  have hrel : Interp.relevantEnv
      (BasicEnv.singleton x (.base s.argBase)) s.argType
      (.ret (.free x)) = BasicEnv.singleton x (.base s.argBase) := by
    simp only [Interp.relevantEnv, Interp.relevantAtoms, hfree,
      Term.support, Value.support, Finset.empty_union]
    apply BasicEnv.restrict_eq_self
    simp
  rw [hrel] at hworld
  have hbind : m ⊨ Context.interp (.bind x s.argType) := by
    change m ⊨
      (Interp.basicWorld (BasicEnv.singleton x s.argType.erase) ∧ᶜ
        ContextType.interp (BasicEnv.singleton x s.argType.erase)
          s.argType (.ret (.free x)))
    simpa [PrimitiveSignature.argType] using
      Formula.models_and_intro hworld harg
  have hout := (hs.semantic x).1 m hbind
  have hagreeResult : BasicEnv.AgreeOn
      ((s.resultType.openAt 0 x).freeAtoms ∪
        (.primitive op (.free x) : Term).support)
      (Context.bind x s.argType).erase Γ.erase := by
    intro y hy
    have hopen := s.resultType.freeAtoms_openAt_subset 0 x
    have hyx : y = x := by
      rcases Finset.mem_union.1 hy with hy | hy
      · rcases Finset.mem_union.1 (hopen hy) with hy | hy
        · exact Finset.mem_singleton.1 hy
        · exact False.elim (by simpa using hs.result.freeAtoms_subset hy)
      · simpa [Term.support, Value.support] using hy
    subst y
    change (BasicEnv.singleton x s.argType.erase).lookup x =
      Γ.erase.lookup x
    simpa [PrimitiveSignature.argType] using hlookup.symm
  rw [ContextType.interp_eq_of_agreeOn hagreeResult] at hout
  exact hout

end SemTyp

end ContextTypes
