# ContextTypes naming and module conventions

This document fixes the public vocabulary, notation, and proof boundaries for
the ContextTypes formalization.  New code should extend these conventions
instead of introducing parallel names or notation.

## Module boundaries

| Module | Responsibility |
| --- | --- |
| `Syntax.lean` | Core-language and context-type syntax, binding operations, and erasure |
| `Notation.lean` | Scoped surface syntax for terms, context types, and contexts |
| `OperSem.lean` | Primitive, head, small-step, and multi-step operational semantics |
| `BasicTyp.lean` | Simple typing and syntactic well-formedness |
| `Capability.lean` | Contextual capabilities, algebra, fibers, and extensions |
| `CtxLogic.lean` | Qualifiers, formulas, satisfaction, entailment, and logic laws |
| `Interp.lean` | Type and context interpretation and semantic subtyping |
| `Pretty.lean` | Delaborators for readable InfoView output |
| `SynTyp.lean` | The context-typing judgment and its regularity properties |
| `SemTyp.lean` | Semantic typing and compatibility rules for typing cases |
| `Fundamental.lean` | Assembly of compatibility cases into the Fundamental theorem |
| `Soundness.lean` | Closed-program denotational soundness |

The detailed dependency policy is recorded in [`struct.md`](struct.md).

## Public vocabulary

Use the following principal names:

| Name | Meaning |
| --- | --- |
| `Atom` | A free variable name |
| `LogicVar` | A bound or free logical variable |
| `Store` | A finite environment from atoms to core values |
| `Capability` | A nonempty set of stores sharing one domain |
| `Qualifier` | A predicate with explicit logical-variable support |
| `Formula` | A context-logic formula |
| `Value` | A core-language value |
| `Term` | A core-language term |
| `ContextType` | An over/under context type |
| `Context` | A bunched context of context types |
| `PrimitiveContext` | Context-type signatures for primitive operations |
| `HasContextType` | The syntactic context-typing judgment |
| `SemTyp` | The semantic context-typing judgment |

Use `Capability` as the public name for the paper's contextual capabilities.
Do not add synonyms such as `Resource`, `World`, `WfWorld`, `Res`, or
`SemanticWorld` as public types.  “Resource” and “world” may be used in prose
when discussing the algebraic or Kripke role of a capability.

Use `Context` for a context-type context and `Δ` for an erased/basic typing
environment.  Do not introduce aliases named `Ctx`, `Gamma`, or `TypingCtx`.

## Principal judgments and interpretations

Open the project scope before using notation:

```lean
open scoped ContextTypes
```

| Meaning | Preferred form | Declaration |
| --- | --- | --- |
| Basic value typing | `Δ ⊢ᵥ v ⋮ T` | `ValueTyping Δ v T` |
| Basic term typing | `Δ ⊢ₑ e ⋮ T` | `TermTyping Δ e T` |
| Capability projection order | `m ⊑ n` | `SqSubsetEq.sqSubsetEq m n` |
| Same-domain possibility inclusion | `m ⊆ᵣ n` | `Capability.Subset m n` |
| Formula satisfaction | `m ⊨ P` | `Formula.Models m P` |
| Formula entailment | `P ⊫ Q` | `Formula.Entails P Q` |
| Formula equivalence | `P ⊣⊢ Q` | `Formula.Equiv P Q` |
| Type interpretation | `⟦τ⟧[Δ] e` | `ContextType.interp Δ τ e` |
| Context interpretation | `⟦Γ⟧[Σ]` | `Context.interpUnder Σ Γ` |
| Context typing | `Φ ⊢ᶜ [Σ; Γ] e ⋮ τ` | `HasContextType Φ Σ Γ e τ` |
| Semantic typing | `Φ ⊨ᶜ [Σ; Γ] e ⋮ τ` | `SemTyp Φ Σ Γ e τ` |
| Semantic subtype | `Σ , Γ ⊢ τ₁ <: τ₂` | `SubTypeUnder Σ Γ τ₁ τ₂` |
| Semantic context subtype | `Σ ⊢ Γ₁ ≤[X] Γ₂` | `ContextSubUnder Σ X Γ₁ Γ₂` |

Do not introduce alternate spellings such as `≤w`, `WorldLe`, `Satisfies`,
`SemanticallyTyped`, or `ContextHasType`.

The notation `m ⊑ n` is the projection/Kripke relation: `m` is the
restriction of `n` to the domain visible in `m`.  It is not inclusion between
sets of possible stores.

The notation `m ⊆ᵣ n` compares possible stores at the same domain.  Keep these
relations distinct in definitions, theorem names, and prose.

## Mathematical variables

| Name | Meaning |
| --- | --- |
| `x`, `y`, `z` | Free atoms |
| `k` | Bound-variable index |
| `d` | Binder depth |
| `D`, `X`, `Y` | Variable supports or domains |
| `σ`, `ρ` | Stores or substitutions |
| `m`, `n`, `m₁`, `m₂` | Capabilities |
| `F` | Fiber extension |
| `q`, `q₁`, `q₂` | Qualifiers |
| `P`, `Q`, `R` | Context-logic formulas |
| `b` | Base type |
| `T`, `U` | Erased/simple types |
| `τ`, `τ₁`, `τ₂` | Context types |
| `Γ`, `Γ₁`, `Γ₂` | Context-type contexts |
| `Δ` | Erased/basic typing environment |
| `Σ` | Ambient typing environment |
| `Φ` | Primitive-operation context |
| `v` | Core value |
| `e` | Core term |

Do not use `φ` for both qualifiers and formulas.  Lean declarations use `q`
for qualifiers and `P`/`Q` for formulas even where the paper uses `φ`.

## Connective notation

Use the following notation consistently:

| Form | Meaning |
| --- | --- |
| `x ∷ τ` | Singleton context binding |
| `Γ₁ ,, Γ₂` | Ordinary/entangled context composition |
| `Γ₁ ∗ Γ₂` | Separating context composition |
| `Γ₁ ⊕ Γ₂` | Additive context composition |
| `τ₁ ⊓ τ₂` | Type intersection |
| `τ₁ ⊔ τ₂` | Type union |
| `τ₁ ⊕ τ₂` | Additive/sum type |
| `τ₁ → τ₂` | Ordinary/entangled function type |
| `τ₁ -∗ τ₂` | Separating function type |
| `□ τ` | Persistent type |
| `{ν : b | q}` | Overapproximate/demonic context type |
| `[ν : b | q]` | Underapproximate/angelic context type |
| `P ∗ Q` | Separating conjunction |
| `P -∗[d] Q` | Binder-aware magic wand |
| `🄾 P` | Overapproximate/demonic modality |
| `🅄 P` | Underapproximate/angelic modality |
| `□ P` | Persistent formula |
| `fib D |> P` | Fiber quantification over `D` |

Keep the binder depth explicit in magic wand.  Do not provide a second wand
whose binder accounting is implicit.

Qualifier top observes the result binder.  It must not be represented by an
empty-support predicate.

The modality tokens are `🄾` (U+1F13E, SQUARED LATIN CAPITAL LETTER O) and
`🅄` (U+1F144, SQUARED LATIN CAPITAL LETTER U).  Do not add parallel word-style
notations such as `over P` and `under P`.  The braces and brackets distinguish
the corresponding context-type constructors from formula modalities.

## Notation and pretty printing

Define notation immediately after the declaration it presents and before
derived definitions and theorems.  Public definitions and theorem statements
should use the established notation when it makes their mathematical shape
clearer.

Use local hygiene disabling for judgment-facing notation:

```lean
set_option hygiene false in
scoped notation:50 m:51 " ⊑ " n:51 =>
  SqSubsetEq.sqSubsetEq m n
```

Do not disable hygiene for an entire file.  Project-specific notation belongs
to the `ContextTypes` scope.

`Notation.lean` contains only surface syntax for core terms, context types,
and contexts.  Judgment notation stays with the declaration it presents.

`Pretty.lean` uses `Lean.PrettyPrinter.Delaborator` and `@[app_delab ...]` to
render core terms, context types, formulas, interpretations, and principal
judgments.  Delaborators must contain the usual guards:

```lean
guard !(← getPPOption getPPAll)
guard (← getPPOption getPPNotation)
```

Thus ordinary InfoView output uses paper-facing notation, while
`set_option pp.all true` reveals the underlying constructors and implicit
arguments.  Delaborators are presentational only: elaboration and proofs must
never depend on one succeeding.

## Declaration naming

Types, structures, inductive judgments, and namespaces use `UpperCamelCase`.
Definitions and theorems use domain namespaces rather than repeated prefixes:

```lean
Capability.restrict
Capability.restrict_idem
Capability.sqSubset_trans
Formula.models_kripke
Formula.models_star_iff
ContextType.erase
ContextType.interp
Context.interpUnder
SemTyp.letE
Fundamental.sound
Soundness.denotational
```

Avoid mechanical prefixes such as `resA_`, `rawA_`, `wfworldA_`, and
`better_` in the public Lean API.

Names such as `Semantics`, `Semantic`, `Typing`, `WellFormed`, or `Regular`
are too vague unless qualified by an owning domain namespace.

## Semantic typing and the Fundamental theorem

`SemTyp` is the semantic counterpart of `HasContextType`: context
interpretation entails type interpretation.  The namespace contains one
compatibility theorem for every syntactic typing constructor, with parallel
names such as:

```lean
SemTyp.var
SemTyp.const
SemTyp.sub
SemTyp.ctxSub
SemTyp.letE
SemTyp.letSep
SemTyp.lam
SemTyp.lamSep
SemTyp.app
SemTyp.appSep
SemTyp.primitive
SemTyp.matchBoth
SemTyp.fixpoint
SemTyp.persist
```

`Fundamental.lean` only performs induction on a `HasContextType` derivation
and dispatches to these named compatibility theorems.  Case-specific semantic
proofs do not belong there.

`Soundness.lean` owns the separate closed-program consequence and its result
capability construction.

## Paper and implementation terminology

The initial formalization follows the nondeterministic calculus described in
paper Sections 5.1--5.2, not every possible language extension.

Qualifiers are supported semantic predicates rather than a first-order
qualifier AST.  Arrow, wand, sum, and persistence use the checked result-first
interpretation.  Do not silently replace them with the simpler deterministic
presentation from paper Section 4.

Primitive soundness remains parameterized by `PrimitiveContext`.  Concrete
graph-precise primitives are an instance, not part of the abstract
Fundamental theorem.

## Proof and maintenance rules

- Every change must leave `lake build` green.
- Do not introduce `sorry`, `admit`, or project-specific axioms.
- Keep definitions in their owning module; do not redefine them in proof
  modules.
- Do not preserve one-use helper lemmas mechanically.  Add a Lean lemma when
  it states a stable semantic or structural fact.
- Do not expose the concrete finite-map representation outside its owning
  API.
- Distinguish definitional equality from semantic equivalence in theorem
  names and statements.
- Refactors must preserve the public notation and vocabulary fixed here unless
  this document is updated in the same change.
