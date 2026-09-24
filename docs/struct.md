# Formalization structure

This document fixes the initial architecture of the Lean formalization of
*Context Types: Bunched Modalities for Unifying Safety and Reachability*.
Naming and notation rules are recorded separately in
[`CONVENTIONS.md`](CONVENTIONS.md).

## Mathematical organization

The architecture follows Sections 4.1--4.4 of the paper rather than copying
an implementation directory tree mechanically:

1. define the core language, its operational semantics, and basic typing;
2. define contextual capabilities and their algebra;
3. interpret context logic over capabilities;
4. interpret context types and contexts as context-logic formulas;
5. state syntactic context typing;
6. prove one semantic compatibility theorem for each typing rule;
7. assemble those cases into the Fundamental theorem;
8. derive closed-program denotational soundness.

The intended dependency direction is:

```text
Syntax --> Notation --> OperSem
   |                       |
   +------------------> BasicTyp
   |
   +------------------> Capability --> CtxLogic --> Interp --> Pretty
                                                    |
                                                    v
                                                  SynTyp
                                                    |
                                                    v
                                                  SemTyp
                                                    |
                                                    v
                                               Fundamental
                                                    |
                                                    v
                                                Soundness
```

`SynTyp` depends on `Interp` because the checked calculus uses semantic type
and context subtyping as premises of its syntactic typing rules.

## Public modules

### `Syntax.lean`

Owns the syntax shared by the remainder of the development:

- atoms and locally nameless variables;
- base and simple types;
- constants and primitive-operation names;
- core values and terms;
- context types and bunched contexts;
- opening, closing, substitution, support, and erasure operations.

The first port follows the checked core language: unit, booleans, naturals,
unary primitives, application, let, Boolean matching, lambda, and fixpoint.

### `Notation.lean`

Defines scoped surface syntax for core terms, context types, and contexts.  It
imports only `Syntax.lean`; it is not a project-wide re-export module.

Judgment notation whose declaration is defined later remains with its owning
module.

### `OperSem.lean`

Owns primitive reduction, head reduction, call-by-value small-step reduction,
multi-step reduction, and result predicates.  It corresponds to the paper's
operational semantics and Supplementary Appendix B.

### `BasicTyp.lean`

Owns simple value and term typing, qualifier scoping, context-type
well-formedness, and the regularity results required by the denotation.  It
corresponds to Supplementary Appendix C.

### `Capability.lean`

Owns the semantic domain from paper Sections 4.1--4.2 and Supplementary
Appendix D:

- finite environments from atoms to core values;
- nonempty contextual capabilities whose environments share a domain;
- compatibility, restriction, and the projection order `m ⊑ n`;
- same-domain possibility inclusion `m ⊆ᵣ n`;
- capability product, sum, unit, fibers, and fiber extensions;
- the algebraic and transport laws used by context logic.

The initial implementation is concrete in the core-language value type.  It
will not introduce an extra value-type parameter without an actual reuse case.

### `CtxLogic.lean`

Owns supported qualifiers, context-logic formulas, formula satisfaction, and
semantic entailment.  It includes BI connectives, over- and
underapproximation modalities, sum, persistence, and fiber/binding-reference
quantification.

It also proves Kripke monotonicity and the connective laws needed by the type
interpretation.

### `Interp.lean`

Owns the interpretation of context types and contexts from paper Section 4.4:

- atomic formulas for basic typing, totality, evaluation results, and
  qualifier satisfaction;
- the guard and relevant-environment construction;
- result-first context-type interpretation;
- bunched context interpretation;
- semantic type and context subtyping;
- result, fiber, and persistence transport lemmas.

Basic-denotation atoms are not a separate public mathematical layer.  They
are implementation support for `Interp`.  If `Interp.lean` becomes too large,
it may be split physically as follows without changing the public
architecture:

```text
Interp/
  Atoms.lean
  Guard.lean
  Type.lean
  Context.lean
  Transport.lean
  Persistence.lean
Interp.lean
```

### `Pretty.lean`

Owns custom Lean delaborators for readable InfoView output.  It renders core
terms, context types, formulas, interpretations, and principal judgments using
the established notation.  Pretty printing is presentational only and must
always fall back safely to ordinary Lean output.

### `SynTyp.lean`

Owns the syntactic context-typing judgment and its side conditions:

- primitive-operation signatures and well-formed primitive contexts;
- semantic type and context subtyping premises;
- unreachable-branch premises;
- all constructors of `HasContextType`;
- typing regularity and inversion facts.

### `SemTyp.lean`

Defines semantic typing as entailment from context interpretation to type
interpretation, and proves a compatibility theorem for every constructor of
`HasContextType`.

The public theorems are named by typing case, for example `SemTyp.var`,
`SemTyp.letE`, `SemTyp.lam`, and `SemTyp.matchBoth`.  When the implementation
outgrows one file, it may use an internal directory:

```text
SemTyp/
  Core.lean
  Structural.lean
  Let.lean
  Function.lean
  Application.lean
  Primitive.lean
  Match.lean
  Fixpoint.lean
  Persistence.lean
SemTyp.lean
```

The top-level `SemTyp.lean` remains the public entry point for all compatibility
rules.

### `Fundamental.lean`

Contains only the induction that maps a `HasContextType` derivation to the
matching `SemTyp` compatibility theorem, plus the abstract and concrete
Fundamental theorem wrappers.  Case-specific semantic arguments do not belong
here.

### `Soundness.lean`

Derives closed-program denotational soundness from the Fundamental theorem.
It constructs the capability containing all results of a closed term and
shows that this capability satisfies the result type interpretation.

## Scope of the first port

The first implementation target is the nondeterministic calculus described in
paper Sections 5.1--5.2.  It does not initially add the following extensions:

- general datatype matching;
- fixed list or tree syntax;
- n-ary primitive operations;
- existential context-logic formulas;
- `FixD`;
- the paper's Section 5 case-study programs.

Mathlib will provide finite data structures, set reasoning, relations,
well-founded recursion, and routine proof automation.  Concrete Mathlib data
representations should remain behind the APIs of their owning modules.

## Implementation order

Modules are added with working content rather than as empty placeholders:

1. `Syntax` and `Notation`;
2. `OperSem` and `BasicTyp`;
3. `Capability`;
4. `CtxLogic`;
5. `Interp` and `Pretty`;
6. `SynTyp`;
7. `SemTyp` cases;
8. `Fundamental`;
9. `Soundness`.

Every step must leave `lake build` green.
