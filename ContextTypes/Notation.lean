import ContextTypes.Syntax
import ContextTypes.ContextType

set_option autoImplicit false

/-!
# Surface notation

Scoped, paper-facing notation for context types and bunched contexts.  This
module contains no mathematical definitions.
-/

set_option hygiene false in
scoped[ContextTypes] notation:0 "{" "ν" ":" b "|" q "}" =>
  ContextTypes.ContextType.over b q

set_option hygiene false in
scoped[ContextTypes] notation:0 "[" "ν" ":" b "|" q "]" =>
  ContextTypes.ContextType.under b q

set_option hygiene false in
scoped[ContextTypes] infix:40 " ⊓ " => ContextTypes.ContextType.inter

set_option hygiene false in
scoped[ContextTypes] infix:50 " ⊔ " => ContextTypes.ContextType.union

set_option hygiene false in
scoped[ContextTypes] infixr:70 " ⊕ " => ContextTypes.ContextType.sum

set_option hygiene false in
scoped[ContextTypes] infixr:99 " → " => ContextTypes.ContextType.arrow

set_option hygiene false in
scoped[ContextTypes] infixr:60 " -∗ " => ContextTypes.ContextType.wand

set_option hygiene false in
scoped[ContextTypes] prefix:30 "□ " => ContextTypes.ContextType.persist

set_option hygiene false in
scoped[ContextTypes] notation:60 x:60 " ∷ " τ:200 =>
  ContextTypes.Context.bind x τ

set_option hygiene false in
scoped[ContextTypes] infixl:61 " ,, " => ContextTypes.Context.comma

set_option hygiene false in
scoped[ContextTypes] infixl:40 " ∗ " => ContextTypes.Context.star

set_option hygiene false in
scoped[ContextTypes] infixr:70 " ⊕ " => ContextTypes.Context.sum
