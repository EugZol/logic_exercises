module

public inductive IntFormula : Type
| var : Nat → IntFormula
| and : IntFormula → IntFormula → IntFormula
| or  : IntFormula → IntFormula → IntFormula
| imp  : IntFormula → IntFormula → IntFormula
| bot  : IntFormula
deriving Repr, DecidableEq

@[expose] public def IntFormula.not (x : IntFormula) : IntFormula := IntFormula.imp x IntFormula.bot

@[expose] public def IntFormula.iff (x y : IntFormula) : IntFormula :=
  IntFormula.and (IntFormula.imp x y) (IntFormula.imp y x)

notation "varᵢ" n => IntFormula.var n
prefix:40 "¬ᵢ" => IntFormula.not
notation "⊥ᵢ" => IntFormula.bot
infixr:35 " ∧ᵢ " => IntFormula.and
infixr:30 " ∨ᵢ " => IntFormula.or
infixr:25 " →ᵢ " => IntFormula.imp
infixr:25 " ↔ᵢ " => IntFormula.iff
