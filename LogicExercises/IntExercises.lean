import Mathlib
import LogicExercises.Exercise

-- Intuitionistic logic

inductive IntFormula : Type
| var : Nat → IntFormula
| and : IntFormula → IntFormula → IntFormula
| or  : IntFormula → IntFormula → IntFormula
| imp  : IntFormula → IntFormula → IntFormula
| bot  : IntFormula
deriving Repr, DecidableEq

def not (x : IntFormula) : IntFormula := IntFormula.imp x IntFormula.bot

namespace FormulaNotation

notation "varᵢ" n => IntFormula.var n
notation "¬ᵢ" n => not n
notation "⊥ᵢ" => IntFormula.bot
infixr:35 " ∧ᵢ " => IntFormula.and
infixr:30 " ∨ᵢ " => IntFormula.or
infixr:25 " →ᵢ " => IntFormula.imp

end FormulaNotation

inductive IntDerives (Γ : Set IntFormula) : IntFormula → Prop
-- `hyp`: "hypothesis", if formula is in Γ, it derives
| hyp {a : IntFormula} : exercise → IntDerives Γ a
| ax0 {x : Nat} : IntDerives Γ (varᵢ x)
| ax1 {a b : IntFormula} : IntDerives Γ (a →ᵢ b →ᵢ a)
| ax2 {a b c : IntFormula} : IntDerives Γ ((a →ᵢ b →ᵢ c) →ᵢ (a →ᵢ b) →ᵢ a →ᵢ c)
| ax3_1 {a b : IntFormula} : IntDerives Γ (a ∧ᵢ b →ᵢ a)
| ax3_2 {a b : IntFormula} : IntDerives Γ (a ∧ᵢ b →ᵢ b)
| ax4 {a b : IntFormula} : IntDerives Γ (a →ᵢ b →ᵢ a ∧ᵢ b )
| ax5_1 {a b : IntFormula} : IntDerives Γ (a →ᵢ a ∨ᵢ b)
| ax5_2 {a b : IntFormula} : IntDerives Γ (b →ᵢ a ∨ᵢ b )
| ax6 {a b c : IntFormula} : IntDerives Γ ((a →ᵢ c) →ᵢ (b →ᵢ c) →ᵢ a ∨ᵢ b →ᵢ c)
| ax7 {a b : IntFormula} : IntDerives Γ ((a →ᵢ b) →ᵢ (a →ᵢ ¬ᵢ b) →ᵢ ¬ᵢ a)
| ax8 {a b : IntFormula} : IntDerives Γ (a →ᵢ ¬ᵢ a →ᵢ b)
-- `mp`: "modus ponens", if `a` derives and `a →ᵢ b` derives, then
-- `b` derives (all in the same context)
| mp {a b : IntFormula} : exercise

namespace DerivesNotation

infixr:20 " ⊢ᵢ " => IntDerives

end DerivesNotation

example {Γ : Set IntFormula} (a b c : IntFormula)
    (h1 : Γ ⊢ᵢ a →ᵢ b →ᵢ c) (h2 : Γ ⊢ᵢ a ∧ᵢ b) :
    Γ ⊢ᵢ c := by
  have ha : Γ ⊢ᵢ a := IntDerives.mp h2 IntDerives.ax3_1
  have hb : Γ ⊢ᵢ b := IntDerives.mp h2 IntDerives.ax3_2
  exercise

example {Γ : Set IntFormula} (a b c : IntFormula)
    (h : Γ ⊢ᵢ a ∧ᵢ b →ᵢ c) (ha : Γ ⊢ᵢ a) (hb : Γ ⊢ᵢ b) :
    Γ ⊢ᵢ c := by
  exercise

-- If something derives in context Γ', it derives when adding any hypotheses to Γ'
theorem Γ_ext {Γ Γ' : Set IntFormula} {a : IntFormula} :
    (Γ' ⊆ Γ) → (Γ' ⊢ᵢ a) → (Γ ⊢ᵢ a) := by
  intro hΓ ha
  induction ha with
  exercise

theorem imp_selfᵢ {Γ : Set IntFormula} {a : IntFormula} :
    Γ ⊢ᵢ a →ᵢ a := by
  have ha1 : Γ ⊢ᵢ a →ᵢ a →ᵢ a := exercise
  have ha2 : Γ ⊢ᵢ a →ᵢ (a →ᵢ a) →ᵢ a := exercise
  apply IntDerives.mp ha1
  apply IntDerives.mp ha2
  exact exercise

theorem imp_trueᵢ {Γ : Set IntFormula} {a b : IntFormula} :
    (Γ ⊢ᵢ a) → (Γ ⊢ᵢ b →ᵢ a) := by
  intro h
  exercise

theorem deduction_revert {Γ : Set IntFormula} {a b : IntFormula} :
    (Γ ⊢ᵢ a →ᵢ b) → (Γ ∪ {a} ⊢ᵢ b) := by
  intro h
  have ha : Γ ∪ {a} ⊢ᵢ a := by
    exercise
  exercise

theorem deduction_intro {Γ : Set IntFormula} {a b : IntFormula} :
    (Γ ∪ {a} ⊢ᵢ b) → (Γ ⊢ᵢ a →ᵢ b) := by
  intro h
  induction h with
  | hyp hb =>
    rcases hb with hb | hb
    exercise
  | @ax0 x =>
    exercise
  | @ax1 a' b =>
    exact imp_trueᵢ IntDerives.ax1
  | @ax2 a' b c =>
    exact imp_trueᵢ IntDerives.ax2
  | @ax3_1 a' b =>
    exact imp_trueᵢ IntDerives.ax3_1
  | @ax3_2 a' b =>
    exact imp_trueᵢ IntDerives.ax3_2
  | @ax4 a' b =>
    exact imp_trueᵢ IntDerives.ax4
  | @ax5_1 a' b =>
    exact imp_trueᵢ IntDerives.ax5_1
  | @ax5_2 a' b =>
    exact imp_trueᵢ IntDerives.ax5_2
  | @ax6 a' b =>
    exact imp_trueᵢ IntDerives.ax6
  | @ax7 a' b =>
    exact imp_trueᵢ IntDerives.ax7
  | @ax8 a' b =>
    exact imp_trueᵢ IntDerives.ax8
  | @mp a' b' ha' ha'b' iha ihb =>
    exercise
