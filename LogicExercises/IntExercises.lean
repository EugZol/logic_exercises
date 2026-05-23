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
def iff (x y : IntFormula) : IntFormula := IntFormula.and (IntFormula.imp x y) (IntFormula.imp y x)

namespace FormulaNotation

notation "varᵢ" n => IntFormula.var n
notation "¬ᵢ" n => not n
notation "⊥ᵢ" => IntFormula.bot
infixr:35 " ∧ᵢ " => IntFormula.and
infixr:30 " ∨ᵢ " => IntFormula.or
infixr:25 " →ᵢ " => IntFormula.imp
infixr:25 " ↔ᵢ " => iff

end FormulaNotation

inductive IntDerives (Γ : Set IntFormula) : IntFormula → Prop
-- `hyp`: "hypothesis", if formula is in Γ, it derives
| hyp {a : IntFormula} : exercise → IntDerives Γ a
| var {x : Nat} : IntDerives Γ (varᵢ x)
| imp_k {a b : IntFormula} : IntDerives Γ (a →ᵢ b →ᵢ a)
| imp_s {a b c : IntFormula} : IntDerives Γ ((a →ᵢ b →ᵢ c) →ᵢ (a →ᵢ b) →ᵢ a →ᵢ c)
| and_elim_l {a b : IntFormula} : IntDerives Γ (a ∧ᵢ b →ᵢ a)
| and_elim_r {a b : IntFormula} : IntDerives Γ (a ∧ᵢ b →ᵢ b)
| and_intro {a b : IntFormula} : IntDerives Γ (a →ᵢ b →ᵢ a ∧ᵢ b )
| or_intro_l {a b : IntFormula} : IntDerives Γ (a →ᵢ a ∨ᵢ b)
| or_intro_r {a b : IntFormula} : IntDerives Γ (b →ᵢ a ∨ᵢ b )
| or_elim {a b c : IntFormula} : IntDerives Γ ((a →ᵢ c) →ᵢ (b →ᵢ c) →ᵢ a ∨ᵢ b →ᵢ c)
| contra {a b : IntFormula} : IntDerives Γ ((a →ᵢ b) →ᵢ (a →ᵢ ¬ᵢ b) →ᵢ ¬ᵢ a)
| exfalso {a b : IntFormula} : IntDerives Γ (a →ᵢ ¬ᵢ a →ᵢ b)
-- `mp`: "modus ponens", if `a` derives and `a →ᵢ b` derives, then
-- `b` derives (all in the same context Γ)
| mp {a b : IntFormula} : exercise

namespace DerivesNotation

infixr:20 " ⊢ᵢ " => IntDerives

end DerivesNotation

lemma imp_andᵢ {Γ : Set IntFormula} (a b c : IntFormula)
    (h1 : Γ ⊢ᵢ a →ᵢ b →ᵢ c) (h2 : Γ ⊢ᵢ a ∧ᵢ b) :
    Γ ⊢ᵢ c := by
  have ha : Γ ⊢ᵢ a := IntDerives.mp h2 IntDerives.and_elim_l
  have hb : Γ ⊢ᵢ b := IntDerives.mp h2 IntDerives.and_elim_r
  exercise

lemma and_impᵢ {Γ : Set IntFormula} (a b c : IntFormula)
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
  | @var x =>
    exercise
  | @imp_k a' b =>
    exact imp_trueᵢ IntDerives.imp_k
  | @imp_s a' b c =>
    exact imp_trueᵢ IntDerives.imp_s
  | @and_elim_l a' b =>
    exact imp_trueᵢ IntDerives.and_elim_l
  | @and_elim_r a' b =>
    exact imp_trueᵢ IntDerives.and_elim_r
  | @and_intro a' b =>
    exact imp_trueᵢ IntDerives.and_intro
  | @or_intro_l a' b =>
    exact imp_trueᵢ IntDerives.or_intro_l
  | @or_intro_r a' b =>
    exact imp_trueᵢ IntDerives.or_intro_r
  | @or_elim a' b =>
    exact imp_trueᵢ IntDerives.or_elim
  | @contra a' b =>
    exact imp_trueᵢ IntDerives.contra
  | @exfalso a' b =>
    exact imp_trueᵢ IntDerives.exfalso
  | @mp a' b' ha' ha'b' iha ihb =>
    exercise

theorem deduction_iff {Γ : Set IntFormula} {a b : IntFormula} :
    (Γ ∪ {a} ⊢ᵢ b) ↔ (Γ ⊢ᵢ a →ᵢ b) :=
  ⟨deduction_intro, deduction_revert⟩

theorem and_embed {Γ : Set IntFormula} {a b : IntFormula} :
    (Γ ⊢ᵢ a ∧ᵢ b) ↔ ((Γ ⊢ᵢ a) ∧ (Γ ⊢ᵢ b)) := by
  constructor <;> intro h
  exercise

theorem cut {Γ : Set IntFormula} {a b : IntFormula} :
    (Γ ⊢ᵢ a) → (Γ ∪ {a} ⊢ᵢ b) → (Γ ⊢ᵢ b) := by
  exercise

theorem cut_set {Γ Γ' : Set IntFormula} {hΓ' : Γ'.Finite} {b : IntFormula} :
    (Γ ∪ Γ' ⊢ᵢ b) → (∀ γ ∈ Γ', (Γ ⊢ᵢ γ)) → (Γ ⊢ᵢ b) := by
  intro h_ext h
  induction Γ', hΓ' using Set.Finite.induction_on with
  | empty =>
    exercise
  | @insert a s has hs ih =>
    have ha : (Γ ⊢ᵢ a) := h a (by tauto)
    have hb : (Γ ∪ s ⊢ᵢ b) := by
      exercise
    have hγ : (∀ γ ∈ s, Γ ⊢ᵢ γ) := by
      exercise
    exact ih hb hγ

theorem and_imp_iff {Γ : Set IntFormula} {a b c : IntFormula} :
    (Γ ⊢ᵢ a ∧ᵢ b →ᵢ c) ↔ (Γ ⊢ᵢ a →ᵢ b →ᵢ c) := by
  calc
    (Γ ⊢ᵢ a ∧ᵢ b →ᵢ c) ↔ (Γ ∪ {a ∧ᵢ b} ⊢ᵢ c) := Iff.symm deduction_iff
    _ ↔ (Γ ∪ {a ∧ᵢ b} ∪ {a, b} ⊢ᵢ c) := by
      exercise
    _ ↔ (Γ ∪ {a, b} ⊢ᵢ c) := by
      exercise
    _ ↔ (Γ ∪ {a} ∪ {b} ⊢ᵢ c) := by
      exercise
    _ ↔ (Γ ∪ {a} ⊢ᵢ b →ᵢ c) := exercise
    _ ↔ (Γ ⊢ᵢ a →ᵢ b →ᵢ c) := exercise
