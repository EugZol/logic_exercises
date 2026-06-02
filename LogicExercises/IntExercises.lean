module

import Mathlib
import LogicExercises.Exercise

set_option linter.privateModule false

-- Intuitionistic logic

inductive IntFormula : Type
| var : Nat → IntFormula
| and : IntFormula → IntFormula → IntFormula
| or  : IntFormula → IntFormula → IntFormula
| imp  : IntFormula → IntFormula → IntFormula
| bot  : IntFormula
deriving Repr, DecidableEq

def IntFormula.not (x : IntFormula) : IntFormula := IntFormula.imp x IntFormula.bot
def IntFormula.iff (x y : IntFormula) : IntFormula :=
  IntFormula.and (IntFormula.imp x y) (IntFormula.imp y x)

local notation "varᵢ" n => IntFormula.var n
local prefix:40 "¬ᵢ" => IntFormula.not
local notation "⊥ᵢ" => IntFormula.bot
local infixr:35 " ∧ᵢ " => IntFormula.and
local infixr:30 " ∨ᵢ " => IntFormula.or
local infixr:25 " →ᵢ " => IntFormula.imp
local infixr:25 " ↔ᵢ " => IntFormula.iff

inductive IntDerives (Γ : Set IntFormula) : IntFormula → Prop
| hyp {a : IntFormula} : a ∈ Γ → IntDerives Γ a
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
| mp {a b : IntFormula} : IntDerives Γ a → IntDerives Γ (a →ᵢ b) → IntDerives Γ b

local infixr:20 " ⊢ᵢ " => IntDerives

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
  | _ => exercise

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

-- Kripke semantics

structure IntModel : Type where
  worlds : Set (Set Nat)
  worlds_order : PartialOrder worlds
  mono : ∀ w w' : worlds, w ≤ w' → w.1 ⊆ w'.1

def IntModel.forces {m : IntModel} (w : m.worlds) (φ : IntFormula) : Prop :=
  match φ with
  | IntFormula.var x => x ∈ w.1
  | IntFormula.and φ₁ φ₂ => IntModel.forces w φ₁ ∧ IntModel.forces w φ₂
  | IntFormula.or φ₁ φ₂ => IntModel.forces w φ₁ ∨ IntModel.forces w φ₂
  | IntFormula.imp φ₁ φ₂ => ∀ w' : m.worlds, w ≤ w' →
    IntModel.forces w' φ₁ → IntModel.forces w' φ₂
  | IntFormula.bot => False

local infix:50 " ⊨ᵢ " => IntModel.forces

theorem IntModel.forces_imp_self {m : IntModel} (w : m.worlds) (a b : IntFormula) :
    (w ⊨ᵢ (a →ᵢ b)) → (w ⊨ᵢ a) → (w ⊨ᵢ b) :=
  exercise

theorem IntModel.forces_not {m : IntModel} (w : m.worlds) (φ : IntFormula) :
    w ⊨ᵢ (¬ᵢ φ) ↔
      ∀ w' : m.worlds, w ≤ w' → ¬ w' ⊨ᵢ φ := by
  grind [IntModel.forces, IntFormula.not]

theorem IntModel.forces_not_self {m : IntModel} (w : m.worlds) (φ : IntFormula) :
    w ⊨ᵢ (¬ᵢ φ) → ¬ w ⊨ᵢ φ := by
  grind [IntModel.forces_not]

theorem IntModel.forces_mono {m : IntModel} {w w' : m.worlds}
    (hww' : w ≤ w') {φ : IntFormula} :
    (w ⊨ᵢ φ) → (w' ⊨ᵢ φ) := by
  revert w w'
  -- Use `induction φ`
  exercise

-- Correctness

@[reducible]
def order_by_inclusion {X : Set (Set Nat)} : PartialOrder X :=  {
    le := fun a b => a.1 ⊆ b.1
    le_refl := by tauto
    le_trans := by tauto
    le_antisymm := by
      simp only [Subtype.forall, Subtype.mk.injEq]
      intro a ha b hb hab hba
      grind
  }

theorem derives_imp_model {a : IntFormula} :
    (∅ ⊢ᵢ a) → ∀ (m : IntModel) (w : m.worlds), (w ⊨ᵢ a) := by
  intro h
  induction h <;>
    grind [IntModel.forces_mono, IntModel.forces, IntModel.forces_not,
      IntModel.forces_imp_self]

def no_lem_model : IntModel := {
  worlds := {{}, {0}}
  worlds_order := order_by_inclusion
  mono := by tauto
}

theorem no_lem : ∃ a : IntFormula, ¬ (∅ ⊢ᵢ a ∨ᵢ ¬ᵢ a) := by
  exercise

-- Exercises for derivability/non-derivability

example : ∃ a b : IntFormula, ¬ (∅ ⊢ᵢ (a →ᵢ b) →ᵢ ¬ᵢ a ∨ᵢ b) := by
  -- `A` is `varᵢ 0`, `B` is `varᵢ 1`
  exists varᵢ 0, varᵢ 1
  exercise

lemma not_a_b_imp_a_b : ∀ a b : IntFormula, (∅ ⊢ᵢ ¬ᵢ a ∨ᵢ b →ᵢ (a →ᵢ b)) := by
  exercise

example : ∃ a b : IntFormula, ¬ (∅ ⊢ᵢ ¬ᵢ (a ∧ᵢ b) →ᵢ ¬ᵢ a ∨ᵢ ¬ᵢ b) := by
  exists varᵢ 0, varᵢ 1
  intro h
  have h' := derives_imp_model h
  -- A B
  -- \/
  -- {}
  set counter_model : IntModel := {
    worlds := {{}, {0}, {1}}
    worlds_order := order_by_inclusion
    mono := by tauto
  }
  exercise

example : ∀ a b : IntFormula, (∅ ⊢ᵢ ¬ᵢ a ∨ᵢ ¬ᵢ b →ᵢ ¬ᵢ (a ∧ᵢ b)) := by
  exercise

example : ∃ a b : IntFormula, ¬ (∅ ⊢ᵢ ¬ᵢ (a →ᵢ b) →ᵢ a ∧ᵢ ¬ᵢ b) := by
  exercise

example : ∀ a b : IntFormula, (∅ ⊢ᵢ a ∧ᵢ ¬ᵢb →ᵢ ¬ᵢ(a →ᵢ b)) := by
  exercise

-- Gentzen formulation

inductive GentzDerives : (Γ : Set IntFormula) → IntFormula → Prop
| id {Γ} {a : IntFormula} : GentzDerives (Γ ∪ {a}) a
| exfalso {Γ} {a : IntFormula} : GentzDerives (Γ ∪ {⊥ᵢ}) a
| or_l {Γ} {a b c : IntFormula} :
  GentzDerives (Γ ∪ {a}) c → GentzDerives (Γ ∪ {b}) c → GentzDerives (Γ ∪ {a ∨ᵢ b}) c
| or_r_1 {Γ} {a b : IntFormula} :
  GentzDerives Γ a → GentzDerives Γ (a ∨ᵢ b)
| or_r_2 {Γ} {a b : IntFormula} :
  GentzDerives Γ b → GentzDerives Γ (a ∨ᵢ b)
| and_l {Γ} {a b c : IntFormula} :
  GentzDerives (Γ ∪ {a} ∪ {b}) c → GentzDerives (Γ ∪ {a ∧ᵢ b}) c
| and_r {Γ} {a b : IntFormula} :
  GentzDerives Γ a → GentzDerives Γ b → GentzDerives Γ (a ∧ᵢ b)
| imp_l {Γ} {a b c : IntFormula} :
  GentzDerives Γ a → GentzDerives (Γ ∪ {b}) c → GentzDerives (Γ ∪ {a →ᵢ b}) c
| imp_r {Γ} {a b : IntFormula} :
  GentzDerives (Γ ∪ {a}) b → GentzDerives Γ (a →ᵢ b)

theorem GentzDerives.hyp {Γ : Set IntFormula} {a : IntFormula} :
    a ∈ Γ → GentzDerives Γ a := by
  exercise

theorem GentzDerives.exfalso_in {Γ : Set IntFormula} {a : IntFormula} :
    ⊥ᵢ ∈ Γ → GentzDerives Γ a := by
  exercise

theorem GentzDerives.false_left {Γ : Set IntFormula} {a : IntFormula} :
    GentzDerives Γ a → GentzDerives (Γ ∪ {¬ᵢa}) ⊥ᵢ := by
  exercise

theorem GentzDerives.false_right {Γ : Set IntFormula} {a : IntFormula} :
    GentzDerives (Γ ∪ {a}) ⊥ᵢ → GentzDerives Γ (¬ᵢa) :=
  exercise

lemma set_comm_3 (α : Type) (a b c : Set α) : a ∪ b ∪ c = a ∪ c ∪ b := by ac_rfl

theorem GentzDerives.weaken {Γ : Set IntFormula} {a b : IntFormula} :
    GentzDerives Γ b → GentzDerives (Γ ∪ {a}) b := by
  exercise

theorem GentzDerives.mono {Γ Γ' : Set IntFormula} {a : IntFormula} :
    Γ ⊆ Γ' → GentzDerives Γ a → GentzDerives Γ' a := by
  intro h ha
  induction ha generalizing Γ' with
  | @id Γ'' a' => grind [GentzDerives.hyp]
  | @exfalso Γ'' a' => grind [GentzDerives.exfalso_in]
  | @or_l Γ'' a' b' c ha' hb' iha ihb =>
    have hΓ : Γ' = Γ' \ (Γ'' ∪ {a' ∨ᵢ b'}) ∪ Γ'' ∪ {a' ∨ᵢ b'} := by grind
    grind [or_l]
  | or_r_1 => grind [or_r_1]
  | or_r_2 => grind [or_r_2]
  | @and_l Γ'' a' b' c hc ih =>
    have hΓ : Γ' = Γ' \ (Γ'' ∪ {a' ∧ᵢ b'}) ∪ Γ'' ∪ {a' ∧ᵢ b'} := by grind
    grind [GentzDerives.and_l]
  | and_r => grind [GentzDerives.and_r]
  | @imp_l Γ'' a' b' c ha hc iha ihc =>
    have hΓ : Γ' = Γ' \ (Γ'' ∪ {a' →ᵢ b'}) ∪ Γ'' ∪ {a' →ᵢ b'} := by grind
    grind [GentzDerives.imp_l]
  | imp_r => grind [GentzDerives.imp_r]

theorem GentzDerives.or_inversion_aux {Δ Γ : Set IntFormula} {a b c : IntFormula} :
    Δ ⊆ Γ ∪ {a ∨ᵢ b} →
    GentzDerives Δ c →
    GentzDerives (Γ ∪ {a}) c ∧ GentzDerives (Γ ∪ {b}) c := by
  intro hΔ hc
  induction hc generalizing Γ a b with
  | @id Γ' c =>
    exercise
  | @exfalso Γ' c =>
    exercise
  | @or_l Γ' a' b' c ha' hb' iha ihb =>
    have h : {a' ∨ᵢ b'} ⊆ Γ ∪ {a ∨ᵢ b} := by grind
    simp only [Set.union_singleton, Set.singleton_subset_iff, Set.mem_insert_iff,
      IntFormula.or.injEq] at h
    rcases h with ⟨ha, hb⟩ | h
    exercise
  | @or_r_1 Γ' a' b' ha iha =>
    exercise
  | @or_r_2 Γ' a' b' hb ihb =>
    exercise
  | @and_l Γ' a' b' c hc ih =>
    have h : {a' ∧ᵢ b'} ⊆ Γ ∪ {a ∨ᵢ b} := by grind
    simp only [Set.union_singleton, Set.singleton_subset_iff, Set.mem_insert_iff] at h
    rcases h with ⟨_, _⟩ | h
    exercise
  | @and_r Γ' a' b' ha hb iha ihb =>
    exercise
  | @imp_l Γ' a' b' c ha hc iha ihc =>
    have h : {a' →ᵢ b'} ⊆ Γ ∪ {a ∨ᵢ b} := by grind
    simp only [Set.union_singleton, Set.singleton_subset_iff, Set.mem_insert_iff] at h
    rcases h with h | h
    { injection h }
    exercise
  | @imp_r Γ' a' b' h ih =>
    exercise

theorem GentzDerives.or_inversion {Γ : Set IntFormula} {a b c : IntFormula} :
    GentzDerives (Γ ∪ {a ∨ᵢ b}) c → GentzDerives (Γ ∪ {a}) c ∧ GentzDerives (Γ ∪ {b}) c := by
  exact GentzDerives.or_inversion_aux (by intro x hx; exact hx)

theorem GentzDerives.cut {Γ : Set IntFormula} {a b : IntFormula} :
    GentzDerives Γ a → GentzDerives (Γ ∪ {a}) b → GentzDerives Γ b := by
  intro ha
  induction ha with
  | @id Γ' a' =>
    rw [Set.union_assoc]
    rw [show {(a' : IntFormula)} ∪ {(a' : IntFormula)} = {a'} by grind]
    tauto
  | @exfalso Γ' a' =>
    intro
    exact exfalso
  | @or_l Γ' a' b' c ha' hb' iha ihb =>
    intro h
    rw [set_comm_3] at h

theorem not_derives_imp_counter_model {a : IntFormula} :
    ¬ (∅ ⊢ᵢ a) → ∃ (m : IntModel) (w : m.worlds), ¬ (w ⊨ᵢ a) := by
  sorry
