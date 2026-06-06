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
  -- ex
  exact IntDerives.mp hb (IntDerives.mp ha h1)
  -- /ex

lemma and_impᵢ {Γ : Set IntFormula} (a b c : IntFormula)
    (h : Γ ⊢ᵢ a ∧ᵢ b →ᵢ c) (ha : Γ ⊢ᵢ a) (hb : Γ ⊢ᵢ b) :
    Γ ⊢ᵢ c := by
  -- ex
  have hab : Γ ⊢ᵢ a ∧ᵢ b :=
    IntDerives.mp hb (IntDerives.mp ha IntDerives.and_intro)
  exact IntDerives.mp hab h
  -- /ex

-- If something derives in context Γ', it derives when adding any hypotheses to Γ'
theorem Γ_ext {Γ Γ' : Set IntFormula} {a : IntFormula} :
    (Γ' ⊆ Γ) → (Γ' ⊢ᵢ a) → (Γ ⊢ᵢ a) := by
  intro hΓ ha
  induction ha with
  -- ex
  | hyp hb =>
    apply IntDerives.hyp
    tauto
  | @imp_k a' b =>
    exact IntDerives.imp_k
  | @imp_s a' b c =>
    exact IntDerives.imp_s
  | @and_elim_l a' b =>
    exact IntDerives.and_elim_l
  | @and_elim_r a' b =>
    exact IntDerives.and_elim_r
  | @and_intro a' b =>
    exact IntDerives.and_intro
  | @or_intro_l a' b =>
    exact IntDerives.or_intro_l
  | @or_intro_r a' b =>
    exact IntDerives.or_intro_r
  | @or_elim a' b =>
    exact IntDerives.or_elim
  | @contra a' b =>
    exact IntDerives.contra
  | @exfalso a' b =>
    exact IntDerives.exfalso
  | @mp a' b' ha' ha'b' iha ihb =>
    exact IntDerives.mp iha ihb
  -- /ex

theorem imp_selfᵢ {Γ : Set IntFormula} {a : IntFormula} :
    Γ ⊢ᵢ a →ᵢ a := by
  have ha1 : Γ ⊢ᵢ a →ᵢ a →ᵢ a := /- ex -/ IntDerives.imp_k /- /ex -/
  have ha2 : Γ ⊢ᵢ a →ᵢ (a →ᵢ a) →ᵢ a := /- ex -/ IntDerives.imp_k /- /ex -/
  apply IntDerives.mp ha1
  apply IntDerives.mp ha2
  exact /- ex -/ IntDerives.imp_s /- /ex -/

theorem imp_trueᵢ {Γ : Set IntFormula} {a b : IntFormula} :
    (Γ ⊢ᵢ a) → (Γ ⊢ᵢ b →ᵢ a) := by
  intro h
  -- ex
  exact IntDerives.mp h IntDerives.imp_k
  -- /ex

theorem deduction_revert {Γ : Set IntFormula} {a b : IntFormula} :
    (Γ ⊢ᵢ a →ᵢ b) → (Γ ∪ {a} ⊢ᵢ b) := by
  intro h
  have ha : Γ ∪ {a} ⊢ᵢ a := by
    -- ex
    apply IntDerives.hyp
    tauto
    -- /ex
  -- ex
  apply IntDerives.mp (a := a) ha
  apply Γ_ext (Γ := Γ ∪ {a}) (Γ' := Γ) <;> tauto
  -- /ex

theorem deduction_intro {Γ : Set IntFormula} {a b : IntFormula} :
    (Γ ∪ {a} ⊢ᵢ b) → (Γ ⊢ᵢ a →ᵢ b) := by
  intro h
  induction h with
  | hyp hb =>
    rcases hb with hb | hb
    -- ex
    · eapply IntDerives.mp
      · apply IntDerives.hyp hb
      · apply IntDerives.imp_k
    · simp only [Set.mem_singleton_iff] at hb
      rw [hb]
      exact imp_selfᵢ
    -- /ex
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
    -- ex
    apply IntDerives.mp (a := a →ᵢ a') iha
    apply IntDerives.mp (a := a →ᵢ a' →ᵢ b') ihb
    exact IntDerives.imp_s
    -- /ex

theorem deduction_iff {Γ : Set IntFormula} {a b : IntFormula} :
    (Γ ∪ {a} ⊢ᵢ b) ↔ (Γ ⊢ᵢ a →ᵢ b) :=
  ⟨deduction_intro, deduction_revert⟩

theorem and_embed {Γ : Set IntFormula} {a b : IntFormula} :
    (Γ ⊢ᵢ a ∧ᵢ b) ↔ ((Γ ⊢ᵢ a) ∧ (Γ ⊢ᵢ b)) := by
  constructor <;> intro h
  -- ex
  · constructor
    · have h_and := IntDerives.and_elim_l (Γ := Γ) (a := a) (b := b)
      exact IntDerives.mp h h_and
    · have h_and := IntDerives.and_elim_r (Γ := Γ) (a := a) (b := b)
      exact IntDerives.mp h h_and
  · have h_and := IntDerives.and_intro (Γ := Γ) (a := a) (b := b)
    apply IntDerives.mp (a := b)
    { exact h.2 }
    apply IntDerives.mp (a := a)
    { exact h.1 }
    exact h_and
  -- /ex

theorem cut {Γ : Set IntFormula} {a b : IntFormula} :
    (Γ ⊢ᵢ a) → (Γ ∪ {a} ⊢ᵢ b) → (Γ ⊢ᵢ b) := by
  -- ex
  intro h h_ext
  apply IntDerives.mp h (deduction_intro h_ext)
  -- /ex

theorem cut_set {Γ Γ' : Set IntFormula} {hΓ' : Γ'.Finite} {b : IntFormula} :
    (Γ ∪ Γ' ⊢ᵢ b) → (∀ γ ∈ Γ', (Γ ⊢ᵢ γ)) → (Γ ⊢ᵢ b) := by
  intro h_ext h
  induction Γ', hΓ' using Set.Finite.induction_on with
  | empty =>
    -- ex
    rw [Set.union_empty] at h_ext
    exact h_ext
    -- /ex
  | @insert a s has hs ih =>
    have ha : (Γ ⊢ᵢ a) := h a (by tauto)
    have hb : (Γ ∪ s ⊢ᵢ b) := by
      -- ex
      apply IntDerives.mp (a := a)
      · exact Γ_ext (by tauto) ha
      · conv at h_ext =>
          rw [← Set.union_singleton]
          rw [← Set.union_assoc]
          rw [deduction_iff]
        exact h_ext
      -- /ex
    have hγ : (∀ γ ∈ s, Γ ⊢ᵢ γ) := by
      -- ex
      grind
      -- /ex
    exact ih hb hγ

theorem and_imp_iff {Γ : Set IntFormula} {a b c : IntFormula} :
    (Γ ⊢ᵢ a ∧ᵢ b →ᵢ c) ↔ (Γ ⊢ᵢ a →ᵢ b →ᵢ c) := by
  calc
    (Γ ⊢ᵢ a ∧ᵢ b →ᵢ c) ↔ (Γ ∪ {a ∧ᵢ b} ⊢ᵢ c) := Iff.symm deduction_iff
    _ ↔ (Γ ∪ {a ∧ᵢ b} ∪ {a, b} ⊢ᵢ c) := by
      -- ex
      refine ⟨Γ_ext (by tauto), ?_⟩
      intro h
      apply cut_set h
      · simp only [Set.mem_insert_iff, Set.mem_singleton_iff, forall_eq_or_imp, forall_eq]
        rw [deduction_iff]
        rw [deduction_iff]
        exact ⟨IntDerives.and_elim_l, IntDerives.and_elim_r⟩
      · exact Set.toFinite {a, b}
      -- /ex
    _ ↔ (Γ ∪ {a, b} ⊢ᵢ c) := by
      -- ex
      refine ⟨?_, Γ_ext (by grind)⟩
      conv =>
        left
        left
        rw [Set.union_assoc]
        rw [Set.union_comm {a ∧ᵢ b}]
        rw [← Set.union_assoc]
      apply cut
      rw [and_embed]
      constructor <;> apply IntDerives.hyp <;> tauto
      -- /ex
    _ ↔ (Γ ∪ {a} ∪ {b} ⊢ᵢ c) := by
      -- ex
      suffices Γ ∪ {a, b} = Γ ∪ {a} ∪ {b} by grind
      grind
      -- /ex
    _ ↔ (Γ ∪ {a} ⊢ᵢ b →ᵢ c) := /- ex -/ deduction_iff /- /ex -/
    _ ↔ (Γ ⊢ᵢ a →ᵢ b →ᵢ c) := /- ex -/ deduction_iff /- /ex -/

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
  -- ex
  fun hab ha => hab w (by tauto) ha
  -- /ex

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
  -- ex
  induction φ <;> intro w w' hww' <;>
    have h_mono : w ≤ w' → w.1 ⊆ w'.1 := m.mono w w' <;>
    grind [IntModel.forces]
  -- /ex

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
  -- ex
  exists varᵢ 0
  intro h
  have h' := derives_imp_model h
  specialize h' no_lem_model ⟨{}, by tauto⟩
  simp only [IntModel.forces, Set.mem_empty_iff_false, IntModel.forces_not, Subtype.forall,
    Subtype.mk_le_mk, Set.le_eq_subset, Set.empty_subset, forall_const, false_or] at h'
  specialize h' {0} (by tauto)
  tauto
  -- /ex

-- Exercises for derivability/non-derivability

example : ∃ a b : IntFormula, ¬ (∅ ⊢ᵢ (a →ᵢ b) →ᵢ ¬ᵢ a ∨ᵢ b) := by
  -- `A` is `varᵢ 0`, `B` is `varᵢ 1`
  exists varᵢ 0, varᵢ 1
  -- ex
  intro h
  have h' := derives_imp_model h
  -- Counter-model: `{} ---> {A, B}`
  -- At bottom `A -> B` is forced, but
  -- * `¬ A` is not forced because `A` is forced at the top
  -- * `B` is not forced by definition
  -- * hence, `¬ A ∨ B` is not forced
  set counter_model : IntModel := {
    worlds := {{}, {0, 1}}
    worlds_order := order_by_inclusion
    mono := by tauto
  }
  -- Providing counter-model and counter-world (bottom)
  specialize h' counter_model ⟨{}, by tauto⟩
  -- We have implication case of `forces` here at the root of tree:
  -- `{} ⊨ (A → B) → (¬ A ∨ B)`,
  -- which allows us to get any next world (including current) and get back statement that
  -- left conjunct `A → B` holds only if right conjunct `¬ A ∨ B` holds
  specialize h' ⟨{}, by tauto⟩ (by tauto) (by grind [IntModel.forces])
  -- Now we have statement `{} ⊨ ¬ A ∨ B`. "Or" case of `forces` is at the root.
  -- That case unfolds to `({} ⊨ ¬ A) OR {} ⊨ B`.
  -- `simp` will do the unfold and get rid of `B` case automatically,
  -- because it essentially equivalent to `B ∈ ∅`, which is obviously false.
  simp only [IntModel.forces, Set.mem_empty_iff_false, or_false] at h'
  -- Now we have statement `{} ⊨ ¬ A`. Again, that is implication in disguise,
  -- so we can provide any next world and get back statement that `¬ A` holds in
  -- that world as well.
  specialize h' ⟨{0, 1}, by tauto⟩ (by tauto) (by grind [IntModel.forces])
  -- Finally at h' we have `{A, B} ⊨ ⊥`, which is `False` by construction of `forces`
  -- `simp` or `tauto` will unfold `forces` and close the goal.
  simp [IntModel.forces] at h'
  -- /ex

lemma not_a_b_imp_a_b : ∀ a b : IntFormula, (∅ ⊢ᵢ ¬ᵢ a ∨ᵢ b →ᵢ (a →ᵢ b)) := by
  -- ex
  intro a b
  have or_elim : ∅ ⊢ᵢ (¬ᵢa →ᵢ a →ᵢ b) →ᵢ (b →ᵢ a →ᵢ b) →ᵢ ¬ᵢa ∨ᵢ b →ᵢ a →ᵢ b :=
    IntDerives.or_elim (Γ := ∅) (a := ¬ᵢ a) (b := b) (c := a →ᵢ b)
  have exfalso_alt : ∅ ⊢ᵢ (¬ᵢa →ᵢ a →ᵢ b) := by
    apply deduction_intro
    apply deduction_intro
    rw [Set.union_assoc]
    rw [Set.union_comm {¬ᵢ a}]
    rw [← Set.union_assoc]
    apply deduction_revert
    apply deduction_revert
    exact IntDerives.exfalso
  have imp_k : ∅ ⊢ᵢ b →ᵢ a →ᵢ b := IntDerives.imp_k
  grind [IntDerives.mp]
  -- /ex

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
  -- ex
  have w_unfold : ∀ (w : counter_model.worlds), w.1 ∈ ({∅, {0}, {1}} : Set (Set Nat)) := by
    simp [counter_model]
  have bot_not_a_not_b : (⟨∅, by tauto⟩ : counter_model.worlds) ⊨ᵢ (¬ᵢ((varᵢ 0) ∧ᵢ varᵢ 1)) := by
    intro w hr contra
    grind [IntModel.forces]
  specialize h' counter_model ⟨{}, by tauto⟩
  specialize h' ⟨{}, _⟩ (by tauto) bot_not_a_not_b
  rcases h' with h' | h'
  · specialize h' ⟨{0}, by tauto⟩ (by tauto) (by tauto)
    simp only [IntModel.forces] at h'
  · specialize h' ⟨{1}, by tauto⟩ (by tauto) (by tauto)
    simp only [IntModel.forces] at h'
  -- /ex

example : ∀ a b : IntFormula, (∅ ⊢ᵢ ¬ᵢ a ∨ᵢ ¬ᵢ b →ᵢ ¬ᵢ (a ∧ᵢ b)) := by
  -- ex
  intro a b
  have h := not_a_b_imp_a_b (a := a) (b := ¬ᵢ b)
  apply deduction_revert at h
  apply deduction_intro
  conv =>
    right
    simp [IntFormula.not]
  rw [and_imp_iff]
  exact h
  -- /ex

example : ∃ a b : IntFormula, ¬ (∅ ⊢ᵢ ¬ᵢ (a →ᵢ b) →ᵢ a ∧ᵢ ¬ᵢ b) := by
  -- ex
  exists varᵢ 0, varᵢ 1
  intro h
  have h' := derives_imp_model h
  specialize h' no_lem_model ⟨{}, by tauto⟩
  have w_unfold : ∀ (w : no_lem_model.worlds), w.1 ∈ ({∅, {0}} : Set (Set Nat)) := by
    simp [no_lem_model]
  have no_a_imp_b_top : (⟨{0}, by tauto⟩ : no_lem_model.worlds) ⊨ᵢ (¬ᵢ((varᵢ 0) →ᵢ varᵢ 1)) := by
    intro w' hww'
    have h : {0} ⊆ w'.1 := hww'
    specialize w_unfold w'
    have h : {0} = w'.1 := by
      cases w_unfold <;> grind
    intro hw'
    specialize hw' w' (by tauto) (by tauto)
    simp only [IntModel.forces] at hw'
    grind only [Set.mem_singleton_iff]
  have no_a_imp_b_bot : (⟨{}, by tauto⟩ : no_lem_model.worlds) ⊨ᵢ (¬ᵢ((varᵢ 0) →ᵢ varᵢ 1)) := by
    intro w' hww'
    specialize w_unfold w'
    rcases w_unfold with w_unfold | w_unfold
    · intro hw'
      specialize hw' ⟨{0}, by tauto⟩
      specialize hw' (show w'.1 ⊆ {0} by grind) (by tauto)
      simp only [IntModel.forces] at hw'
      tauto
    · apply no_a_imp_b_top
      grind only [Set.mem_singleton_iff]
  specialize h' ⟨{}, _⟩ (by tauto) no_a_imp_b_bot
  simp only [IntModel.forces] at h'
  tauto
  -- /ex

example : ∀ a b : IntFormula, (∅ ⊢ᵢ a ∧ᵢ ¬ᵢb →ᵢ ¬ᵢ(a →ᵢ b)) := by
  -- ex
  intro a b
  rw [and_imp_iff]
  apply deduction_intro
  apply deduction_intro
  apply deduction_intro
  have h1 : ∅ ∪ {a} ∪ {¬ᵢb} ∪ {a →ᵢ b} ⊢ᵢ b := by
    apply IntDerives.mp (a := a) (IntDerives.hyp _) (IntDerives.hyp _) <;>
      grind
  have h2 : ∅ ∪ {a} ∪ {¬ᵢb} ∪ {a →ᵢ b} ⊢ᵢ b →ᵢ ¬ᵢb →ᵢ ⊥ᵢ :=
    IntDerives.exfalso
  have h3 : ∅ ∪ {a} ∪ {¬ᵢb} ∪ {a →ᵢ b} ⊢ᵢ ¬ᵢb →ᵢ ⊥ᵢ := IntDerives.mp h1 h2
  apply IntDerives.mp (a := ¬ᵢb) (IntDerives.hyp (by grind)) h3
  -- /ex

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
  -- ex
  intro h
  have hΓ : Γ = Γ \ {a} ∪ {a} := by grind
  rw [hΓ]
  apply GentzDerives.id
  -- /ex

theorem GentzDerives.exfalso_in {Γ : Set IntFormula} {a : IntFormula} :
    ⊥ᵢ ∈ Γ → GentzDerives Γ a := by
  -- ex
  intro h
  have hΓ : Γ = Γ \ {⊥ᵢ} ∪ {⊥ᵢ} := by grind
  rw [hΓ]
  apply GentzDerives.exfalso
  -- /ex

theorem GentzDerives.false_left {Γ : Set IntFormula} {a : IntFormula} :
    GentzDerives Γ a → GentzDerives (Γ ∪ {¬ᵢa}) ⊥ᵢ := by
  -- ex
  intro h
  apply GentzDerives.imp_l h
  exact GentzDerives.exfalso
  -- /ex

theorem GentzDerives.false_right {Γ : Set IntFormula} {a : IntFormula} :
    GentzDerives (Γ ∪ {a}) ⊥ᵢ → GentzDerives Γ (¬ᵢa) :=
  /- ex -/ fun h => GentzDerives.imp_r h /- /ex -/

lemma set_comm_3 (α : Type) (a b c : Set α) : a ∪ b ∪ c = a ∪ c ∪ b := by ac_rfl

theorem GentzDerives.weaken {Γ : Set IntFormula} {a b : IntFormula} :
    GentzDerives Γ b → GentzDerives (Γ ∪ {a}) b := by
  -- ex
  intro h
  induction h <;> grind [GentzDerives, set_comm_3]
  -- /ex

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
    -- ex
    have h : {c} ⊆ Γ ∪ {a ∨ᵢ b} := by grind
    simp only [Set.union_singleton, Set.singleton_subset_iff] at h
    cases h <;> constructor
    · grind [GentzDerives.id, or_r_1]
    · grind [GentzDerives.id, GentzDerives.or_r_2]
    all_goals grind [GentzDerives.hyp]
    -- /ex
  | @exfalso Γ' c =>
    -- ex
    have h : {⊥ᵢ} ⊆ Γ ∪ {a ∨ᵢ b} := by grind
    simp only [Set.union_singleton] at h
    constructor <;> apply GentzDerives.exfalso_in <;> grind
    -- /ex
  | @or_l Γ' a' b' c ha' hb' iha ihb =>
    have h : {a' ∨ᵢ b'} ⊆ Γ ∪ {a ∨ᵢ b} := by grind
    simp only [Set.union_singleton, Set.singleton_subset_iff, Set.mem_insert_iff,
      IntFormula.or.injEq] at h
    rcases h with ⟨ha, hb⟩ | h
    -- ex
    · subst ha hb
      specialize iha (Γ := Γ ∪ {a'}) (a := a') (b := b') (by grind [set_comm_3])
      specialize ihb (Γ := Γ ∪ {b'}) (a := a') (b := b') (by grind [set_comm_3])
      simp only [Set.union_singleton, Set.mem_insert_iff, true_or, Set.insert_eq_of_mem] at iha
      simp only [Set.union_singleton, Set.mem_insert_iff, true_or, Set.insert_eq_of_mem] at ihb
      simp only [Set.union_singleton]
      exact ⟨iha.1, ihb.2⟩
    · have : Γ ∪ {a' ∨ᵢ b'} = Γ := by grind
      specialize iha (Γ := Γ ∪ {a'}) (a := a) (b := b) (by grind [set_comm_3])
      specialize ihb (Γ := Γ ∪ {b'}) (a := a) (b := b) (by grind [set_comm_3])
      have : GentzDerives (Γ ∪ {a} ∪ {a' ∨ᵢ b'}) c := by grind only [GentzDerives.or_l]
      have : GentzDerives (Γ ∪ {b} ∪ {a' ∨ᵢ b'}) c := by grind only [GentzDerives.or_l]
      grind only
    -- /ex
  | @or_r_1 Γ' a' b' ha iha =>
    -- ex
    grind only [GentzDerives.or_r_1]
    -- /ex
  | @or_r_2 Γ' a' b' hb ihb =>
    -- ex
    grind only [GentzDerives.or_r_2]
    -- /ex
  | @and_l Γ' a' b' c hc ih =>
    have h : {a' ∧ᵢ b'} ⊆ Γ ∪ {a ∨ᵢ b} := by grind
    simp only [Set.union_singleton, Set.singleton_subset_iff, Set.mem_insert_iff] at h
    rcases h with ⟨_, _⟩ | h
    -- ex
    have : Γ ∪ {a' ∧ᵢ b'} = Γ := by grind
    specialize ih (Γ := Γ ∪ {a'} ∪ {b'}) (a := a) (b := b) (by grind [set_comm_3])
    have : GentzDerives (Γ ∪ {a} ∪ {a' ∧ᵢ b'}) c := by grind only [GentzDerives.and_l]
    have : GentzDerives (Γ ∪ {b} ∪ {a' ∧ᵢ b'}) c := by grind only [GentzDerives.and_l]
    grind only
    -- /ex
  | @and_r Γ' a' b' ha hb iha ihb =>
    -- ex
    grind only [GentzDerives.and_r]
    -- /ex
  | @imp_l Γ' a' b' c ha hc iha ihc =>
    have h : {a' →ᵢ b'} ⊆ Γ ∪ {a ∨ᵢ b} := by grind
    simp only [Set.union_singleton, Set.singleton_subset_iff, Set.mem_insert_iff] at h
    rcases h with h | h
    { injection h }
    -- ex
    have hΓ : Γ ∪ {a' →ᵢ b'} = Γ := by grind
    constructor <;>
      rw [← hΓ] <;>
      rw [set_comm_3] <;>
      apply GentzDerives.imp_l
    · apply And.left
      apply iha (show Γ' ⊆ Γ ∪ {a ∨ᵢ b} by grind)
    · rw [set_comm_3]
      apply And.left
      apply ihc (show Γ' ∪ {b'} ⊆ Γ ∪ {b'} ∪ {a ∨ᵢ b} by grind)
    · apply And.right
      apply iha (show Γ' ⊆ Γ ∪ {a ∨ᵢ b} by grind)
    · rw [set_comm_3]
      apply And.right
      apply ihc (show Γ' ∪ {b'} ⊆ Γ ∪ {b'} ∪ {a ∨ᵢ b} by grind)
    -- /ex
  | @imp_r Γ' a' b' h ih =>
    -- ex
    constructor <;> apply GentzDerives.imp_r <;> rw [set_comm_3]
    · apply And.left
      apply ih (show Γ' ∪ {a'} ⊆ Γ ∪ {a'} ∪ {a ∨ᵢ b} by grind)
    · apply And.right
      apply ih (show Γ' ∪ {a'} ⊆ Γ ∪ {a'} ∪ {a ∨ᵢ b} by grind)
    -- /ex

theorem GentzDerives.or_inversion {Γ : Set IntFormula} {a b c : IntFormula} :
    GentzDerives (Γ ∪ {a ∨ᵢ b}) c → GentzDerives (Γ ∪ {a}) c ∧ GentzDerives (Γ ∪ {b}) c :=
  GentzDerives.or_inversion_aux (fun _ x => x)

theorem GentzDerives.and_inversion_aux {Δ Γ : Set IntFormula} {a b c : IntFormula} :
    Δ ⊆ Γ ∪ {a ∧ᵢ b} →
    GentzDerives Δ c →
    GentzDerives (Γ ∪ {a} ∪ {b}) c := by
  intro hΔ hc
  induction hc generalizing Γ a b with
  | @id Γ' c =>
    -- ex
    have h : {c} ⊆ Γ ∪ {a ∧ᵢ b} := by grind
    simp only [Set.union_singleton, Set.singleton_subset_iff] at h
    rcases h with h | h
    · subst h
      apply GentzDerives.and_r <;> apply GentzDerives.hyp <;> grind
    · apply GentzDerives.hyp
      grind
    -- /ex
  | @exfalso Γ' c =>
    -- ex
    have h : {⊥ᵢ} ⊆ Γ ∪ {a ∧ᵢ b} := by grind
    simp only [Set.union_singleton] at h
    apply GentzDerives.exfalso_in
    grind
    -- /ex
  | @or_l Γ' a' b' c ha' hb' iha ihb =>
    have h : {a' ∨ᵢ b'} ⊆ Γ ∪ {a ∧ᵢ b} := by grind
    simp only [Set.union_singleton, Set.singleton_subset_iff, Set.mem_insert_iff] at h
    rcases h with ⟨_, _⟩ | h
    -- ex
    have h_or : Γ ∪ {a' ∨ᵢ b'} = Γ := by grind
    have hΓ : Γ' ⊆ Γ ∪ {a ∧ᵢ b} := by grind
    rw [← h_or]
    rw [show Γ ∪ {a' ∨ᵢ b'} ∪ {a} ∪ {b} = Γ ∪ {a} ∪ {b} ∪ {a' ∨ᵢ b'} by grind]
    apply GentzDerives.or_l
    · specialize iha (Γ := Γ ∪ {a'}) (a := a) (b := b) (by grind)
      grind only
    · specialize ihb (Γ := Γ ∪ {b'}) (a := a) (b := b) (by grind)
      grind only
    -- /ex
  | @or_r_1 Γ' a' b' ha iha =>
    -- ex
    grind only [GentzDerives.or_r_1]
    -- /ex
  | @or_r_2 Γ' a' b' hb ihb =>
    -- ex
    grind only [GentzDerives.or_r_2]
    -- /ex
  | @and_l Γ' a' b' c hc ih =>
    -- ex
    have h_and : (a' ∧ᵢ b') ∈ Γ ∪ {a ∧ᵢ b} := by grind
    rcases h_and with h_and | ⟨ha, hb⟩
    · have : Γ' ⊆ Γ ∪ {a ∧ᵢ b} := by grind
      specialize ih (Γ := Γ ∪ {a'} ∪ {b'}) (a := a) (b := b) (by grind)
      have ih : GentzDerives (Γ ∪ {a} ∪ {b} ∪ {a' ∧ᵢ b'}) c := by grind [GentzDerives.and_l]
      have : Γ ∪ {a' ∧ᵢ b'} = Γ := by grind
      grind only
    · have : Γ' ⊆ Γ ∪ {a' ∧ᵢ b'} := by grind
      specialize ih (Γ := Γ ∪ {a'} ∪ {b'}) (a := a') (b := b') (by grind)
      rw [show Γ ∪ {a'} ∪ {b'} ∪ {a'} ∪ {b'} = Γ ∪ {a'} ∪ {b'} by grind] at ih
      exact ih
    -- /ex
  | @and_r Γ' a' b' ha hb iha ihb =>
    -- ex
    grind only [GentzDerives.and_r]
    -- /ex
  | @imp_l Γ' a' b' c ha hc iha ihc =>
    have h : {a' →ᵢ b'} ⊆ Γ ∪ {a ∧ᵢ b} := by grind
    simp only [Set.union_singleton, Set.singleton_subset_iff, Set.mem_insert_iff] at h
    rcases h with h | h
    { injection h }
    -- ex
    specialize ihc (Γ := Γ ∪ {b'}) (a := a) (b := b) (by grind)
    rw [show Γ ∪ {b'} ∪ {a} ∪ {b} = Γ ∪ {a} ∪ {b} ∪ {b'} by grind] at ihc
    specialize iha (Γ := Γ) (a := a) (b := b) (by grind)
    rw [show Γ ∪ {a} ∪ {b} = Γ ∪ {a} ∪ {b} ∪ {a' →ᵢ b'} by grind]
    apply GentzDerives.imp_l iha ihc
    -- /ex
  | @imp_r Γ' a' b' h ih =>
    -- ex
    apply GentzDerives.imp_r
    specialize ih (Γ := Γ ∪ {a'}) (a := a) (b := b) (by grind)
    grind only
    -- /ex

theorem GentzDerives.and_inversion {Γ : Set IntFormula} {a b c : IntFormula} :
    GentzDerives (Γ ∪ {a ∧ᵢ b}) c →
    GentzDerives (Γ ∪ {a} ∪ {b}) c :=
  GentzDerives.and_inversion_aux (fun _ x => x)

theorem GentzDerives.and_r_inversion_aux {Δ Γ : Set IntFormula} {a b : IntFormula} :
    Δ ⊆ Γ →
    GentzDerives Δ (a ∧ᵢ b) →
    GentzDerives Γ a ∧ GentzDerives Γ b := by
  intro hΔ hab
  generalize hab' : (a ∧ᵢ b) = c at hab
  induction hab generalizing Γ a b with
  | @id Γ' a' =>
    -- ex
    grind [GentzDerives.mono, GentzDerives.and_l, GentzDerives.hyp]
    -- /ex
  | @exfalso =>
    -- ex
    grind [GentzDerives.exfalso_in]
    -- /ex
  | @or_l Γ' a' b' c ha' hb' iha ihb =>
    -- ex
    subst hab'
    specialize @iha (Γ ∪ {a'}) a b (by grind) rfl
    specialize @ihb (Γ ∪ {b'}) a b (by grind) rfl
    have hΓ : Γ = Γ ∪ {a' ∨ᵢ b'} := by grind
    grind [GentzDerives.or_l]
    -- /ex
  | @or_r_1 Γ' a' b' ha iha =>
    -- ex
    grind only [GentzDerives.or_r_1]
    -- /ex
  | @or_r_2 Γ' a' b' hb ihb =>
    -- ex
    grind only [GentzDerives.or_r_2]
    -- /ex
  | @and_l Γ' a' b' c hc ih =>
    -- ex
    specialize @ih (Γ ∪ {a'} ∪ {b'}) a b
    have : Γ = Γ ∪ {a' ∧ᵢ b'} := by grind
    grind [GentzDerives.and_l]
    -- /ex
  | @and_r Γ' a' b' ha hb iha ihb =>
    -- ex
    grind [GentzDerives.mono]
    -- /ex
  | @imp_l Γ' a' b' c ha hc iha ihc =>
    -- ex
    have hΓ : Γ = Γ ∪ {a' →ᵢ b'} := by grind
    specialize @ihc (Γ ∪ {b'}) a b
    grind [GentzDerives.imp_l, GentzDerives.mono]
    -- /ex
  | @imp_r Γ' a' b' h ih =>
    -- ex
    injection hab'
    -- /ex

theorem GentzDerives.and_r_inversion {Γ : Set IntFormula} {a b : IntFormula} :
    GentzDerives Γ (a ∧ᵢ b) →
    GentzDerives Γ a ∧ GentzDerives Γ b :=
  GentzDerives.and_r_inversion_aux (fun _ x => x)

theorem GentzDerives.cut_aux
    {Γ Δ : Set IntFormula} {a b : IntFormula} :
    Δ ⊆ Γ →
    GentzDerives Δ a →
    GentzDerives (Γ ∪ {a}) b →
    GentzDerives Γ b := by
  induction a generalizing Γ Δ b with
  | var x =>
    intro hΔ ha hb
    generalize hag : (varᵢ x) = a at ha
    induction ha generalizing Γ Θ b with
    | @id Γ' a' =>
      have hΓ : Γ = Γ ∪ {varᵢ x} := by grind
      grind [GentzDerives.mono]
    | @exfalso => exact GentzDerives.exfalso_in (by grind)
    | @or_l Γ' a' b' c ha' hb' iha ihb =>
      subst hag
      specialize iha (Γ := Γ ∪ {a'}) (b := b) (by grind)
        (by grind) hb rfl
      specialize ihb (Γ := Γ ∪ {b'}) (Θ := Θ) (b := b) (by grind)
        (by grind) hb rfl
      rw [show Γ = Γ ∪ {a' ∨ᵢ b'} by grind]
      exact GentzDerives.or_l iha ihb
    | @or_r_1 => injection hag
    | @or_r_2 => injection hag
    | @and_l Γ' a' b' c hc ih =>
      subst hag
      specialize ih (Γ := Γ ∪ {a'} ∪ {b'}) (Θ := Θ) (b := b) (by grind)
        (by grind) hb rfl
      rw [show Γ = Γ ∪ {a' ∧ᵢ b'} by grind]
      exact GentzDerives.and_l ih
    | @and_r => injection hag
    | @imp_l Γ' a' b' c ha hc iha ihc =>
      subst hag
      rw [show Γ = Γ ∪ {a' →ᵢ b'} by grind]
      specialize ihc (Γ := Γ ∪ {b'})  (Θ := Θ) (b := b) (by grind)
        (by grind) hb rfl
      apply GentzDerives.imp_l ?_ ihc
      apply GentzDerives.mono (by grind) ha
    | @imp_r => injection hag
  | and a' b' iha ihb =>
    intro hΔ ha hb
    generalize hag : (a' ∧ᵢ b') = a at ha
    induction ha generalizing Γ b with
    | @id Γ' a'' =>
      have hΓ : Γ = Γ ∪ {a' ∧ᵢ b'} := by grind
      grind [GentzDerives.mono]
    | @exfalso => exact GentzDerives.exfalso_in (by grind)
    | @or_l Γ' a'' b'' c ha'' hb'' iha' ihb' =>
      subst hag
      rw [show Γ = Γ ∪ {a'' ∨ᵢ b''} by grind]
      apply GentzDerives.or_l
      · have : GentzDerives (Γ ∪ {a''} ∪ {a' ∧ᵢ b'}) b := by
          rw [set_comm_3]
          apply GentzDerives.mono (by grind) hb
        specialize @iha' (Γ ∪ {a''}) b (by grind) (by assumption) rfl
        exact iha'
      · have : GentzDerives (Γ ∪ {b''} ∪ {a' ∧ᵢ b'}) b := by
          rw [set_comm_3]
          apply GentzDerives.mono (by grind) hb
        specialize @ihb' (Γ ∪ {b''}) b (by grind) (by assumption) rfl
        exact ihb'
    | @or_r_1 => injection hag
    | @or_r_2 => injection hag
    | @and_l Γ' a'' b'' c hc ih =>
      subst hag
      have : GentzDerives (Γ ∪ {a''} ∪ {b''} ∪ {a' ∧ᵢ b'}) b := by
        rw [show Γ ∪ {a''} ∪ {b''} ∪ {a' ∧ᵢ b'} = Γ ∪ {a' ∧ᵢ b'} ∪ {a''} ∪ {b''} by grind]
        apply GentzDerives.mono (by grind) hb
      specialize @ih (Γ ∪ {a''} ∪ {b''}) b (by grind) (by assumption) rfl
      rw [show Γ = Γ ∪ {a'' ∧ᵢ b''} by grind]
      apply GentzDerives.and_l ih
    | @and_r Γ' a'' b'' ha'' hb'' iha'' ihb'' =>
      injection hag with haeq hbeq
      subst haeq hbeq

      have : GentzDerives (Γ ∪ {a'} ∪ {a' ∧ᵢ b'}) b :=
        GentzDerives.mono (Γ := Γ ∪ {a' ∧ᵢ b'}) (by grind) hb
      specialize @iha (Γ ∪ {a'}) Γ' b (by grind) (by assumption)
    | @imp_l Γ' a' b' c ha hc iha ihc =>
      specialize ihc (Γ := Γ ∪ {b'})  (Θ := Θ) (b := b)
      have : Γ = Γ ∪ {a' →ᵢ b'} := by grind
      grind [GentzDerives.imp_l, GentzDerives.mono]
    | @imp_r => injection hag

-- theorem not_derives_imp_counter_model {a : IntFormula} :
--     ¬ (∅ ⊢ᵢ a) → ∃ (m : IntModel) (w : m.worlds), ¬ (w ⊨ᵢ a) := by
--   sorry
