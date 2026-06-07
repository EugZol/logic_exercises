module

import Mathlib
import LogicExercises.Exercise
import LogicExercises.IntFormula

set_option linter.privateModule false

-- Intuitionistic logic

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
