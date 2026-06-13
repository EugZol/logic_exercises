module

import Mathlib
import LogicExercises.Exercise
import LogicExercises.IntFormula

set_option linter.privateModule false

-- Gentzen formulation of intuitionistic logic

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
  | _ => exercise

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
    GentzDerives (Γ ∪ {a ∨ᵢ b}) c → GentzDerives (Γ ∪ {a}) c ∧ GentzDerives (Γ ∪ {b}) c :=
  GentzDerives.or_inversion_aux (fun _ x => x)

theorem GentzDerives.and_inversion_aux {Δ Γ : Set IntFormula} {a b c : IntFormula} :
    Δ ⊆ Γ ∪ {a ∧ᵢ b} →
    GentzDerives Δ c →
    GentzDerives (Γ ∪ {a} ∪ {b}) c := by
  intro hΔ hc
  induction hc generalizing Γ a b with
  | @id Γ' c =>
    exercise
  | @exfalso Γ' c =>
    exercise
  | @or_l Γ' a' b' c ha' hb' iha ihb =>
    have h : {a' ∨ᵢ b'} ⊆ Γ ∪ {a ∧ᵢ b} := by grind
    simp only [Set.union_singleton, Set.singleton_subset_iff, Set.mem_insert_iff] at h
    rcases h with ⟨_, _⟩ | h
    exercise
  | @or_r_1 Γ' a' b' ha iha =>
    exercise
  | @or_r_2 Γ' a' b' hb ihb =>
    exercise
  | @and_l Γ' a' b' c hc ih =>
    exercise
  | @and_r Γ' a' b' ha hb iha ihb =>
    exercise
  | @imp_l Γ' a' b' c ha hc iha ihc =>
    have h : {a' →ᵢ b'} ⊆ Γ ∪ {a ∧ᵢ b} := by grind
    simp only [Set.union_singleton, Set.singleton_subset_iff, Set.mem_insert_iff] at h
    rcases h with h | h
    { injection h }
    exercise
  | @imp_r Γ' a' b' h ih =>
    exercise

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
    exercise
  | @exfalso =>
    exercise
  | @or_l Γ' a' b' c ha' hb' iha ihb =>
    exercise
  | @or_r_1 Γ' a' b' ha iha =>
    exercise
  | @or_r_2 Γ' a' b' hb ihb =>
    exercise
  | @and_l Γ' a' b' c hc ih =>
    exercise
  | @and_r Γ' a' b' ha hb iha ihb =>
    exercise
  | @imp_l Γ' a' b' c ha hc iha ihc =>
    exercise
  | @imp_r Γ' a' b' h ih =>
    exercise

theorem GentzDerives.and_r_inversion {Γ : Set IntFormula} {a b : IntFormula} :
    GentzDerives Γ (a ∧ᵢ b) →
    GentzDerives Γ a ∧ GentzDerives Γ b :=
  GentzDerives.and_r_inversion_aux (fun _ x => x)

theorem GentzDerives.imp_inversion_aux {Δ Γ : Set IntFormula} {a b c : IntFormula} :
    Δ ⊆ Γ ∪ {a →ᵢ b} →
    GentzDerives Δ c →
    GentzDerives (Γ ∪ {b}) c := by
  intro hΔ hc
  induction hc generalizing Γ a b with
  | @id Γ' c =>
    exercise
  | @exfalso Γ' c =>
    exercise
  | @or_l Γ' a' b' c ha' hb' iha ihb =>
    have h : {a' ∨ᵢ b'} ⊆ Γ ∪ {a →ᵢ b} := by grind
    simp only [Set.union_singleton, Set.singleton_subset_iff, Set.mem_insert_iff] at h
    rcases h with ⟨_, _⟩ | h
    exercise
  | @or_r_1 Γ' a' b' ha iha =>
    exercise
  | @or_r_2 Γ' a' b' hb ihb =>
    exercise
  | @and_l Γ' a' b' c hc ih =>
    exercise
  | @and_r Γ' a' b' ha hb iha ihb =>
    exercise
  | @imp_l Γ' a' b' c' ha hc iha ihc =>
    have h : {a' →ᵢ b'} ⊆ Γ ∪ {a →ᵢ b} := by grind
    simp only [Set.union_singleton, Set.singleton_subset_iff, Set.mem_insert_iff] at h
    rcases h with ⟨_, _⟩ | h
    exercise
  | @imp_r Γ' a' b' h ih =>
    exercise

theorem GentzDerives.imp_inversion {Γ : Set IntFormula} {a b c : IntFormula} :
    GentzDerives (Γ ∪ {a →ᵢ b}) c →
    GentzDerives (Γ ∪ {b}) c :=
  GentzDerives.imp_inversion_aux (fun _ x => x)

theorem GentzDerives.bot_inversion_aux {Δ Γ : Set IntFormula} {a : IntFormula} :
    Δ ⊆ Γ →
    GentzDerives Δ ⊥ᵢ →
    GentzDerives Γ a := by
  intro hΔ hb
  generalize hb' : ⊥ᵢ = b at hb
  induction hb generalizing Γ a with
  | @id Γ' a' =>
    exercise
  | @exfalso => exercise
  | @or_l Γ' a' b' c ha' hb' iha ihb =>
    exercise
  | @or_r_1 => injection hb'
  | @or_r_2 => injection hb'
  | @and_l Γ' a' b' c hc ih =>
    exercise
  | @and_r => injection hb'
  | @imp_l Γ' a' b' c ha hc iha ihc =>
    exercise
  | @imp_r => injection hb'

theorem GentzDerives.bot_inversion {Γ : Set IntFormula} {a : IntFormula} :
    GentzDerives Γ ⊥ᵢ →
    GentzDerives Γ a :=
  GentzDerives.bot_inversion_aux (fun _ x => x)

-- Extracting parts of GentzDerives.cut_aux for performance

lemma GentzDerives.cut_aux_var_case (x : ℕ) (Γ Δ : Set IntFormula) (b : IntFormula) :
    Δ ⊆ Γ →
    GentzDerives Δ (varᵢ x) →
    GentzDerives (Γ ∪ {varᵢ x}) b →
    GentzDerives Γ b := by
  intro hΔ ha hb
  generalize hag : (varᵢ x) = a at ha
  induction ha generalizing Γ b with
  | @id Γ' a' =>
    exercise
  | @exfalso => exact GentzDerives.exfalso_in (by grind)
  | @or_l Γ' a' b' c ha' hb' iha ihb =>
    exercise
  | @or_r_1 => injection hag
  | @or_r_2 => injection hag
  | @and_l Γ' a' b' c hc ih =>
    exercise
  | @and_r => injection hag
  | @imp_l Γ' a' b' c ha hc iha ihc =>
    exercise
  | @imp_r => injection hag

lemma GentzDerives.cut_aux_and_case (a' b' : IntFormula)
    (iha : ∀ {Γ Δ : Set IntFormula} {b : IntFormula},
      Δ ⊆ Γ → GentzDerives Δ a' → GentzDerives (Γ ∪ {a'}) b → GentzDerives Γ b)
    (ihb : ∀ {Γ Δ : Set IntFormula} {b : IntFormula},
      Δ ⊆ Γ → GentzDerives Δ b' → GentzDerives (Γ ∪ {b'}) b → GentzDerives Γ b)
    (Γ Δ : Set IntFormula) (b : IntFormula) :
    Δ ⊆ Γ →
    GentzDerives Δ (a' ∧ᵢ b') →
    GentzDerives (Γ ∪ {a' ∧ᵢ b'}) b →
    GentzDerives Γ b := by
  intro hΔ ha hb
  generalize hag : (a' ∧ᵢ b') = a at ha
  induction ha generalizing Γ b with
  | @id Γ' a'' =>
    exercise
  | @exfalso => exercise
  | @or_l Γ' a'' b'' c ha'' hb'' iha' ihb' =>
    exercise
  | @or_r_1 => injection hag
  | @or_r_2 => injection hag
  | @and_l Γ' a'' b'' c hc ih =>
    exercise
  | @and_r Γ' a'' b'' ha'' hb'' iha'' ihb'' =>
    exercise
  | @imp_l Γ' a'' b'' c ha hc iha' ihc' =>
    exercise
  | @imp_r => injection hag

lemma GentzDerives.cut_aux_or_case (a' b' : IntFormula)
    (iha : ∀ {Γ Δ : Set IntFormula} {b : IntFormula},
      Δ ⊆ Γ → GentzDerives Δ a' → GentzDerives (Γ ∪ {a'}) b → GentzDerives Γ b)
    (ihb : ∀ {Γ Δ : Set IntFormula} {b : IntFormula},
      Δ ⊆ Γ → GentzDerives Δ b' → GentzDerives (Γ ∪ {b'}) b → GentzDerives Γ b)
    (Γ Δ : Set IntFormula) (b : IntFormula) :
    Δ ⊆ Γ →
    GentzDerives Δ (a' ∨ᵢ b') →
    GentzDerives (Γ ∪ {a' ∨ᵢ b'}) b →
    GentzDerives Γ b := by
  intro hΔ ha hb
  generalize hag : (a' ∨ᵢ b') = a at ha
  induction ha generalizing Γ b with
  | @id Γ' a'' =>
    exercise
  | @exfalso => exercise
  | @or_l Γ' a'' b'' c ha'' hb'' iha' ihb' =>
    exercise
  | @or_r_1 Γ' a'' b'' ha iha' =>
    exercise
  | @or_r_2 Γ' a'' b'' ha iha' =>
    exercise
  | @and_l Γ' a'' b'' c hc ih =>
    exercise
  | @and_r Γ' a'' b'' ha'' hb'' iha'' ihb'' => injection hag
  | @imp_l Γ' a'' b'' c ha hc iha' ihc' =>
    exercise
  | @imp_r => injection hag

lemma GentzDerives.cut_aux_imp_imp_r_case {Θ Γ Δ : Set IntFormula} {a b c : IntFormula}
    (iha : ∀ {Γ Δ : Set IntFormula} {c : IntFormula},
      Δ ⊆ Γ → GentzDerives Δ a →
      GentzDerives (Γ ∪ {a}) c → GentzDerives Γ c)
    (ihb : ∀ {Γ Δ : Set IntFormula} {c : IntFormula},
      Δ ⊆ Γ → GentzDerives Δ b →
      GentzDerives (Γ ∪ {b}) c → GentzDerives Γ c) :
    Θ ⊆ Γ ∪ {a →ᵢ b} →
    Δ ⊆ Γ →
    GentzDerives (Δ ∪ {a}) b →
    GentzDerives Θ c →
    GentzDerives Γ c := by
  intro hΘ hΔ hab hc
  induction hc generalizing Γ Δ with
  | @id Γ' a' =>
    exercise
  | @exfalso Γ' a' =>
    exercise
  | @or_l Γ' a' b' c ha' hb' iha' ihb' =>
    exercise
  | @or_r_1 Γ' a' b' ha iha' =>
    exercise
  | @or_r_2 Γ' a' b' ha iha' =>
    exercise
  | @and_l Γ' a' b' c hc ih =>
    exercise
  | @and_r Γ' a' b' ha hb iha' ihb' =>
    exercise
  | @imp_l Γ' a'' b'' c ha hc iha' ihc' =>
    have h : (a'' →ᵢ b'') ∈ Γ ∪ {a →ᵢ b} := by
      clear iha ihb iha' ihc'
      grind
    rcases h with h | h
    · have : Γ = Γ ∪ {a'' →ᵢ b''} := by
        clear iha ihb iha' ihc'
        grind
      exercise
    · cases h
      have hΓa : GentzDerives Γ a := by
        exercise
      have hΓab : GentzDerives (Γ ∪ {a}) b := by
        exercise
      have hΓb : GentzDerives Γ b := by
        exercise
      have hΓbc : GentzDerives (Γ ∪ {b}) c := by
        exercise
      have : GentzDerives Γ c := by
        exercise
      exact this
  | @imp_r Γ' a' b' ha' iha' =>
    exercise

lemma GentzDerives.cut_aux_imp_case (a' b' : IntFormula)
    (iha : ∀ {Γ Δ : Set IntFormula} {b : IntFormula},
      Δ ⊆ Γ → GentzDerives Δ a' → GentzDerives (Γ ∪ {a'}) b → GentzDerives Γ b)
    (ihb : ∀ {Γ Δ : Set IntFormula} {b : IntFormula},
      Δ ⊆ Γ → GentzDerives Δ b' → GentzDerives (Γ ∪ {b'}) b → GentzDerives Γ b)
    (Γ Δ : Set IntFormula) (b : IntFormula) :
    Δ ⊆ Γ →
    GentzDerives Δ (a' →ᵢ b') →
    GentzDerives (Γ ∪ {a' →ᵢ b'}) b →
    GentzDerives Γ b := by
  intro hΔ ha hb
  generalize hag : (a' →ᵢ b') = a at ha
  induction ha generalizing Γ b with
  | @id Γ' a'' =>
    exercise
  | @exfalso => exercise
  | @or_l Γ' a'' b'' c ha'' hb'' iha' ihb' =>
    exercise
  | @or_r_1 Γ' a'' b'' ha iha' => injection hag
  | @or_r_2 Γ' a'' b'' ha iha' => injection hag
  | @and_l Γ' a'' b'' c hc ih =>
    exercise
  | @and_r => injection hag
  | @imp_l Γ' a'' b'' c ha hc iha' ihc' =>
    exercise
  | @imp_r Γ' a'' b'' ha'' iha'' =>
    exercise

theorem GentzDerives.cut_aux
    {Γ Δ : Set IntFormula} {a b : IntFormula} :
    Δ ⊆ Γ →
    GentzDerives Δ a →
    GentzDerives (Γ ∪ {a}) b →
    GentzDerives Γ b := by
  induction a generalizing Γ Δ b with
  | var x => apply GentzDerives.cut_aux_var_case
  | and a' b' iha ihb =>
    apply GentzDerives.cut_aux_and_case
    · apply iha
    · apply ihb
  | or a' b' iha ihb =>
    apply GentzDerives.cut_aux_or_case
    · apply iha
    · apply ihb
  | imp a' b' iha ihb =>
    apply GentzDerives.cut_aux_imp_case
    · apply iha
    · apply ihb
  | bot =>
    intro hΔ hΔb hΓb
    apply GentzDerives.mono hΔ
    exact GentzDerives.bot_inversion hΔb

theorem GentzDerives.cut
    {Γ : Set IntFormula} {a b : IntFormula} :
    GentzDerives Γ a →
    GentzDerives (Γ ∪ {a}) b →
    GentzDerives Γ b :=
  GentzDerives.cut_aux (fun _ x => x)
