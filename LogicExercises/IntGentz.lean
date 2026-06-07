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

theorem GentzDerives.imp_inversion_aux {Δ Γ : Set IntFormula} {a b c : IntFormula} :
    Δ ⊆ Γ ∪ {a →ᵢ b} →
    GentzDerives Δ c →
    GentzDerives (Γ ∪ {b}) c := by
  intro hΔ hc
  induction hc generalizing Γ a b with
  | @id Γ' c =>
    -- ex
    have hc : c ∈ Γ ∪ {a →ᵢ b} := by grind
    rcases hc with hc | hc
    · exact GentzDerives.hyp (by grind)
    · rw [hc]
      apply GentzDerives.imp_r
      apply GentzDerives.hyp (by grind)
    -- /ex
  | @exfalso Γ' c =>
    -- ex
    have h : {⊥ᵢ} ⊆ Γ ∪ {a →ᵢ b} := by grind
    simp only [Set.union_singleton] at h
    exact GentzDerives.exfalso_in (by grind)
    -- /ex
  | @or_l Γ' a' b' c ha' hb' iha ihb =>
    have h : {a' ∨ᵢ b'} ⊆ Γ ∪ {a →ᵢ b} := by grind
    simp only [Set.union_singleton, Set.singleton_subset_iff, Set.mem_insert_iff] at h
    rcases h with ⟨_, _⟩ | h
    -- ex
    rw [show Γ ∪ {b} = Γ ∪ {b} ∪ {a' ∨ᵢ b'} by grind]
    apply GentzDerives.or_l <;> rw [set_comm_3]
    · exact @iha (Γ ∪ {a'}) a b (by grind [set_comm_3])
    · exact @ihb (Γ ∪ {b'}) a b (by grind [set_comm_3])
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
    have h : (a' ∧ᵢ b') ∈ Γ := by
      have : {a' ∧ᵢ b'} ⊆ Γ ∪ {a →ᵢ b} := by grind
      grind
    rw [show Γ ∪ {b} = Γ ∪ {b} ∪ {a' ∧ᵢ b'} by grind]
    apply GentzDerives.and_l
    rw [show Γ ∪ {b} ∪ {a'} ∪ {b'} = Γ ∪ {a'} ∪ {b'} ∪ {b} by ac_rfl]
    exact @ih (Γ ∪ {a'} ∪ {b'}) a b (by grind [set_comm_3])
    -- /ex
  | @and_r Γ' a' b' ha hb iha ihb =>
    -- ex
    grind only [GentzDerives.and_r]
    -- /ex
  | @imp_l Γ' a' b' c' ha hc iha ihc =>
    have h : {a' →ᵢ b'} ⊆ Γ ∪ {a →ᵢ b} := by grind
    simp only [Set.union_singleton, Set.singleton_subset_iff, Set.mem_insert_iff] at h
    rcases h with ⟨_, _⟩ | h
    -- ex
    · rw [show Γ ∪ {b'} = Γ ∪ {b'} ∪ {b'} by grind]
      exact @ihc (Γ ∪ {b'}) a' b' (by grind)
    · rw [show Γ ∪ {b} = Γ ∪ {b} ∪ {a' →ᵢ b'} by grind]
      apply GentzDerives.imp_l
      · exact iha (show Γ' ⊆ Γ ∪ {a →ᵢ b} by grind)
      · rw [set_comm_3]
        exact ihc (show Γ' ∪ {b'} ⊆ Γ ∪ {b'} ∪ {a →ᵢ b} by grind)
    -- /ex
  | @imp_r Γ' a' b' h ih =>
    -- ex
    apply GentzDerives.imp_r
    rw [set_comm_3]
    apply ih (show Γ' ∪ {a'} ⊆ Γ ∪ {a'} ∪ {a →ᵢ b} by grind)
    -- /ex

theorem GentzDerives.imp_inversion {Γ : Set IntFormula} {a b c : IntFormula} :
    GentzDerives (Γ ∪ {a →ᵢ b}) c →
    GentzDerives (Γ ∪ {b}) c :=
  GentzDerives.imp_inversion_aux (fun _ x => x)

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
    have hΓ : Γ = Γ ∪ {varᵢ x} := by grind
    grind [GentzDerives.mono]
  | @exfalso => exact GentzDerives.exfalso_in (by grind)
  | @or_l Γ' a' b' c ha' hb' iha ihb =>
    subst hag
    have : GentzDerives (Γ ∪ {a'} ∪ {varᵢ x}) b :=
      GentzDerives.mono (show Γ ∪ {varᵢ x} ⊆ Γ ∪ {a'} ∪ {varᵢ x} by grind) hb
    specialize @iha (Γ ∪ {a'}) b (by grind) (by assumption) rfl
    have : GentzDerives (Γ ∪ {b'} ∪ {varᵢ x}) b :=
      GentzDerives.mono (show Γ ∪ {varᵢ x} ⊆ Γ ∪ {b'} ∪ {varᵢ x} by grind) hb
    specialize @ihb (Γ ∪ {b'}) b (by grind) (by assumption) rfl
    rw [show Γ = Γ ∪ {a' ∨ᵢ b'} by grind]
    exact GentzDerives.or_l iha ihb
  | @or_r_1 => injection hag
  | @or_r_2 => injection hag
  | @and_l Γ' a' b' c hc ih =>
    subst hag
    have : GentzDerives (Γ ∪ {a'} ∪ {b'} ∪ {varᵢ x}) b :=
      GentzDerives.mono (show Γ ∪ {varᵢ x} ⊆ Γ ∪ {a'} ∪ {b'} ∪ {varᵢ x} by grind) hb
    specialize @ih (Γ ∪ {a'} ∪ {b'}) b (by grind) (by assumption) rfl
    rw [show Γ = Γ ∪ {a' ∧ᵢ b'} by grind]
    exact GentzDerives.and_l ih
  | @and_r => injection hag
  | @imp_l Γ' a' b' c ha hc iha ihc =>
    subst hag
    rw [show Γ = Γ ∪ {a' →ᵢ b'} by grind]
    have : GentzDerives (Γ ∪ {b'} ∪ {varᵢ x}) b :=
      GentzDerives.mono (show Γ ∪ {varᵢ x} ⊆ Γ ∪ {b'} ∪ {varᵢ x} by grind) hb
    specialize @ihc (Γ ∪ {b'}) b (by grind) (by assumption) rfl
    apply GentzDerives.imp_l ?_ ihc
    apply GentzDerives.mono (by grind) ha
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
    have : GentzDerives (Γ ∪ {a'} ∪ {b'}) b :=
      GentzDerives.and_inversion hb
    specialize @ihb (Γ ∪ {a'}) Γ' b (by grind) (by assumption)
      (by assumption)
    exact iha hΔ ha'' ihb
  | @imp_l Γ' a'' b'' c ha hc iha' ihc' =>
    subst hag
    have hΓ : Γ = Γ ∪ {a'' →ᵢ b''} := by grind
    rw [hΓ]
    apply GentzDerives.imp_l
    · exact GentzDerives.mono (show Γ' ⊆ Γ by grind) ha
    · have : GentzDerives (Γ ∪ {b''} ∪ {a' ∧ᵢ b'}) b :=
        GentzDerives.mono (show Γ ∪ {a' ∧ᵢ b'} ⊆ Γ ∪ {b''} ∪ {a' ∧ᵢ b'} by grind) hb
      specialize @ihc' (Γ ∪ {b''}) b (by grind)
      apply GentzDerives.and_inversion at hb
      apply ihc' (by grind) rfl
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
    have hΓ : Γ = Γ ∪ {a' ∨ᵢ b'} := by grind
    grind [GentzDerives.mono]
  | @exfalso => exact GentzDerives.exfalso_in (by grind)
  | @or_l Γ' a'' b'' c ha'' hb'' iha' ihb' =>
    subst hag
    rw [show Γ = Γ ∪ {a'' ∨ᵢ b''} by grind]
    apply GentzDerives.or_l
    · have : GentzDerives (Γ ∪ {a''} ∪ {a' ∨ᵢ b'}) b := by
        rw [set_comm_3]
        apply GentzDerives.mono (by grind) hb
      specialize @iha' (Γ ∪ {a''}) b (by grind) (by assumption) rfl
      exact iha'
    · have : GentzDerives (Γ ∪ {b''} ∪ {a' ∨ᵢ b'}) b := by
        rw [set_comm_3]
        apply GentzDerives.mono (by grind) hb
      specialize @ihb' (Γ ∪ {b''}) b (by grind) (by assumption) rfl
      exact ihb'
  | @or_r_1 Γ' a'' b'' ha iha' =>
    cases hag
    apply GentzDerives.or_inversion at hb
    exact @iha Γ Γ' b hΔ ha hb.1
  | @or_r_2 Γ' a'' b'' ha iha' =>
    cases hag
    apply GentzDerives.or_inversion at hb
    exact @ihb Γ Γ' b hΔ ha hb.2
  | @and_l Γ' a'' b'' c hc ih =>
    subst hag
    have : GentzDerives (Γ ∪ {a''} ∪ {b''} ∪ {a' ∨ᵢ b'}) b := by
      rw [show Γ ∪ {a''} ∪ {b''} ∪ {a' ∨ᵢ b'} = Γ ∪ {a' ∨ᵢ b'} ∪ {a''} ∪ {b''} by grind]
      apply GentzDerives.mono (by grind) hb
    specialize @ih (Γ ∪ {a''} ∪ {b''}) b (by grind) (by assumption) rfl
    rw [show Γ = Γ ∪ {a'' ∧ᵢ b''} by grind]
    apply GentzDerives.and_l ih
  | @and_r Γ' a'' b'' ha'' hb'' iha'' ihb'' => injection hag
  | @imp_l Γ' a'' b'' c ha hc iha' ihc' =>
    subst hag
    have hΓ : Γ = Γ ∪ {a'' →ᵢ b''} := by grind
    rw [hΓ]
    apply GentzDerives.imp_l
    · exact GentzDerives.mono (show Γ' ⊆ Γ by grind) ha
    · have : GentzDerives (Γ ∪ {b''} ∪ {a' ∨ᵢ b'}) b :=
        GentzDerives.mono (show Γ ∪ {a' ∨ᵢ b'} ⊆ Γ ∪ {b''} ∪ {a' ∨ᵢ b'} by grind) hb
      specialize @ihc' (Γ ∪ {b''}) b (by grind)
      apply GentzDerives.or_inversion at hb
      apply ihc' (by grind) rfl
  | @imp_r => injection hag

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
    have hΓ : Γ = Γ ∪ {a' →ᵢ b'} := by grind
    grind [GentzDerives.mono]
  | @exfalso => exact GentzDerives.exfalso_in (by grind)
  | @or_l Γ' a'' b'' c ha'' hb'' iha' ihb' =>
    subst hag
    rw [show Γ = Γ ∪ {a'' ∨ᵢ b''} by grind]
    apply GentzDerives.or_l
    · have : GentzDerives (Γ ∪ {a''} ∪ {a' →ᵢ b'}) b := by
        rw [set_comm_3]
        apply GentzDerives.mono (by grind) hb
      specialize @iha' (Γ ∪ {a''}) b (by grind) (by assumption) rfl
      exact iha'
    · have : GentzDerives (Γ ∪ {b''} ∪ {a' →ᵢ b'}) b := by
        rw [set_comm_3]
        apply GentzDerives.mono (by grind) hb
      have : Γ' ∪ {b''} ⊆ Γ ∪ {b''} :=
        Set.union_subset_union_left {b''} (by grind)
      exact @ihb' (Γ ∪ {b''}) b (by assumption) (by assumption) rfl
  | @or_r_1 Γ' a'' b'' ha iha' => injection hag
  | @or_r_2 Γ' a'' b'' ha iha' => injection hag
  | @and_l Γ' a'' b'' c hc ih =>
    subst hag
    have : GentzDerives (Γ ∪ {a''} ∪ {b''} ∪ {a' →ᵢ b'}) b :=
      GentzDerives.mono (show Γ ∪ {a' →ᵢ b'} ⊆ Γ ∪ {a''} ∪ {b''} ∪ {a' →ᵢ b'} by grind) hb
    specialize @ih (Γ ∪ {a''} ∪ {b''}) b (by grind) (by assumption) rfl
    rw [show Γ = Γ ∪ {a'' ∧ᵢ b''} by grind]
    exact GentzDerives.and_l ih
  | @and_r => injection hag
  | @imp_l Γ' a'' b'' c ha hc iha' ihc' =>
    subst hag
    have hΓ : Γ = Γ ∪ {a'' →ᵢ b''} := by grind
    rw [hΓ]
    apply GentzDerives.imp_l
    · exact GentzDerives.mono (show Γ' ⊆ Γ by grind) ha
    · have : GentzDerives (Γ ∪ {b''} ∪ {a' →ᵢ b'}) b :=
        GentzDerives.mono (show Γ ∪ {a' →ᵢ b'} ⊆ Γ ∪ {b''} ∪ {a' →ᵢ b'} by grind) hb
      specialize @ihc' (Γ ∪ {b''}) b (by grind) (by assumption) rfl
      exact ihc'
  | @imp_r Γ' a'' b'' ha'' iha'' =>
    cases hag

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
  | imp a' b' iha ihb => sorry

-- theorem not_derives_imp_counter_model {a : IntFormula} :
--     ¬ (∅ ⊢ᵢ a) → ∃ (m : IntModel) (w : m.worlds), ¬ (w ⊨ᵢ a) := by
--   sorry
