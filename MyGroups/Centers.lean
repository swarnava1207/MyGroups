import MyGroups.Defs
import MyGroups.Actions
import MyGroups.Homs
import MyGroups.SubGroups

universe u v
open MyGroup

def centralizer (G : Type u) [MyGroup G] (H : Set G) : Set G :=
  { g : G | ∀ a ∈ H, a * g = g * a }

def center (G : Type u) [MyGroup G] : Set G :=
  { g : G | ∀ a : G, a * g = g * a }

theorem centralizer_subgroup (G : Type u) [MyGroup G] (H : Set G) :
  SubGroup G (centralizer G H) := by
    constructor
    · simp [centralizer]
    · intro a ha
      simp [centralizer] at ha
      simp [centralizer]
      intro b hb
      have h1 : b * a * a⁻¹ = a * b * a⁻¹ := by
        rw [cancel_right]
        apply ha
        assumption
      have h2 : a ⁻¹ * b * a * a⁻¹ = a ⁻¹ * a * b * a⁻¹ := by
        rw [assoc a⁻¹ b a, assoc a⁻¹ a b]
        rw [assoc , assoc a⁻¹ (a * b) a⁻¹]
        rw [cancel_left]
        assumption
      simp at h2
      rw [h2]
    · intro a b ha hb
      simp [centralizer] at ha hb
      simp [centralizer]
      intro c hc
      rw [← assoc, ha c]
      rw [← hb c, assoc]
      assumption
      assumption

theorem center_subgroup (G : Type u) [MyGroup G] :
  SubGroup G (center G) := by
    rw [subgrp_iff]
    constructor
    · use (1 : G)
      simp [center]
    · intro g h hg hh
      simp [center] at hg hh
      simp [center]
      intro a
      rw [← assoc, hg a, assoc]
      rw [← inv_of_inv a, ← inv_of_prod h a⁻¹]
      rw [← hh a⁻¹, inv_of_prod]

instance left_mul_set {G : Type u} [MyGroup G] : HMul G (Set G) (Set G) where
  hMul := fun g H => { g * a | a ∈ H}

instance right_mul_set {G : Type u} [MyGroup G] : HMul (Set G) G (Set G) where
  hMul := fun H g => { a * g | a ∈ H}

theorem normal_assoc {G : Type u} [MyGroup G] (g h : G) (H : Set G) :
  g * (H * h) = (g * H) * h := by
    apply Set.ext
    intro x
    constructor
    · intro hx
      simp [left_mul_set] at hx
      let ⟨ a , ha ⟩ := hx
      simp [right_mul_set] at ha
      let ⟨ b , hb ⟩ := ha.1
      use g * b
      constructor
      · use b
        constructor
        · apply hb.1
        · rfl
      · rw [assoc, hb.2]
        rw [ha.2]
    · intro hx
      simp [right_mul_set] at hx
      let ⟨ a , ha ⟩ := hx
      simp [left_mul_set] at ha
      let ⟨ b , hb ⟩ := ha.1
      use b * h
      constructor
      · use b
        constructor
        · apply hb.1
        · rfl
      · rw [← assoc, hb.2]
        rw [ha.2]

theorem left_mul_assoc {G : Type u} [MyGroup G] (g h : G) (H : Set G) :
  g * (h * H) = (g * h) * H := by
    apply Set.ext
    intro x
    constructor
    · intro hx
      simp [left_mul_set] at hx
      let ⟨ a , ha ⟩ := hx
      use a
      simp [left_mul_set]
      assumption
    · intro hx
      simp [left_mul_set] at hx
      let ⟨ a , ha ⟩ := hx
      use h * a
      simp [left_mul_set]
      constructor
      · use a
        constructor
        · apply ha.1
        · rfl
      · apply ha.2

theorem right_mul_assoc {G : Type u} [MyGroup G] (H : Set G) (g h : G) :
  (H * g) * h = H * (g * h) := by
    apply Set.ext
    intro x
    constructor
    · intro hx
      simp [right_mul_set] at hx
      let ⟨ a , ha ⟩ := hx
      use a
    · intro hx
      simp [right_mul_set] at hx
      let ⟨ a , ha ⟩ := hx
      use a * g
      simp [right_mul_set]
      constructor
      · use a
        constructor
        · apply ha.1
        · rfl
      · apply ha.2

def normalizer (G : Type u) [MyGroup G] (H : Set G) : Set G :=
  { g : G | g * H = H * g }

theorem normalizer_subgroup (G : Type u) [MyGroup G] (H : Set G) :
  SubGroup G (normalizer G H) := by
    constructor
    · simp [normalizer]
      apply Set.ext
      intro x
      constructor
      · intro h
        simp [right_mul_set]
        simp [left_mul_set] at h
        assumption
      · intro h
        simp [left_mul_set]
        simp [right_mul_set] at h
        assumption
    · intro a ha
      simp [normalizer] at ha
      simp [normalizer]
      apply Set.ext
      simp [Set.ext_iff] at ha
      simp [left_mul_set, right_mul_set] at ha
      intro x
      constructor
      · intro h
        simp [right_mul_set]
        simp [left_mul_set] at h
        let ⟨ a₃ , ha₃ ⟩ := h
        let ⟨ h₁ , h₂ ⟩ := ha (a * x * a)
        have hsub : ∃ a₃ ∈ H , a₃ * a = a * x * a := by
          use a₃
          constructor
          · apply ha₃.1
          · rw [← ha₃.2]
            rw [← assoc a a⁻¹ a₃]
            simp
        let ⟨ a₂ , ha₂ ⟩ := h₂ hsub
        use a₂
        constructor
        · apply ha₂.1
        · simp [cancel_left] at ha₂
          rw [ha₂.2]
          simp
      · intro h
        simp [left_mul_set]
        simp [right_mul_set] at h
        let ⟨ a₃ , ha₃ ⟩ := h
        let ⟨ h₁ , h₂ ⟩ := ha (a * x * a)
        have hsub : ∃ a₃ ∈ H , a * a₃ = a * x * a := by
          use a₃
          constructor
          · apply ha₃.1
          · rw [← ha₃.2]
            rw [← assoc a a₃ a⁻¹]
            simp
        let ⟨ a₂ , ha₂ ⟩ := h₁ hsub
        use a₂
        constructor
        · apply ha₂.1
        · rw [cancel_right a a₂ (a * x)] at ha₂
          rw [ha₂.2, ← assoc]
          simp
    · intro a b ha hb
      simp [normalizer] at ha hb
      simp [normalizer]
      rw [← right_mul_assoc]
      rw [← ha]
      rw [← normal_assoc]
      rw [← hb]
      rw [left_mul_assoc]


def stabilizer_element {G : Type u} [MyGroup G] (A : Type v) [Action G A] (a : A) : Set G :=
  { g : G | Action.act g a = a }

theorem stabilizer_element_subgroup {G : Type u} [MyGroup G] (A : Type v) [Action G A] (a : A) :
  SubGroup G (stabilizer_element A a) := by
    constructor
    · simp [stabilizer_element]
      exact id_act a
    · intro g hg
      simp [stabilizer_element] at hg
      simp [stabilizer_element]
      rw [← hg]
      rw [← assoc_act]
      simp [hg, id_act]
    · intro g h hg hh
      simp [stabilizer_element] at hg hh
      simp [stabilizer_element]
      rw [assoc_act]
      rw [hh, hg]

