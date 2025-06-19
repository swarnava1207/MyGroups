import MyGroups.Defs
import MyGroups.Homs

universe u v
namespace MyGroup

class Action (G : Type u) (A : Type v) [MyGroup G] where
  act : G → A → A
  id_act_prop : ∀ a : A, act 1 a = a
  assoc_act_prop : ∀ (g h : G) (a : A), act (g * h) a = act g (act h a)

theorem id_act {G : Type u} {A : Type v} [MyGroup G] [Action G A] :
  ∀ a : A, Action.act (1 : G) a = a := by
    intro a
    exact Action.id_act_prop a
theorem assoc_act {G : Type u} {A : Type v} [MyGroup G] [Action G A] :
  ∀ (g h : G) (a : A), Action.act (g * h) a = Action.act g (Action.act h a) := by
    intro g h a
    exact Action.assoc_act_prop g h a

def action_corr {G : Type u} (A : Type v) [MyGroup G] [Action G A] (g : G) : A → A :=
  Action.act g

theorem action_corr_perm {G : Type u} {A : Type v} [MyGroup G] [Action G A] :
  ∀ (g : G) , Function.Bijective (action_corr A g) := by
    intro g
    apply And.intro
    · intro a b
      simp [action_corr]
      intro h1
      have h2 : Action.act (g⁻¹ * g) a = Action.act (g⁻¹ * g) b := by
        rw [assoc_act, assoc_act]
        simp [h1]
      simp [inv_left, id_act] at h2
      assumption
    · intro a
      use Action.act g⁻¹ a
      simp [action_corr]
      rw [← assoc_act,inv_right,id_act]

def perm_rep (G : Type u) (A : Type v) [MyGroup G] [Action G A] : G → A → A :=
  action_corr A

def faithful {G : Type u} {A : Type v} [MyGroup G] (f : Action G A) : Prop :=
  Function.Injective (perm_rep G A)

def kernel {G : Type u} {A : Type v} [MyGroup G] [Action G A] : Set G :=
  { g : G | ∀ a : A, Action.act g a = a }

instance left_mul (G : Type u) [MyGroup G] : Action G G where
  act := Mul.mul
  id_act_prop := by
    intro a
    exact (MyGroup.id_prop a).2
  assoc_act_prop := by
    intro g h a
    simp [Mul.mul]
    show g * h * a = g * (h * a)
    rw [assoc]

theorem left_mul_faithful (G : Type u) [MyGroup G] : faithful (left_mul G) := by
  intro g h
  simp [perm_rep, action_corr, left_mul]
  intro h1
  have h2 : ∀ a : G, g * a = h * a := by
    intro a
    simp [Mul.mul] at h1
    show op g a = op h a
    rw [h1]
  rw [← cancel_right g g h]
  apply h2


end MyGroup
