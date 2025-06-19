import MyGroups.Defs

universe u
def neg : ℤ → ℤ := fun n => - n

def Function.id {A : Type u} : A → A := fun a => a

def PermSet (A : Type u) : Set (A → A) := {f : A → A | Function.Bijective f}

instance : MyGroup ℤ where
  op := Int.add
  id := 0
  inv := neg
  associativity := Int.add_assoc
  id_proposition := by
      intro a
      repeat (first | apply And.intro | simp)
  inv_left_prop := by simp [neg]
  inv_right_prop := by simp [neg]


