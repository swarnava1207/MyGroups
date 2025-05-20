import MyGroups.Defs

def neg : ℤ → ℤ := fun n => - n

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

