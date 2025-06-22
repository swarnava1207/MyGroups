import MyGroups.Defs

universe u v
open Classical

namespace MyGroup

noncomputable def order {G : Type u} [MyGroup G] (a : G) : ℕ :=
  if h : ∃ n : ℕ, a^n = 1 then Nat.find h else 0

theorem pow_comm {G : Type u} [MyGroup G] (a : G) (n : ℕ) :
  a^n * a = a * a^n := by
    induction n with
    | zero =>
      simp [raise_nat]
      unfold pow
      simp
      show 1 * a = a * 1
      simp
    | succ n ih =>
      simp [raise_nat]
      unfold pow
      simp [ih]
      show (a * a ^ n) * a = a * (a * a ^ n)
      simp [assoc]
      rw [ih]

theorem pow_add_on_multn {G : Type u} [MyGroup G] (a : G) (n m : ℕ) :
  a^(n + m) = a^n * a^m := by
    induction m with
    | zero =>
      simp
      simp [raise_nat]
      unfold pow
      simp
      split
      next h =>
        subst h
        show 1 = 1 * 1
        simp
      next h =>
        show op a (pow G a (n - 1)) = op a (pow G a (n - 1)) * 1
        simp
    | succ m ih =>
      simp [raise_nat]
      unfold pow
      simp [ih]
      split
      next h =>
        subst h
        simp
        show op a (pow G a m) = 1 * op a (pow G a m)
        simp
      next h =>
        show a * a ^ (n + m) = (a * a ^ (n -1)) * (a * a ^ m)
        simp [assoc]
        rw [← assoc (a ^ (n - 1)) a (a ^ m)]
        simp [pow_comm]
        simp [ih]
        have himp : ∀ m : ℕ , a * a ^ m = a ^ (m + 1) := by
          simp [raise_nat]
          unfold pow
          simp
          intro m
          split
          next h =>
            subst h
            simp [pow]
            rfl
          next h =>
            show a * op a (pow G a (m - 1)) = a * (pow G a m)
            simp [cancel_left]
            show a * a ^ (m - 1) = pow G a m
            unfold pow
            show op a (pow G a (m -1)) = if m = 0 then id else op a (pow G a (m - 1))
            split
            next h =>
              subst h
              contradiction
            next h =>
              rfl
        match n with
        | 0 => contradiction
        | n + 1 =>
          simp
          rw [← himp n]
          simp

theorem id_pow {G : Type u} [MyGroup G] : ∀ n : ℕ, (1 : G)^n = 1 := by
    intro n
    induction n with
    | zero =>
      simp [raise_nat]
      simp [pow]
      rfl
    | succ n ih =>
      simp [raise_nat]
      show (1 : G) ^ (n + 1) = 1
      simp [pow_add_on_multn]
      simp [ih]
      show pow G 1 1 = 1
      simp [pow]
      show (1 : G) * 1 = 1
      simp

theorem pow_zero {G : Type u} [MyGroup G] (a : G) : a^0 = 1 := by
    simp [raise_nat]
    unfold pow
    simp
    rfl

theorem pow_one {G : Type u} [MyGroup G] (a : G) : a^1 = a := by
    simp [raise_nat]
    unfold pow
    simp
    show a * (a ^ 0) = a
    simp [pow_zero]

theorem pow_mul {G : Type u} [MyGroup G] (a : G) (n m : ℕ) :
  a^(n * m) = (a^n)^m := by
    induction m with
    | zero =>
      simp
      simp [pow_zero]
    | succ m ih =>
      simp [pow_add_on_multn]
      rw [← ih]
      show a ^ (n * m + n) = a ^ (n * m) * (a ^ n) ^ 1
      simp [pow_add_on_multn]
      simp [cancel_left]
      simp [pow_one]

theorem order_pow {G : Type u} [MyGroup G] (a : G) :
  a^(order a) = 1 := by
    unfold order
    split
    next h =>
      let n := Nat.find h
      show a ^ n = 1
      rw [Nat.find_spec h]
    next h =>
      simp [pow_zero]

