import data.real.basic

variables a b c d : ℝ

-- BEGIN
#check (min_le_left a b : min a b ≤ a)
#check (min_le_right a b : min a b ≤ b)
#check (le_min : c ≤ a → c ≤ b → c ≤ min a b)
-- ENDimport data.real.basic

variables a b : ℝ

-- BEGIN
example : min a b = min b a :=
begin
  apply le_antisymm,
  { show min a b ≤ min b a,
    apply le_min,
    { apply min_le_right },
    apply min_le_left },
  { show min b a ≤ min a b,
    apply le_min,
    { apply min_le_right },
    apply min_le_left }
end
-- ENDimport data.real.basic

variables a b : ℝ

-- BEGIN
example : min a b = min b a :=
begin
  have h : ∀ x y, min x y ≤ min y x,
  { intros x y,
    apply le_min,
    apply min_le_right,
    apply min_le_left },
  apply le_antisymm, apply h, apply h
end
-- ENDimport data.real.basic

variables a b : ℝ

-- BEGIN
example : min a b = min b a :=
begin
  apply le_antisymm,
  repeat {
    apply le_min,
    apply min_le_right,
    apply min_le_left }
end
-- ENDimport data.real.basic

variables a b c : ℝ

-- BEGIN
example : max a b = max b a :=
begin
  sorry
end

example : min (min a b) c = min a (min b c) :=
sorry
-- ENDimport data.real.basic

variables a b c : ℝ

-- BEGIN
lemma aux : min a b + c ≤ min (a + c) (b + c) :=
begin
  sorry
end

example : min a b + c = min (a + c) (b + c) :=
begin
  sorry
end
-- ENDimport data.real.basic

-- BEGIN
#check (abs_add : ∀ a b : ℝ, abs (a + b) ≤ abs a + abs b)
-- ENDimport data.real.basic

variables a b : ℝ

-- BEGIN
example : abs a - abs b ≤ abs (a - b) :=
begin
  sorry
end
-- ENDimport data.nat.gcd

variables x y z : ℕ

example (h₀ : x ∣ y) (h₁ : y ∣ z) : x ∣ z :=
dvd_trans h₀ h₁

example : x ∣ y * x * z :=
begin
  apply dvd_mul_of_dvd_left,
  apply dvd_mul_left
end

example : x ∣ x^2 :=
begin
  rw nat.pow_two,
  apply dvd_mul_left
endimport data.nat.gcd

variables w x y z : ℕ

example (h : x ∣ w): x ∣ y * (x * z) + x^2 + w^2 :=
begin
  sorry
endimport data.nat.gcd

open nat

variables n : ℕ

#check (gcd_zero_right n : gcd n 0 = n)
#check (gcd_zero_left n  : gcd 0 n = n)
#check (lcm_zero_right n : lcm n 0 = 0)
#check (lcm_zero_left n  : lcm 0 n = 0)import data.nat.gcd

open nat

variables m n : ℕ

-- BEGIN
example : gcd m n = gcd n m :=
begin
  sorry
end
-- END