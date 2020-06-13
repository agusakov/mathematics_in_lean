import data.real.basic
import analysis.special_functions.exp_log
import tactic

variables a b c d e : ℝ

/-Rewriting is great for proving equations, but 
what about other sorts of theorems? For example, 
how can we prove an inequality, like the fact that 
𝑎+𝑒𝑏≤𝑎+𝑒𝑐 holds whenever 𝑏≤𝑐? We have already seen 
that theorems can be applied to arguments and 
hypotheses, and that the apply and exact tactics 
can be used to solve goals. In this section, we will 
make good use of these tools.

Consider the library theorems le_refl and le_trans:-/

#check (le_refl : ∀ a : ℝ, a ≤ a)
#check (le_trans : a ≤ b → b ≤ c → a ≤ c)

/-The library designers have set the arguments to 
le_trans implicit, so that Lean will not let you 
provide them explicitly. Rather, it expects to infer 
them from the context in which they are used. For 
example, when hypotheses h : a ≤ b and h' : b ≤ c 
are in the context, all the following work:
-/

-- BEGIN
variables (h : a ≤ b) (h' : b ≤ c)

#check (le_refl : ∀ a : real, a ≤ a)
#check (le_refl a : a ≤ a)
#check (le_trans : a ≤ b → b ≤ c → a ≤ c)
#check (le_trans h : b ≤ c → a ≤ c)
#check (le_trans h h' : a ≤ c)
-- END

/-The apply tactic takes a proof of a general 
statement or implication, tries to match the conclusion 
with the current goal, and leaves the hypotheses, 
if any, as new goals. If the given proof matches the 
goal exactly, you can use the exact tactic instead of 
apply. So, all of these work:
-/

-- BEGIN
example (x y z : ℝ) (h₀ : x ≤ y) (h₁ : y ≤ z) : x ≤ z :=
begin
  apply le_trans,
  { apply h₀ },
  apply h₁
end

example (x y z : ℝ) (h₀ : x ≤ y) (h₁ : y ≤ z) : x ≤ z :=
begin
  apply le_trans h₀,
  apply h₁
end

example (x y z : ℝ) (h₀ : x ≤ y) (h₁ : y ≤ z) : x ≤ z :=
by exact le_trans h₀ h₁

example (x y z : ℝ) (h₀ : x ≤ y) (h₁ : y ≤ z) : x ≤ z :=
le_trans h₀ h₁

example (x : ℝ) : x ≤ x :=
by apply le_refl

example (x : ℝ) : x ≤ x :=
by exact le_refl x

example (x : ℝ) : x ≤ x :=
le_refl x
-- END

/-In the first example, applying le_trans creates two 
goals, and we use the curly braces to enclose the proof 
of the first one. In the fourth example and in the last 
example, we avoid going into tactic mode entirely: 
le_trans h₀ h₁ and le_refl x are the proof terms we need.

Here are a few more library theorems:-/

-- BEGIN
#check (le_refl  : ∀ a, a ≤ a)
#check (le_trans : a ≤ b → b ≤ c → a ≤ c)
#check (lt_of_le_of_lt : a ≤ b → b < c → a < c)
#check (lt_of_lt_of_le : a < b → b ≤ c → a < c)
#check (lt_trans : a < b → b < c → a < c)
-- END


/-Use them together with apply and exact to prove the following:-/

-- BEGIN
example (a b c d e : ℝ) (h₀ : a ≤ b) (h₁ : b < c) (h₂ : c ≤ d)
    (h₃ : d < e) :
  a < e :=
  begin
    exact lt_trans (lt_of_le_of_lt h₀ h₁) (lt_of_le_of_lt h₂ h₃),
  end
-- END

/-In fact, Lean has a tactic that does this sort of thing 
automatically:
-/

-- BEGIN
example (a b c d e : ℝ) (h₀ : a ≤ b) (h₁ : b < c) (h₂ : c ≤ d)
    (h₃ : d < e) :
  a < e :=
by linarith
-- END

/-The linarith tactic is designed to handle linear arithmetic.
-/
-- BEGIN
example (h : 2 * a ≤ 3 * b) (h' : 1 ≤ a) (h'' : d = 2) :
  d + a ≤ 5 * b :=
by linarith
-- END

/-In addition to equations and inequalities in the 
context, linarith will use additional inequalities 
that you pass as arguments.
-/
-- BEGIN
open real
--variables a b c : ℝ
example (h : 1 ≤ a) (h' : b ≤ c) :
  2 + a + exp b ≤ 3 * a + exp c :=
by linarith [exp_le_exp.mpr h']
-- END

/-Here are some more theorems in the library that 
can be used to establish inequalities on the real numbers.-/
--variables  a b c d : ℝ
#check (exp_le_exp : exp a ≤ exp b ↔ a ≤ b)
#check (exp_lt_exp : exp a < exp b ↔ a < b)
#check (log_le_log : 0 < a → 0 < b → (log a ≤ log b ↔ a ≤ b))
#check (log_lt_log : 0 < a → a < b → log a < log b)
#check (add_le_add : a ≤ b → c ≤ d → a + c ≤ b + d)
#check (add_lt_add_of_le_of_lt : a ≤ b → c < d → a + c < b + d)
#check (add_lt_add_of_le_of_lt : a ≤ b → c < d → a + c < b + d)
#check (add_nonneg : 0 ≤ a → 0 ≤ b → 0 ≤ a + b)
#check (add_pos : 0 < a → 0 < b → 0 < a + b)
#check (add_pos_of_pos_of_nonneg : 0 < a → 0 ≤ b → 0 < a + b)
#check (exp_pos : ∀ a, 0 < exp a)


/-Some of the theorems, exp_le_exp, exp_lt_exp, and 
log_le_log use a bi-implication, which represents the 
phrase “if and only if.” (You can type it in VS Code 
with \lr of \iff). We will discuss this connective in 
greater detail in the next chapter. Such a theorem can 
be used with rw to rewrite a goal to an equivalent one:
-/
-- BEGIN
example (a b : ℝ) (h : a ≤ b) : exp a ≤ exp b :=
begin
  rw exp_le_exp,
  exact h
end
-- END

/-In this section, however, we will use that fact that 
if h : A ↔ B is such an equivalence, then h.mp 
establishes the forward direction, A → B, and 
h.mpr establishes the reverse direction, B → A. 
Here, mp stands for “modus ponens” and mpr stands 
for “modus ponens reverse.” You can also use h.1 and 
h.2 for h.mp and h.mpr, respectively, if you prefer. 
Thus the following proof works: -/
--variables a b c d e : ℝ
-- BEGIN
example (h₀ : a ≤ b) (h₁ : c < d) : a + exp c + e < b + exp d + e :=
begin
  apply add_lt_add_of_lt_of_le,
  { apply add_lt_add_of_le_of_lt h₀,
    apply exp_lt_exp.mpr h₁ },
  apply le_refl
end
-- END

/-The first line, apply add_lt_add_of_lt_of_le, 
creates two goals, and once again we use the curly 
brackets to separate the proof of the first from the 
proof of the second.

Try the following examples on your own. The example in 
the middle shows you that the norm_num tactic can be 
used to solve concrete numeric goals.-/

--variables a b c d e : ℝ

-- BEGIN
example (h₀ : d ≤ e) : c + exp (a + d) ≤ c + exp (a + e) :=
begin
  apply add_le_add (le_refl c),
  rw exp_le_exp,
  apply add_le_add (le_refl a) h₀,
end

example : (0 : ℝ) < 1 :=
by norm_num

example (h : a ≤ b) : log (1 + exp a) ≤ log (1 + exp b) :=
begin
  have h₀ : 0 < 1 + exp a, { 
    apply add_pos,
    norm_num,
    apply exp_pos,
  },
  have h₁ : 0 < 1 + exp b, { 
    apply add_pos,
    norm_num,
    apply exp_pos,
  },
  apply (log_le_log h₀ h₁).mpr,
  apply add_le_add, 
    refl,
    rw exp_le_exp,
    assumption,
end
-- END

/-From these examples, it should be clear that being able to find 
the library theorems you need constitutes an important part of formalization. 
There are a number of strategies you can use:
  * You can browse mathlib in its GitHub repository.
  * You can use the API documentation on the mathlib web pages.
  * You can rely on mathlib naming conventions and tab completion in the 
    editor to guess a theorem name. In Lean, a theorem named A_of_B_of_C 
    establishes something of the form A from hypotheses of the form B and C, 
    where A, B, and C approximate the way we might read the goals out loud. 
    So a theorem establishing something like x + y ≤ ... will probably start 
    with add_le. Typing add_le and hitting tab will give you some helpful choices.
  * If you right-click on an existing theorem in VS Code, the editor will 
    show a menu with the option to jump to the file where the theorem is defined, 
    and you can find similar theorems nearby.
  * You can use the library_search tactic, which tries to find the relevant 
    theorem in the library.-/


example (a : ℝ) : 0 ≤ a^2 :=
begin
  --library_search,
  exact pow_two_nonneg a
end


/-To try out library_search in this example, delete the exact command 
and uncomment the previous line. Using these tricks, see if you can 
find what you need to do the next example:
-/

--variables a b c : ℝ

-- BEGIN
example (h : a ≤ b) : c - exp b ≤ c - exp a :=
begin
  rw ← exp_le_exp at h,
  exact sub_le_sub_left h c,
end
--Also, confirm that linarith can do it with a bit of help:
example (h : a ≤ b) : c - exp b ≤ c - exp a :=
begin
  rw ← exp_le_exp at h,
  linarith,
end
-- END

/-Here is another example of an inequality: -/
--variables a b : ℝ
-- BEGIN
example : 2*a*b ≤ a^2 + b^2 :=
begin
  have h : 0 ≤ a^2 - 2*a*b + b^2,
  calc
    a^2 - 2*a*b + b^2 = (a - b)^2     : by ring
    ... ≥ 0                           : by apply pow_two_nonneg,
  calc
    2*a*b
        = 2*a*b + 0                   : by ring
    ... ≤ 2*a*b + (a^2 - 2*a*b + b^2) : add_le_add (le_refl _) h
    ... = a^2 + b^2                   : by ring
end
-- END

--variables a b : ℝ

-- BEGIN
example : 2*a*b ≤ a^2 + b^2 :=
begin
  have h : 0 ≤ a^2 - 2*a*b + b^2,
  calc
    a^2 - 2*a*b + b^2 = (a - b)^2 : by ring
    ... ≥ 0                       : by apply pow_two_nonneg,
  linarith
end
-- END


--variables a b : ℝ

-- BEGIN
example : abs (a*b) ≤ (a^2 + b^2) / 2 :=
begin
  have h : (0 : ℝ) < 2 := by linarith,
  apply abs_le_of_le_of_neg_le,
  have hp1 : 0 ≤ a^2 - 2*a*b + b^2,
    calc
      a^2 - 2*a*b + b^2 = (a - b)^2 : by ring
      ... ≥ 0                       : by apply pow_two_nonneg,
  have hp2 : 2*a*b ≤ a^2 + b^2,
    by linarith,
  rw [mul_comm, ← mul_assoc, mul_comm, ← mul_assoc] at hp2,
  exact le_div_of_mul_le h hp2,
  have hm1 : 0 ≤ a^2 + 2*a*b + b^2,
    calc
      a^2 + 2*a*b + b^2 = (a + b)^2 : by ring
      ... ≥ 0                       : by apply pow_two_nonneg,
  have hm2 : -(2*a*b) ≤ a^2 + b^2,
    by linarith,
  rw [mul_comm, ← mul_assoc, mul_comm, ← mul_assoc, neg_mul_eq_neg_mul] at hm2,
  exact le_div_of_mul_le h hm2,
end

#check abs_le_of_le_of_neg_le
-- END
