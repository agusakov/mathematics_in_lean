import algebra.ring
import tactic
import algebra.group
import algebra.group_power

variables (R : Type*) [ring R]

/-Mathematically, a ring consists of a 
  - set, 𝑅, 
  - operations + ×, and 
  - constants 0 and 1, and 
  - an operation 𝑥 ↦ −𝑥 such that:
    * 𝑅 with + is an abelian group, with 0 as the 
    additive identity and negation as inverse.
    * Multiplication is associative with identity 1, 
    and multiplication distributes over addition.

In Lean, we base our algebraic structures on types 
rather than sets. Modulo this difference, we can 
take the ring axioms to be as follows:-/

#check (add_assoc : ∀ a b c : R, a + b + c = a + (b + c))
#check (add_comm : ∀ a b : R, a + b = b + a)
#check (zero_add : ∀ a : R, 0 + a = a)
#check (add_left_neg : ∀ a : R, -a + a = 0)
#check (mul_assoc : ∀ a b c : R, a * b * c = a * (b * c))
#check (mul_one : ∀ a : R, a * 1 = a)
#check (one_mul : ∀ a : R, 1 * a = a)
#check (mul_add : ∀ a b c : R, a * (b + c) = a * b + a * c)
#check (add_mul : ∀ a b c : R, (a + b) * c = a * c + b * c)

/-You will learn more about the square brackets in the 
first line later, but for the time being, suffice it to say 
that the declaration gives us a type, R, and a ring structure 
on R. Lean then allows us to use generic ring notation with 
elements of R, and to make use of a library of theorems about 
rings.

The names of some of the theorems should look familiar: they 
are exactly the ones we used to calculate with the real numbers 
in the last section. Lean is good not only for proving things 
about concrete mathematical structures like the natural numbers 
and the integers, but also for proving things about abstract 
structures, characterized axiomatically, like rings. Moreover, 
Lean supports generic reasoning about both abstract and concrete 
structures, and can be trained to recognized appropriate instances. 
So any theorem about rings can be applied to concrete rings like 
the integers, ℤ, the rational numbers, ℚ, and the complex numbers 
ℂ. It can also be applied to any instance of an abstract structure 
that extends rings, such as any ordered ring or any field.

Not all important properties of the real numbers hold in an 
arbitrary ring, however. For example, multiplication on the 
real numbers is commutative, but that does not hold in general. 
If you have taken a course in linear algebra, you will recognize 
that, for every 𝑛, the 𝑛 by 𝑛 matrices of real numbers form a ring 
in which commutativity fails. If we declare R to be a commutative
ring, in fact, all the theorems in the last section continue to 
hold when we replace ℝ by R.-/

namespace comm

variables (R' : Type*) [comm_ring R']
variables a b c d : R'

example : (c * b) * a = b * (a * c) :=
by ring

example : (a + b) * (a + b) = a * a + 2 * (a * b) + b * b :=
by ring

example : (a + b) * (a - b) = a^2 - b^2 :=
by ring

example (hyp : c = d * a + b) (hyp' : b = a * d) :
  c = 2 * a * d :=
begin
  rw [hyp, hyp'],
  ring
end

end comm

/-We leave it to you to check that all the other proofs 
go through unchanged.

The goal of this section is to strengthen the skills you 
have developed in the last section and apply them to reasoning 
axiomatically about rings. We will start with the axioms 
listed above, and use them to derive other facts. Most of the 
facts we prove are already in mathlib. We will give the versions 
we prove the same names to help you learn the contents of the 
library as well as the naming conventions. To avoid error messages 
from Lean, we will put our versions in a new namespace called my_ring.

The next example shows that we do not need add_zero or 
add_right_neg as ring axioms, because they follow from the 
other axioms.-/

-- algebra.ring

namespace my_ring

variables {R' : Type*} [ring R']

theorem add_zero (a : R') : a + 0 = a :=
by rw [add_comm, zero_add]

theorem add_right_neg (a : R') : a + -a = 0 :=
by rw [add_comm, add_left_neg]

#check @my_ring.add_zero
#check @add_zero

/-The net effect is that we can temporarily reprove a 
theorem in the library, and then go on using the library 
version after that. But don’t cheat! In the exercises that 
follow, take care to use only the general facts about rings 
that we have proved earlier in this section.

(If you are paying careful attention, you may have noticed 
that we changed the round brackets in (R : Type*) for curly 
brackets in {R : Type*}. This declares R to be an implicit 
argument. We will explain what this means in a moment, but 
don’t worry about it in the meanwhile.)

Here is a useful theorem:-/
-- BEGIN
theorem neg_add_cancel_left (a b : R') : -a + (a + b) = b :=
by rw [←add_assoc, add_left_neg, zero_add]
-- END

/-Prove the companion version:-/
-- BEGIN
theorem neg_add_cancel_right (a b : R') : (a + b) + -b = a :=
by rw [add_assoc, add_right_neg, add_zero]
-- END

/-Use these to prove the following:-/
-- BEGIN
theorem add_left_cancel {a b c : R'} (h : a + b = a + c) : b = c :=
by rw [← zero_add b, ← add_left_neg a, add_assoc, h, neg_add_cancel_left]

theorem add_right_cancel {a b c : R'} (h : a + b = c + b) : a = c :=
by rw [← add_zero a, ← add_left_neg b, ← add_comm b, ← add_assoc, h, neg_add_cancel_right]
-- END

/-If you are clever, you can do each of them with three rewrites.

We can now explain the use of the curly braces. Imagine 
you are in a situation where you have a, b, and c in your 
context, as well as a hypothesis h : a + b = a + c, and you 
would like to draw the conclusion b = c. In Lean, you can apply 
a theorem to hypotheses and facts just the same way that you 
can apply them to objects, so you might think that add_left_cancel 
a b c h is a proof of the fact b = c. But notice that explicitly 
writing a, b, and c is redundant, because the hypothesis h makes 
it clear that those are the objects we have in mind. In this case, 
typing a few extra characters is not onerous, but if we wanted to 
apply add_left_cancel to more complicated expressions, writing 
them would be tedious. In cases like these, Lean allows us to mark 
arguments as implicit, meaning that they are supposed to be left 
out and inferred by other means, such as later arguments and 
hypotheses. The curly brackets in {a b c : R} do exactly that. 
So, given the statement of the theorem above, the correct 
expression is simply add_left_cancel h.

To illustrate, let us show that a * 0 = 0 follows from the 
ring axioms.-/

-- BEGIN
theorem mul_zero (a : R') : a * 0 = 0 :=
begin
  have h : a * 0 + a * 0 = a * 0 + 0,
  { rw [←mul_add, add_zero, add_zero] },
  rw add_left_cancel h
end
-- END

/-We have used a new trick! If you step through 
the proof, you can see what is going on. The have 
tactic introduces a new goal, a * 0 + a * 0 = a * 0 + 0, 
with the same context as the original goal. In the next 
line, we could have omitted the curly brackets, which serve 
as an inner begin ... end pair. Using them promotes a modular 
style of proof: the part of the proof inside the brackets 
establishes the goal that was introduced by the have. After 
that, we are back to proving the original goal, except a new 
hypothesis h has been added: having proved it, we are now free 
to use it. At this point, the goal is exactly the result of 
add_left_cancel h. We could equally well have closed the proof 
with apply add_left_cancel h or exact add_left_cancel h. We will 
discuss apply and exact in the next section.

Remember that multiplication is not assumed to be commutative, 
so the following theorem also requires some work.-/
-- BEGIN
theorem zero_mul (a : R') : 0 * a = 0 :=
begin
    have h : 0 * a + 0 * a = 0 * a + 0,
    { rw [←add_mul, add_zero, add_zero]},
    rw add_left_cancel h,
end
-- END

/-By now, you should also be able replace each sorry in the 
next exercise with a proof, still using only facts about 
rings that we have established in this section.-/
-- BEGIN
theorem neg_eq_of_add_eq_zero {a b : R'} (h : a + b = 0) : -a = b :=
begin
    rw ← add_left_neg a at h,
    rw add_comm a at h,
    rw add_right_cancel h,
end

theorem eq_neg_of_add_eq_zero {a b : R'} (h : a + b = 0) : a = -b :=
begin
    rw ← add_left_neg b at h,
    rw add_right_cancel h,
end

theorem neg_zero : (-0 : R') = 0 :=
begin
    apply neg_eq_of_add_eq_zero,
    rw add_zero
end

theorem neg_neg (a : R') : -(-a) = a :=
begin
    apply neg_eq_of_add_eq_zero,
    exact add_left_neg a,
end
-- END

/-We had to use the annotation (-0 : R) instead of 
0 in the third theorem because without specifying 
R it is impossible for Lean to infer which 0 we have 
in mind.

In Lean, subtraction in a ring is defined to be addition 
of the additive inverse.-/
-- BEGIN
theorem sub_eq_add_neg (a b : R') : a - b = a + -b :=
rfl

example (a b : R') : a - b = a + -b :=
by reflexivity
-- END

/-The proof term rfl is short for reflexivity. 
Presenting it as a proof of a - b = a + -b forces 
Lean to unfold the definition and recognize both sides 
as being the same. The reflexivity tactic, which can be 
abbreviated as refl, does the same. This is an instance 
of what is known as a definitional equality in Lean’s 
underlying logic. This means that not only can one rewrite 
with sub_eq_add_neg to replace a - b = a + -b, but in some 
contexts you can use the two sides of the equation 
interchangeably. For example, you now have enough information 
to prove the theorem self_sub from the last section:
-/
-- BEGIN
theorem self_sub (a : R') : a - a = 0 :=
begin
    rw sub_eq_add_neg,
    rw add_comm,
    exact add_left_neg a,
end

theorem self_sub' (a : R') : a - a = 0 :=
begin
    {rw [sub_eq_add_neg, add_comm, add_left_neg]},
end
-- END

/-Extra points if you do it two different ways: 
  - once using rw, and 
  - once using either apply or exact.

For another example of definitional equality, Lean 
knows that 1 + 1 = 2 holds in any ring. With a bit of 
cleverness, you can use that to prove the theorem two_mul 
from the last section:-/
-- BEGIN
lemma one_add_one_eq_two : 1 + 1 = (2 : R') :=
by refl

theorem two_mul (a : R') : 2 * a = a + a :=
begin
    {rw [← one_add_one_eq_two, add_mul, one_mul]}
end
-- END

end my_ring


/-We close this section by noting that some of the 
facts about addition and negation that we established 
above do not need the full strength of the ring axioms, 
or even commutativity of addition. The weaker notion of a 
group can be axiomatized as follows:
-/

variables (A : Type*) [add_group A]

#check (add_assoc : ∀ a b c : A, a + b + c = a + (b + c))
#check (zero_add : ∀ a : A, 0 + a = a)
#check (add_left_neg : ∀ a : A, -a + a = 0)


/-It is conventional to use additive notation when the 
group operation is commutative, and multiplicative notation 
otherwise. So Lean defines a multiplicative version as well 
as the additive version (and also their abelian variants, 
add_comm_group and comm_group).
-/

variables (G : Type*) [group G]

#check (mul_assoc : ∀ a b c : G, a * b * c = a * (b * c))
#check (one_mul : ∀ a : G, 1 * a = a)
#check (mul_left_inv : ∀ a : G, a⁻¹ * a = 1)

/-If you are feeling cocky, try proving the following 
facts about groups, using only these axioms. You will 
need to prove a number of helper lemmas along the way. 
The proofs we have carried out in this section provide 
some hints.
-/

variables {G' : Type*} [group G']

#check (mul_assoc : ∀ a b c : G', a * b * c = a * (b * c))
#check (one_mul : ∀ a : G', 1 * a = a)
#check (mul_left_inv : ∀ a : G', a⁻¹ * a = 1)

namespace my_group


lemma inv_mul_cancel_left (a b : G') : a⁻¹ * (a * b) = b :=
by rw [←mul_assoc, mul_left_inv, one_mul]

lemma mul_left_cancel {a b c : G'} (h : a * b = a * c) : b = c :=
by rw [← one_mul b, ← mul_left_inv a, mul_assoc, h, inv_mul_cancel_left]

/-lemma inv_eq_of_mul_eq_one {a b : G'} (h : b * a = 1) : b = a⁻¹ :=
begin
    rw ← mul_left_inv b at h,
    rw add_comm a at h,
    rw add_right_cancel h,
end-/

theorem mul_one (a : G') : a * 1 = a :=
begin
    have h : a⁻¹ * (a * a⁻¹ * a) = a⁻¹ * a,
    {rw [mul_assoc, mul_left_inv, ←mul_assoc, mul_left_inv, one_mul]},
    rw ← mul_left_inv a,
    rw ← mul_assoc,
    apply mul_left_cancel h,
end

lemma inv_mul_cancel_right (a b : G') : (a * b⁻¹) * b = a :=
by rw [mul_assoc, mul_left_inv, mul_one]

theorem mul_right_inv (a : G') : a * a⁻¹ = 1 :=
begin
    rw ← mul_left_inv a,
    have h1 : 1 * a⁻¹ = a⁻¹ * 1,
    {rw [one_mul, mul_one]},
    have h2 : a⁻¹ * (a * a⁻¹) = a⁻¹ * (a⁻¹ * a),
    {rw [mul_left_inv, ← mul_assoc, mul_left_inv, h1]},
    apply mul_left_cancel h2,
end

theorem mul_inv_rev (a b : G') : (a * b)⁻¹ = b⁻¹ * a ⁻¹ :=
begin
    have h1 : (a * b) * (b⁻¹ * a⁻¹) = 1,
    {rw [mul_assoc, ← mul_assoc b, mul_right_inv, one_mul, mul_right_inv]},
    have h2 : (a * b) * (a * b)⁻¹ = (a * b) * (b⁻¹ * a⁻¹),
    {rw [mul_right_inv, h1]},
    apply mul_left_cancel h2,
end

end my_group
 
--650 hw 4 q1
namespace my_ring

variables {R' : Type*} [ring R']

lemma square_comm {a b : R'} (h : ∀ a : R', a^2 = a) : a*b = b*a :=
begin
    have h1 : a + b = a + (b * a + a * b) + b,
    calc
        a + b 
        = (a + b)^2:
            by rw [h]
        ... = a^2 + b * a + (a * b + b^2) :
            by {repeat {rw pow_two}, rw mul_add, repeat {rw add_mul}}
        ... = a + (b * a + a * b) + b :
            by rw [h a, h b, add_assoc, ← add_assoc (b * a), ← add_assoc],
    
    have h2 : -(a * b) = a * b,
    calc
        -(a * b) 
        = (-(a * b))^2 :
            by rw [h]
        ... = -(a * b) * -(a * b) :
            by rw [pow_two]
        ... = (a * b)^2 :
            by rw [neg_mul_neg, pow_two]
        ... = a * b :
            by rw [h],
    rw add_assoc at h1,
    rw ← add_zero (a + b) at h1,
    rw add_assoc at h1,
    rw add_left_cancel_iff at h1,
    rw add_comm at h1,
    rw add_right_cancel_iff at h1,
    symmetry' at h1,
    symmetry' at h2,
    rw h2,
    rw eq_neg_of_add_eq_zero h1,
end

lemma cube_comm {a b : R'} (h : ∀ a : R', a^3 = a) : a*b = b*a :=
begin
    have h1 : a^3 + b = a^3 + a^2 * b + a * b * a + a * b^2 + b * a^2 + b * a * b + b^2 * a + b^3,
    calc
        a^3 + b 
        = a + b:
            by rw [h]
        ... = (a + b)^3 :
            by rw [h]
        ... = (a + b) * (a + b)^2 :
            by rw [← pow_succ]
        ... = (a + b) * (a^2 + a * b + b * a + b^2) :
            by {repeat {rw pow_two}, rw [← mul_add, add_assoc, ← mul_add, ← add_mul]}
            --by rw [pow_two, pow_two, pow_two, ← mul_add, add_assoc, ← mul_add, ← add_mul]
        ... = a * a ^ 2 + a * (a * b) + a * (b * a) + a * b ^ 2 + (b * a ^ 2 + b * (a * b) + b * (b * a) + b * b ^ 2) :
            by {rw add_mul, repeat {rw mul_add}}
        ... = a * a ^ 2 + a * a * b + a * b * a + a * b ^ 2 + b * a ^ 2 + b * a * b + b * b * a + b * b ^ 2 :
            by {repeat {rw ← mul_assoc}, repeat {rw ← add_assoc}}
        ... = a^3 + a^2 * b + a * b * a + a * b^2 + b * a^2 + b * a * b + b^2 * a + b^3 :
            by {repeat {rw ← pow_succ}, repeat {rw ← pow_two}},

    have h2 : (a - b)^2 = a^2 - a * b - b * a + b^2,
    calc
        (a - b)^2
        = (a - b) * (a - b):
            by rw [pow_two]
        ... = a * a - a * b - b * a + b * b :
            by sorry
            /-by rw [sub_mul, mul_sub, mul_sub, add_sub]-/
        ... = a^2 - a * b - b * a + b^2 :
            by sorry,

    
    have h3 : a^3 - b = a^3 - a^2 * b - a * b * a + a * b^2 - b * a^2 + b * a * b + b^2 * a - b^3,
    calc
        a^3 - b 
        = a - b:
            by rw [h]
        ... = (a - b)^3 :
            by rw [h]
        ... = (a - b) * (a - b)^2 :
            by rw [← pow_succ]
        ... = (a - b) * (a^2 - a * b - b * a + b^2) :
            by {repeat {rw pow_two}, repeat { rw mul_sub },
  repeat { rw sub_mul },
  repeat { rw add_sub },
  repeat { rw ←sub_add },
  repeat { rw ←mul_assoc }}
        ... = a * b :
            by rw [h],
    rw add_assoc at h1,
    rw ← add_zero (a + b) at h1,
    rw add_assoc at h1,
    rw add_left_cancel_iff at h1,
    rw add_comm at h1,
    rw add_right_cancel_iff at h1,
    symmetry' at h1,
    symmetry' at h2,
    rw h2,
    rw eq_neg_of_add_eq_zero h1,
end

lemma problem_nine_1 {x : R'} (h : ∀ x, ∃ y : R', x * y * x = x) : 
    (∀ a b : R', a * b = 0 → a = 0 ∨ b = 0) :=
begin
    exfalso,
    have h2 := ∃ a b : R', (a * b = 0) → ((a ≠ 0) ∧ (b ≠ 0)),
    sorry,
end

variables {α : Type*} [domain α]

lemma problem_nine_2 [no_zero_divisors α] {x y : R'} (h1 : x * y * x = x): 
    (y * x * y = y) :=
begin
    /-have h3 : x * y * x = x * (y * x * y * x),
    calc
        x * y * x 
        = (x * y * x) * y * x :
            by {rw [h1, h1]}
        ... = x * (y * x * y * x) :
            by rw [mul_assoc, mul_assoc, mul_assoc, ← mul_assoc _ _ x, ← mul_assoc y, ← mul_assoc y],
    rw mul_assoc at h3,
    rw mul_left_cancel_iff at h3,-/
    sorry
end



end my_ring