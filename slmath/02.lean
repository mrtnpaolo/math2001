import Mathlib.Data.Real.Basic

section

example (a b c : ℝ) : a * (b * c) = b * (c * a) := by
  rw [mul_comm, mul_assoc]

example (a b c : ℝ) : a * (b * c) = b * (a * c) := by
  rw [← mul_assoc, mul_comm a, mul_assoc]

example (a b c d e f : ℝ) (h : b * c = e * f) : a * b * c * d = a * e * f * d := by
  rw [mul_assoc a b c, h, mul_assoc a e f]

example (a b c d : ℝ) (hyp : c = b * a - d) (hyp' : d = a * b) : c = 0 := by
  rw [hyp, hyp', mul_comm]
  exact sub_self (a * b)

end

section
variable (a b : ℝ)

example : (a + b) * (a + b) = a * a + 2 * (a * b) + b * b := by
  rw [mul_add, add_mul, add_mul]
  rw [← add_assoc, add_assoc (a * a)]
  rw [mul_comm b a, ← two_mul]

-- yay

#check mul_add

example : (a + b) * (a + b) = a * a + 2 * (a * b) + b * b := by
  calc
    (a + b) * (a + b) = a * a + b * a + (a * b + b * b) := by
      rw [mul_add, add_mul, add_mul]
    _ = a * a + (b * a + a * b) + b * b := by
      rw [← add_assoc, add_assoc (a * a)]
    _ = a * a + 2 * (a * b) + b * b := by
      rw [mul_comm b a, two_mul]

end

section
variable (a b c d : ℝ)

example : (a+b)*(c+d) = a*c + a*d + b*c + b*d := by
  calc
    (a+b)*(c+d) = a*(c+d) + b*(c+d) := by
      rw [ add_mul ]
    _ = a*c + a*d + (b*c + b*d) := by
      rw [ mul_add a, mul_add b ]
    _ = a*c + a*d + b*c + b*d := by
      rw [ ← add_assoc ]

example : (a+b)*(a-b) = a^2 - b^2 := by
  calc
    (a+b)*(a-b) = a*a - a*b + a*b - b*b := by
      rw [ add_mul, mul_sub a, mul_sub b, add_sub, mul_comm b a ]
    _ = a^2 - b^2 := by
      show_term rw [ sub_add_cancel, pow_two, pow_two ]

-- yay

example : (a+b)*(a-b) = a^2 - b^2 := by
  ring
