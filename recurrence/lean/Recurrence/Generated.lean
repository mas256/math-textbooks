import Recurrence.Theory

namespace Recurrence

def p248 (n : ℕ) : ℚ := ((-2 : ℚ) ^ n)
theorem p248_base_valid : FirstCertificate p248 (1 : ℚ) (fun n x => ((-2 : ℚ) * x + (0 : ℚ)) / (1 : ℚ)) := by
  apply linear_certificate p248 (1 : ℚ) (fun n : ℕ => (1 : ℚ)) (fun n : ℕ => (-2 : ℚ)) (fun n : ℕ => (0 : ℚ))
  · norm_num [p248]
  · intro n; positivity
  · intro n
    simp only [p248, Nat.cast_add, Nat.cast_one, pow_succ, pow_add] at *
    ring
theorem p248_valid : FirstCertificate p248 (1 : ℚ) (fun n x => ((-2 : ℚ) * x + (0 : ℚ)) / (1 : ℚ)) := p248_base_valid
theorem p248_unique (a : ℕ → ℚ) (ha : FirstCertificate a (1 : ℚ) (fun n x => ((-2 : ℚ) * x + (0 : ℚ)) / (1 : ℚ))) :
    ∀ n, a n = p248 n := first_unique p248_valid ha
#print axioms p248_valid
#print axioms p248_unique

def p249 (n : ℕ) : ℚ := ((-1 : ℚ) ^ n)
theorem p249_base_valid : FirstCertificate p249 (1 : ℚ) (fun n x => ((-1 : ℚ) * x + (0 : ℚ)) / (1 : ℚ)) := by
  apply linear_certificate p249 (1 : ℚ) (fun n : ℕ => (1 : ℚ)) (fun n : ℕ => (-1 : ℚ)) (fun n : ℕ => (0 : ℚ))
  · norm_num [p249]
  · intro n; positivity
  · intro n
    simp only [p249, Nat.cast_add, Nat.cast_one, pow_succ, pow_add] at *
    ring
theorem p249_valid : FirstCertificate p249 (1 : ℚ) (fun n x => ((-1 : ℚ) * x + (0 : ℚ)) / (1 : ℚ)) := p249_base_valid
theorem p249_unique (a : ℕ → ℚ) (ha : FirstCertificate a (1 : ℚ) (fun n x => ((-1 : ℚ) * x + (0 : ℚ)) / (1 : ℚ))) :
    ∀ n, a n = p249 n := first_unique p249_valid ha
#print axioms p249_valid
#print axioms p249_unique

def p054 (n : ℕ) : ℚ := ((2 : ℚ) * ((2 : ℚ) ^ n))
theorem p054_base_valid : FirstCertificate p054 (2 : ℚ) (fun n x => ((2 : ℚ) * x + (0 : ℚ)) / (1 : ℚ)) := by
  apply linear_certificate p054 (2 : ℚ) (fun n : ℕ => (1 : ℚ)) (fun n : ℕ => (2 : ℚ)) (fun n : ℕ => (0 : ℚ))
  · norm_num [p054]
  · intro n; positivity
  · intro n
    simp only [p054, Nat.cast_add, Nat.cast_one, pow_succ, pow_add] at *
    ring
theorem p054_valid : FirstCertificate p054 (2 : ℚ) (fun n x => ((2 : ℚ) * x + (0 : ℚ)) / (1 : ℚ)) := p054_base_valid
theorem p054_unique (a : ℕ → ℚ) (ha : FirstCertificate a (2 : ℚ) (fun n x => ((2 : ℚ) * x + (0 : ℚ)) / (1 : ℚ))) :
    ∀ n, a n = p054 n := first_unique p054_valid ha
#print axioms p054_valid
#print axioms p054_unique

def p007 (n : ℕ) : ℚ := ((3 : ℚ) ^ n)
theorem p007_base_valid : FirstCertificate p007 (1 : ℚ) (fun n x => ((3 : ℚ) * x + (0 : ℚ)) / (1 : ℚ)) := by
  apply linear_certificate p007 (1 : ℚ) (fun n : ℕ => (1 : ℚ)) (fun n : ℕ => (3 : ℚ)) (fun n : ℕ => (0 : ℚ))
  · norm_num [p007]
  · intro n; positivity
  · intro n
    simp only [p007, Nat.cast_add, Nat.cast_one, pow_succ, pow_add] at *
    ring
theorem p007_valid : FirstCertificate p007 (1 : ℚ) (fun n x => ((3 : ℚ) * x + (0 : ℚ)) / (1 : ℚ)) := p007_base_valid
theorem p007_unique (a : ℕ → ℚ) (ha : FirstCertificate a (1 : ℚ) (fun n x => ((3 : ℚ) * x + (0 : ℚ)) / (1 : ℚ))) :
    ∀ n, a n = p007 n := first_unique p007_valid ha
#print axioms p007_valid
#print axioms p007_unique

def p253 (n : ℕ) : ℚ := (((1 : ℚ) / 2) ^ n)
theorem p253_base_valid : FirstCertificate p253 (1 : ℚ) (fun n x => (((1 : ℚ) / 2) * x + (0 : ℚ)) / (1 : ℚ)) := by
  apply linear_certificate p253 (1 : ℚ) (fun n : ℕ => (1 : ℚ)) (fun n : ℕ => ((1 : ℚ) / 2)) (fun n : ℕ => (0 : ℚ))
  · norm_num [p253]
  · intro n; positivity
  · intro n
    simp only [p253, Nat.cast_add, Nat.cast_one, pow_succ, pow_add] at *
    ring
theorem p253_valid : FirstCertificate p253 (1 : ℚ) (fun n x => (((1 : ℚ) / 2) * x + (0 : ℚ)) / (1 : ℚ)) := p253_base_valid
theorem p253_unique (a : ℕ → ℚ) (ha : FirstCertificate a (1 : ℚ) (fun n x => (((1 : ℚ) / 2) * x + (0 : ℚ)) / (1 : ℚ))) :
    ∀ n, a n = p253 n := first_unique p253_valid ha
#print axioms p253_valid
#print axioms p253_unique

def p057 (n : ℕ) : ℚ := (((8 : ℚ) * ((2 : ℚ) ^ n)) + (1 : ℚ))
theorem p057_base_valid : FirstCertificate p057 (9 : ℚ) (fun n x => ((2 : ℚ) * x + (-1 : ℚ)) / (1 : ℚ)) := by
  apply linear_certificate p057 (9 : ℚ) (fun n : ℕ => (1 : ℚ)) (fun n : ℕ => (2 : ℚ)) (fun n : ℕ => (-1 : ℚ))
  · norm_num [p057]
  · intro n; positivity
  · intro n
    simp only [p057, Nat.cast_add, Nat.cast_one, pow_succ, pow_add] at *
    ring
theorem p057_valid : FirstCertificate p057 (9 : ℚ) (fun n x => ((2 : ℚ) * x + (-1 : ℚ)) / (1 : ℚ)) := p057_base_valid
theorem p057_unique (a : ℕ → ℚ) (ha : FirstCertificate a (9 : ℚ) (fun n x => ((2 : ℚ) * x + (-1 : ℚ)) / (1 : ℚ))) :
    ∀ n, a n = p057 n := first_unique p057_valid ha
#print axioms p057_valid
#print axioms p057_unique

def p015 (n : ℕ) : ℚ := (((3 : ℚ) * ((2 : ℚ) ^ n)) + (2 : ℚ))
theorem p015_base_valid : FirstCertificate p015 (5 : ℚ) (fun n x => ((2 : ℚ) * x + (-2 : ℚ)) / (1 : ℚ)) := by
  apply linear_certificate p015 (5 : ℚ) (fun n : ℕ => (1 : ℚ)) (fun n : ℕ => (2 : ℚ)) (fun n : ℕ => (-2 : ℚ))
  · norm_num [p015]
  · intro n; positivity
  · intro n
    simp only [p015, Nat.cast_add, Nat.cast_one, pow_succ, pow_add] at *
    ring
theorem p015_valid : FirstCertificate p015 (5 : ℚ) (fun n x => ((2 : ℚ) * x + (-2 : ℚ)) / (1 : ℚ)) := p015_base_valid
theorem p015_unique (a : ℕ → ℚ) (ha : FirstCertificate a (5 : ℚ) (fun n x => ((2 : ℚ) * x + (-2 : ℚ)) / (1 : ℚ))) :
    ∀ n, a n = p015 n := first_unique p015_valid ha
#print axioms p015_valid
#print axioms p015_unique

def p058 (n : ℕ) : ℚ := (((2 : ℚ) * ((2 : ℚ) ^ n)) + (3 : ℚ))
theorem p058_base_valid : FirstCertificate p058 (5 : ℚ) (fun n x => ((2 : ℚ) * x + (-3 : ℚ)) / (1 : ℚ)) := by
  apply linear_certificate p058 (5 : ℚ) (fun n : ℕ => (1 : ℚ)) (fun n : ℕ => (2 : ℚ)) (fun n : ℕ => (-3 : ℚ))
  · norm_num [p058]
  · intro n; positivity
  · intro n
    simp only [p058, Nat.cast_add, Nat.cast_one, pow_succ, pow_add] at *
    ring
theorem p058_valid : FirstCertificate p058 (5 : ℚ) (fun n x => ((2 : ℚ) * x + (-3 : ℚ)) / (1 : ℚ)) := p058_base_valid
theorem p058_unique (a : ℕ → ℚ) (ha : FirstCertificate a (5 : ℚ) (fun n x => ((2 : ℚ) * x + (-3 : ℚ)) / (1 : ℚ))) :
    ∀ n, a n = p058 n := first_unique p058_valid ha
#print axioms p058_valid
#print axioms p058_unique

def p011 (n : ℕ) : ℚ := (((4 : ℚ) * ((3 : ℚ) ^ n)) + (1 : ℚ))
theorem p011_base_valid : FirstCertificate p011 (5 : ℚ) (fun n x => ((3 : ℚ) * x + (-2 : ℚ)) / (1 : ℚ)) := by
  apply linear_certificate p011 (5 : ℚ) (fun n : ℕ => (1 : ℚ)) (fun n : ℕ => (3 : ℚ)) (fun n : ℕ => (-2 : ℚ))
  · norm_num [p011]
  · intro n; positivity
  · intro n
    simp only [p011, Nat.cast_add, Nat.cast_one, pow_succ, pow_add] at *
    ring
theorem p011_valid : FirstCertificate p011 (5 : ℚ) (fun n x => ((3 : ℚ) * x + (-2 : ℚ)) / (1 : ℚ)) := p011_base_valid
theorem p011_unique (a : ℕ → ℚ) (ha : FirstCertificate a (5 : ℚ) (fun n x => ((3 : ℚ) * x + (-2 : ℚ)) / (1 : ℚ))) :
    ∀ n, a n = p011 n := first_unique p011_valid ha
#print axioms p011_valid
#print axioms p011_unique

def p012 (n : ℕ) : ℚ := (((3 : ℚ) ^ n) + (2 : ℚ))
theorem p012_base_valid : FirstCertificate p012 (3 : ℚ) (fun n x => ((3 : ℚ) * x + (-4 : ℚ)) / (1 : ℚ)) := by
  apply linear_certificate p012 (3 : ℚ) (fun n : ℕ => (1 : ℚ)) (fun n : ℕ => (3 : ℚ)) (fun n : ℕ => (-4 : ℚ))
  · norm_num [p012]
  · intro n; positivity
  · intro n
    simp only [p012, Nat.cast_add, Nat.cast_one, pow_succ, pow_add] at *
    ring
theorem p012_valid : FirstCertificate p012 (3 : ℚ) (fun n x => ((3 : ℚ) * x + (-4 : ℚ)) / (1 : ℚ)) := p012_base_valid
theorem p012_unique (a : ℕ → ℚ) (ha : FirstCertificate a (3 : ℚ) (fun n x => ((3 : ℚ) * x + (-4 : ℚ)) / (1 : ℚ))) :
    ∀ n, a n = p012 n := first_unique p012_valid ha
#print axioms p012_valid
#print axioms p012_unique

def p061 (n : ℕ) : ℚ := ((3 : ℚ) * (((2 : ℚ) * ((n : ℚ) + 1)) + (1 : ℚ)))
theorem p061_base_valid : FirstCertificate p061 (9 : ℚ) (fun n x => ((((2 : ℚ) * ((n : ℚ) + 1)) + (3 : ℚ)) * x + (0 : ℚ)) / (((2 : ℚ) * ((n : ℚ) + 1)) + (1 : ℚ))) := by
  apply linear_certificate p061 (9 : ℚ) (fun n : ℕ => (((2 : ℚ) * ((n : ℚ) + 1)) + (1 : ℚ))) (fun n : ℕ => (((2 : ℚ) * ((n : ℚ) + 1)) + (3 : ℚ))) (fun n : ℕ => (0 : ℚ))
  · norm_num [p061]
  · intro n; positivity
  · intro n
    simp only [p061, Nat.cast_add, Nat.cast_one, pow_succ, pow_add] at *
    ring
theorem p061_valid : FirstCertificate p061 (9 : ℚ) (fun n x => ((((2 : ℚ) * ((n : ℚ) + 1)) + (3 : ℚ)) * x + (0 : ℚ)) / (((2 : ℚ) * ((n : ℚ) + 1)) + (1 : ℚ))) := p061_base_valid
theorem p061_unique (a : ℕ → ℚ) (ha : FirstCertificate a (9 : ℚ) (fun n x => ((((2 : ℚ) * ((n : ℚ) + 1)) + (3 : ℚ)) * x + (0 : ℚ)) / (((2 : ℚ) * ((n : ℚ) + 1)) + (1 : ℚ)))) :
    ∀ n, a n = p061 n := first_unique p061_valid ha
#print axioms p061_valid
#print axioms p061_unique

def p062 (n : ℕ) : ℚ := ((3 : ℚ) / (((2 : ℚ) * ((n : ℚ) + 1)) + (1 : ℚ)))
theorem p062_base_valid : FirstCertificate p062 (1 : ℚ) (fun n x => ((((2 : ℚ) * ((n : ℚ) + 1)) + (1 : ℚ)) * x + (0 : ℚ)) / (((2 : ℚ) * ((n : ℚ) + 1)) + (3 : ℚ))) := by
  apply linear_certificate p062 (1 : ℚ) (fun n : ℕ => (((2 : ℚ) * ((n : ℚ) + 1)) + (3 : ℚ))) (fun n : ℕ => (((2 : ℚ) * ((n : ℚ) + 1)) + (1 : ℚ))) (fun n : ℕ => (0 : ℚ))
  · norm_num [p062]
  · intro n; positivity
  · intro n
    have hd0 : (((2 : ℚ) * ((n : ℚ) + 1)) + (1 : ℚ)) ≠ 0 := by positivity
    have he0 : (((2 : ℚ) * (((n + 1) : ℚ) + 1)) + (1 : ℚ)) ≠ 0 := by positivity
    simp only [p062, Nat.cast_add, Nat.cast_one, pow_succ, pow_add] at *
    field_simp [hd0, he0] <;> ring
theorem p062_valid : FirstCertificate p062 (1 : ℚ) (fun n x => ((((2 : ℚ) * ((n : ℚ) + 1)) + (1 : ℚ)) * x + (0 : ℚ)) / (((2 : ℚ) * ((n : ℚ) + 1)) + (3 : ℚ))) := p062_base_valid
theorem p062_unique (a : ℕ → ℚ) (ha : FirstCertificate a (1 : ℚ) (fun n x => ((((2 : ℚ) * ((n : ℚ) + 1)) + (1 : ℚ)) * x + (0 : ℚ)) / (((2 : ℚ) * ((n : ℚ) + 1)) + (3 : ℚ)))) :
    ∀ n, a n = p062 n := first_unique p062_valid ha
#print axioms p062_valid
#print axioms p062_unique

def p063 (n : ℕ) : ℚ := ((3 : ℚ) * (((n : ℚ) + 1) + (1 : ℚ)))
theorem p063_base_valid : FirstCertificate p063 (6 : ℚ) (fun n x => ((((n : ℚ) + 1) + (2 : ℚ)) * x + (0 : ℚ)) / (((n : ℚ) + 1) + (1 : ℚ))) := by
  apply linear_certificate p063 (6 : ℚ) (fun n : ℕ => (((n : ℚ) + 1) + (1 : ℚ))) (fun n : ℕ => (((n : ℚ) + 1) + (2 : ℚ))) (fun n : ℕ => (0 : ℚ))
  · norm_num [p063]
  · intro n; positivity
  · intro n
    simp only [p063, Nat.cast_add, Nat.cast_one, pow_succ, pow_add] at *
    ring
theorem p063_valid : FirstCertificate p063 (6 : ℚ) (fun n x => ((((n : ℚ) + 1) + (2 : ℚ)) * x + (0 : ℚ)) / (((n : ℚ) + 1) + (1 : ℚ))) := p063_base_valid
theorem p063_unique (a : ℕ → ℚ) (ha : FirstCertificate a (6 : ℚ) (fun n x => ((((n : ℚ) + 1) + (2 : ℚ)) * x + (0 : ℚ)) / (((n : ℚ) + 1) + (1 : ℚ)))) :
    ∀ n, a n = p063 n := first_unique p063_valid ha
#print axioms p063_valid
#print axioms p063_unique

def p064 (n : ℕ) : ℚ := ((3 : ℚ) / ((n : ℚ) + 1))
theorem p064_base_valid : FirstCertificate p064 (3 : ℚ) (fun n x => (((n : ℚ) + 1) * x + (0 : ℚ)) / (((n : ℚ) + 1) + (1 : ℚ))) := by
  apply linear_certificate p064 (3 : ℚ) (fun n : ℕ => (((n : ℚ) + 1) + (1 : ℚ))) (fun n : ℕ => ((n : ℚ) + 1)) (fun n : ℕ => (0 : ℚ))
  · norm_num [p064]
  · intro n; positivity
  · intro n
    have hd0 : ((n : ℚ) + 1) ≠ 0 := by positivity
    have he0 : (((n + 1) : ℚ) + 1) ≠ 0 := by positivity
    simp only [p064, Nat.cast_add, Nat.cast_one, pow_succ, pow_add] at *
    field_simp [hd0, he0] <;> ring
theorem p064_valid : FirstCertificate p064 (3 : ℚ) (fun n x => (((n : ℚ) + 1) * x + (0 : ℚ)) / (((n : ℚ) + 1) + (1 : ℚ))) := p064_base_valid
theorem p064_unique (a : ℕ → ℚ) (ha : FirstCertificate a (3 : ℚ) (fun n x => (((n : ℚ) + 1) * x + (0 : ℚ)) / (((n : ℚ) + 1) + (1 : ℚ)))) :
    ∀ n, a n = p064 n := first_unique p064_valid ha
#print axioms p064_valid
#print axioms p064_unique

def p065 (n : ℕ) : ℚ := ((3 : ℚ) / (((n : ℚ) + 1) + (1 : ℚ)))
theorem p065_base_valid : FirstCertificate p065 ((3 : ℚ) / 2) (fun n x => ((((n : ℚ) + 1) + (1 : ℚ)) * x + (0 : ℚ)) / (((n : ℚ) + 1) + (2 : ℚ))) := by
  apply linear_certificate p065 ((3 : ℚ) / 2) (fun n : ℕ => (((n : ℚ) + 1) + (2 : ℚ))) (fun n : ℕ => (((n : ℚ) + 1) + (1 : ℚ))) (fun n : ℕ => (0 : ℚ))
  · norm_num [p065]
  · intro n; positivity
  · intro n
    have hd0 : (((n : ℚ) + 1) + (1 : ℚ)) ≠ 0 := by positivity
    have he0 : ((((n + 1) : ℚ) + 1) + (1 : ℚ)) ≠ 0 := by positivity
    simp only [p065, Nat.cast_add, Nat.cast_one, pow_succ, pow_add] at *
    field_simp [hd0, he0] <;> ring
theorem p065_valid : FirstCertificate p065 ((3 : ℚ) / 2) (fun n x => ((((n : ℚ) + 1) + (1 : ℚ)) * x + (0 : ℚ)) / (((n : ℚ) + 1) + (2 : ℚ))) := p065_base_valid
theorem p065_unique (a : ℕ → ℚ) (ha : FirstCertificate a ((3 : ℚ) / 2) (fun n x => ((((n : ℚ) + 1) + (1 : ℚ)) * x + (0 : ℚ)) / (((n : ℚ) + 1) + (2 : ℚ)))) :
    ∀ n, a n = p065 n := first_unique p065_valid ha
#print axioms p065_valid
#print axioms p065_unique

def p066 (n : ℕ) : ℚ := ((3 : ℚ) / (((n : ℚ) + 1) * (((n : ℚ) + 1) + (1 : ℚ))))
theorem p066_base_valid : FirstCertificate p066 ((3 : ℚ) / 2) (fun n x => (((n : ℚ) + 1) * x + (0 : ℚ)) / (((n : ℚ) + 1) + (2 : ℚ))) := by
  apply linear_certificate p066 ((3 : ℚ) / 2) (fun n : ℕ => (((n : ℚ) + 1) + (2 : ℚ))) (fun n : ℕ => ((n : ℚ) + 1)) (fun n : ℕ => (0 : ℚ))
  · norm_num [p066]
  · intro n; positivity
  · intro n
    have hd0 : (((n : ℚ) + 1) * (((n : ℚ) + 1) + (1 : ℚ))) ≠ 0 := by positivity
    have he0 : ((((n + 1) : ℚ) + 1) * ((((n + 1) : ℚ) + 1) + (1 : ℚ))) ≠ 0 := by positivity
    simp only [p066, Nat.cast_add, Nat.cast_one, pow_succ, pow_add] at *
    field_simp [hd0, he0] <;> ring
theorem p066_valid : FirstCertificate p066 ((3 : ℚ) / 2) (fun n x => (((n : ℚ) + 1) * x + (0 : ℚ)) / (((n : ℚ) + 1) + (2 : ℚ))) := p066_base_valid
theorem p066_unique (a : ℕ → ℚ) (ha : FirstCertificate a ((3 : ℚ) / 2) (fun n x => (((n : ℚ) + 1) * x + (0 : ℚ)) / (((n : ℚ) + 1) + (2 : ℚ)))) :
    ∀ n, a n = p066 n := first_unique p066_valid ha
#print axioms p066_valid
#print axioms p066_unique

def p067 (n : ℕ) : ℚ := ((3 : ℚ) * ((n : ℚ) + 1))
theorem p067_base_valid : FirstCertificate p067 (3 : ℚ) (fun n x => ((((n : ℚ) + 1) + (1 : ℚ)) * x + (0 : ℚ)) / ((n : ℚ) + 1)) := by
  apply linear_certificate p067 (3 : ℚ) (fun n : ℕ => ((n : ℚ) + 1)) (fun n : ℕ => (((n : ℚ) + 1) + (1 : ℚ))) (fun n : ℕ => (0 : ℚ))
  · norm_num [p067]
  · intro n; positivity
  · intro n
    simp only [p067, Nat.cast_add, Nat.cast_one, pow_succ, pow_add] at *
    ring
theorem p067_valid : FirstCertificate p067 (3 : ℚ) (fun n x => ((((n : ℚ) + 1) + (1 : ℚ)) * x + (0 : ℚ)) / ((n : ℚ) + 1)) := p067_base_valid
theorem p067_unique (a : ℕ → ℚ) (ha : FirstCertificate a (3 : ℚ) (fun n x => ((((n : ℚ) + 1) + (1 : ℚ)) * x + (0 : ℚ)) / ((n : ℚ) + 1))) :
    ∀ n, a n = p067 n := first_unique p067_valid ha
#print axioms p067_valid
#print axioms p067_unique

def p068 (n : ℕ) : ℚ := ((3 : ℚ) * ((n : ℚ) + 1) * (((n : ℚ) + 1) + (1 : ℚ)))
theorem p068_base_valid : FirstCertificate p068 (6 : ℚ) (fun n x => ((((n : ℚ) + 1) + (2 : ℚ)) * x + (0 : ℚ)) / ((n : ℚ) + 1)) := by
  apply linear_certificate p068 (6 : ℚ) (fun n : ℕ => ((n : ℚ) + 1)) (fun n : ℕ => (((n : ℚ) + 1) + (2 : ℚ))) (fun n : ℕ => (0 : ℚ))
  · norm_num [p068]
  · intro n; positivity
  · intro n
    simp only [p068, Nat.cast_add, Nat.cast_one, pow_succ, pow_add] at *
    ring
theorem p068_valid : FirstCertificate p068 (6 : ℚ) (fun n x => ((((n : ℚ) + 1) + (2 : ℚ)) * x + (0 : ℚ)) / ((n : ℚ) + 1)) := p068_base_valid
theorem p068_unique (a : ℕ → ℚ) (ha : FirstCertificate a (6 : ℚ) (fun n x => ((((n : ℚ) + 1) + (2 : ℚ)) * x + (0 : ℚ)) / ((n : ℚ) + 1))) :
    ∀ n, a n = p068 n := first_unique p068_valid ha
#print axioms p068_valid
#print axioms p068_unique

def p069 (n : ℕ) : ℚ := ((3 : ℚ) / (((n : ℚ) + 1) * (((n : ℚ) + 1) + (2 : ℚ))))
theorem p069_base_valid : FirstCertificate p069 (1 : ℚ) (fun n x => ((((n : ℚ) + 1) * (((n : ℚ) + 1) + (2 : ℚ))) * x + (0 : ℚ)) / ((((n : ℚ) + 1) + (1 : ℚ)) * (((n : ℚ) + 1) + (3 : ℚ)))) := by
  apply linear_certificate p069 (1 : ℚ) (fun n : ℕ => ((((n : ℚ) + 1) + (1 : ℚ)) * (((n : ℚ) + 1) + (3 : ℚ)))) (fun n : ℕ => (((n : ℚ) + 1) * (((n : ℚ) + 1) + (2 : ℚ)))) (fun n : ℕ => (0 : ℚ))
  · norm_num [p069]
  · intro n; positivity
  · intro n
    have hd0 : (((n : ℚ) + 1) * (((n : ℚ) + 1) + (2 : ℚ))) ≠ 0 := by positivity
    have he0 : ((((n + 1) : ℚ) + 1) * ((((n + 1) : ℚ) + 1) + (2 : ℚ))) ≠ 0 := by positivity
    simp only [p069, Nat.cast_add, Nat.cast_one, pow_succ, pow_add] at *
    field_simp [hd0, he0] <;> ring
theorem p069_valid : FirstCertificate p069 (1 : ℚ) (fun n x => ((((n : ℚ) + 1) * (((n : ℚ) + 1) + (2 : ℚ))) * x + (0 : ℚ)) / ((((n : ℚ) + 1) + (1 : ℚ)) * (((n : ℚ) + 1) + (3 : ℚ)))) := p069_base_valid
theorem p069_unique (a : ℕ → ℚ) (ha : FirstCertificate a (1 : ℚ) (fun n x => ((((n : ℚ) + 1) * (((n : ℚ) + 1) + (2 : ℚ))) * x + (0 : ℚ)) / ((((n : ℚ) + 1) + (1 : ℚ)) * (((n : ℚ) + 1) + (3 : ℚ))))) :
    ∀ n, a n = p069 n := first_unique p069_valid ha
#print axioms p069_valid
#print axioms p069_unique

def p070 (n : ℕ) : ℚ := ((3 : ℚ) / (((n : ℚ) + 1) ^ 2))
theorem p070_base_valid : FirstCertificate p070 (3 : ℚ) (fun n x => ((((n : ℚ) + 1) ^ 2) * x + (0 : ℚ)) / ((((n : ℚ) + 1) + (1 : ℚ)) ^ 2)) := by
  apply linear_certificate p070 (3 : ℚ) (fun n : ℕ => ((((n : ℚ) + 1) + (1 : ℚ)) ^ 2)) (fun n : ℕ => (((n : ℚ) + 1) ^ 2)) (fun n : ℕ => (0 : ℚ))
  · norm_num [p070]
  · intro n; positivity
  · intro n
    have hd0 : (((n : ℚ) + 1) ^ 2) ≠ 0 := by positivity
    have he0 : ((((n + 1) : ℚ) + 1) ^ 2) ≠ 0 := by positivity
    simp only [p070, Nat.cast_add, Nat.cast_one, pow_succ, pow_add] at *
    field_simp [hd0, he0] <;> ring
theorem p070_valid : FirstCertificate p070 (3 : ℚ) (fun n x => ((((n : ℚ) + 1) ^ 2) * x + (0 : ℚ)) / ((((n : ℚ) + 1) + (1 : ℚ)) ^ 2)) := p070_base_valid
theorem p070_unique (a : ℕ → ℚ) (ha : FirstCertificate a (3 : ℚ) (fun n x => ((((n : ℚ) + 1) ^ 2) * x + (0 : ℚ)) / ((((n : ℚ) + 1) + (1 : ℚ)) ^ 2))) :
    ∀ n, a n = p070 n := first_unique p070_valid ha
#print axioms p070_valid
#print axioms p070_unique

def p016 (n : ℕ) : ℚ := (((n : ℚ) + 1) * (((n : ℚ) + 1) + (2 : ℚ)))
theorem p016_base_valid : FirstCertificate p016 (3 : ℚ) (fun n x => (((((n : ℚ) + 1) + (1 : ℚ)) * (((n : ℚ) + 1) + (3 : ℚ))) * x + (0 : ℚ)) / (((n : ℚ) + 1) * (((n : ℚ) + 1) + (2 : ℚ)))) := by
  apply linear_certificate p016 (3 : ℚ) (fun n : ℕ => (((n : ℚ) + 1) * (((n : ℚ) + 1) + (2 : ℚ)))) (fun n : ℕ => ((((n : ℚ) + 1) + (1 : ℚ)) * (((n : ℚ) + 1) + (3 : ℚ)))) (fun n : ℕ => (0 : ℚ))
  · norm_num [p016]
  · intro n; positivity
  · intro n
    simp only [p016, Nat.cast_add, Nat.cast_one, pow_succ, pow_add] at *
    ring
theorem p016_valid : FirstCertificate p016 (3 : ℚ) (fun n x => (((((n : ℚ) + 1) + (1 : ℚ)) * (((n : ℚ) + 1) + (3 : ℚ))) * x + (0 : ℚ)) / (((n : ℚ) + 1) * (((n : ℚ) + 1) + (2 : ℚ)))) := p016_base_valid
theorem p016_unique (a : ℕ → ℚ) (ha : FirstCertificate a (3 : ℚ) (fun n x => (((((n : ℚ) + 1) + (1 : ℚ)) * (((n : ℚ) + 1) + (3 : ℚ))) * x + (0 : ℚ)) / (((n : ℚ) + 1) * (((n : ℚ) + 1) + (2 : ℚ))))) :
    ∀ n, a n = p016 n := first_unique p016_valid ha
#print axioms p016_valid
#print axioms p016_unique

def p071 (n : ℕ) : ℚ := ((3 : ℚ) * (((n : ℚ) + 1) ^ 2))
theorem p071_base_valid : FirstCertificate p071 (3 : ℚ) (fun n x => (((((n : ℚ) + 1) + (1 : ℚ)) ^ 2) * x + (0 : ℚ)) / (((n : ℚ) + 1) ^ 2)) := by
  apply linear_certificate p071 (3 : ℚ) (fun n : ℕ => (((n : ℚ) + 1) ^ 2)) (fun n : ℕ => ((((n : ℚ) + 1) + (1 : ℚ)) ^ 2)) (fun n : ℕ => (0 : ℚ))
  · norm_num [p071]
  · intro n; positivity
  · intro n
    simp only [p071, Nat.cast_add, Nat.cast_one, pow_succ, pow_add] at *
    ring
theorem p071_valid : FirstCertificate p071 (3 : ℚ) (fun n x => (((((n : ℚ) + 1) + (1 : ℚ)) ^ 2) * x + (0 : ℚ)) / (((n : ℚ) + 1) ^ 2)) := p071_base_valid
theorem p071_unique (a : ℕ → ℚ) (ha : FirstCertificate a (3 : ℚ) (fun n x => (((((n : ℚ) + 1) + (1 : ℚ)) ^ 2) * x + (0 : ℚ)) / (((n : ℚ) + 1) ^ 2))) :
    ∀ n, a n = p071 n := first_unique p071_valid ha
#print axioms p071_valid
#print axioms p071_unique

def p072 (n : ℕ) : ℚ := (((6 : ℚ) / (((2 : ℚ) * ((n : ℚ) + 1)) + (1 : ℚ))) + (-1 : ℚ))
theorem p072_base_valid : FirstCertificate p072 (1 : ℚ) (fun n x => ((((2 : ℚ) * ((n : ℚ) + 1)) + (1 : ℚ)) * x + (-2 : ℚ)) / (((2 : ℚ) * ((n : ℚ) + 1)) + (3 : ℚ))) := by
  apply linear_certificate p072 (1 : ℚ) (fun n : ℕ => (((2 : ℚ) * ((n : ℚ) + 1)) + (3 : ℚ))) (fun n : ℕ => (((2 : ℚ) * ((n : ℚ) + 1)) + (1 : ℚ))) (fun n : ℕ => (-2 : ℚ))
  · norm_num [p072]
  · intro n; positivity
  · intro n
    have hd0 : (((2 : ℚ) * ((n : ℚ) + 1)) + (1 : ℚ)) ≠ 0 := by positivity
    have he0 : (((2 : ℚ) * (((n + 1) : ℚ) + 1)) + (1 : ℚ)) ≠ 0 := by positivity
    simp only [p072, Nat.cast_add, Nat.cast_one, pow_succ, pow_add] at *
    field_simp [hd0, he0] <;> ring
theorem p072_valid : FirstCertificate p072 (1 : ℚ) (fun n x => ((((2 : ℚ) * ((n : ℚ) + 1)) + (1 : ℚ)) * x + (-2 : ℚ)) / (((2 : ℚ) * ((n : ℚ) + 1)) + (3 : ℚ))) := p072_base_valid
theorem p072_unique (a : ℕ → ℚ) (ha : FirstCertificate a (1 : ℚ) (fun n x => ((((2 : ℚ) * ((n : ℚ) + 1)) + (1 : ℚ)) * x + (-2 : ℚ)) / (((2 : ℚ) * ((n : ℚ) + 1)) + (3 : ℚ)))) :
    ∀ n, a n = p072 n := first_unique p072_valid ha
#print axioms p072_valid
#print axioms p072_unique

def p073 (n : ℕ) : ℚ := (((6 : ℚ) * ((n : ℚ) + 1)) + (-1 : ℚ))
theorem p073_base_valid : FirstCertificate p073 (5 : ℚ) (fun n x => ((((n : ℚ) + 1) + (1 : ℚ)) * x + (1 : ℚ)) / ((n : ℚ) + 1)) := by
  apply linear_certificate p073 (5 : ℚ) (fun n : ℕ => ((n : ℚ) + 1)) (fun n : ℕ => (((n : ℚ) + 1) + (1 : ℚ))) (fun n : ℕ => (1 : ℚ))
  · norm_num [p073]
  · intro n; positivity
  · intro n
    simp only [p073, Nat.cast_add, Nat.cast_one, pow_succ, pow_add] at *
    ring
theorem p073_valid : FirstCertificate p073 (5 : ℚ) (fun n x => ((((n : ℚ) + 1) + (1 : ℚ)) * x + (1 : ℚ)) / ((n : ℚ) + 1)) := p073_base_valid
theorem p073_unique (a : ℕ → ℚ) (ha : FirstCertificate a (5 : ℚ) (fun n x => ((((n : ℚ) + 1) + (1 : ℚ)) * x + (1 : ℚ)) / ((n : ℚ) + 1))) :
    ∀ n, a n = p073 n := first_unique p073_valid ha
#print axioms p073_valid
#print axioms p073_unique

def p074 (n : ℕ) : ℚ := (((6 : ℚ) / (((n : ℚ) + 1) + (1 : ℚ))) + (-1 : ℚ))
theorem p074_base_valid : FirstCertificate p074 (2 : ℚ) (fun n x => ((((n : ℚ) + 1) + (1 : ℚ)) * x + (-1 : ℚ)) / (((n : ℚ) + 1) + (2 : ℚ))) := by
  apply linear_certificate p074 (2 : ℚ) (fun n : ℕ => (((n : ℚ) + 1) + (2 : ℚ))) (fun n : ℕ => (((n : ℚ) + 1) + (1 : ℚ))) (fun n : ℕ => (-1 : ℚ))
  · norm_num [p074]
  · intro n; positivity
  · intro n
    have hd0 : (((n : ℚ) + 1) + (1 : ℚ)) ≠ 0 := by positivity
    have he0 : ((((n + 1) : ℚ) + 1) + (1 : ℚ)) ≠ 0 := by positivity
    simp only [p074, Nat.cast_add, Nat.cast_one, pow_succ, pow_add] at *
    field_simp [hd0, he0] <;> ring
theorem p074_valid : FirstCertificate p074 (2 : ℚ) (fun n x => ((((n : ℚ) + 1) + (1 : ℚ)) * x + (-1 : ℚ)) / (((n : ℚ) + 1) + (2 : ℚ))) := p074_base_valid
theorem p074_unique (a : ℕ → ℚ) (ha : FirstCertificate a (2 : ℚ) (fun n x => ((((n : ℚ) + 1) + (1 : ℚ)) * x + (-1 : ℚ)) / (((n : ℚ) + 1) + (2 : ℚ)))) :
    ∀ n, a n = p074 n := first_unique p074_valid ha
#print axioms p074_valid
#print axioms p074_unique

def p075 (n : ℕ) : ℚ := (((6 : ℚ) / (((n : ℚ) + 1) * (((n : ℚ) + 1) + (1 : ℚ)))) + (-1 : ℚ))
theorem p075_base_valid : FirstCertificate p075 (2 : ℚ) (fun n x => (((n : ℚ) + 1) * x + (-2 : ℚ)) / (((n : ℚ) + 1) + (2 : ℚ))) := by
  apply linear_certificate p075 (2 : ℚ) (fun n : ℕ => (((n : ℚ) + 1) + (2 : ℚ))) (fun n : ℕ => ((n : ℚ) + 1)) (fun n : ℕ => (-2 : ℚ))
  · norm_num [p075]
  · intro n; positivity
  · intro n
    have hd0 : (((n : ℚ) + 1) * (((n : ℚ) + 1) + (1 : ℚ))) ≠ 0 := by positivity
    have he0 : ((((n + 1) : ℚ) + 1) * ((((n + 1) : ℚ) + 1) + (1 : ℚ))) ≠ 0 := by positivity
    simp only [p075, Nat.cast_add, Nat.cast_one, pow_succ, pow_add] at *
    field_simp [hd0, he0] <;> ring
theorem p075_valid : FirstCertificate p075 (2 : ℚ) (fun n x => (((n : ℚ) + 1) * x + (-2 : ℚ)) / (((n : ℚ) + 1) + (2 : ℚ))) := p075_base_valid
theorem p075_unique (a : ℕ → ℚ) (ha : FirstCertificate a (2 : ℚ) (fun n x => (((n : ℚ) + 1) * x + (-2 : ℚ)) / (((n : ℚ) + 1) + (2 : ℚ)))) :
    ∀ n, a n = p075 n := first_unique p075_valid ha
#print axioms p075_valid
#print axioms p075_unique

def p076 (n : ℕ) : ℚ := (((6 : ℚ) * (((n : ℚ) + 1) ^ 2)) + (-1 : ℚ))
theorem p076_base_valid : FirstCertificate p076 (5 : ℚ) (fun n x => (((((n : ℚ) + 1) + (1 : ℚ)) ^ 2) * x + (((2 : ℚ) * ((n : ℚ) + 1)) + (1 : ℚ))) / (((n : ℚ) + 1) ^ 2)) := by
  apply linear_certificate p076 (5 : ℚ) (fun n : ℕ => (((n : ℚ) + 1) ^ 2)) (fun n : ℕ => ((((n : ℚ) + 1) + (1 : ℚ)) ^ 2)) (fun n : ℕ => (((2 : ℚ) * ((n : ℚ) + 1)) + (1 : ℚ)))
  · norm_num [p076]
  · intro n; positivity
  · intro n
    simp only [p076, Nat.cast_add, Nat.cast_one, pow_succ, pow_add] at *
    ring
theorem p076_valid : FirstCertificate p076 (5 : ℚ) (fun n x => (((((n : ℚ) + 1) + (1 : ℚ)) ^ 2) * x + (((2 : ℚ) * ((n : ℚ) + 1)) + (1 : ℚ))) / (((n : ℚ) + 1) ^ 2)) := p076_base_valid
theorem p076_unique (a : ℕ → ℚ) (ha : FirstCertificate a (5 : ℚ) (fun n x => (((((n : ℚ) + 1) + (1 : ℚ)) ^ 2) * x + (((2 : ℚ) * ((n : ℚ) + 1)) + (1 : ℚ))) / (((n : ℚ) + 1) ^ 2))) :
    ∀ n, a n = p076 n := first_unique p076_valid ha
#print axioms p076_valid
#print axioms p076_unique

def p077 (n : ℕ) : ℚ := (((3 : ℚ) * ((n : ℚ) + 1) * (((n : ℚ) + 1) + (2 : ℚ))) + (-1 : ℚ))
theorem p077_base_valid : FirstCertificate p077 (8 : ℚ) (fun n x => (((((n : ℚ) + 1) + (1 : ℚ)) * (((n : ℚ) + 1) + (3 : ℚ))) * x + (((2 : ℚ) * ((n : ℚ) + 1)) + (3 : ℚ))) / (((n : ℚ) + 1) * (((n : ℚ) + 1) + (2 : ℚ)))) := by
  apply linear_certificate p077 (8 : ℚ) (fun n : ℕ => (((n : ℚ) + 1) * (((n : ℚ) + 1) + (2 : ℚ)))) (fun n : ℕ => ((((n : ℚ) + 1) + (1 : ℚ)) * (((n : ℚ) + 1) + (3 : ℚ)))) (fun n : ℕ => (((2 : ℚ) * ((n : ℚ) + 1)) + (3 : ℚ)))
  · norm_num [p077]
  · intro n; positivity
  · intro n
    simp only [p077, Nat.cast_add, Nat.cast_one, pow_succ, pow_add] at *
    ring
theorem p077_valid : FirstCertificate p077 (8 : ℚ) (fun n x => (((((n : ℚ) + 1) + (1 : ℚ)) * (((n : ℚ) + 1) + (3 : ℚ))) * x + (((2 : ℚ) * ((n : ℚ) + 1)) + (3 : ℚ))) / (((n : ℚ) + 1) * (((n : ℚ) + 1) + (2 : ℚ)))) := p077_base_valid
theorem p077_unique (a : ℕ → ℚ) (ha : FirstCertificate a (8 : ℚ) (fun n x => (((((n : ℚ) + 1) + (1 : ℚ)) * (((n : ℚ) + 1) + (3 : ℚ))) * x + (((2 : ℚ) * ((n : ℚ) + 1)) + (3 : ℚ))) / (((n : ℚ) + 1) * (((n : ℚ) + 1) + (2 : ℚ))))) :
    ∀ n, a n = p077 n := first_unique p077_valid ha
#print axioms p077_valid
#print axioms p077_unique

def p078 (n : ℕ) : ℚ := ((((8 : ℚ) * ((2 : ℚ) ^ n)) + (1 : ℚ)) / (((2 : ℚ) * ((n : ℚ) + 1)) + (1 : ℚ)))
theorem p078_base_valid : FirstCertificate p078 (3 : ℚ) (fun n x => (((2 : ℚ) * (((2 : ℚ) * ((n : ℚ) + 1)) + (1 : ℚ))) * x + (-1 : ℚ)) / (((2 : ℚ) * ((n : ℚ) + 1)) + (3 : ℚ))) := by
  apply linear_certificate p078 (3 : ℚ) (fun n : ℕ => (((2 : ℚ) * ((n : ℚ) + 1)) + (3 : ℚ))) (fun n : ℕ => ((2 : ℚ) * (((2 : ℚ) * ((n : ℚ) + 1)) + (1 : ℚ)))) (fun n : ℕ => (-1 : ℚ))
  · norm_num [p078]
  · intro n; positivity
  · intro n
    have hd0 : (((2 : ℚ) * ((n : ℚ) + 1)) + (1 : ℚ)) ≠ 0 := by positivity
    have he0 : (((2 : ℚ) * (((n + 1) : ℚ) + 1)) + (1 : ℚ)) ≠ 0 := by positivity
    simp only [p078, Nat.cast_add, Nat.cast_one, pow_succ, pow_add] at *
    field_simp [hd0, he0] <;> ring
theorem p078_valid : FirstCertificate p078 (3 : ℚ) (fun n x => (((2 : ℚ) * (((2 : ℚ) * ((n : ℚ) + 1)) + (1 : ℚ))) * x + (-1 : ℚ)) / (((2 : ℚ) * ((n : ℚ) + 1)) + (3 : ℚ))) := p078_base_valid
theorem p078_unique (a : ℕ → ℚ) (ha : FirstCertificate a (3 : ℚ) (fun n x => (((2 : ℚ) * (((2 : ℚ) * ((n : ℚ) + 1)) + (1 : ℚ))) * x + (-1 : ℚ)) / (((2 : ℚ) * ((n : ℚ) + 1)) + (3 : ℚ)))) :
    ∀ n, a n = p078 n := first_unique p078_valid ha
#print axioms p078_valid
#print axioms p078_unique

def p111 (n : ℕ) : ℚ := (((n : ℚ) + 1) * (((3 : ℚ) ^ n) + (1 : ℚ)))
theorem p111_base_valid : FirstCertificate p111 (2 : ℚ) (fun n x => (((3 : ℚ) * (((n : ℚ) + 1) + (1 : ℚ))) * x + ((-2 : ℚ) * ((n : ℚ) + 1) * (((n : ℚ) + 1) + (1 : ℚ)))) / ((n : ℚ) + 1)) := by
  apply linear_certificate p111 (2 : ℚ) (fun n : ℕ => ((n : ℚ) + 1)) (fun n : ℕ => ((3 : ℚ) * (((n : ℚ) + 1) + (1 : ℚ)))) (fun n : ℕ => ((-2 : ℚ) * ((n : ℚ) + 1) * (((n : ℚ) + 1) + (1 : ℚ))))
  · norm_num [p111]
  · intro n; positivity
  · intro n
    simp only [p111, Nat.cast_add, Nat.cast_one, pow_succ, pow_add] at *
    ring
theorem p111_valid : FirstCertificate p111 (2 : ℚ) (fun n x => (((3 : ℚ) * (((n : ℚ) + 1) + (1 : ℚ))) * x + ((-2 : ℚ) * ((n : ℚ) + 1) * (((n : ℚ) + 1) + (1 : ℚ)))) / ((n : ℚ) + 1)) := p111_base_valid
theorem p111_unique (a : ℕ → ℚ) (ha : FirstCertificate a (2 : ℚ) (fun n x => (((3 : ℚ) * (((n : ℚ) + 1) + (1 : ℚ))) * x + ((-2 : ℚ) * ((n : ℚ) + 1) * (((n : ℚ) + 1) + (1 : ℚ)))) / ((n : ℚ) + 1))) :
    ∀ n, a n = p111 n := first_unique p111_valid ha
#print axioms p111_valid
#print axioms p111_unique

def p080 (n : ℕ) : ℚ := ((((8 : ℚ) * ((2 : ℚ) ^ n)) + (1 : ℚ)) / (((n : ℚ) + 1) + (1 : ℚ)))
theorem p080_base_valid : FirstCertificate p080 ((9 : ℚ) / 2) (fun n x => (((2 : ℚ) * (((n : ℚ) + 1) + (1 : ℚ))) * x + (-1 : ℚ)) / (((n : ℚ) + 1) + (2 : ℚ))) := by
  apply linear_certificate p080 ((9 : ℚ) / 2) (fun n : ℕ => (((n : ℚ) + 1) + (2 : ℚ))) (fun n : ℕ => ((2 : ℚ) * (((n : ℚ) + 1) + (1 : ℚ)))) (fun n : ℕ => (-1 : ℚ))
  · norm_num [p080]
  · intro n; positivity
  · intro n
    have hd0 : (((n : ℚ) + 1) + (1 : ℚ)) ≠ 0 := by positivity
    have he0 : ((((n + 1) : ℚ) + 1) + (1 : ℚ)) ≠ 0 := by positivity
    simp only [p080, Nat.cast_add, Nat.cast_one, pow_succ, pow_add] at *
    field_simp [hd0, he0] <;> ring
theorem p080_valid : FirstCertificate p080 ((9 : ℚ) / 2) (fun n x => (((2 : ℚ) * (((n : ℚ) + 1) + (1 : ℚ))) * x + (-1 : ℚ)) / (((n : ℚ) + 1) + (2 : ℚ))) := p080_base_valid
theorem p080_unique (a : ℕ → ℚ) (ha : FirstCertificate a ((9 : ℚ) / 2) (fun n x => (((2 : ℚ) * (((n : ℚ) + 1) + (1 : ℚ))) * x + (-1 : ℚ)) / (((n : ℚ) + 1) + (2 : ℚ)))) :
    ∀ n, a n = p080 n := first_unique p080_valid ha
#print axioms p080_valid
#print axioms p080_unique

def p113 (n : ℕ) : ℚ := ((((3 : ℚ) ^ n) + (1 : ℚ)) / (((n : ℚ) + 1) * (((n : ℚ) + 1) + (1 : ℚ))))
theorem p113_base_valid : FirstCertificate p113 (1 : ℚ) (fun n x => (((3 : ℚ) * ((n : ℚ) + 1) * (((n : ℚ) + 1) + (1 : ℚ))) * x + (-2 : ℚ)) / ((((n : ℚ) + 1) + (1 : ℚ)) * (((n : ℚ) + 1) + (2 : ℚ)))) := by
  apply linear_certificate p113 (1 : ℚ) (fun n : ℕ => ((((n : ℚ) + 1) + (1 : ℚ)) * (((n : ℚ) + 1) + (2 : ℚ)))) (fun n : ℕ => ((3 : ℚ) * ((n : ℚ) + 1) * (((n : ℚ) + 1) + (1 : ℚ)))) (fun n : ℕ => (-2 : ℚ))
  · norm_num [p113]
  · intro n; positivity
  · intro n
    have hd0 : (((n : ℚ) + 1) * (((n : ℚ) + 1) + (1 : ℚ))) ≠ 0 := by positivity
    have he0 : ((((n + 1) : ℚ) + 1) * ((((n + 1) : ℚ) + 1) + (1 : ℚ))) ≠ 0 := by positivity
    simp only [p113, Nat.cast_add, Nat.cast_one, pow_succ, pow_add] at *
    field_simp [hd0, he0] <;> ring
theorem p113_valid : FirstCertificate p113 (1 : ℚ) (fun n x => (((3 : ℚ) * ((n : ℚ) + 1) * (((n : ℚ) + 1) + (1 : ℚ))) * x + (-2 : ℚ)) / ((((n : ℚ) + 1) + (1 : ℚ)) * (((n : ℚ) + 1) + (2 : ℚ)))) := p113_base_valid
theorem p113_unique (a : ℕ → ℚ) (ha : FirstCertificate a (1 : ℚ) (fun n x => (((3 : ℚ) * ((n : ℚ) + 1) * (((n : ℚ) + 1) + (1 : ℚ))) * x + (-2 : ℚ)) / ((((n : ℚ) + 1) + (1 : ℚ)) * (((n : ℚ) + 1) + (2 : ℚ))))) :
    ∀ n, a n = p113 n := first_unique p113_valid ha
#print axioms p113_valid
#print axioms p113_unique

def p082 (n : ℕ) : ℚ := ((((8 : ℚ) * ((2 : ℚ) ^ n)) + (1 : ℚ)) / (((n : ℚ) + 1) * (((n : ℚ) + 1) + (2 : ℚ))))
theorem p082_base_valid : FirstCertificate p082 (3 : ℚ) (fun n x => (((2 : ℚ) * ((n : ℚ) + 1) * (((n : ℚ) + 1) + (2 : ℚ))) * x + (-1 : ℚ)) / ((((n : ℚ) + 1) + (1 : ℚ)) * (((n : ℚ) + 1) + (3 : ℚ)))) := by
  apply linear_certificate p082 (3 : ℚ) (fun n : ℕ => ((((n : ℚ) + 1) + (1 : ℚ)) * (((n : ℚ) + 1) + (3 : ℚ)))) (fun n : ℕ => ((2 : ℚ) * ((n : ℚ) + 1) * (((n : ℚ) + 1) + (2 : ℚ)))) (fun n : ℕ => (-1 : ℚ))
  · norm_num [p082]
  · intro n; positivity
  · intro n
    have hd0 : (((n : ℚ) + 1) * (((n : ℚ) + 1) + (2 : ℚ))) ≠ 0 := by positivity
    have he0 : ((((n + 1) : ℚ) + 1) * ((((n + 1) : ℚ) + 1) + (2 : ℚ))) ≠ 0 := by positivity
    simp only [p082, Nat.cast_add, Nat.cast_one, pow_succ, pow_add] at *
    field_simp [hd0, he0] <;> ring
theorem p082_valid : FirstCertificate p082 (3 : ℚ) (fun n x => (((2 : ℚ) * ((n : ℚ) + 1) * (((n : ℚ) + 1) + (2 : ℚ))) * x + (-1 : ℚ)) / ((((n : ℚ) + 1) + (1 : ℚ)) * (((n : ℚ) + 1) + (3 : ℚ)))) := p082_base_valid
theorem p082_unique (a : ℕ → ℚ) (ha : FirstCertificate a (3 : ℚ) (fun n x => (((2 : ℚ) * ((n : ℚ) + 1) * (((n : ℚ) + 1) + (2 : ℚ))) * x + (-1 : ℚ)) / ((((n : ℚ) + 1) + (1 : ℚ)) * (((n : ℚ) + 1) + (3 : ℚ))))) :
    ∀ n, a n = p082 n := first_unique p082_valid ha
#print axioms p082_valid
#print axioms p082_unique

def p117 (n : ℕ) : ℚ := ((((3 : ℚ) ^ n) + (1 : ℚ)) / (((n : ℚ) + 1) ^ 2))
theorem p117_base_valid : FirstCertificate p117 (2 : ℚ) (fun n x => (((3 : ℚ) * (((n : ℚ) + 1) ^ 2)) * x + (-2 : ℚ)) / ((((n : ℚ) + 1) + (1 : ℚ)) ^ 2)) := by
  apply linear_certificate p117 (2 : ℚ) (fun n : ℕ => ((((n : ℚ) + 1) + (1 : ℚ)) ^ 2)) (fun n : ℕ => ((3 : ℚ) * (((n : ℚ) + 1) ^ 2))) (fun n : ℕ => (-2 : ℚ))
  · norm_num [p117]
  · intro n; positivity
  · intro n
    have hd0 : (((n : ℚ) + 1) ^ 2) ≠ 0 := by positivity
    have he0 : ((((n + 1) : ℚ) + 1) ^ 2) ≠ 0 := by positivity
    simp only [p117, Nat.cast_add, Nat.cast_one, pow_succ, pow_add] at *
    field_simp [hd0, he0] <;> ring
theorem p117_valid : FirstCertificate p117 (2 : ℚ) (fun n x => (((3 : ℚ) * (((n : ℚ) + 1) ^ 2)) * x + (-2 : ℚ)) / ((((n : ℚ) + 1) + (1 : ℚ)) ^ 2)) := p117_base_valid
theorem p117_unique (a : ℕ → ℚ) (ha : FirstCertificate a (2 : ℚ) (fun n x => (((3 : ℚ) * (((n : ℚ) + 1) ^ 2)) * x + (-2 : ℚ)) / ((((n : ℚ) + 1) + (1 : ℚ)) ^ 2))) :
    ∀ n, a n = p117 n := first_unique p117_valid ha
#print axioms p117_valid
#print axioms p117_unique

def p185 (n : ℕ) : ℚ := (((3 : ℚ) ^ n) + ((-1 : ℚ) ^ n))
theorem p185_valid : SecondCertificate p185 (2 : ℚ) (2 : ℚ) (2 : ℚ) (3 : ℚ) := by
  constructor
  · norm_num [p185]
  · norm_num [p185]
  · intro n
    simp only [p185, pow_succ, pow_add] <;> ring
theorem p185_unique (a : ℕ → ℚ) (ha : SecondCertificate a (2 : ℚ) (2 : ℚ) (2 : ℚ) (3 : ℚ)) :
    ∀ n, a n = p185 n := second_unique p185_valid ha
#print axioms p185_valid
#print axioms p185_unique

def p173 (n : ℕ) : ℚ := (((2 : ℚ) ^ n) + ((1 : ℚ) ^ n))
theorem p173_valid : SecondCertificate p173 (2 : ℚ) (3 : ℚ) (3 : ℚ) (-2 : ℚ) := by
  constructor
  · norm_num [p173]
  · norm_num [p173]
  · intro n
    simp only [p173, pow_succ, pow_add] <;> ring
theorem p173_unique (a : ℕ → ℚ) (ha : SecondCertificate a (2 : ℚ) (3 : ℚ) (3 : ℚ) (-2 : ℚ)) :
    ∀ n, a n = p173 n := second_unique p173_valid ha
#print axioms p173_valid
#print axioms p173_unique

def p239 (n : ℕ) : ℚ := (((3 : ℚ) ^ n) + ((1 : ℚ) ^ n))
theorem p239_valid : SecondCertificate p239 (2 : ℚ) (4 : ℚ) (4 : ℚ) (-3 : ℚ) := by
  constructor
  · norm_num [p239]
  · norm_num [p239]
  · intro n
    simp only [p239, pow_succ, pow_add] <;> ring
theorem p239_unique (a : ℕ → ℚ) (ha : SecondCertificate a (2 : ℚ) (4 : ℚ) (4 : ℚ) (-3 : ℚ)) :
    ∀ n, a n = p239 n := second_unique p239_valid ha
#print axioms p239_valid
#print axioms p239_unique

def p243 (n : ℕ) : ℚ := (((2 : ℚ) ^ n) + ((-2 : ℚ) ^ n))
theorem p243_valid : SecondCertificate p243 (2 : ℚ) (0 : ℚ) (0 : ℚ) (4 : ℚ) := by
  constructor
  · norm_num [p243]
  · norm_num [p243]
  · intro n
    simp only [p243, pow_succ, pow_add] <;> ring
theorem p243_unique (a : ℕ → ℚ) (ha : SecondCertificate a (2 : ℚ) (0 : ℚ) (0 : ℚ) (4 : ℚ)) :
    ∀ n, a n = p243 n := second_unique p243_valid ha
#print axioms p243_valid
#print axioms p243_unique

def p086 (n : ℕ) : ℚ := (((2 : ℚ) ^ n) + ((3 : ℚ) ^ n))
theorem p086_valid : SecondCertificate p086 (2 : ℚ) (5 : ℚ) (5 : ℚ) (-6 : ℚ) := by
  constructor
  · norm_num [p086]
  · norm_num [p086]
  · intro n
    simp only [p086, pow_succ, pow_add] <;> ring
theorem p086_unique (a : ℕ → ℚ) (ha : SecondCertificate a (2 : ℚ) (5 : ℚ) (5 : ℚ) (-6 : ℚ)) :
    ∀ n, a n = p086 n := second_unique p086_valid ha
#print axioms p086_valid
#print axioms p086_unique

def p089 (n : ℕ) : ℚ := ((2 : ℚ) * ((2 : ℚ) ^ (n * (n + 2))))
theorem p089_base_valid : FirstCertificate p089 (2 : ℚ) (fun n x => (((2 : ℚ) ^ ((2 * (n + 1)) + 1)) * x + (0 : ℚ)) / (1 : ℚ)) := by
  apply linear_certificate p089 (2 : ℚ) (fun n : ℕ => (1 : ℚ)) (fun n : ℕ => ((2 : ℚ) ^ ((2 * (n + 1)) + 1))) (fun n : ℕ => (0 : ℚ))
  · norm_num [p089]
  · intro n; positivity
  · intro n
    have he : (n + 1) * (n + 3) = n * (n + 2) + (2 * (n + 1) + 1) := by ring
    simp only [p089, Nat.add_assoc]
    rw [he]
    simp only [pow_add] <;> ring
theorem p089_valid : FirstCertificate p089 (2 : ℚ) (fun n x => (((2 : ℚ) ^ ((2 * (n + 1)) + 1)) * x + (0 : ℚ)) / (1 : ℚ)) := p089_base_valid
theorem p089_unique (a : ℕ → ℚ) (ha : FirstCertificate a (2 : ℚ) (fun n x => (((2 : ℚ) ^ ((2 * (n + 1)) + 1)) * x + (0 : ℚ)) / (1 : ℚ))) :
    ∀ n, a n = p089 n := first_unique p089_valid ha
#print axioms p089_valid
#print axioms p089_unique

def p037 (n : ℕ) : ℚ := ((3 : ℚ) ^ ((n + 1).choose 2))
theorem p037_base_valid : FirstCertificate p037 (1 : ℚ) (fun n x => (((3 : ℚ) ^ (n + 1)) * x + (0 : ℚ)) / (1 : ℚ)) := by
  apply linear_certificate p037 (1 : ℚ) (fun n : ℕ => (1 : ℚ)) (fun n : ℕ => ((3 : ℚ) ^ (n + 1))) (fun n : ℕ => (0 : ℚ))
  · norm_num [p037]
  · intro n; positivity
  · intro n
    simp only [p037, Nat.choose_succ_succ, Nat.choose_one_right, Nat.choose_zero_right, pow_succ, pow_add] <;> ring
theorem p037_valid : FirstCertificate p037 (1 : ℚ) (fun n x => (((3 : ℚ) ^ (n + 1)) * x + (0 : ℚ)) / (1 : ℚ)) := p037_base_valid
theorem p037_unique (a : ℕ → ℚ) (ha : FirstCertificate a (1 : ℚ) (fun n x => (((3 : ℚ) ^ (n + 1)) * x + (0 : ℚ)) / (1 : ℚ))) :
    ∀ n, a n = p037 n := first_unique p037_valid ha
#print axioms p037_valid
#print axioms p037_unique

def p091 (n : ℕ) : ℚ := ((2 : ℚ) * ((2 : ℚ) ^ ((n + 2)).choose 3))
theorem p091_base_valid : FirstCertificate p091 (2 : ℚ) (fun n x => (((2 : ℚ) ^ ((n + 2)).choose 2) * x + (0 : ℚ)) / (1 : ℚ)) := by
  apply linear_certificate p091 (2 : ℚ) (fun n : ℕ => (1 : ℚ)) (fun n : ℕ => ((2 : ℚ) ^ ((n + 2)).choose 2)) (fun n : ℕ => (0 : ℚ))
  · norm_num [p091]
  · intro n; positivity
  · intro n
    simp only [p091, Nat.choose_succ_succ, Nat.choose_one_right, Nat.choose_zero_right, pow_succ, pow_add] <;> ring
theorem p091_valid : FirstCertificate p091 (2 : ℚ) (fun n x => (((2 : ℚ) ^ ((n + 2)).choose 2) * x + (0 : ℚ)) / (1 : ℚ)) := p091_base_valid
theorem p091_unique (a : ℕ → ℚ) (ha : FirstCertificate a (2 : ℚ) (fun n x => (((2 : ℚ) ^ ((n + 2)).choose 2) * x + (0 : ℚ)) / (1 : ℚ))) :
    ∀ n, a n = p091 n := first_unique p091_valid ha
#print axioms p091_valid
#print axioms p091_unique

def p116 (n : ℕ) : ℚ := ((3 : ℚ) ^ (n * (n + 2)))
theorem p116_base_valid : FirstCertificate p116 (1 : ℚ) (fun n x => (((3 : ℚ) ^ ((2 * (n + 1)) + 1)) * x + (0 : ℚ)) / (1 : ℚ)) := by
  apply linear_certificate p116 (1 : ℚ) (fun n : ℕ => (1 : ℚ)) (fun n : ℕ => ((3 : ℚ) ^ ((2 * (n + 1)) + 1))) (fun n : ℕ => (0 : ℚ))
  · norm_num [p116]
  · intro n; positivity
  · intro n
    have he : (n + 1) * (n + 3) = n * (n + 2) + (2 * (n + 1) + 1) := by ring
    simp only [p116, Nat.add_assoc]
    rw [he]
    simp only [pow_add] <;> ring
theorem p116_valid : FirstCertificate p116 (1 : ℚ) (fun n x => (((3 : ℚ) ^ ((2 * (n + 1)) + 1)) * x + (0 : ℚ)) / (1 : ℚ)) := p116_base_valid
theorem p116_unique (a : ℕ → ℚ) (ha : FirstCertificate a (1 : ℚ) (fun n x => (((3 : ℚ) ^ ((2 * (n + 1)) + 1)) * x + (0 : ℚ)) / (1 : ℚ))) :
    ∀ n, a n = p116 n := first_unique p116_valid ha
#print axioms p116_valid
#print axioms p116_unique

def p090 (n : ℕ) : ℚ := ((2 : ℚ) * ((2 : ℚ) ^ ((n + 1).choose 2)))
theorem p090_base_valid : FirstCertificate p090 (2 : ℚ) (fun n x => (((2 : ℚ) ^ (n + 1)) * x + (0 : ℚ)) / (1 : ℚ)) := by
  apply linear_certificate p090 (2 : ℚ) (fun n : ℕ => (1 : ℚ)) (fun n : ℕ => ((2 : ℚ) ^ (n + 1))) (fun n : ℕ => (0 : ℚ))
  · norm_num [p090]
  · intro n; positivity
  · intro n
    simp only [p090, Nat.choose_succ_succ, Nat.choose_one_right, Nat.choose_zero_right, pow_succ, pow_add] <;> ring
theorem p090_valid : FirstCertificate p090 (2 : ℚ) (fun n x => (((2 : ℚ) ^ (n + 1)) * x + (0 : ℚ)) / (1 : ℚ)) := p090_base_valid
theorem p090_unique (a : ℕ → ℚ) (ha : FirstCertificate a (2 : ℚ) (fun n x => (((2 : ℚ) ^ (n + 1)) * x + (0 : ℚ)) / (1 : ℚ))) :
    ∀ n, a n = p090 n := first_unique p090_valid ha
#print axioms p090_valid
#print axioms p090_unique

def p112 (n : ℕ) : ℚ := ((3 : ℚ) ^ ((n + 2)).choose 3)
theorem p112_base_valid : FirstCertificate p112 (1 : ℚ) (fun n x => (((3 : ℚ) ^ ((n + 2)).choose 2) * x + (0 : ℚ)) / (1 : ℚ)) := by
  apply linear_certificate p112 (1 : ℚ) (fun n : ℕ => (1 : ℚ)) (fun n : ℕ => ((3 : ℚ) ^ ((n + 2)).choose 2)) (fun n : ℕ => (0 : ℚ))
  · norm_num [p112]
  · intro n; positivity
  · intro n
    simp only [p112, Nat.choose_succ_succ, Nat.choose_one_right, Nat.choose_zero_right, pow_succ, pow_add] <;> ring
theorem p112_valid : FirstCertificate p112 (1 : ℚ) (fun n x => (((3 : ℚ) ^ ((n + 2)).choose 2) * x + (0 : ℚ)) / (1 : ℚ)) := p112_base_valid
theorem p112_unique (a : ℕ → ℚ) (ha : FirstCertificate a (1 : ℚ) (fun n x => (((3 : ℚ) ^ ((n + 2)).choose 2) * x + (0 : ℚ)) / (1 : ℚ))) :
    ∀ n, a n = p112 n := first_unique p112_valid ha
#print axioms p112_valid
#print axioms p112_unique

def p045 (n : ℕ) : ℚ := ((1 : ℚ) / (((3 : ℚ) * ((2 : ℚ) ^ n)) + (2 : ℚ)))
def p045_base (n : ℕ) : ℚ := (((3 : ℚ) * ((2 : ℚ) ^ n)) + (2 : ℚ))
theorem p045_base_valid : FirstCertificate p045_base (5 : ℚ) (fun n x => ((2 : ℚ) * x + (-2 : ℚ)) / (1 : ℚ)) := by
  apply linear_certificate p045_base (5 : ℚ) (fun n : ℕ => (1 : ℚ)) (fun n : ℕ => (2 : ℚ)) (fun n : ℕ => (-2 : ℚ))
  · norm_num [p045_base]
  · intro n; positivity
  · intro n
    simp only [p045_base, Nat.cast_add, Nat.cast_one, pow_succ, pow_add] at *
    ring
theorem p045_positive (n : ℕ) : 0 < p045_base n := by
  unfold p045_base
  positivity
theorem p045_valid : FirstCertificate p045 ((1 : ℚ) / 5) (fun n x => (1 : ℚ) * x / ((2 : ℚ) + (-2 : ℚ) * x)) := by
  have h := reciprocal_certificate p045_base_valid p045_positive (by intro n; positivity)
  have heq : p045 = (fun n => 1 / p045_base n) := by
    funext n
    simp [p045, p045_base, div_eq_mul_inv] <;> ring
  rw [heq]
  convert h.1 using 1 <;> norm_num
theorem p045_domain : (∀ n : ℕ, (2 : ℚ) + (-2 : ℚ) * p045 n ≠ 0) ∧ (∀ n, p045 n ≠ 0) := by
  have h := reciprocal_certificate p045_base_valid p045_positive (by intro n; positivity)
  simpa [p045, p045_base, div_eq_mul_inv] using h.2
#print axioms p045_domain
theorem p045_unique (a : ℕ → ℚ) (ha : FirstCertificate a ((1 : ℚ) / 5) (fun n x => (1 : ℚ) * x / ((2 : ℚ) + (-2 : ℚ) * x))) :
    ∀ n, a n = p045 n := first_unique p045_valid ha
#print axioms p045_valid
#print axioms p045_unique

def p041 (n : ℕ) : ℚ := ((1 : ℚ) / (((4 : ℚ) * ((3 : ℚ) ^ n)) + (1 : ℚ)))
def p041_base (n : ℕ) : ℚ := (((4 : ℚ) * ((3 : ℚ) ^ n)) + (1 : ℚ))
theorem p041_base_valid : FirstCertificate p041_base (5 : ℚ) (fun n x => ((3 : ℚ) * x + (-2 : ℚ)) / (1 : ℚ)) := by
  apply linear_certificate p041_base (5 : ℚ) (fun n : ℕ => (1 : ℚ)) (fun n : ℕ => (3 : ℚ)) (fun n : ℕ => (-2 : ℚ))
  · norm_num [p041_base]
  · intro n; positivity
  · intro n
    simp only [p041_base, Nat.cast_add, Nat.cast_one, pow_succ, pow_add] at *
    ring
theorem p041_positive (n : ℕ) : 0 < p041_base n := by
  unfold p041_base
  positivity
theorem p041_valid : FirstCertificate p041 ((1 : ℚ) / 5) (fun n x => (1 : ℚ) * x / ((3 : ℚ) + (-2 : ℚ) * x)) := by
  have h := reciprocal_certificate p041_base_valid p041_positive (by intro n; positivity)
  have heq : p041 = (fun n => 1 / p041_base n) := by
    funext n
    simp [p041, p041_base, div_eq_mul_inv] <;> ring
  rw [heq]
  convert h.1 using 1 <;> norm_num
theorem p041_domain : (∀ n : ℕ, (3 : ℚ) + (-2 : ℚ) * p041 n ≠ 0) ∧ (∀ n, p041 n ≠ 0) := by
  have h := reciprocal_certificate p041_base_valid p041_positive (by intro n; positivity)
  simpa [p041, p041_base, div_eq_mul_inv] using h.2
#print axioms p041_domain
theorem p041_unique (a : ℕ → ℚ) (ha : FirstCertificate a ((1 : ℚ) / 5) (fun n x => (1 : ℚ) * x / ((3 : ℚ) + (-2 : ℚ) * x))) :
    ∀ n, a n = p041 n := first_unique p041_valid ha
#print axioms p041_valid
#print axioms p041_unique

def p093 (n : ℕ) : ℚ := ((1 : ℚ) / (((2 : ℚ) * ((2 : ℚ) ^ n)) + (3 : ℚ)))
def p093_base (n : ℕ) : ℚ := (((2 : ℚ) * ((2 : ℚ) ^ n)) + (3 : ℚ))
theorem p093_base_valid : FirstCertificate p093_base (5 : ℚ) (fun n x => ((2 : ℚ) * x + (-3 : ℚ)) / (1 : ℚ)) := by
  apply linear_certificate p093_base (5 : ℚ) (fun n : ℕ => (1 : ℚ)) (fun n : ℕ => (2 : ℚ)) (fun n : ℕ => (-3 : ℚ))
  · norm_num [p093_base]
  · intro n; positivity
  · intro n
    simp only [p093_base, Nat.cast_add, Nat.cast_one, pow_succ, pow_add] at *
    ring
theorem p093_positive (n : ℕ) : 0 < p093_base n := by
  unfold p093_base
  positivity
theorem p093_valid : FirstCertificate p093 ((1 : ℚ) / 5) (fun n x => (1 : ℚ) * x / ((2 : ℚ) + (-3 : ℚ) * x)) := by
  have h := reciprocal_certificate p093_base_valid p093_positive (by intro n; positivity)
  have heq : p093 = (fun n => 1 / p093_base n) := by
    funext n
    simp [p093, p093_base, div_eq_mul_inv] <;> ring
  rw [heq]
  convert h.1 using 1 <;> norm_num
theorem p093_domain : (∀ n : ℕ, (2 : ℚ) + (-3 : ℚ) * p093 n ≠ 0) ∧ (∀ n, p093 n ≠ 0) := by
  have h := reciprocal_certificate p093_base_valid p093_positive (by intro n; positivity)
  simpa [p093, p093_base, div_eq_mul_inv] using h.2
#print axioms p093_domain
theorem p093_unique (a : ℕ → ℚ) (ha : FirstCertificate a ((1 : ℚ) / 5) (fun n x => (1 : ℚ) * x / ((2 : ℚ) + (-3 : ℚ) * x))) :
    ∀ n, a n = p093 n := first_unique p093_valid ha
#print axioms p093_valid
#print axioms p093_unique

def p042 (n : ℕ) : ℚ := ((1 : ℚ) / (((3 : ℚ) ^ n) + (2 : ℚ)))
def p042_base (n : ℕ) : ℚ := (((3 : ℚ) ^ n) + (2 : ℚ))
theorem p042_base_valid : FirstCertificate p042_base (3 : ℚ) (fun n x => ((3 : ℚ) * x + (-4 : ℚ)) / (1 : ℚ)) := by
  apply linear_certificate p042_base (3 : ℚ) (fun n : ℕ => (1 : ℚ)) (fun n : ℕ => (3 : ℚ)) (fun n : ℕ => (-4 : ℚ))
  · norm_num [p042_base]
  · intro n; positivity
  · intro n
    simp only [p042_base, Nat.cast_add, Nat.cast_one, pow_succ, pow_add] at *
    ring
theorem p042_positive (n : ℕ) : 0 < p042_base n := by
  unfold p042_base
  positivity
theorem p042_valid : FirstCertificate p042 ((1 : ℚ) / 3) (fun n x => (1 : ℚ) * x / ((3 : ℚ) + (-4 : ℚ) * x)) := by
  have h := reciprocal_certificate p042_base_valid p042_positive (by intro n; positivity)
  have heq : p042 = (fun n => 1 / p042_base n) := by
    funext n
    simp [p042, p042_base, div_eq_mul_inv] <;> ring
  rw [heq]
  convert h.1 using 1 <;> norm_num
theorem p042_domain : (∀ n : ℕ, (3 : ℚ) + (-4 : ℚ) * p042 n ≠ 0) ∧ (∀ n, p042 n ≠ 0) := by
  have h := reciprocal_certificate p042_base_valid p042_positive (by intro n; positivity)
  simpa [p042, p042_base, div_eq_mul_inv] using h.2
#print axioms p042_domain
theorem p042_unique (a : ℕ → ℚ) (ha : FirstCertificate a ((1 : ℚ) / 3) (fun n x => (1 : ℚ) * x / ((3 : ℚ) + (-4 : ℚ) * x))) :
    ∀ n, a n = p042 n := first_unique p042_valid ha
#print axioms p042_valid
#print axioms p042_unique

def p095 (n : ℕ) : ℚ := ((1 : ℚ) / (((2 : ℚ) * ((3 : ℚ) ^ n)) + (3 : ℚ)))
def p095_base (n : ℕ) : ℚ := (((2 : ℚ) * ((3 : ℚ) ^ n)) + (3 : ℚ))
theorem p095_base_valid : FirstCertificate p095_base (5 : ℚ) (fun n x => ((3 : ℚ) * x + (-6 : ℚ)) / (1 : ℚ)) := by
  apply linear_certificate p095_base (5 : ℚ) (fun n : ℕ => (1 : ℚ)) (fun n : ℕ => (3 : ℚ)) (fun n : ℕ => (-6 : ℚ))
  · norm_num [p095_base]
  · intro n; positivity
  · intro n
    simp only [p095_base, Nat.cast_add, Nat.cast_one, pow_succ, pow_add] at *
    ring
theorem p095_positive (n : ℕ) : 0 < p095_base n := by
  unfold p095_base
  positivity
theorem p095_valid : FirstCertificate p095 ((1 : ℚ) / 5) (fun n x => (1 : ℚ) * x / ((3 : ℚ) + (-6 : ℚ) * x)) := by
  have h := reciprocal_certificate p095_base_valid p095_positive (by intro n; positivity)
  have heq : p095 = (fun n => 1 / p095_base n) := by
    funext n
    simp [p095, p095_base, div_eq_mul_inv] <;> ring
  rw [heq]
  convert h.1 using 1 <;> norm_num
theorem p095_domain : (∀ n : ℕ, (3 : ℚ) + (-6 : ℚ) * p095 n ≠ 0) ∧ (∀ n, p095 n ≠ 0) := by
  have h := reciprocal_certificate p095_base_valid p095_positive (by intro n; positivity)
  simpa [p095, p095_base, div_eq_mul_inv] using h.2
#print axioms p095_domain
theorem p095_unique (a : ℕ → ℚ) (ha : FirstCertificate a ((1 : ℚ) / 5) (fun n x => (1 : ℚ) * x / ((3 : ℚ) + (-6 : ℚ) * x))) :
    ∀ n, a n = p095 n := first_unique p095_valid ha
#print axioms p095_valid
#print axioms p095_unique

def p096 (n : ℕ) : ℚ := ((1 : ℚ) / (((n : ℚ) + 1) * (((3 : ℚ) * ((2 : ℚ) ^ n)) + (2 : ℚ))))
def p096_base (n : ℕ) : ℚ := (((n : ℚ) + 1) * (((3 : ℚ) * ((2 : ℚ) ^ n)) + (2 : ℚ)))
theorem p096_base_valid : FirstCertificate p096_base (5 : ℚ) (fun n x => (((2 : ℚ) * (((n : ℚ) + 1) + (1 : ℚ))) * x + ((-2 : ℚ) * ((n : ℚ) + 1) * (((n : ℚ) + 1) + (1 : ℚ)))) / ((n : ℚ) + 1)) := by
  apply linear_certificate p096_base (5 : ℚ) (fun n : ℕ => ((n : ℚ) + 1)) (fun n : ℕ => ((2 : ℚ) * (((n : ℚ) + 1) + (1 : ℚ)))) (fun n : ℕ => ((-2 : ℚ) * ((n : ℚ) + 1) * (((n : ℚ) + 1) + (1 : ℚ))))
  · norm_num [p096_base]
  · intro n; positivity
  · intro n
    simp only [p096_base, Nat.cast_add, Nat.cast_one, pow_succ, pow_add] at *
    ring
theorem p096_positive (n : ℕ) : 0 < p096_base n := by
  unfold p096_base
  positivity
theorem p096_valid : FirstCertificate p096 ((1 : ℚ) / 5) (fun n x => ((n : ℚ) + 1) * x / (((2 : ℚ) * (((n : ℚ) + 1) + (1 : ℚ))) + ((-2 : ℚ) * ((n : ℚ) + 1) * (((n : ℚ) + 1) + (1 : ℚ))) * x)) := by
  have h := reciprocal_certificate p096_base_valid p096_positive (by intro n; positivity)
  have heq : p096 = (fun n => 1 / p096_base n) := by
    funext n
    simp [p096, p096_base, div_eq_mul_inv] <;> ring
  rw [heq]
  convert h.1 using 1 <;> norm_num
theorem p096_domain : (∀ n : ℕ, ((2 : ℚ) * (((n : ℚ) + 1) + (1 : ℚ))) + ((-2 : ℚ) * ((n : ℚ) + 1) * (((n : ℚ) + 1) + (1 : ℚ))) * p096 n ≠ 0) ∧ (∀ n, p096 n ≠ 0) := by
  have h := reciprocal_certificate p096_base_valid p096_positive (by intro n; positivity)
  simpa [p096, p096_base, div_eq_mul_inv] using h.2
#print axioms p096_domain
theorem p096_unique (a : ℕ → ℚ) (ha : FirstCertificate a ((1 : ℚ) / 5) (fun n x => ((n : ℚ) + 1) * x / (((2 : ℚ) * (((n : ℚ) + 1) + (1 : ℚ))) + ((-2 : ℚ) * ((n : ℚ) + 1) * (((n : ℚ) + 1) + (1 : ℚ))) * x))) :
    ∀ n, a n = p096 n := first_unique p096_valid ha
#print axioms p096_valid
#print axioms p096_unique

def p114 (n : ℕ) : ℚ := ((((n : ℚ) + 1) + (1 : ℚ)) / (((3 : ℚ) ^ n) + (1 : ℚ)))
def p114_base (n : ℕ) : ℚ := ((((3 : ℚ) ^ n) + (1 : ℚ)) / (((n : ℚ) + 1) + (1 : ℚ)))
theorem p114_base_valid : FirstCertificate p114_base (1 : ℚ) (fun n x => (((3 : ℚ) * (((n : ℚ) + 1) + (1 : ℚ))) * x + (-2 : ℚ)) / (((n : ℚ) + 1) + (2 : ℚ))) := by
  apply linear_certificate p114_base (1 : ℚ) (fun n : ℕ => (((n : ℚ) + 1) + (2 : ℚ))) (fun n : ℕ => ((3 : ℚ) * (((n : ℚ) + 1) + (1 : ℚ)))) (fun n : ℕ => (-2 : ℚ))
  · norm_num [p114_base]
  · intro n; positivity
  · intro n
    have hd0 : (((n : ℚ) + 1) + (1 : ℚ)) ≠ 0 := by positivity
    have he0 : ((((n + 1) : ℚ) + 1) + (1 : ℚ)) ≠ 0 := by positivity
    simp only [p114_base, Nat.cast_add, Nat.cast_one, pow_succ, pow_add] at *
    field_simp [hd0, he0] <;> ring
theorem p114_positive (n : ℕ) : 0 < p114_base n := by
  unfold p114_base
  positivity
theorem p114_valid : FirstCertificate p114 (1 : ℚ) (fun n x => (((n : ℚ) + 1) + (2 : ℚ)) * x / (((3 : ℚ) * (((n : ℚ) + 1) + (1 : ℚ))) + (-2 : ℚ) * x)) := by
  have h := reciprocal_certificate p114_base_valid p114_positive (by intro n; positivity)
  have heq : p114 = (fun n => 1 / p114_base n) := by
    funext n
    simp [p114, p114_base, div_eq_mul_inv] <;> ring
  rw [heq]
  convert h.1 using 1 <;> norm_num
theorem p114_domain : (∀ n : ℕ, ((3 : ℚ) * (((n : ℚ) + 1) + (1 : ℚ))) + (-2 : ℚ) * p114 n ≠ 0) ∧ (∀ n, p114 n ≠ 0) := by
  have h := reciprocal_certificate p114_base_valid p114_positive (by intro n; positivity)
  simpa [p114, p114_base, div_eq_mul_inv] using h.2
#print axioms p114_domain
theorem p114_unique (a : ℕ → ℚ) (ha : FirstCertificate a (1 : ℚ) (fun n x => (((n : ℚ) + 1) + (2 : ℚ)) * x / (((3 : ℚ) * (((n : ℚ) + 1) + (1 : ℚ))) + (-2 : ℚ) * x))) :
    ∀ n, a n = p114 n := first_unique p114_valid ha
#print axioms p114_valid
#print axioms p114_unique

def p098 (n : ℕ) : ℚ := ((((2 : ℚ) * ((n : ℚ) + 1)) + (1 : ℚ)) / (((3 : ℚ) * ((2 : ℚ) ^ n)) + (2 : ℚ)))
def p098_base (n : ℕ) : ℚ := ((((3 : ℚ) * ((2 : ℚ) ^ n)) + (2 : ℚ)) / (((2 : ℚ) * ((n : ℚ) + 1)) + (1 : ℚ)))
theorem p098_base_valid : FirstCertificate p098_base ((5 : ℚ) / 3) (fun n x => (((2 : ℚ) * (((2 : ℚ) * ((n : ℚ) + 1)) + (1 : ℚ))) * x + (-2 : ℚ)) / (((2 : ℚ) * ((n : ℚ) + 1)) + (3 : ℚ))) := by
  apply linear_certificate p098_base ((5 : ℚ) / 3) (fun n : ℕ => (((2 : ℚ) * ((n : ℚ) + 1)) + (3 : ℚ))) (fun n : ℕ => ((2 : ℚ) * (((2 : ℚ) * ((n : ℚ) + 1)) + (1 : ℚ)))) (fun n : ℕ => (-2 : ℚ))
  · norm_num [p098_base]
  · intro n; positivity
  · intro n
    have hd0 : (((2 : ℚ) * ((n : ℚ) + 1)) + (1 : ℚ)) ≠ 0 := by positivity
    have he0 : (((2 : ℚ) * (((n + 1) : ℚ) + 1)) + (1 : ℚ)) ≠ 0 := by positivity
    simp only [p098_base, Nat.cast_add, Nat.cast_one, pow_succ, pow_add] at *
    field_simp [hd0, he0] <;> ring
theorem p098_positive (n : ℕ) : 0 < p098_base n := by
  unfold p098_base
  positivity
theorem p098_valid : FirstCertificate p098 ((3 : ℚ) / 5) (fun n x => (((2 : ℚ) * ((n : ℚ) + 1)) + (3 : ℚ)) * x / (((2 : ℚ) * (((2 : ℚ) * ((n : ℚ) + 1)) + (1 : ℚ))) + (-2 : ℚ) * x)) := by
  have h := reciprocal_certificate p098_base_valid p098_positive (by intro n; positivity)
  have heq : p098 = (fun n => 1 / p098_base n) := by
    funext n
    simp [p098, p098_base, div_eq_mul_inv] <;> ring
  rw [heq]
  convert h.1 using 1 <;> norm_num
theorem p098_domain : (∀ n : ℕ, ((2 : ℚ) * (((2 : ℚ) * ((n : ℚ) + 1)) + (1 : ℚ))) + (-2 : ℚ) * p098 n ≠ 0) ∧ (∀ n, p098 n ≠ 0) := by
  have h := reciprocal_certificate p098_base_valid p098_positive (by intro n; positivity)
  simpa [p098, p098_base, div_eq_mul_inv] using h.2
#print axioms p098_domain
theorem p098_unique (a : ℕ → ℚ) (ha : FirstCertificate a ((3 : ℚ) / 5) (fun n x => (((2 : ℚ) * ((n : ℚ) + 1)) + (3 : ℚ)) * x / (((2 : ℚ) * (((2 : ℚ) * ((n : ℚ) + 1)) + (1 : ℚ))) + (-2 : ℚ) * x))) :
    ∀ n, a n = p098 n := first_unique p098_valid ha
#print axioms p098_valid
#print axioms p098_unique

def p115 (n : ℕ) : ℚ := ((((n : ℚ) + 1) ^ 2) / (((3 : ℚ) ^ n) + (1 : ℚ)))
def p115_base (n : ℕ) : ℚ := ((((3 : ℚ) ^ n) + (1 : ℚ)) / (((n : ℚ) + 1) ^ 2))
theorem p115_base_valid : FirstCertificate p115_base (2 : ℚ) (fun n x => (((3 : ℚ) * (((n : ℚ) + 1) ^ 2)) * x + (-2 : ℚ)) / ((((n : ℚ) + 1) + (1 : ℚ)) ^ 2)) := by
  apply linear_certificate p115_base (2 : ℚ) (fun n : ℕ => ((((n : ℚ) + 1) + (1 : ℚ)) ^ 2)) (fun n : ℕ => ((3 : ℚ) * (((n : ℚ) + 1) ^ 2))) (fun n : ℕ => (-2 : ℚ))
  · norm_num [p115_base]
  · intro n; positivity
  · intro n
    have hd0 : (((n : ℚ) + 1) ^ 2) ≠ 0 := by positivity
    have he0 : ((((n + 1) : ℚ) + 1) ^ 2) ≠ 0 := by positivity
    simp only [p115_base, Nat.cast_add, Nat.cast_one, pow_succ, pow_add] at *
    field_simp [hd0, he0] <;> ring
theorem p115_positive (n : ℕ) : 0 < p115_base n := by
  unfold p115_base
  positivity
theorem p115_valid : FirstCertificate p115 ((1 : ℚ) / 2) (fun n x => ((((n : ℚ) + 1) + (1 : ℚ)) ^ 2) * x / (((3 : ℚ) * (((n : ℚ) + 1) ^ 2)) + (-2 : ℚ) * x)) := by
  have h := reciprocal_certificate p115_base_valid p115_positive (by intro n; positivity)
  have heq : p115 = (fun n => 1 / p115_base n) := by
    funext n
    simp [p115, p115_base, div_eq_mul_inv] <;> ring
  rw [heq]
  convert h.1 using 1 <;> norm_num
theorem p115_domain : (∀ n : ℕ, ((3 : ℚ) * (((n : ℚ) + 1) ^ 2)) + (-2 : ℚ) * p115 n ≠ 0) ∧ (∀ n, p115 n ≠ 0) := by
  have h := reciprocal_certificate p115_base_valid p115_positive (by intro n; positivity)
  simpa [p115, p115_base, div_eq_mul_inv] using h.2
#print axioms p115_domain
theorem p115_unique (a : ℕ → ℚ) (ha : FirstCertificate a ((1 : ℚ) / 2) (fun n x => ((((n : ℚ) + 1) + (1 : ℚ)) ^ 2) * x / (((3 : ℚ) * (((n : ℚ) + 1) ^ 2)) + (-2 : ℚ) * x))) :
    ∀ n, a n = p115 n := first_unique p115_valid ha
#print axioms p115_valid
#print axioms p115_unique

def p100 (n : ℕ) : ℚ := ((((n : ℚ) + 1) * (((n : ℚ) + 1) + (1 : ℚ))) / (((3 : ℚ) * ((2 : ℚ) ^ n)) + (2 : ℚ)))
def p100_base (n : ℕ) : ℚ := ((((3 : ℚ) * ((2 : ℚ) ^ n)) + (2 : ℚ)) / (((n : ℚ) + 1) * (((n : ℚ) + 1) + (1 : ℚ))))
theorem p100_base_valid : FirstCertificate p100_base ((5 : ℚ) / 2) (fun n x => (((2 : ℚ) * ((n : ℚ) + 1) * (((n : ℚ) + 1) + (1 : ℚ))) * x + (-2 : ℚ)) / ((((n : ℚ) + 1) + (1 : ℚ)) * (((n : ℚ) + 1) + (2 : ℚ)))) := by
  apply linear_certificate p100_base ((5 : ℚ) / 2) (fun n : ℕ => ((((n : ℚ) + 1) + (1 : ℚ)) * (((n : ℚ) + 1) + (2 : ℚ)))) (fun n : ℕ => ((2 : ℚ) * ((n : ℚ) + 1) * (((n : ℚ) + 1) + (1 : ℚ)))) (fun n : ℕ => (-2 : ℚ))
  · norm_num [p100_base]
  · intro n; positivity
  · intro n
    have hd0 : (((n : ℚ) + 1) * (((n : ℚ) + 1) + (1 : ℚ))) ≠ 0 := by positivity
    have he0 : ((((n + 1) : ℚ) + 1) * ((((n + 1) : ℚ) + 1) + (1 : ℚ))) ≠ 0 := by positivity
    simp only [p100_base, Nat.cast_add, Nat.cast_one, pow_succ, pow_add] at *
    field_simp [hd0, he0] <;> ring
theorem p100_positive (n : ℕ) : 0 < p100_base n := by
  unfold p100_base
  positivity
theorem p100_valid : FirstCertificate p100 ((2 : ℚ) / 5) (fun n x => ((((n : ℚ) + 1) + (1 : ℚ)) * (((n : ℚ) + 1) + (2 : ℚ))) * x / (((2 : ℚ) * ((n : ℚ) + 1) * (((n : ℚ) + 1) + (1 : ℚ))) + (-2 : ℚ) * x)) := by
  have h := reciprocal_certificate p100_base_valid p100_positive (by intro n; positivity)
  have heq : p100 = (fun n => 1 / p100_base n) := by
    funext n
    simp [p100, p100_base, div_eq_mul_inv] <;> ring
  rw [heq]
  convert h.1 using 1 <;> norm_num
theorem p100_domain : (∀ n : ℕ, ((2 : ℚ) * ((n : ℚ) + 1) * (((n : ℚ) + 1) + (1 : ℚ))) + (-2 : ℚ) * p100 n ≠ 0) ∧ (∀ n, p100 n ≠ 0) := by
  have h := reciprocal_certificate p100_base_valid p100_positive (by intro n; positivity)
  simpa [p100, p100_base, div_eq_mul_inv] using h.2
#print axioms p100_domain
theorem p100_unique (a : ℕ → ℚ) (ha : FirstCertificate a ((2 : ℚ) / 5) (fun n x => ((((n : ℚ) + 1) + (1 : ℚ)) * (((n : ℚ) + 1) + (2 : ℚ))) * x / (((2 : ℚ) * ((n : ℚ) + 1) * (((n : ℚ) + 1) + (1 : ℚ))) + (-2 : ℚ) * x))) :
    ∀ n, a n = p100 n := first_unique p100_valid ha
#print axioms p100_valid
#print axioms p100_unique

def p101 (n : ℕ) : ℚ := (((8 : ℚ) * ((2 : ℚ) ^ n)) + ((-2 : ℚ) * ((n : ℚ) + 1)) + (-2 : ℚ))
theorem p101_base_valid : FirstCertificate p101 (4 : ℚ) (fun n x => ((2 : ℚ) * x + ((2 : ℚ) * ((n : ℚ) + 1))) / (1 : ℚ)) := by
  apply linear_certificate p101 (4 : ℚ) (fun n : ℕ => (1 : ℚ)) (fun n : ℕ => (2 : ℚ)) (fun n : ℕ => ((2 : ℚ) * ((n : ℚ) + 1)))
  · norm_num [p101]
  · intro n; positivity
  · intro n
    simp only [p101, Nat.cast_add, Nat.cast_one, pow_succ, pow_add] at *
    ring
theorem p101_valid : FirstCertificate p101 (4 : ℚ) (fun n x => ((2 : ℚ) * x + ((2 : ℚ) * ((n : ℚ) + 1))) / (1 : ℚ)) := p101_base_valid
theorem p101_unique (a : ℕ → ℚ) (ha : FirstCertificate a (4 : ℚ) (fun n x => ((2 : ℚ) * x + ((2 : ℚ) * ((n : ℚ) + 1))) / (1 : ℚ))) :
    ∀ n, a n = p101 n := first_unique p101_valid ha
#print axioms p101_valid
#print axioms p101_unique

def p102 (n : ℕ) : ℚ := (((8 : ℚ) * ((2 : ℚ) ^ n)) + ((-3 : ℚ) * ((n : ℚ) + 1)) + (-3 : ℚ))
theorem p102_base_valid : FirstCertificate p102 (2 : ℚ) (fun n x => ((2 : ℚ) * x + ((3 : ℚ) * ((n : ℚ) + 1))) / (1 : ℚ)) := by
  apply linear_certificate p102 (2 : ℚ) (fun n : ℕ => (1 : ℚ)) (fun n : ℕ => (2 : ℚ)) (fun n : ℕ => ((3 : ℚ) * ((n : ℚ) + 1)))
  · norm_num [p102]
  · intro n; positivity
  · intro n
    simp only [p102, Nat.cast_add, Nat.cast_one, pow_succ, pow_add] at *
    ring
theorem p102_valid : FirstCertificate p102 (2 : ℚ) (fun n x => ((2 : ℚ) * x + ((3 : ℚ) * ((n : ℚ) + 1))) / (1 : ℚ)) := p102_base_valid
theorem p102_unique (a : ℕ → ℚ) (ha : FirstCertificate a (2 : ℚ) (fun n x => ((2 : ℚ) * x + ((3 : ℚ) * ((n : ℚ) + 1))) / (1 : ℚ))) :
    ∀ n, a n = p102 n := first_unique p102_valid ha
#print axioms p102_valid
#print axioms p102_unique

def p103 (n : ℕ) : ℚ := (((8 : ℚ) * ((2 : ℚ) ^ n)) + ((-1 : ℚ) * ((n : ℚ) + 1)) + (-1 : ℚ))
theorem p103_base_valid : FirstCertificate p103 (6 : ℚ) (fun n x => ((2 : ℚ) * x + ((n : ℚ) + 1)) / (1 : ℚ)) := by
  apply linear_certificate p103 (6 : ℚ) (fun n : ℕ => (1 : ℚ)) (fun n : ℕ => (2 : ℚ)) (fun n : ℕ => ((n : ℚ) + 1))
  · norm_num [p103]
  · intro n; positivity
  · intro n
    simp only [p103, Nat.cast_add, Nat.cast_one, pow_succ, pow_add] at *
    ring
theorem p103_valid : FirstCertificate p103 (6 : ℚ) (fun n x => ((2 : ℚ) * x + ((n : ℚ) + 1)) / (1 : ℚ)) := p103_base_valid
theorem p103_unique (a : ℕ → ℚ) (ha : FirstCertificate a (6 : ℚ) (fun n x => ((2 : ℚ) * x + ((n : ℚ) + 1)) / (1 : ℚ))) :
    ∀ n, a n = p103 n := first_unique p103_valid ha
#print axioms p103_valid
#print axioms p103_unique

def p104 (n : ℕ) : ℚ := (((6 : ℚ) * ((3 : ℚ) ^ n)) + ((-1 : ℚ) * ((n : ℚ) + 1)) + ((-1 : ℚ) / 2))
theorem p104_base_valid : FirstCertificate p104 ((9 : ℚ) / 2) (fun n x => ((3 : ℚ) * x + ((2 : ℚ) * ((n : ℚ) + 1))) / (1 : ℚ)) := by
  apply linear_certificate p104 ((9 : ℚ) / 2) (fun n : ℕ => (1 : ℚ)) (fun n : ℕ => (3 : ℚ)) (fun n : ℕ => ((2 : ℚ) * ((n : ℚ) + 1)))
  · norm_num [p104]
  · intro n; positivity
  · intro n
    simp only [p104, Nat.cast_add, Nat.cast_one, pow_succ, pow_add] at *
    ring
theorem p104_valid : FirstCertificate p104 ((9 : ℚ) / 2) (fun n x => ((3 : ℚ) * x + ((2 : ℚ) * ((n : ℚ) + 1))) / (1 : ℚ)) := p104_base_valid
theorem p104_unique (a : ℕ → ℚ) (ha : FirstCertificate a ((9 : ℚ) / 2) (fun n x => ((3 : ℚ) * x + ((2 : ℚ) * ((n : ℚ) + 1))) / (1 : ℚ))) :
    ∀ n, a n = p104 n := first_unique p104_valid ha
#print axioms p104_valid
#print axioms p104_unique

def p105 (n : ℕ) : ℚ := (((5 : ℚ) * ((3 : ℚ) ^ n)) + ((-2 : ℚ) * ((n : ℚ) + 1)) + (-1 : ℚ))
theorem p105_base_valid : FirstCertificate p105 (2 : ℚ) (fun n x => ((3 : ℚ) * x + ((4 : ℚ) * ((n : ℚ) + 1))) / (1 : ℚ)) := by
  apply linear_certificate p105 (2 : ℚ) (fun n : ℕ => (1 : ℚ)) (fun n : ℕ => (3 : ℚ)) (fun n : ℕ => ((4 : ℚ) * ((n : ℚ) + 1)))
  · norm_num [p105]
  · intro n; positivity
  · intro n
    simp only [p105, Nat.cast_add, Nat.cast_one, pow_succ, pow_add] at *
    ring
theorem p105_valid : FirstCertificate p105 (2 : ℚ) (fun n x => ((3 : ℚ) * x + ((4 : ℚ) * ((n : ℚ) + 1))) / (1 : ℚ)) := p105_base_valid
theorem p105_unique (a : ℕ → ℚ) (ha : FirstCertificate a (2 : ℚ) (fun n x => ((3 : ℚ) * x + ((4 : ℚ) * ((n : ℚ) + 1))) / (1 : ℚ))) :
    ∀ n, a n = p105 n := first_unique p105_valid ha
#print axioms p105_valid
#print axioms p105_unique

def p106 (n : ℕ) : ℚ := ((1 : ℚ) / (((8 : ℚ) * ((2 : ℚ) ^ n)) + ((-2 : ℚ) * ((n : ℚ) + 1)) + (-2 : ℚ)))
def p106_base (n : ℕ) : ℚ := (((8 : ℚ) * ((2 : ℚ) ^ n)) + ((-2 : ℚ) * ((n : ℚ) + 1)) + (-2 : ℚ))
theorem p106_base_valid : FirstCertificate p106_base (4 : ℚ) (fun n x => ((2 : ℚ) * x + ((2 : ℚ) * ((n : ℚ) + 1))) / (1 : ℚ)) := by
  apply linear_certificate p106_base (4 : ℚ) (fun n : ℕ => (1 : ℚ)) (fun n : ℕ => (2 : ℚ)) (fun n : ℕ => ((2 : ℚ) * ((n : ℚ) + 1)))
  · norm_num [p106_base]
  · intro n; positivity
  · intro n
    simp only [p106_base, Nat.cast_add, Nat.cast_one, pow_succ, pow_add] at *
    ring
theorem p106_positive (n : ℕ) : 0 < p106_base n := by
  induction n with
  | zero => norm_num [p106_base]
  | succ n ih => rw [p106_base_valid.recurrence]; positivity
theorem p106_valid : FirstCertificate p106 ((1 : ℚ) / 4) (fun n x => (1 : ℚ) * x / ((2 : ℚ) + ((2 : ℚ) * ((n : ℚ) + 1)) * x)) := by
  have h := reciprocal_certificate p106_base_valid p106_positive (by intro n; positivity)
  have heq : p106 = (fun n => 1 / p106_base n) := by
    funext n
    simp [p106, p106_base, div_eq_mul_inv] <;> ring
  rw [heq]
  convert h.1 using 1 <;> norm_num
theorem p106_domain : (∀ n : ℕ, (2 : ℚ) + ((2 : ℚ) * ((n : ℚ) + 1)) * p106 n ≠ 0) ∧ (∀ n, p106 n ≠ 0) := by
  have h := reciprocal_certificate p106_base_valid p106_positive (by intro n; positivity)
  simpa [p106, p106_base, div_eq_mul_inv] using h.2
#print axioms p106_domain
theorem p106_unique (a : ℕ → ℚ) (ha : FirstCertificate a ((1 : ℚ) / 4) (fun n x => (1 : ℚ) * x / ((2 : ℚ) + ((2 : ℚ) * ((n : ℚ) + 1)) * x))) :
    ∀ n, a n = p106 n := first_unique p106_valid ha
#print axioms p106_valid
#print axioms p106_unique

def p107 (n : ℕ) : ℚ := ((1 : ℚ) / (((8 : ℚ) * ((2 : ℚ) ^ n)) + ((-3 : ℚ) * ((n : ℚ) + 1)) + (-3 : ℚ)))
def p107_base (n : ℕ) : ℚ := (((8 : ℚ) * ((2 : ℚ) ^ n)) + ((-3 : ℚ) * ((n : ℚ) + 1)) + (-3 : ℚ))
theorem p107_base_valid : FirstCertificate p107_base (2 : ℚ) (fun n x => ((2 : ℚ) * x + ((3 : ℚ) * ((n : ℚ) + 1))) / (1 : ℚ)) := by
  apply linear_certificate p107_base (2 : ℚ) (fun n : ℕ => (1 : ℚ)) (fun n : ℕ => (2 : ℚ)) (fun n : ℕ => ((3 : ℚ) * ((n : ℚ) + 1)))
  · norm_num [p107_base]
  · intro n; positivity
  · intro n
    simp only [p107_base, Nat.cast_add, Nat.cast_one, pow_succ, pow_add] at *
    ring
theorem p107_positive (n : ℕ) : 0 < p107_base n := by
  induction n with
  | zero => norm_num [p107_base]
  | succ n ih => rw [p107_base_valid.recurrence]; positivity
theorem p107_valid : FirstCertificate p107 ((1 : ℚ) / 2) (fun n x => (1 : ℚ) * x / ((2 : ℚ) + ((3 : ℚ) * ((n : ℚ) + 1)) * x)) := by
  have h := reciprocal_certificate p107_base_valid p107_positive (by intro n; positivity)
  have heq : p107 = (fun n => 1 / p107_base n) := by
    funext n
    simp [p107, p107_base, div_eq_mul_inv] <;> ring
  rw [heq]
  convert h.1 using 1 <;> norm_num
theorem p107_domain : (∀ n : ℕ, (2 : ℚ) + ((3 : ℚ) * ((n : ℚ) + 1)) * p107 n ≠ 0) ∧ (∀ n, p107 n ≠ 0) := by
  have h := reciprocal_certificate p107_base_valid p107_positive (by intro n; positivity)
  simpa [p107, p107_base, div_eq_mul_inv] using h.2
#print axioms p107_domain
theorem p107_unique (a : ℕ → ℚ) (ha : FirstCertificate a ((1 : ℚ) / 2) (fun n x => (1 : ℚ) * x / ((2 : ℚ) + ((3 : ℚ) * ((n : ℚ) + 1)) * x))) :
    ∀ n, a n = p107 n := first_unique p107_valid ha
#print axioms p107_valid
#print axioms p107_unique

def p108 (n : ℕ) : ℚ := ((1 : ℚ) / (((5 : ℚ) * ((3 : ℚ) ^ n)) + ((-2 : ℚ) * ((n : ℚ) + 1)) + (-1 : ℚ)))
def p108_base (n : ℕ) : ℚ := (((5 : ℚ) * ((3 : ℚ) ^ n)) + ((-2 : ℚ) * ((n : ℚ) + 1)) + (-1 : ℚ))
theorem p108_base_valid : FirstCertificate p108_base (2 : ℚ) (fun n x => ((3 : ℚ) * x + ((4 : ℚ) * ((n : ℚ) + 1))) / (1 : ℚ)) := by
  apply linear_certificate p108_base (2 : ℚ) (fun n : ℕ => (1 : ℚ)) (fun n : ℕ => (3 : ℚ)) (fun n : ℕ => ((4 : ℚ) * ((n : ℚ) + 1)))
  · norm_num [p108_base]
  · intro n; positivity
  · intro n
    simp only [p108_base, Nat.cast_add, Nat.cast_one, pow_succ, pow_add] at *
    ring
theorem p108_positive (n : ℕ) : 0 < p108_base n := by
  induction n with
  | zero => norm_num [p108_base]
  | succ n ih => rw [p108_base_valid.recurrence]; positivity
theorem p108_valid : FirstCertificate p108 ((1 : ℚ) / 2) (fun n x => (1 : ℚ) * x / ((3 : ℚ) + ((4 : ℚ) * ((n : ℚ) + 1)) * x)) := by
  have h := reciprocal_certificate p108_base_valid p108_positive (by intro n; positivity)
  have heq : p108 = (fun n => 1 / p108_base n) := by
    funext n
    simp [p108, p108_base, div_eq_mul_inv] <;> ring
  rw [heq]
  convert h.1 using 1 <;> norm_num
theorem p108_domain : (∀ n : ℕ, (3 : ℚ) + ((4 : ℚ) * ((n : ℚ) + 1)) * p108 n ≠ 0) ∧ (∀ n, p108 n ≠ 0) := by
  have h := reciprocal_certificate p108_base_valid p108_positive (by intro n; positivity)
  simpa [p108, p108_base, div_eq_mul_inv] using h.2
#print axioms p108_domain
theorem p108_unique (a : ℕ → ℚ) (ha : FirstCertificate a ((1 : ℚ) / 2) (fun n x => (1 : ℚ) * x / ((3 : ℚ) + ((4 : ℚ) * ((n : ℚ) + 1)) * x))) :
    ∀ n, a n = p108 n := first_unique p108_valid ha
#print axioms p108_valid
#print axioms p108_unique

def p109 (n : ℕ) : ℚ := ((1 : ℚ) / (((3 : ℚ) * ((2 : ℚ) ^ n)) + ((-1 : ℚ) * ((n : ℚ) + 1)) + (-1 : ℚ)))
def p109_base (n : ℕ) : ℚ := (((3 : ℚ) * ((2 : ℚ) ^ n)) + ((-1 : ℚ) * ((n : ℚ) + 1)) + (-1 : ℚ))
theorem p109_base_valid : FirstCertificate p109_base (1 : ℚ) (fun n x => ((2 : ℚ) * x + ((n : ℚ) + 1)) / (1 : ℚ)) := by
  apply linear_certificate p109_base (1 : ℚ) (fun n : ℕ => (1 : ℚ)) (fun n : ℕ => (2 : ℚ)) (fun n : ℕ => ((n : ℚ) + 1))
  · norm_num [p109_base]
  · intro n; positivity
  · intro n
    simp only [p109_base, Nat.cast_add, Nat.cast_one, pow_succ, pow_add] at *
    ring
theorem p109_positive (n : ℕ) : 0 < p109_base n := by
  induction n with
  | zero => norm_num [p109_base]
  | succ n ih => rw [p109_base_valid.recurrence]; positivity
theorem p109_valid : FirstCertificate p109 (1 : ℚ) (fun n x => (1 : ℚ) * x / ((2 : ℚ) + ((n : ℚ) + 1) * x)) := by
  have h := reciprocal_certificate p109_base_valid p109_positive (by intro n; positivity)
  have heq : p109 = (fun n => 1 / p109_base n) := by
    funext n
    simp [p109, p109_base, div_eq_mul_inv] <;> ring
  rw [heq]
  convert h.1 using 1 <;> norm_num
theorem p109_domain : (∀ n : ℕ, (2 : ℚ) + ((n : ℚ) + 1) * p109 n ≠ 0) ∧ (∀ n, p109 n ≠ 0) := by
  have h := reciprocal_certificate p109_base_valid p109_positive (by intro n; positivity)
  simpa [p109, p109_base, div_eq_mul_inv] using h.2
#print axioms p109_domain
theorem p109_unique (a : ℕ → ℚ) (ha : FirstCertificate a (1 : ℚ) (fun n x => (1 : ℚ) * x / ((2 : ℚ) + ((n : ℚ) + 1) * x))) :
    ∀ n, a n = p109 n := first_unique p109_valid ha
#print axioms p109_valid
#print axioms p109_unique

def p110 (n : ℕ) : ℚ := ((1 : ℚ) / (((6 : ℚ) * ((3 : ℚ) ^ n)) + ((-1 : ℚ) * ((n : ℚ) + 1)) + ((-1 : ℚ) / 2)))
def p110_base (n : ℕ) : ℚ := (((6 : ℚ) * ((3 : ℚ) ^ n)) + ((-1 : ℚ) * ((n : ℚ) + 1)) + ((-1 : ℚ) / 2))
theorem p110_base_valid : FirstCertificate p110_base ((9 : ℚ) / 2) (fun n x => ((3 : ℚ) * x + ((2 : ℚ) * ((n : ℚ) + 1))) / (1 : ℚ)) := by
  apply linear_certificate p110_base ((9 : ℚ) / 2) (fun n : ℕ => (1 : ℚ)) (fun n : ℕ => (3 : ℚ)) (fun n : ℕ => ((2 : ℚ) * ((n : ℚ) + 1)))
  · norm_num [p110_base]
  · intro n; positivity
  · intro n
    simp only [p110_base, Nat.cast_add, Nat.cast_one, pow_succ, pow_add] at *
    ring
theorem p110_positive (n : ℕ) : 0 < p110_base n := by
  induction n with
  | zero => norm_num [p110_base]
  | succ n ih => rw [p110_base_valid.recurrence]; positivity
theorem p110_valid : FirstCertificate p110 ((2 : ℚ) / 9) (fun n x => (1 : ℚ) * x / ((3 : ℚ) + ((2 : ℚ) * ((n : ℚ) + 1)) * x)) := by
  have h := reciprocal_certificate p110_base_valid p110_positive (by intro n; positivity)
  have heq : p110 = (fun n => 1 / p110_base n) := by
    funext n
    simp [p110, p110_base, div_eq_mul_inv] <;> ring
  rw [heq]
  convert h.1 using 1 <;> norm_num
theorem p110_domain : (∀ n : ℕ, (3 : ℚ) + ((2 : ℚ) * ((n : ℚ) + 1)) * p110 n ≠ 0) ∧ (∀ n, p110 n ≠ 0) := by
  have h := reciprocal_certificate p110_base_valid p110_positive (by intro n; positivity)
  simpa [p110, p110_base, div_eq_mul_inv] using h.2
#print axioms p110_domain
theorem p110_unique (a : ℕ → ℚ) (ha : FirstCertificate a ((2 : ℚ) / 9) (fun n x => (1 : ℚ) * x / ((3 : ℚ) + ((2 : ℚ) * ((n : ℚ) + 1)) * x))) :
    ∀ n, a n = p110 n := first_unique p110_valid ha
#print axioms p110_valid
#print axioms p110_unique

def p180 (n : ℕ) : ℚ := ((((2 : ℚ) ^ n) + ((2 : ℚ) * ((-2 : ℚ) ^ n))) / (((2 : ℚ) * ((n : ℚ) + 1)) + (1 : ℚ)))
theorem p180_valid : GeneralSecondCertificate p180 (1 : ℚ) ((-2 : ℚ) / 5) (fun n x y => ((0 : ℚ) * y + ((4 : ℚ) * (((2 : ℚ) * ((n : ℚ) + 1)) + (1 : ℚ))) * x) / (((2 : ℚ) * ((n : ℚ) + 1)) + (5 : ℚ))) := by
  apply linear_second_certificate p180 (1 : ℚ) ((-2 : ℚ) / 5) (fun n => (((2 : ℚ) * ((n : ℚ) + 1)) + (5 : ℚ))) (fun n => (0 : ℚ)) (fun n => ((4 : ℚ) * (((2 : ℚ) * ((n : ℚ) + 1)) + (1 : ℚ))))
  · norm_num [p180]
  · norm_num [p180]
  · intro n; positivity
  · intro n
    have h0_0 : (((2 : ℚ) * ((n : ℚ) + 1)) + (1 : ℚ)) ≠ 0 := by positivity
    have h1_0 : (((2 : ℚ) * (((n + 1) : ℚ) + 1)) + (1 : ℚ)) ≠ 0 := by positivity
    have h2_0 : (((2 : ℚ) * (((n + 2) : ℚ) + 1)) + (1 : ℚ)) ≠ 0 := by positivity
    simp only [p180, Nat.cast_add, Nat.cast_one, pow_succ, pow_add] at *
    field_simp [h0_0, h1_0, h2_0] <;> ring
theorem p180_unique (a : ℕ → ℚ) (hi : a 0 = (1 : ℚ)) (hj : a 1 = ((-2 : ℚ) / 5))
    (ha : ∀ n : ℕ, (((2 : ℚ) * ((n : ℚ) + 1)) + (5 : ℚ)) * a (n + 2) = (0 : ℚ) * a (n + 1) + ((4 : ℚ) * (((2 : ℚ) * ((n : ℚ) + 1)) + (1 : ℚ))) * a n) :
    ∀ n, a n = p180 n := by
  apply general_second_unique p180_valid
  exact linear_second_certificate a (1 : ℚ) ((-2 : ℚ) / 5) (fun n => (((2 : ℚ) * ((n : ℚ) + 1)) + (5 : ℚ))) (fun n => (0 : ℚ)) (fun n => ((4 : ℚ) * (((2 : ℚ) * ((n : ℚ) + 1)) + (1 : ℚ)))) hi hj (by intro n; positivity) ha
#print axioms p180_valid
#print axioms p180_unique

def p139 (n : ℕ) : ℚ := ((((2 : ℚ) ^ n) + ((3 : ℚ) ^ n)) / ((n : ℚ) + 1))
theorem p139_valid : GeneralSecondCertificate p139 (2 : ℚ) ((5 : ℚ) / 2) (fun n x y => (((5 : ℚ) * (((n : ℚ) + 1) + (1 : ℚ))) * y + ((-6 : ℚ) * ((n : ℚ) + 1)) * x) / (((n : ℚ) + 1) + (2 : ℚ))) := by
  apply linear_second_certificate p139 (2 : ℚ) ((5 : ℚ) / 2) (fun n => (((n : ℚ) + 1) + (2 : ℚ))) (fun n => ((5 : ℚ) * (((n : ℚ) + 1) + (1 : ℚ)))) (fun n => ((-6 : ℚ) * ((n : ℚ) + 1)))
  · norm_num [p139]
  · norm_num [p139]
  · intro n; positivity
  · intro n
    have h0_0 : ((n : ℚ) + 1) ≠ 0 := by positivity
    have h1_0 : (((n + 1) : ℚ) + 1) ≠ 0 := by positivity
    have h2_0 : (((n + 2) : ℚ) + 1) ≠ 0 := by positivity
    simp only [p139, Nat.cast_add, Nat.cast_one, pow_succ, pow_add] at *
    field_simp [h0_0, h1_0, h2_0] <;> ring
theorem p139_unique (a : ℕ → ℚ) (hi : a 0 = (2 : ℚ)) (hj : a 1 = ((5 : ℚ) / 2))
    (ha : ∀ n : ℕ, (((n : ℚ) + 1) + (2 : ℚ)) * a (n + 2) = ((5 : ℚ) * (((n : ℚ) + 1) + (1 : ℚ))) * a (n + 1) + ((-6 : ℚ) * ((n : ℚ) + 1)) * a n) :
    ∀ n, a n = p139 n := by
  apply general_second_unique p139_valid
  exact linear_second_certificate a (2 : ℚ) ((5 : ℚ) / 2) (fun n => (((n : ℚ) + 1) + (2 : ℚ))) (fun n => ((5 : ℚ) * (((n : ℚ) + 1) + (1 : ℚ)))) (fun n => ((-6 : ℚ) * ((n : ℚ) + 1))) hi hj (by intro n; positivity) ha
#print axioms p139_valid
#print axioms p139_unique

def p130 (n : ℕ) : ℚ := ((((2 : ℚ) ^ n) + ((4 : ℚ) ^ n)) / (((n : ℚ) + 1) + (1 : ℚ)))
theorem p130_valid : GeneralSecondCertificate p130 (1 : ℚ) (2 : ℚ) (fun n x y => (((6 : ℚ) * (((n : ℚ) + 1) + (2 : ℚ))) * y + ((-8 : ℚ) * (((n : ℚ) + 1) + (1 : ℚ))) * x) / (((n : ℚ) + 1) + (3 : ℚ))) := by
  apply linear_second_certificate p130 (1 : ℚ) (2 : ℚ) (fun n => (((n : ℚ) + 1) + (3 : ℚ))) (fun n => ((6 : ℚ) * (((n : ℚ) + 1) + (2 : ℚ)))) (fun n => ((-8 : ℚ) * (((n : ℚ) + 1) + (1 : ℚ))))
  · norm_num [p130]
  · norm_num [p130]
  · intro n; positivity
  · intro n
    have h0_0 : (((n : ℚ) + 1) + (1 : ℚ)) ≠ 0 := by positivity
    have h1_0 : ((((n + 1) : ℚ) + 1) + (1 : ℚ)) ≠ 0 := by positivity
    have h2_0 : ((((n + 2) : ℚ) + 1) + (1 : ℚ)) ≠ 0 := by positivity
    simp only [p130, Nat.cast_add, Nat.cast_one, pow_succ, pow_add] at *
    field_simp [h0_0, h1_0, h2_0] <;> ring
theorem p130_unique (a : ℕ → ℚ) (hi : a 0 = (1 : ℚ)) (hj : a 1 = (2 : ℚ))
    (ha : ∀ n : ℕ, (((n : ℚ) + 1) + (3 : ℚ)) * a (n + 2) = ((6 : ℚ) * (((n : ℚ) + 1) + (2 : ℚ))) * a (n + 1) + ((-8 : ℚ) * (((n : ℚ) + 1) + (1 : ℚ))) * a n) :
    ∀ n, a n = p130 n := by
  apply general_second_unique p130_valid
  exact linear_second_certificate a (1 : ℚ) (2 : ℚ) (fun n => (((n : ℚ) + 1) + (3 : ℚ))) (fun n => ((6 : ℚ) * (((n : ℚ) + 1) + (2 : ℚ)))) (fun n => ((-8 : ℚ) * (((n : ℚ) + 1) + (1 : ℚ)))) hi hj (by intro n; positivity) ha
#print axioms p130_valid
#print axioms p130_unique

def p238 (n : ℕ) : ℚ := ((((3 : ℚ) ^ n) + ((2 : ℚ) * ((-1 : ℚ) ^ n))) / (((n : ℚ) + 1) * (((n : ℚ) + 1) + (2 : ℚ))))
theorem p238_valid : GeneralSecondCertificate p238 (1 : ℚ) ((1 : ℚ) / 8) (fun n x y => (((2 : ℚ) * (((n : ℚ) + 1) + (1 : ℚ)) * (((n : ℚ) + 1) + (3 : ℚ))) * y + ((3 : ℚ) * ((n : ℚ) + 1) * (((n : ℚ) + 1) + (2 : ℚ))) * x) / ((((n : ℚ) + 1) + (2 : ℚ)) * (((n : ℚ) + 1) + (4 : ℚ)))) := by
  apply linear_second_certificate p238 (1 : ℚ) ((1 : ℚ) / 8) (fun n => ((((n : ℚ) + 1) + (2 : ℚ)) * (((n : ℚ) + 1) + (4 : ℚ)))) (fun n => ((2 : ℚ) * (((n : ℚ) + 1) + (1 : ℚ)) * (((n : ℚ) + 1) + (3 : ℚ)))) (fun n => ((3 : ℚ) * ((n : ℚ) + 1) * (((n : ℚ) + 1) + (2 : ℚ))))
  · norm_num [p238]
  · norm_num [p238]
  · intro n; positivity
  · intro n
    have h0_0 : (((n : ℚ) + 1) * (((n : ℚ) + 1) + (2 : ℚ))) ≠ 0 := by positivity
    have h1_0 : ((((n + 1) : ℚ) + 1) * ((((n + 1) : ℚ) + 1) + (2 : ℚ))) ≠ 0 := by positivity
    have h2_0 : ((((n + 2) : ℚ) + 1) * ((((n + 2) : ℚ) + 1) + (2 : ℚ))) ≠ 0 := by positivity
    simp only [p238, Nat.cast_add, Nat.cast_one, pow_succ, pow_add] at *
    field_simp [h0_0, h1_0, h2_0] <;> ring
theorem p238_unique (a : ℕ → ℚ) (hi : a 0 = (1 : ℚ)) (hj : a 1 = ((1 : ℚ) / 8))
    (ha : ∀ n : ℕ, ((((n : ℚ) + 1) + (2 : ℚ)) * (((n : ℚ) + 1) + (4 : ℚ))) * a (n + 2) = ((2 : ℚ) * (((n : ℚ) + 1) + (1 : ℚ)) * (((n : ℚ) + 1) + (3 : ℚ))) * a (n + 1) + ((3 : ℚ) * ((n : ℚ) + 1) * (((n : ℚ) + 1) + (2 : ℚ))) * a n) :
    ∀ n, a n = p238 n := by
  apply general_second_unique p238_valid
  exact linear_second_certificate a (1 : ℚ) ((1 : ℚ) / 8) (fun n => ((((n : ℚ) + 1) + (2 : ℚ)) * (((n : ℚ) + 1) + (4 : ℚ)))) (fun n => ((2 : ℚ) * (((n : ℚ) + 1) + (1 : ℚ)) * (((n : ℚ) + 1) + (3 : ℚ)))) (fun n => ((3 : ℚ) * ((n : ℚ) + 1) * (((n : ℚ) + 1) + (2 : ℚ)))) hi hj (by intro n; positivity) ha
#print axioms p238_valid
#print axioms p238_unique

def p205 (n : ℕ) : ℚ := (((n : ℚ) + 1) * (((n : ℚ) + 1) + (2 : ℚ)) * (((2 : ℚ) ^ n) + ((-2 : ℚ) ^ n)))
theorem p205_valid : GeneralSecondCertificate p205 (6 : ℚ) (0 : ℚ) (fun n x y => ((0 : ℚ) * y + (((4 : ℚ) * ((n : ℚ) + 1)) + (16 : ℚ)) * x) / ((n : ℚ) + 1)) := by
  apply linear_second_certificate p205 (6 : ℚ) (0 : ℚ) (fun n => ((n : ℚ) + 1)) (fun n => (0 : ℚ)) (fun n => (((4 : ℚ) * ((n : ℚ) + 1)) + (16 : ℚ)))
  · norm_num [p205]
  · norm_num [p205]
  · intro n; positivity
  · intro n
    simp only [p205, Nat.cast_add, Nat.cast_one, pow_succ, pow_add] at *
    ring
theorem p205_unique (a : ℕ → ℚ) (hi : a 0 = (6 : ℚ)) (hj : a 1 = (0 : ℚ))
    (ha : ∀ n : ℕ, ((n : ℚ) + 1) * a (n + 2) = (0 : ℚ) * a (n + 1) + (((4 : ℚ) * ((n : ℚ) + 1)) + (16 : ℚ)) * a n) :
    ∀ n, a n = p205 n := by
  apply general_second_unique p205_valid
  exact linear_second_certificate a (6 : ℚ) (0 : ℚ) (fun n => ((n : ℚ) + 1)) (fun n => (0 : ℚ)) (fun n => (((4 : ℚ) * ((n : ℚ) + 1)) + (16 : ℚ))) hi hj (by intro n; positivity) ha
#print axioms p205_valid
#print axioms p205_unique

def p191 (n : ℕ) : ℚ := (((n : ℚ) + 1) * (((2 : ℚ) ^ n) + ((1 : ℚ) ^ n)))
theorem p191_valid : GeneralSecondCertificate p191 (2 : ℚ) (6 : ℚ) (fun n x y => (((3 : ℚ) * ((n : ℚ) + 1) * (((n : ℚ) + 1) + (2 : ℚ))) * y + ((-2 : ℚ) * (((n : ℚ) + 1) + (1 : ℚ)) * (((n : ℚ) + 1) + (2 : ℚ))) * x) / (((n : ℚ) + 1) * (((n : ℚ) + 1) + (1 : ℚ)))) := by
  apply linear_second_certificate p191 (2 : ℚ) (6 : ℚ) (fun n => (((n : ℚ) + 1) * (((n : ℚ) + 1) + (1 : ℚ)))) (fun n => ((3 : ℚ) * ((n : ℚ) + 1) * (((n : ℚ) + 1) + (2 : ℚ)))) (fun n => ((-2 : ℚ) * (((n : ℚ) + 1) + (1 : ℚ)) * (((n : ℚ) + 1) + (2 : ℚ))))
  · norm_num [p191]
  · norm_num [p191]
  · intro n; positivity
  · intro n
    simp only [p191, Nat.cast_add, Nat.cast_one, pow_succ, pow_add] at *
    ring
theorem p191_unique (a : ℕ → ℚ) (hi : a 0 = (2 : ℚ)) (hj : a 1 = (6 : ℚ))
    (ha : ∀ n : ℕ, (((n : ℚ) + 1) * (((n : ℚ) + 1) + (1 : ℚ))) * a (n + 2) = ((3 : ℚ) * ((n : ℚ) + 1) * (((n : ℚ) + 1) + (2 : ℚ))) * a (n + 1) + ((-2 : ℚ) * (((n : ℚ) + 1) + (1 : ℚ)) * (((n : ℚ) + 1) + (2 : ℚ))) * a n) :
    ∀ n, a n = p191 n := by
  apply general_second_unique p191_valid
  exact linear_second_certificate a (2 : ℚ) (6 : ℚ) (fun n => (((n : ℚ) + 1) * (((n : ℚ) + 1) + (1 : ℚ)))) (fun n => ((3 : ℚ) * ((n : ℚ) + 1) * (((n : ℚ) + 1) + (2 : ℚ)))) (fun n => ((-2 : ℚ) * (((n : ℚ) + 1) + (1 : ℚ)) * (((n : ℚ) + 1) + (2 : ℚ)))) hi hj (by intro n; positivity) ha
#print axioms p191_valid
#print axioms p191_unique

def p201 (n : ℕ) : ℚ := ((((3 : ℚ) ^ n) + ((1 : ℚ) ^ n)) / (((n : ℚ) + 1) * (((n : ℚ) + 1) + (1 : ℚ))))
theorem p201_valid : GeneralSecondCertificate p201 (1 : ℚ) ((2 : ℚ) / 3) (fun n x y => (((4 : ℚ) * (((n : ℚ) + 1) + (1 : ℚ)) * (((n : ℚ) + 1) + (2 : ℚ))) * y + ((-3 : ℚ) * ((n : ℚ) + 1) * (((n : ℚ) + 1) + (1 : ℚ))) * x) / ((((n : ℚ) + 1) + (2 : ℚ)) * (((n : ℚ) + 1) + (3 : ℚ)))) := by
  apply linear_second_certificate p201 (1 : ℚ) ((2 : ℚ) / 3) (fun n => ((((n : ℚ) + 1) + (2 : ℚ)) * (((n : ℚ) + 1) + (3 : ℚ)))) (fun n => ((4 : ℚ) * (((n : ℚ) + 1) + (1 : ℚ)) * (((n : ℚ) + 1) + (2 : ℚ)))) (fun n => ((-3 : ℚ) * ((n : ℚ) + 1) * (((n : ℚ) + 1) + (1 : ℚ))))
  · norm_num [p201]
  · norm_num [p201]
  · intro n; positivity
  · intro n
    have h0_0 : (((n : ℚ) + 1) * (((n : ℚ) + 1) + (1 : ℚ))) ≠ 0 := by positivity
    have h1_0 : ((((n + 1) : ℚ) + 1) * ((((n + 1) : ℚ) + 1) + (1 : ℚ))) ≠ 0 := by positivity
    have h2_0 : ((((n + 2) : ℚ) + 1) * ((((n + 2) : ℚ) + 1) + (1 : ℚ))) ≠ 0 := by positivity
    simp only [p201, Nat.cast_add, Nat.cast_one, pow_succ, pow_add] at *
    field_simp [h0_0, h1_0, h2_0] <;> ring
theorem p201_unique (a : ℕ → ℚ) (hi : a 0 = (1 : ℚ)) (hj : a 1 = ((2 : ℚ) / 3))
    (ha : ∀ n : ℕ, ((((n : ℚ) + 1) + (2 : ℚ)) * (((n : ℚ) + 1) + (3 : ℚ))) * a (n + 2) = ((4 : ℚ) * (((n : ℚ) + 1) + (1 : ℚ)) * (((n : ℚ) + 1) + (2 : ℚ))) * a (n + 1) + ((-3 : ℚ) * ((n : ℚ) + 1) * (((n : ℚ) + 1) + (1 : ℚ))) * a n) :
    ∀ n, a n = p201 n := by
  apply general_second_unique p201_valid
  exact linear_second_certificate a (1 : ℚ) ((2 : ℚ) / 3) (fun n => ((((n : ℚ) + 1) + (2 : ℚ)) * (((n : ℚ) + 1) + (3 : ℚ)))) (fun n => ((4 : ℚ) * (((n : ℚ) + 1) + (1 : ℚ)) * (((n : ℚ) + 1) + (2 : ℚ)))) (fun n => ((-3 : ℚ) * ((n : ℚ) + 1) * (((n : ℚ) + 1) + (1 : ℚ)))) hi hj (by intro n; positivity) ha
#print axioms p201_valid
#print axioms p201_unique

def p247 (n : ℕ) : ℚ := ((((2 : ℚ) ^ n) + ((-1 : ℚ) ^ n)) / (((n : ℚ) + 1) ^ 2))
theorem p247_valid : GeneralSecondCertificate p247 (2 : ℚ) ((1 : ℚ) / 4) (fun n x y => (((((n : ℚ) + 1) + (1 : ℚ)) ^ 2) * y + ((2 : ℚ) * (((n : ℚ) + 1) ^ 2)) * x) / ((((n : ℚ) + 1) + (2 : ℚ)) ^ 2)) := by
  apply linear_second_certificate p247 (2 : ℚ) ((1 : ℚ) / 4) (fun n => ((((n : ℚ) + 1) + (2 : ℚ)) ^ 2)) (fun n => ((((n : ℚ) + 1) + (1 : ℚ)) ^ 2)) (fun n => ((2 : ℚ) * (((n : ℚ) + 1) ^ 2)))
  · norm_num [p247]
  · norm_num [p247]
  · intro n; positivity
  · intro n
    have h0_0 : (((n : ℚ) + 1) ^ 2) ≠ 0 := by positivity
    have h1_0 : ((((n + 1) : ℚ) + 1) ^ 2) ≠ 0 := by positivity
    have h2_0 : ((((n + 2) : ℚ) + 1) ^ 2) ≠ 0 := by positivity
    simp only [p247, Nat.cast_add, Nat.cast_one, pow_succ, pow_add] at *
    field_simp [h0_0, h1_0, h2_0] <;> ring
theorem p247_unique (a : ℕ → ℚ) (hi : a 0 = (2 : ℚ)) (hj : a 1 = ((1 : ℚ) / 4))
    (ha : ∀ n : ℕ, ((((n : ℚ) + 1) + (2 : ℚ)) ^ 2) * a (n + 2) = ((((n : ℚ) + 1) + (1 : ℚ)) ^ 2) * a (n + 1) + ((2 : ℚ) * (((n : ℚ) + 1) ^ 2)) * a n) :
    ∀ n, a n = p247 n := by
  apply general_second_unique p247_valid
  exact linear_second_certificate a (2 : ℚ) ((1 : ℚ) / 4) (fun n => ((((n : ℚ) + 1) + (2 : ℚ)) ^ 2)) (fun n => ((((n : ℚ) + 1) + (1 : ℚ)) ^ 2)) (fun n => ((2 : ℚ) * (((n : ℚ) + 1) ^ 2))) hi hj (by intro n; positivity) ha
#print axioms p247_valid
#print axioms p247_unique

def p174 (n : ℕ) : ℚ := ((((n : ℚ) + 1) ^ 2) * (((2 : ℚ) ^ n) + ((-2 : ℚ) ^ n)))
theorem p174_valid : GeneralSecondCertificate p174 (2 : ℚ) (0 : ℚ) (fun n x y => ((0 : ℚ) * y + (((4 : ℚ) * (((n : ℚ) + 1) ^ 2)) + ((16 : ℚ) * ((n : ℚ) + 1)) + (16 : ℚ)) * x) / (((n : ℚ) + 1) ^ 2)) := by
  apply linear_second_certificate p174 (2 : ℚ) (0 : ℚ) (fun n => (((n : ℚ) + 1) ^ 2)) (fun n => (0 : ℚ)) (fun n => (((4 : ℚ) * (((n : ℚ) + 1) ^ 2)) + ((16 : ℚ) * ((n : ℚ) + 1)) + (16 : ℚ)))
  · norm_num [p174]
  · norm_num [p174]
  · intro n; positivity
  · intro n
    simp only [p174, Nat.cast_add, Nat.cast_one, pow_succ, pow_add] at *
    ring
theorem p174_unique (a : ℕ → ℚ) (hi : a 0 = (2 : ℚ)) (hj : a 1 = (0 : ℚ))
    (ha : ∀ n : ℕ, (((n : ℚ) + 1) ^ 2) * a (n + 2) = (0 : ℚ) * a (n + 1) + (((4 : ℚ) * (((n : ℚ) + 1) ^ 2)) + ((16 : ℚ) * ((n : ℚ) + 1)) + (16 : ℚ)) * a n) :
    ∀ n, a n = p174 n := by
  apply general_second_unique p174_valid
  exact linear_second_certificate a (2 : ℚ) (0 : ℚ) (fun n => (((n : ℚ) + 1) ^ 2)) (fun n => (0 : ℚ)) (fun n => (((4 : ℚ) * (((n : ℚ) + 1) ^ 2)) + ((16 : ℚ) * ((n : ℚ) + 1)) + (16 : ℚ))) hi hj (by intro n; positivity) ha
#print axioms p174_valid
#print axioms p174_unique

def p199 (n : ℕ) : ℚ := ((((n : ℚ) + 1) + (1 : ℚ)) * (((3 : ℚ) ^ n) + ((-2 : ℚ) ^ n)))
theorem p199_valid : GeneralSecondCertificate p199 (4 : ℚ) (3 : ℚ) (fun n x y => (((((n : ℚ) + 1) + (1 : ℚ)) * (((n : ℚ) + 1) + (3 : ℚ))) * y + ((6 : ℚ) * (((n : ℚ) + 1) + (2 : ℚ)) * (((n : ℚ) + 1) + (3 : ℚ))) * x) / ((((n : ℚ) + 1) + (1 : ℚ)) * (((n : ℚ) + 1) + (2 : ℚ)))) := by
  apply linear_second_certificate p199 (4 : ℚ) (3 : ℚ) (fun n => ((((n : ℚ) + 1) + (1 : ℚ)) * (((n : ℚ) + 1) + (2 : ℚ)))) (fun n => ((((n : ℚ) + 1) + (1 : ℚ)) * (((n : ℚ) + 1) + (3 : ℚ)))) (fun n => ((6 : ℚ) * (((n : ℚ) + 1) + (2 : ℚ)) * (((n : ℚ) + 1) + (3 : ℚ))))
  · norm_num [p199]
  · norm_num [p199]
  · intro n; positivity
  · intro n
    simp only [p199, Nat.cast_add, Nat.cast_one, pow_succ, pow_add] at *
    ring
theorem p199_unique (a : ℕ → ℚ) (hi : a 0 = (4 : ℚ)) (hj : a 1 = (3 : ℚ))
    (ha : ∀ n : ℕ, ((((n : ℚ) + 1) + (1 : ℚ)) * (((n : ℚ) + 1) + (2 : ℚ))) * a (n + 2) = ((((n : ℚ) + 1) + (1 : ℚ)) * (((n : ℚ) + 1) + (3 : ℚ))) * a (n + 1) + ((6 : ℚ) * (((n : ℚ) + 1) + (2 : ℚ)) * (((n : ℚ) + 1) + (3 : ℚ))) * a n) :
    ∀ n, a n = p199 n := by
  apply general_second_unique p199_valid
  exact linear_second_certificate a (4 : ℚ) (3 : ℚ) (fun n => ((((n : ℚ) + 1) + (1 : ℚ)) * (((n : ℚ) + 1) + (2 : ℚ)))) (fun n => ((((n : ℚ) + 1) + (1 : ℚ)) * (((n : ℚ) + 1) + (3 : ℚ)))) (fun n => ((6 : ℚ) * (((n : ℚ) + 1) + (2 : ℚ)) * (((n : ℚ) + 1) + (3 : ℚ)))) hi hj (by intro n; positivity) ha
#print axioms p199_valid
#print axioms p199_unique

def p233 (n : ℕ) : ℚ := ((((2 : ℚ) * ((n : ℚ) + 1)) + (1 : ℚ)) * (((3 : ℚ) ^ n) + ((4 : ℚ) ^ n)))
theorem p233_valid : GeneralSecondCertificate p233 (6 : ℚ) (35 : ℚ) (fun n x y => (((7 : ℚ) * (((2 : ℚ) * ((n : ℚ) + 1)) + (1 : ℚ)) * (((2 : ℚ) * ((n : ℚ) + 1)) + (5 : ℚ))) * y + ((-12 : ℚ) * (((2 : ℚ) * ((n : ℚ) + 1)) + (3 : ℚ)) * (((2 : ℚ) * ((n : ℚ) + 1)) + (5 : ℚ))) * x) / ((((2 : ℚ) * ((n : ℚ) + 1)) + (1 : ℚ)) * (((2 : ℚ) * ((n : ℚ) + 1)) + (3 : ℚ)))) := by
  apply linear_second_certificate p233 (6 : ℚ) (35 : ℚ) (fun n => ((((2 : ℚ) * ((n : ℚ) + 1)) + (1 : ℚ)) * (((2 : ℚ) * ((n : ℚ) + 1)) + (3 : ℚ)))) (fun n => ((7 : ℚ) * (((2 : ℚ) * ((n : ℚ) + 1)) + (1 : ℚ)) * (((2 : ℚ) * ((n : ℚ) + 1)) + (5 : ℚ)))) (fun n => ((-12 : ℚ) * (((2 : ℚ) * ((n : ℚ) + 1)) + (3 : ℚ)) * (((2 : ℚ) * ((n : ℚ) + 1)) + (5 : ℚ))))
  · norm_num [p233]
  · norm_num [p233]
  · intro n; positivity
  · intro n
    simp only [p233, Nat.cast_add, Nat.cast_one, pow_succ, pow_add] at *
    ring
theorem p233_unique (a : ℕ → ℚ) (hi : a 0 = (6 : ℚ)) (hj : a 1 = (35 : ℚ))
    (ha : ∀ n : ℕ, ((((2 : ℚ) * ((n : ℚ) + 1)) + (1 : ℚ)) * (((2 : ℚ) * ((n : ℚ) + 1)) + (3 : ℚ))) * a (n + 2) = ((7 : ℚ) * (((2 : ℚ) * ((n : ℚ) + 1)) + (1 : ℚ)) * (((2 : ℚ) * ((n : ℚ) + 1)) + (5 : ℚ))) * a (n + 1) + ((-12 : ℚ) * (((2 : ℚ) * ((n : ℚ) + 1)) + (3 : ℚ)) * (((2 : ℚ) * ((n : ℚ) + 1)) + (5 : ℚ))) * a n) :
    ∀ n, a n = p233 n := by
  apply general_second_unique p233_valid
  exact linear_second_certificate a (6 : ℚ) (35 : ℚ) (fun n => ((((2 : ℚ) * ((n : ℚ) + 1)) + (1 : ℚ)) * (((2 : ℚ) * ((n : ℚ) + 1)) + (3 : ℚ)))) (fun n => ((7 : ℚ) * (((2 : ℚ) * ((n : ℚ) + 1)) + (1 : ℚ)) * (((2 : ℚ) * ((n : ℚ) + 1)) + (5 : ℚ)))) (fun n => ((-12 : ℚ) * (((2 : ℚ) * ((n : ℚ) + 1)) + (3 : ℚ)) * (((2 : ℚ) * ((n : ℚ) + 1)) + (5 : ℚ)))) hi hj (by intro n; positivity) ha
#print axioms p233_valid
#print axioms p233_unique

def p217 (n : ℕ) : ℚ := (((n : ℚ) + 1) * (((n : ℚ) + 1) + (1 : ℚ)) * (((2 : ℚ) * ((2 : ℚ) ^ n)) + ((3 : ℚ) * ((-1 : ℚ) ^ n))))
theorem p217_valid : GeneralSecondCertificate p217 (10 : ℚ) (6 : ℚ) (fun n x y => (((((n : ℚ) + 1) ^ 2) + ((3 : ℚ) * ((n : ℚ) + 1))) * y + (((2 : ℚ) * (((n : ℚ) + 1) ^ 2)) + ((10 : ℚ) * ((n : ℚ) + 1)) + (12 : ℚ)) * x) / ((((n : ℚ) + 1) ^ 2) + ((n : ℚ) + 1))) := by
  apply linear_second_certificate p217 (10 : ℚ) (6 : ℚ) (fun n => ((((n : ℚ) + 1) ^ 2) + ((n : ℚ) + 1))) (fun n => ((((n : ℚ) + 1) ^ 2) + ((3 : ℚ) * ((n : ℚ) + 1)))) (fun n => (((2 : ℚ) * (((n : ℚ) + 1) ^ 2)) + ((10 : ℚ) * ((n : ℚ) + 1)) + (12 : ℚ)))
  · norm_num [p217]
  · norm_num [p217]
  · intro n; positivity
  · intro n
    simp only [p217, Nat.cast_add, Nat.cast_one, pow_succ, pow_add] at *
    ring
theorem p217_unique (a : ℕ → ℚ) (hi : a 0 = (10 : ℚ)) (hj : a 1 = (6 : ℚ))
    (ha : ∀ n : ℕ, ((((n : ℚ) + 1) ^ 2) + ((n : ℚ) + 1)) * a (n + 2) = ((((n : ℚ) + 1) ^ 2) + ((3 : ℚ) * ((n : ℚ) + 1))) * a (n + 1) + (((2 : ℚ) * (((n : ℚ) + 1) ^ 2)) + ((10 : ℚ) * ((n : ℚ) + 1)) + (12 : ℚ)) * a n) :
    ∀ n, a n = p217 n := by
  apply general_second_unique p217_valid
  exact linear_second_certificate a (10 : ℚ) (6 : ℚ) (fun n => ((((n : ℚ) + 1) ^ 2) + ((n : ℚ) + 1))) (fun n => ((((n : ℚ) + 1) ^ 2) + ((3 : ℚ) * ((n : ℚ) + 1)))) (fun n => (((2 : ℚ) * (((n : ℚ) + 1) ^ 2)) + ((10 : ℚ) * ((n : ℚ) + 1)) + (12 : ℚ))) hi hj (by intro n; positivity) ha
#print axioms p217_valid
#print axioms p217_unique

def p134 (n : ℕ) : ℚ := (((((n : ℚ) + 1) + (-2 : ℚ)) * ((2 : ℚ) ^ n)) + (2 : ℚ))
theorem p134_valid : GeneralSecondCertificate p134 (1 : ℚ) (2 : ℚ) (fun n x y => ((((3 : ℚ) * ((n : ℚ) + 1)) + (2 : ℚ)) * y + ((-2 : ℚ) * (((n : ℚ) + 1) + (1 : ℚ))) * x) / ((n : ℚ) + 1)) := by
  apply linear_second_certificate p134 (1 : ℚ) (2 : ℚ) (fun n => ((n : ℚ) + 1)) (fun n => (((3 : ℚ) * ((n : ℚ) + 1)) + (2 : ℚ))) (fun n => ((-2 : ℚ) * (((n : ℚ) + 1) + (1 : ℚ))))
  · norm_num [p134]
  · norm_num [p134]
  · intro n; positivity
  · intro n
    simp only [p134, Nat.cast_add, Nat.cast_one, pow_succ, pow_add] at *
    ring
theorem p134_unique (a : ℕ → ℚ) (hi : a 0 = (1 : ℚ)) (hj : a 1 = (2 : ℚ))
    (ha : ∀ n : ℕ, ((n : ℚ) + 1) * a (n + 2) = (((3 : ℚ) * ((n : ℚ) + 1)) + (2 : ℚ)) * a (n + 1) + ((-2 : ℚ) * (((n : ℚ) + 1) + (1 : ℚ))) * a n) :
    ∀ n, a n = p134 n := by
  apply general_second_unique p134_valid
  exact linear_second_certificate a (1 : ℚ) (2 : ℚ) (fun n => ((n : ℚ) + 1)) (fun n => (((3 : ℚ) * ((n : ℚ) + 1)) + (2 : ℚ))) (fun n => ((-2 : ℚ) * (((n : ℚ) + 1) + (1 : ℚ)))) hi hj (by intro n; positivity) ha
#print axioms p134_valid
#print axioms p134_unique

def p176 (n : ℕ) : ℚ := ((((((1 : ℚ) / 2) * ((n : ℚ) + 1)) + ((-1 : ℚ) / 4)) * ((3 : ℚ) ^ n)) + ((3 : ℚ) / 4))
theorem p176_valid : GeneralSecondCertificate p176 (1 : ℚ) (3 : ℚ) (fun n x y => ((((4 : ℚ) * ((n : ℚ) + 1)) + (7 : ℚ)) * y + ((-3 : ℚ) * (((n : ℚ) + 1) + (2 : ℚ))) * x) / (((n : ℚ) + 1) + (1 : ℚ))) := by
  apply linear_second_certificate p176 (1 : ℚ) (3 : ℚ) (fun n => (((n : ℚ) + 1) + (1 : ℚ))) (fun n => (((4 : ℚ) * ((n : ℚ) + 1)) + (7 : ℚ))) (fun n => ((-3 : ℚ) * (((n : ℚ) + 1) + (2 : ℚ))))
  · norm_num [p176]
  · norm_num [p176]
  · intro n; positivity
  · intro n
    simp only [p176, Nat.cast_add, Nat.cast_one, pow_succ, pow_add] at *
    ring
theorem p176_unique (a : ℕ → ℚ) (hi : a 0 = (1 : ℚ)) (hj : a 1 = (3 : ℚ))
    (ha : ∀ n : ℕ, (((n : ℚ) + 1) + (1 : ℚ)) * a (n + 2) = (((4 : ℚ) * ((n : ℚ) + 1)) + (7 : ℚ)) * a (n + 1) + ((-3 : ℚ) * (((n : ℚ) + 1) + (2 : ℚ))) * a n) :
    ∀ n, a n = p176 n := by
  apply general_second_unique p176_valid
  exact linear_second_certificate a (1 : ℚ) (3 : ℚ) (fun n => (((n : ℚ) + 1) + (1 : ℚ))) (fun n => (((4 : ℚ) * ((n : ℚ) + 1)) + (7 : ℚ))) (fun n => ((-3 : ℚ) * (((n : ℚ) + 1) + (2 : ℚ)))) hi hj (by intro n; positivity) ha
#print axioms p176_valid
#print axioms p176_unique

def p146 (n : ℕ) : ℚ := (((((2 : ℚ) * ((n : ℚ) + 1)) + (-3 : ℚ)) * ((2 : ℚ) ^ n)) + (2 : ℚ))
theorem p146_valid : GeneralSecondCertificate p146 (1 : ℚ) (4 : ℚ) (fun n x y => ((((6 : ℚ) * ((n : ℚ) + 1)) + (7 : ℚ)) * y + ((-2 : ℚ) * (((2 : ℚ) * ((n : ℚ) + 1)) + (3 : ℚ))) * x) / (((2 : ℚ) * ((n : ℚ) + 1)) + (1 : ℚ))) := by
  apply linear_second_certificate p146 (1 : ℚ) (4 : ℚ) (fun n => (((2 : ℚ) * ((n : ℚ) + 1)) + (1 : ℚ))) (fun n => (((6 : ℚ) * ((n : ℚ) + 1)) + (7 : ℚ))) (fun n => ((-2 : ℚ) * (((2 : ℚ) * ((n : ℚ) + 1)) + (3 : ℚ))))
  · norm_num [p146]
  · norm_num [p146]
  · intro n; positivity
  · intro n
    simp only [p146, Nat.cast_add, Nat.cast_one, pow_succ, pow_add] at *
    ring
theorem p146_unique (a : ℕ → ℚ) (hi : a 0 = (1 : ℚ)) (hj : a 1 = (4 : ℚ))
    (ha : ∀ n : ℕ, (((2 : ℚ) * ((n : ℚ) + 1)) + (1 : ℚ)) * a (n + 2) = (((6 : ℚ) * ((n : ℚ) + 1)) + (7 : ℚ)) * a (n + 1) + ((-2 : ℚ) * (((2 : ℚ) * ((n : ℚ) + 1)) + (3 : ℚ))) * a n) :
    ∀ n, a n = p146 n := by
  apply general_second_unique p146_valid
  exact linear_second_certificate a (1 : ℚ) (4 : ℚ) (fun n => (((2 : ℚ) * ((n : ℚ) + 1)) + (1 : ℚ))) (fun n => (((6 : ℚ) * ((n : ℚ) + 1)) + (7 : ℚ))) (fun n => ((-2 : ℚ) * (((2 : ℚ) * ((n : ℚ) + 1)) + (3 : ℚ)))) hi hj (by intro n; positivity) ha
#print axioms p146_valid
#print axioms p146_unique

def p153 (n : ℕ) : ℚ := ((((((1 : ℚ) / 2) * ((n : ℚ) + 1)) + ((-3 : ℚ) / 4)) * ((3 : ℚ) ^ n)) + ((5 : ℚ) / 4))
theorem p153_valid : GeneralSecondCertificate p153 (1 : ℚ) (2 : ℚ) (fun n x y => ((((4 : ℚ) * ((n : ℚ) + 1)) + (3 : ℚ)) * y + ((-3 : ℚ) * (((n : ℚ) + 1) + (1 : ℚ))) * x) / ((n : ℚ) + 1)) := by
  apply linear_second_certificate p153 (1 : ℚ) (2 : ℚ) (fun n => ((n : ℚ) + 1)) (fun n => (((4 : ℚ) * ((n : ℚ) + 1)) + (3 : ℚ))) (fun n => ((-3 : ℚ) * (((n : ℚ) + 1) + (1 : ℚ))))
  · norm_num [p153]
  · norm_num [p153]
  · intro n; positivity
  · intro n
    simp only [p153, Nat.cast_add, Nat.cast_one, pow_succ, pow_add] at *
    ring
theorem p153_unique (a : ℕ → ℚ) (hi : a 0 = (1 : ℚ)) (hj : a 1 = (2 : ℚ))
    (ha : ∀ n : ℕ, ((n : ℚ) + 1) * a (n + 2) = (((4 : ℚ) * ((n : ℚ) + 1)) + (3 : ℚ)) * a (n + 1) + ((-3 : ℚ) * (((n : ℚ) + 1) + (1 : ℚ))) * a n) :
    ∀ n, a n = p153 n := by
  apply general_second_unique p153_valid
  exact linear_second_certificate a (1 : ℚ) (2 : ℚ) (fun n => ((n : ℚ) + 1)) (fun n => (((4 : ℚ) * ((n : ℚ) + 1)) + (3 : ℚ))) (fun n => ((-3 : ℚ) * (((n : ℚ) + 1) + (1 : ℚ)))) hi hj (by intro n; positivity) ha
#print axioms p153_valid
#print axioms p153_unique

def p156 (n : ℕ) : ℚ := ((((((1 : ℚ) / 2) * ((n : ℚ) + 1)) + ((-1 : ℚ) / 2)) * ((2 : ℚ) ^ n)) + (1 : ℚ))
theorem p156_valid : GeneralSecondCertificate p156 (1 : ℚ) (2 : ℚ) (fun n x y => ((((3 : ℚ) * ((n : ℚ) + 1)) + (5 : ℚ)) * y + ((-2 : ℚ) * (((n : ℚ) + 1) + (2 : ℚ))) * x) / (((n : ℚ) + 1) + (1 : ℚ))) := by
  apply linear_second_certificate p156 (1 : ℚ) (2 : ℚ) (fun n => (((n : ℚ) + 1) + (1 : ℚ))) (fun n => (((3 : ℚ) * ((n : ℚ) + 1)) + (5 : ℚ))) (fun n => ((-2 : ℚ) * (((n : ℚ) + 1) + (2 : ℚ))))
  · norm_num [p156]
  · norm_num [p156]
  · intro n; positivity
  · intro n
    simp only [p156, Nat.cast_add, Nat.cast_one, pow_succ, pow_add] at *
    ring
theorem p156_unique (a : ℕ → ℚ) (hi : a 0 = (1 : ℚ)) (hj : a 1 = (2 : ℚ))
    (ha : ∀ n : ℕ, (((n : ℚ) + 1) + (1 : ℚ)) * a (n + 2) = (((3 : ℚ) * ((n : ℚ) + 1)) + (5 : ℚ)) * a (n + 1) + ((-2 : ℚ) * (((n : ℚ) + 1) + (2 : ℚ))) * a n) :
    ∀ n, a n = p156 n := by
  apply general_second_unique p156_valid
  exact linear_second_certificate a (1 : ℚ) (2 : ℚ) (fun n => (((n : ℚ) + 1) + (1 : ℚ))) (fun n => (((3 : ℚ) * ((n : ℚ) + 1)) + (5 : ℚ))) (fun n => ((-2 : ℚ) * (((n : ℚ) + 1) + (2 : ℚ)))) hi hj (by intro n; positivity) ha
#print axioms p156_valid
#print axioms p156_unique

def p133 (n : ℕ) : ℚ := (((((3 : ℚ) * ((n : ℚ) + 1)) + (-3 : ℚ)) * ((3 : ℚ) ^ n)) + (1 : ℚ))
theorem p133_valid : GeneralSecondCertificate p133 (1 : ℚ) (10 : ℚ) (fun n x y => ((((8 : ℚ) * ((n : ℚ) + 1)) + (10 : ℚ)) * y + ((-3 : ℚ) * (((2 : ℚ) * ((n : ℚ) + 1)) + (3 : ℚ))) * x) / (((2 : ℚ) * ((n : ℚ) + 1)) + (1 : ℚ))) := by
  apply linear_second_certificate p133 (1 : ℚ) (10 : ℚ) (fun n => (((2 : ℚ) * ((n : ℚ) + 1)) + (1 : ℚ))) (fun n => (((8 : ℚ) * ((n : ℚ) + 1)) + (10 : ℚ))) (fun n => ((-3 : ℚ) * (((2 : ℚ) * ((n : ℚ) + 1)) + (3 : ℚ))))
  · norm_num [p133]
  · norm_num [p133]
  · intro n; positivity
  · intro n
    simp only [p133, Nat.cast_add, Nat.cast_one, pow_succ, pow_add] at *
    ring
theorem p133_unique (a : ℕ → ℚ) (hi : a 0 = (1 : ℚ)) (hj : a 1 = (10 : ℚ))
    (ha : ∀ n : ℕ, (((2 : ℚ) * ((n : ℚ) + 1)) + (1 : ℚ)) * a (n + 2) = (((8 : ℚ) * ((n : ℚ) + 1)) + (10 : ℚ)) * a (n + 1) + ((-3 : ℚ) * (((2 : ℚ) * ((n : ℚ) + 1)) + (3 : ℚ))) * a n) :
    ∀ n, a n = p133 n := by
  apply general_second_unique p133_valid
  exact linear_second_certificate a (1 : ℚ) (10 : ℚ) (fun n => (((2 : ℚ) * ((n : ℚ) + 1)) + (1 : ℚ))) (fun n => (((8 : ℚ) * ((n : ℚ) + 1)) + (10 : ℚ))) (fun n => ((-3 : ℚ) * (((2 : ℚ) * ((n : ℚ) + 1)) + (3 : ℚ)))) hi hj (by intro n; positivity) ha
#print axioms p133_valid
#print axioms p133_unique

def p129 (n : ℕ) : ℚ := (((((2 : ℚ) * ((n : ℚ) + 1)) + (-4 : ℚ)) * ((2 : ℚ) ^ n)) + (3 : ℚ))
theorem p129_valid : GeneralSecondCertificate p129 (1 : ℚ) (3 : ℚ) (fun n x y => ((((3 : ℚ) * ((n : ℚ) + 1)) + (2 : ℚ)) * y + ((-2 : ℚ) * (((n : ℚ) + 1) + (1 : ℚ))) * x) / ((n : ℚ) + 1)) := by
  apply linear_second_certificate p129 (1 : ℚ) (3 : ℚ) (fun n => ((n : ℚ) + 1)) (fun n => (((3 : ℚ) * ((n : ℚ) + 1)) + (2 : ℚ))) (fun n => ((-2 : ℚ) * (((n : ℚ) + 1) + (1 : ℚ))))
  · norm_num [p129]
  · norm_num [p129]
  · intro n; positivity
  · intro n
    simp only [p129, Nat.cast_add, Nat.cast_one, pow_succ, pow_add] at *
    ring
theorem p129_unique (a : ℕ → ℚ) (hi : a 0 = (1 : ℚ)) (hj : a 1 = (3 : ℚ))
    (ha : ∀ n : ℕ, ((n : ℚ) + 1) * a (n + 2) = (((3 : ℚ) * ((n : ℚ) + 1)) + (2 : ℚ)) * a (n + 1) + ((-2 : ℚ) * (((n : ℚ) + 1) + (1 : ℚ))) * a n) :
    ∀ n, a n = p129 n := by
  apply general_second_unique p129_valid
  exact linear_second_certificate a (1 : ℚ) (3 : ℚ) (fun n => ((n : ℚ) + 1)) (fun n => (((3 : ℚ) * ((n : ℚ) + 1)) + (2 : ℚ))) (fun n => ((-2 : ℚ) * (((n : ℚ) + 1) + (1 : ℚ)))) hi hj (by intro n; positivity) ha
#print axioms p129_valid
#print axioms p129_unique

def p212 (n : ℕ) : ℚ := (((((n : ℚ) + 1) + ((-1 : ℚ) / 2)) * ((3 : ℚ) ^ n)) + ((1 : ℚ) / 2))
theorem p212_valid : GeneralSecondCertificate p212 (1 : ℚ) (5 : ℚ) (fun n x y => ((((4 : ℚ) * ((n : ℚ) + 1)) + (7 : ℚ)) * y + ((-3 : ℚ) * (((n : ℚ) + 1) + (2 : ℚ))) * x) / (((n : ℚ) + 1) + (1 : ℚ))) := by
  apply linear_second_certificate p212 (1 : ℚ) (5 : ℚ) (fun n => (((n : ℚ) + 1) + (1 : ℚ))) (fun n => (((4 : ℚ) * ((n : ℚ) + 1)) + (7 : ℚ))) (fun n => ((-3 : ℚ) * (((n : ℚ) + 1) + (2 : ℚ))))
  · norm_num [p212]
  · norm_num [p212]
  · intro n; positivity
  · intro n
    simp only [p212, Nat.cast_add, Nat.cast_one, pow_succ, pow_add] at *
    ring
theorem p212_unique (a : ℕ → ℚ) (hi : a 0 = (1 : ℚ)) (hj : a 1 = (5 : ℚ))
    (ha : ∀ n : ℕ, (((n : ℚ) + 1) + (1 : ℚ)) * a (n + 2) = (((4 : ℚ) * ((n : ℚ) + 1)) + (7 : ℚ)) * a (n + 1) + ((-3 : ℚ) * (((n : ℚ) + 1) + (2 : ℚ))) * a n) :
    ∀ n, a n = p212 n := by
  apply general_second_unique p212_valid
  exact linear_second_certificate a (1 : ℚ) (5 : ℚ) (fun n => (((n : ℚ) + 1) + (1 : ℚ))) (fun n => (((4 : ℚ) * ((n : ℚ) + 1)) + (7 : ℚ))) (fun n => ((-3 : ℚ) * (((n : ℚ) + 1) + (2 : ℚ)))) hi hj (by intro n; positivity) ha
#print axioms p212_valid
#print axioms p212_unique

def p161 (n : ℕ) : ℚ := (((((4 : ℚ) * ((n : ℚ) + 1)) + (-6 : ℚ)) * ((2 : ℚ) ^ n)) + (3 : ℚ))
theorem p161_valid : GeneralSecondCertificate p161 (1 : ℚ) (7 : ℚ) (fun n x y => ((((6 : ℚ) * ((n : ℚ) + 1)) + (7 : ℚ)) * y + ((-2 : ℚ) * (((2 : ℚ) * ((n : ℚ) + 1)) + (3 : ℚ))) * x) / (((2 : ℚ) * ((n : ℚ) + 1)) + (1 : ℚ))) := by
  apply linear_second_certificate p161 (1 : ℚ) (7 : ℚ) (fun n => (((2 : ℚ) * ((n : ℚ) + 1)) + (1 : ℚ))) (fun n => (((6 : ℚ) * ((n : ℚ) + 1)) + (7 : ℚ))) (fun n => ((-2 : ℚ) * (((2 : ℚ) * ((n : ℚ) + 1)) + (3 : ℚ))))
  · norm_num [p161]
  · norm_num [p161]
  · intro n; positivity
  · intro n
    simp only [p161, Nat.cast_add, Nat.cast_one, pow_succ, pow_add] at *
    ring
theorem p161_unique (a : ℕ → ℚ) (hi : a 0 = (1 : ℚ)) (hj : a 1 = (7 : ℚ))
    (ha : ∀ n : ℕ, (((2 : ℚ) * ((n : ℚ) + 1)) + (1 : ℚ)) * a (n + 2) = (((6 : ℚ) * ((n : ℚ) + 1)) + (7 : ℚ)) * a (n + 1) + ((-2 : ℚ) * (((2 : ℚ) * ((n : ℚ) + 1)) + (3 : ℚ))) * a n) :
    ∀ n, a n = p161 n := by
  apply general_second_unique p161_valid
  exact linear_second_certificate a (1 : ℚ) (7 : ℚ) (fun n => (((2 : ℚ) * ((n : ℚ) + 1)) + (1 : ℚ))) (fun n => (((6 : ℚ) * ((n : ℚ) + 1)) + (7 : ℚ))) (fun n => ((-2 : ℚ) * (((2 : ℚ) * ((n : ℚ) + 1)) + (3 : ℚ)))) hi hj (by intro n; positivity) ha
#print axioms p161_valid
#print axioms p161_unique

def p158 (n : ℕ) : ℚ := (((((n : ℚ) + 1) + ((-3 : ℚ) / 2)) * ((3 : ℚ) ^ n)) + ((3 : ℚ) / 2))
theorem p158_valid : GeneralSecondCertificate p158 (1 : ℚ) (3 : ℚ) (fun n x y => ((((4 : ℚ) * ((n : ℚ) + 1)) + (3 : ℚ)) * y + ((-3 : ℚ) * (((n : ℚ) + 1) + (1 : ℚ))) * x) / ((n : ℚ) + 1)) := by
  apply linear_second_certificate p158 (1 : ℚ) (3 : ℚ) (fun n => ((n : ℚ) + 1)) (fun n => (((4 : ℚ) * ((n : ℚ) + 1)) + (3 : ℚ))) (fun n => ((-3 : ℚ) * (((n : ℚ) + 1) + (1 : ℚ))))
  · norm_num [p158]
  · norm_num [p158]
  · intro n; positivity
  · intro n
    simp only [p158, Nat.cast_add, Nat.cast_one, pow_succ, pow_add] at *
    ring
theorem p158_unique (a : ℕ → ℚ) (hi : a 0 = (1 : ℚ)) (hj : a 1 = (3 : ℚ))
    (ha : ∀ n : ℕ, ((n : ℚ) + 1) * a (n + 2) = (((4 : ℚ) * ((n : ℚ) + 1)) + (3 : ℚ)) * a (n + 1) + ((-3 : ℚ) * (((n : ℚ) + 1) + (1 : ℚ))) * a n) :
    ∀ n, a n = p158 n := by
  apply general_second_unique p158_valid
  exact linear_second_certificate a (1 : ℚ) (3 : ℚ) (fun n => ((n : ℚ) + 1)) (fun n => (((4 : ℚ) * ((n : ℚ) + 1)) + (3 : ℚ))) (fun n => ((-3 : ℚ) * (((n : ℚ) + 1) + (1 : ℚ)))) hi hj (by intro n; positivity) ha
#print axioms p158_valid
#print axioms p158_unique

def p120 (n : ℕ) : ℚ := (((((n : ℚ) + 1) + (-1 : ℚ)) * ((2 : ℚ) ^ n)) + (1 : ℚ))
theorem p120_valid : GeneralSecondCertificate p120 (1 : ℚ) (3 : ℚ) (fun n x y => ((((3 : ℚ) * ((n : ℚ) + 1)) + (5 : ℚ)) * y + ((-2 : ℚ) * (((n : ℚ) + 1) + (2 : ℚ))) * x) / (((n : ℚ) + 1) + (1 : ℚ))) := by
  apply linear_second_certificate p120 (1 : ℚ) (3 : ℚ) (fun n => (((n : ℚ) + 1) + (1 : ℚ))) (fun n => (((3 : ℚ) * ((n : ℚ) + 1)) + (5 : ℚ))) (fun n => ((-2 : ℚ) * (((n : ℚ) + 1) + (2 : ℚ))))
  · norm_num [p120]
  · norm_num [p120]
  · intro n; positivity
  · intro n
    simp only [p120, Nat.cast_add, Nat.cast_one, pow_succ, pow_add] at *
    ring
theorem p120_unique (a : ℕ → ℚ) (hi : a 0 = (1 : ℚ)) (hj : a 1 = (3 : ℚ))
    (ha : ∀ n : ℕ, (((n : ℚ) + 1) + (1 : ℚ)) * a (n + 2) = (((3 : ℚ) * ((n : ℚ) + 1)) + (5 : ℚ)) * a (n + 1) + ((-2 : ℚ) * (((n : ℚ) + 1) + (2 : ℚ))) * a n) :
    ∀ n, a n = p120 n := by
  apply general_second_unique p120_valid
  exact linear_second_certificate a (1 : ℚ) (3 : ℚ) (fun n => (((n : ℚ) + 1) + (1 : ℚ))) (fun n => (((3 : ℚ) * ((n : ℚ) + 1)) + (5 : ℚ))) (fun n => ((-2 : ℚ) * (((n : ℚ) + 1) + (2 : ℚ)))) hi hj (by intro n; positivity) ha
#print axioms p120_valid
#print axioms p120_unique

def p123 (n : ℕ) : ℚ := (((((5 : ℚ) * ((n : ℚ) + 1)) + (-5 : ℚ)) * ((3 : ℚ) ^ n)) + (1 : ℚ))
theorem p123_valid : GeneralSecondCertificate p123 (1 : ℚ) (16 : ℚ) (fun n x y => ((((8 : ℚ) * ((n : ℚ) + 1)) + (10 : ℚ)) * y + ((-3 : ℚ) * (((2 : ℚ) * ((n : ℚ) + 1)) + (3 : ℚ))) * x) / (((2 : ℚ) * ((n : ℚ) + 1)) + (1 : ℚ))) := by
  apply linear_second_certificate p123 (1 : ℚ) (16 : ℚ) (fun n => (((2 : ℚ) * ((n : ℚ) + 1)) + (1 : ℚ))) (fun n => (((8 : ℚ) * ((n : ℚ) + 1)) + (10 : ℚ))) (fun n => ((-3 : ℚ) * (((2 : ℚ) * ((n : ℚ) + 1)) + (3 : ℚ))))
  · norm_num [p123]
  · norm_num [p123]
  · intro n; positivity
  · intro n
    simp only [p123, Nat.cast_add, Nat.cast_one, pow_succ, pow_add] at *
    ring
theorem p123_unique (a : ℕ → ℚ) (hi : a 0 = (1 : ℚ)) (hj : a 1 = (16 : ℚ))
    (ha : ∀ n : ℕ, (((2 : ℚ) * ((n : ℚ) + 1)) + (1 : ℚ)) * a (n + 2) = (((8 : ℚ) * ((n : ℚ) + 1)) + (10 : ℚ)) * a (n + 1) + ((-3 : ℚ) * (((2 : ℚ) * ((n : ℚ) + 1)) + (3 : ℚ))) * a n) :
    ∀ n, a n = p123 n := by
  apply general_second_unique p123_valid
  exact linear_second_certificate a (1 : ℚ) (16 : ℚ) (fun n => (((2 : ℚ) * ((n : ℚ) + 1)) + (1 : ℚ))) (fun n => (((8 : ℚ) * ((n : ℚ) + 1)) + (10 : ℚ))) (fun n => ((-3 : ℚ) * (((2 : ℚ) * ((n : ℚ) + 1)) + (3 : ℚ)))) hi hj (by intro n; positivity) ha
#print axioms p123_valid
#print axioms p123_unique

def p122 (n : ℕ) : ℚ := (((-1 : ℚ) * ((2 : ℚ) ^ n)) + ((2 : ℚ) * ((3 : ℚ) ^ n)))
def p122_base (n : ℕ) : ℚ := (((-1 : ℚ) * ((2 : ℚ) ^ n)) + ((2 : ℚ) * ((3 : ℚ) ^ n)))
theorem p122_base_valid : SecondCertificate p122_base (1 : ℚ) (4 : ℚ) (5 : ℚ) (-6 : ℚ) := by
  constructor
  · norm_num [p122_base]
  · norm_num [p122_base]
  · intro n
    simp only [p122_base, Nat.cast_add, Nat.cast_one, pow_succ, pow_add] at *
    ring
theorem p122_valid : WeightedSumCertificate p122 (1 : ℚ) (fun n : ℕ => (1 : ℚ)) (6 : ℚ) (-2 : ℚ) := by
  apply weighted_sum_from_second p122 p122_base (fun n : ℕ => (1 : ℚ)) (1 : ℚ) (1 : ℚ) (4 : ℚ) (6 : ℚ) (-2 : ℚ)
  · convert p122_base_valid using 1 <;> norm_num
  · norm_num
  · intro n; positivity
  · intro n; simp only [p122, p122_base] <;> ring
  · norm_num [p122]
theorem p122_unique (a : ℕ → ℚ) (ha : WeightedSumCertificate a (1 : ℚ) (fun n : ℕ => (1 : ℚ)) (6 : ℚ) (-2 : ℚ)) :
    ∀ n, a n = p122 n := weighted_sum_unique p122_valid ha
#print axioms p122_valid
#print axioms p122_unique

def p142 (n : ℕ) : ℚ := (((((1 : ℚ) / 2) * (((n : ℚ) + 1) + (-1 : ℚ))) + (1 : ℚ)) * ((2 : ℚ) ^ n))
def p142_base (n : ℕ) : ℚ := (((((1 : ℚ) / 2) * (((n : ℚ) + 1) + (-1 : ℚ))) + (1 : ℚ)) * ((2 : ℚ) ^ n))
theorem p142_base_valid : SecondCertificate p142_base (1 : ℚ) (3 : ℚ) (4 : ℚ) (-4 : ℚ) := by
  constructor
  · norm_num [p142_base]
  · norm_num [p142_base]
  · intro n
    simp only [p142_base, Nat.cast_add, Nat.cast_one, pow_succ, pow_add] at *
    ring
theorem p142_valid : WeightedSumCertificate p142 (1 : ℚ) (fun n : ℕ => (1 : ℚ)) (4 : ℚ) (-1 : ℚ) := by
  apply weighted_sum_from_second p142 p142_base (fun n : ℕ => (1 : ℚ)) (1 : ℚ) (1 : ℚ) (3 : ℚ) (4 : ℚ) (-1 : ℚ)
  · convert p142_base_valid using 1 <;> norm_num
  · norm_num
  · intro n; positivity
  · intro n; simp only [p142, p142_base] <;> ring
  · norm_num [p142]
theorem p142_unique (a : ℕ → ℚ) (ha : WeightedSumCertificate a (1 : ℚ) (fun n : ℕ => (1 : ℚ)) (4 : ℚ) (-1 : ℚ)) :
    ∀ n, a n = p142 n := weighted_sum_unique p142_valid ha
#print axioms p142_valid
#print axioms p142_unique

def p131 (n : ℕ) : ℚ := (((n : ℚ) + 1) * ((((-1 : ℚ) / 2) * ((2 : ℚ) ^ n)) + (((3 : ℚ) / 2) * ((4 : ℚ) ^ n))))
def p131_base (n : ℕ) : ℚ := ((((-1 : ℚ) / 2) * ((2 : ℚ) ^ n)) + (((3 : ℚ) / 2) * ((4 : ℚ) ^ n)))
theorem p131_base_valid : SecondCertificate p131_base (1 : ℚ) (5 : ℚ) (6 : ℚ) (-8 : ℚ) := by
  constructor
  · norm_num [p131_base]
  · norm_num [p131_base]
  · intro n
    simp only [p131_base, Nat.cast_add, Nat.cast_one, pow_succ, pow_add] at *
    ring
theorem p131_valid : WeightedSumCertificate p131 (1 : ℚ) (fun n : ℕ => ((n : ℚ) + 1)) (8 : ℚ) (-3 : ℚ) := by
  apply weighted_sum_from_second p131 p131_base (fun n : ℕ => ((n : ℚ) + 1)) (1 : ℚ) (1 : ℚ) (5 : ℚ) (8 : ℚ) (-3 : ℚ)
  · convert p131_base_valid using 1 <;> norm_num
  · norm_num
  · intro n; positivity
  · intro n; simp only [p131, p131_base] <;> ring
  · norm_num [p131]
theorem p131_unique (a : ℕ → ℚ) (ha : WeightedSumCertificate a (1 : ℚ) (fun n : ℕ => ((n : ℚ) + 1)) (8 : ℚ) (-3 : ℚ)) :
    ∀ n, a n = p131 n := weighted_sum_unique p131_valid ha
#print axioms p131_valid
#print axioms p131_unique

def p121 (n : ℕ) : ℚ := (((n : ℚ) + 1) * ((((2 : ℚ) / 3) * (((n : ℚ) + 1) + (-1 : ℚ))) + (1 : ℚ)) * ((3 : ℚ) ^ n))
def p121_base (n : ℕ) : ℚ := (((((2 : ℚ) / 3) * (((n : ℚ) + 1) + (-1 : ℚ))) + (1 : ℚ)) * ((3 : ℚ) ^ n))
theorem p121_base_valid : SecondCertificate p121_base (1 : ℚ) (5 : ℚ) (6 : ℚ) (-9 : ℚ) := by
  constructor
  · norm_num [p121_base]
  · norm_num [p121_base]
  · intro n
    simp only [p121_base, Nat.cast_add, Nat.cast_one, pow_succ, pow_add] at *
    ring
theorem p121_valid : WeightedSumCertificate p121 (1 : ℚ) (fun n : ℕ => ((n : ℚ) + 1)) (9 : ℚ) (-4 : ℚ) := by
  apply weighted_sum_from_second p121 p121_base (fun n : ℕ => ((n : ℚ) + 1)) (1 : ℚ) (1 : ℚ) (5 : ℚ) (9 : ℚ) (-4 : ℚ)
  · convert p121_base_valid using 1 <;> norm_num
  · norm_num
  · intro n; positivity
  · intro n; simp only [p121, p121_base] <;> ring
  · norm_num [p121]
theorem p121_unique (a : ℕ → ℚ) (ha : WeightedSumCertificate a (1 : ℚ) (fun n : ℕ => ((n : ℚ) + 1)) (9 : ℚ) (-4 : ℚ)) :
    ∀ n, a n = p121 n := weighted_sum_unique p121_valid ha
#print axioms p121_valid
#print axioms p121_unique

def p200 (n : ℕ) : ℚ := ((((2 : ℚ) * ((n : ℚ) + 1)) + (1 : ℚ)) * (((-2 : ℚ) * ((3 : ℚ) ^ n)) + ((3 : ℚ) * ((4 : ℚ) ^ n))))
def p200_base (n : ℕ) : ℚ := (((-2 : ℚ) * ((3 : ℚ) ^ n)) + ((3 : ℚ) * ((4 : ℚ) ^ n)))
theorem p200_base_valid : SecondCertificate p200_base (1 : ℚ) (6 : ℚ) (7 : ℚ) (-12 : ℚ) := by
  constructor
  · norm_num [p200_base]
  · norm_num [p200_base]
  · intro n
    simp only [p200_base, Nat.cast_add, Nat.cast_one, pow_succ, pow_add] at *
    ring
theorem p200_valid : WeightedSumCertificate p200 (3 : ℚ) (fun n : ℕ => (((2 : ℚ) * ((n : ℚ) + 1)) + (1 : ℚ))) (12 : ℚ) (-6 : ℚ) := by
  apply weighted_sum_from_second p200 p200_base (fun n : ℕ => (((2 : ℚ) * ((n : ℚ) + 1)) + (1 : ℚ))) (3 : ℚ) (1 : ℚ) (6 : ℚ) (12 : ℚ) (-6 : ℚ)
  · convert p200_base_valid using 1 <;> norm_num
  · norm_num
  · intro n; positivity
  · intro n; simp only [p200, p200_base] <;> ring
  · norm_num [p200]
theorem p200_unique (a : ℕ → ℚ) (ha : WeightedSumCertificate a (3 : ℚ) (fun n : ℕ => (((2 : ℚ) * ((n : ℚ) + 1)) + (1 : ℚ))) (12 : ℚ) (-6 : ℚ)) :
    ∀ n, a n = p200 n := weighted_sum_unique p200_valid ha
#print axioms p200_valid
#print axioms p200_unique

def p125 (n : ℕ) : ℚ := ((((n : ℚ) + 1) + (1 : ℚ)) * ((((-1 : ℚ) / 2) * ((2 : ℚ) ^ n)) + (((3 : ℚ) / 2) * ((4 : ℚ) ^ n))))
def p125_base (n : ℕ) : ℚ := ((((-1 : ℚ) / 2) * ((2 : ℚ) ^ n)) + (((3 : ℚ) / 2) * ((4 : ℚ) ^ n)))
theorem p125_base_valid : SecondCertificate p125_base (1 : ℚ) (5 : ℚ) (6 : ℚ) (-8 : ℚ) := by
  constructor
  · norm_num [p125_base]
  · norm_num [p125_base]
  · intro n
    simp only [p125_base, Nat.cast_add, Nat.cast_one, pow_succ, pow_add] at *
    ring
theorem p125_valid : WeightedSumCertificate p125 (2 : ℚ) (fun n : ℕ => (((n : ℚ) + 1) + (1 : ℚ))) (8 : ℚ) (-3 : ℚ) := by
  apply weighted_sum_from_second p125 p125_base (fun n : ℕ => (((n : ℚ) + 1) + (1 : ℚ))) (2 : ℚ) (1 : ℚ) (5 : ℚ) (8 : ℚ) (-3 : ℚ)
  · convert p125_base_valid using 1 <;> norm_num
  · norm_num
  · intro n; positivity
  · intro n; simp only [p125, p125_base] <;> ring
  · norm_num [p125]
theorem p125_unique (a : ℕ → ℚ) (ha : WeightedSumCertificate a (2 : ℚ) (fun n : ℕ => (((n : ℚ) + 1) + (1 : ℚ))) (8 : ℚ) (-3 : ℚ)) :
    ∀ n, a n = p125 n := weighted_sum_unique p125_valid ha
#print axioms p125_valid
#print axioms p125_unique

def p157 (n : ℕ) : ℚ := ((((2 : ℚ) * ((n : ℚ) + 1)) + (1 : ℚ)) * ((((1 : ℚ) / 2) * (((n : ℚ) + 1) + (-1 : ℚ))) + (1 : ℚ)) * ((2 : ℚ) ^ n))
def p157_base (n : ℕ) : ℚ := (((((1 : ℚ) / 2) * (((n : ℚ) + 1) + (-1 : ℚ))) + (1 : ℚ)) * ((2 : ℚ) ^ n))
theorem p157_base_valid : SecondCertificate p157_base (1 : ℚ) (3 : ℚ) (4 : ℚ) (-4 : ℚ) := by
  constructor
  · norm_num [p157_base]
  · norm_num [p157_base]
  · intro n
    simp only [p157_base, Nat.cast_add, Nat.cast_one, pow_succ, pow_add] at *
    ring
theorem p157_valid : WeightedSumCertificate p157 (3 : ℚ) (fun n : ℕ => (((2 : ℚ) * ((n : ℚ) + 1)) + (1 : ℚ))) (4 : ℚ) (-1 : ℚ) := by
  apply weighted_sum_from_second p157 p157_base (fun n : ℕ => (((2 : ℚ) * ((n : ℚ) + 1)) + (1 : ℚ))) (3 : ℚ) (1 : ℚ) (3 : ℚ) (4 : ℚ) (-1 : ℚ)
  · convert p157_base_valid using 1 <;> norm_num
  · norm_num
  · intro n; positivity
  · intro n; simp only [p157, p157_base] <;> ring
  · norm_num [p157]
theorem p157_unique (a : ℕ → ℚ) (ha : WeightedSumCertificate a (3 : ℚ) (fun n : ℕ => (((2 : ℚ) * ((n : ℚ) + 1)) + (1 : ℚ))) (4 : ℚ) (-1 : ℚ)) :
    ∀ n, a n = p157 n := weighted_sum_unique p157_valid ha
#print axioms p157_valid
#print axioms p157_unique

def p126 (n : ℕ) : ℚ := ((((n : ℚ) + 1) + (1 : ℚ)) * ((((1 : ℚ) / 3) * (((n : ℚ) + 1) + (-1 : ℚ))) + ((1 : ℚ) / 2)) * ((3 : ℚ) ^ n))
def p126_base (n : ℕ) : ℚ := (((((1 : ℚ) / 3) * (((n : ℚ) + 1) + (-1 : ℚ))) + ((1 : ℚ) / 2)) * ((3 : ℚ) ^ n))
theorem p126_base_valid : SecondCertificate p126_base ((1 : ℚ) / 2) ((5 : ℚ) / 2) (6 : ℚ) (-9 : ℚ) := by
  constructor
  · norm_num [p126_base]
  · norm_num [p126_base]
  · intro n
    simp only [p126_base, Nat.cast_add, Nat.cast_one, pow_succ, pow_add] at *
    ring
theorem p126_valid : WeightedSumCertificate p126 (1 : ℚ) (fun n : ℕ => (((n : ℚ) + 1) + (1 : ℚ))) (9 : ℚ) (-4 : ℚ) := by
  apply weighted_sum_from_second p126 p126_base (fun n : ℕ => (((n : ℚ) + 1) + (1 : ℚ))) (1 : ℚ) ((1 : ℚ) / 2) ((5 : ℚ) / 2) (9 : ℚ) (-4 : ℚ)
  · convert p126_base_valid using 1 <;> norm_num
  · norm_num
  · intro n; positivity
  · intro n; simp only [p126, p126_base] <;> ring
  · norm_num [p126]
theorem p126_unique (a : ℕ → ℚ) (ha : WeightedSumCertificate a (1 : ℚ) (fun n : ℕ => (((n : ℚ) + 1) + (1 : ℚ))) (9 : ℚ) (-4 : ℚ)) :
    ∀ n, a n = p126 n := weighted_sum_unique p126_valid ha
#print axioms p126_valid
#print axioms p126_unique

def p186 (n : ℕ) : ℚ := (((-2 : ℚ) * ((3 : ℚ) ^ n)) + ((3 : ℚ) * ((4 : ℚ) ^ n)))
def p186_base (n : ℕ) : ℚ := (((-2 : ℚ) * ((3 : ℚ) ^ n)) + ((3 : ℚ) * ((4 : ℚ) ^ n)))
theorem p186_base_valid : SecondCertificate p186_base (1 : ℚ) (6 : ℚ) (7 : ℚ) (-12 : ℚ) := by
  constructor
  · norm_num [p186_base]
  · norm_num [p186_base]
  · intro n
    simp only [p186_base, Nat.cast_add, Nat.cast_one, pow_succ, pow_add] at *
    ring
theorem p186_valid : WeightedSumCertificate p186 (1 : ℚ) (fun n : ℕ => (1 : ℚ)) (12 : ℚ) (-6 : ℚ) := by
  apply weighted_sum_from_second p186 p186_base (fun n : ℕ => (1 : ℚ)) (1 : ℚ) (1 : ℚ) (6 : ℚ) (12 : ℚ) (-6 : ℚ)
  · convert p186_base_valid using 1 <;> norm_num
  · norm_num
  · intro n; positivity
  · intro n; simp only [p186, p186_base] <;> ring
  · norm_num [p186]
theorem p186_unique (a : ℕ → ℚ) (ha : WeightedSumCertificate a (1 : ℚ) (fun n : ℕ => (1 : ℚ)) (12 : ℚ) (-6 : ℚ)) :
    ∀ n, a n = p186 n := weighted_sum_unique p186_valid ha
#print axioms p186_valid
#print axioms p186_unique

def p140 (n : ℕ) : ℚ := (((((2 : ℚ) / 3) * (((n : ℚ) + 1) + (-1 : ℚ))) + (1 : ℚ)) * ((3 : ℚ) ^ n))
def p140_base (n : ℕ) : ℚ := (((((2 : ℚ) / 3) * (((n : ℚ) + 1) + (-1 : ℚ))) + (1 : ℚ)) * ((3 : ℚ) ^ n))
theorem p140_base_valid : SecondCertificate p140_base (1 : ℚ) (5 : ℚ) (6 : ℚ) (-9 : ℚ) := by
  constructor
  · norm_num [p140_base]
  · norm_num [p140_base]
  · intro n
    simp only [p140_base, Nat.cast_add, Nat.cast_one, pow_succ, pow_add] at *
    ring
theorem p140_valid : WeightedSumCertificate p140 (1 : ℚ) (fun n : ℕ => (1 : ℚ)) (9 : ℚ) (-4 : ℚ) := by
  apply weighted_sum_from_second p140 p140_base (fun n : ℕ => (1 : ℚ)) (1 : ℚ) (1 : ℚ) (5 : ℚ) (9 : ℚ) (-4 : ℚ)
  · convert p140_base_valid using 1 <;> norm_num
  · norm_num
  · intro n; positivity
  · intro n; simp only [p140, p140_base] <;> ring
  · norm_num [p140]
theorem p140_unique (a : ℕ → ℚ) (ha : WeightedSumCertificate a (1 : ℚ) (fun n : ℕ => (1 : ℚ)) (9 : ℚ) (-4 : ℚ)) :
    ∀ n, a n = p140 n := weighted_sum_unique p140_valid ha
#print axioms p140_valid
#print axioms p140_unique

def p144 (n : ℕ) : ℚ := (((n : ℚ) + 1) * (((-1 : ℚ) * ((2 : ℚ) ^ n)) + ((2 : ℚ) * ((3 : ℚ) ^ n))))
def p144_base (n : ℕ) : ℚ := (((-1 : ℚ) * ((2 : ℚ) ^ n)) + ((2 : ℚ) * ((3 : ℚ) ^ n)))
theorem p144_base_valid : SecondCertificate p144_base (1 : ℚ) (4 : ℚ) (5 : ℚ) (-6 : ℚ) := by
  constructor
  · norm_num [p144_base]
  · norm_num [p144_base]
  · intro n
    simp only [p144_base, Nat.cast_add, Nat.cast_one, pow_succ, pow_add] at *
    ring
theorem p144_valid : WeightedSumCertificate p144 (1 : ℚ) (fun n : ℕ => ((n : ℚ) + 1)) (6 : ℚ) (-2 : ℚ) := by
  apply weighted_sum_from_second p144 p144_base (fun n : ℕ => ((n : ℚ) + 1)) (1 : ℚ) (1 : ℚ) (4 : ℚ) (6 : ℚ) (-2 : ℚ)
  · convert p144_base_valid using 1 <;> norm_num
  · norm_num
  · intro n; positivity
  · intro n; simp only [p144, p144_base] <;> ring
  · norm_num [p144]
theorem p144_unique (a : ℕ → ℚ) (ha : WeightedSumCertificate a (1 : ℚ) (fun n : ℕ => ((n : ℚ) + 1)) (6 : ℚ) (-2 : ℚ)) :
    ∀ n, a n = p144 n := weighted_sum_unique p144_valid ha
#print axioms p144_valid
#print axioms p144_unique

def p164 (n : ℕ) : ℚ := (((n : ℚ) + 1) * ((((1 : ℚ) / 2) * (((n : ℚ) + 1) + (-1 : ℚ))) + (1 : ℚ)) * ((2 : ℚ) ^ n))
def p164_base (n : ℕ) : ℚ := (((((1 : ℚ) / 2) * (((n : ℚ) + 1) + (-1 : ℚ))) + (1 : ℚ)) * ((2 : ℚ) ^ n))
theorem p164_base_valid : SecondCertificate p164_base (1 : ℚ) (3 : ℚ) (4 : ℚ) (-4 : ℚ) := by
  constructor
  · norm_num [p164_base]
  · norm_num [p164_base]
  · intro n
    simp only [p164_base, Nat.cast_add, Nat.cast_one, pow_succ, pow_add] at *
    ring
theorem p164_valid : WeightedSumCertificate p164 (1 : ℚ) (fun n : ℕ => ((n : ℚ) + 1)) (4 : ℚ) (-1 : ℚ) := by
  apply weighted_sum_from_second p164 p164_base (fun n : ℕ => ((n : ℚ) + 1)) (1 : ℚ) (1 : ℚ) (3 : ℚ) (4 : ℚ) (-1 : ℚ)
  · convert p164_base_valid using 1 <;> norm_num
  · norm_num
  · intro n; positivity
  · intro n; simp only [p164, p164_base] <;> ring
  · norm_num [p164]
theorem p164_unique (a : ℕ → ℚ) (ha : WeightedSumCertificate a (1 : ℚ) (fun n : ℕ => ((n : ℚ) + 1)) (4 : ℚ) (-1 : ℚ)) :
    ∀ n, a n = p164 n := weighted_sum_unique p164_valid ha
#print axioms p164_valid
#print axioms p164_unique

def p159 (n : ℕ) : ℚ := ((2 : ℚ) ^ (1 + (3 * n) + (n).choose 2))
theorem p159_valid : GeneralSecondCertificate p159 (2 : ℚ) (16 : ℚ) (fun n x y => (2 : ℚ) ^ (1) * y ^ 2 / x) := by
  have he : ∀ n : ℕ, ((1 + (3 * (n + 2)) + ((n + 2)).choose 2)) + ((1 + (3 * n) + (n).choose 2)) = (1) + 2 * ((1 + (3 * (n + 1)) + ((n + 1)).choose 2)) := by
    intro n
    simp only [Nat.add_assoc, Nat.choose_succ_succ, Nat.choose_one_right, Nat.choose_zero_right]
    ring
  have h := multiplicative_certificate (2 : ℚ) (fun n : ℕ => (1 + (3 * n) + (n).choose 2)) (fun n : ℕ => 1) (by norm_num) he
  convert h.1 using 1 <;> norm_num [p159]
theorem p159_domain : ∀ n, p159 n ≠ 0 := by
  intro n; unfold p159; positivity
theorem p159_unique (a : ℕ → ℚ) (hi : a 0 = (2 : ℚ)) (hj : a 1 = (16 : ℚ))
    (ha : ∀ n : ℕ, a (n + 2) * a n = (2 : ℚ) ^ (1) * a (n + 1) ^ 2) :
    ∀ n, a n = p159 n := by
  apply general_second_unique p159_valid
  apply multiplicative_from_relation a (2 : ℚ) (16 : ℚ) (fun n => (2 : ℚ) ^ (1)) hi hj
  · norm_num
  · norm_num
  · intro n; positivity
  · exact ha
#print axioms p159_domain
#print axioms p159_valid
#print axioms p159_unique

def p149 (n : ℕ) : ℚ := ((3 : ℚ) ^ ((n + 1) + (3 * (n).choose 2) + (2 * (n).choose 3)))
theorem p149_valid : GeneralSecondCertificate p149 (3 : ℚ) (9 : ℚ) (fun n x y => (3 : ℚ) ^ ((1 + (2 * (n + 1)))) * y ^ 2 / x) := by
  have he : ∀ n : ℕ, ((((n + 2) + 1) + (3 * ((n + 2)).choose 2) + (2 * ((n + 2)).choose 3))) + (((n + 1) + (3 * (n).choose 2) + (2 * (n).choose 3))) = ((1 + (2 * (n + 1)))) + 2 * ((((n + 1) + 1) + (3 * ((n + 1)).choose 2) + (2 * ((n + 1)).choose 3))) := by
    intro n
    simp only [Nat.add_assoc, Nat.choose_succ_succ, Nat.choose_one_right, Nat.choose_zero_right]
    ring
  have h := multiplicative_certificate (3 : ℚ) (fun n : ℕ => ((n + 1) + (3 * (n).choose 2) + (2 * (n).choose 3))) (fun n : ℕ => (1 + (2 * (n + 1)))) (by norm_num) he
  convert h.1 using 1 <;> norm_num [p149]
theorem p149_domain : ∀ n, p149 n ≠ 0 := by
  intro n; unfold p149; positivity
theorem p149_unique (a : ℕ → ℚ) (hi : a 0 = (3 : ℚ)) (hj : a 1 = (9 : ℚ))
    (ha : ∀ n : ℕ, a (n + 2) * a n = (3 : ℚ) ^ ((1 + (2 * (n + 1)))) * a (n + 1) ^ 2) :
    ∀ n, a n = p149 n := by
  apply general_second_unique p149_valid
  apply multiplicative_from_relation a (3 : ℚ) (9 : ℚ) (fun n => (3 : ℚ) ^ ((1 + (2 * (n + 1))))) hi hj
  · norm_num
  · norm_num
  · intro n; positivity
  · exact ha
#print axioms p149_domain
#print axioms p149_valid
#print axioms p149_unique

def p135 (n : ℕ) : ℚ := ((2 : ℚ) ^ (1 + (3 * n) + (2 * (n).choose 2) + (2 * (n).choose 3)))
theorem p135_valid : GeneralSecondCertificate p135 (2 : ℚ) (16 : ℚ) (fun n x y => (2 : ℚ) ^ ((2 * (n + 1))) * y ^ 2 / x) := by
  have he : ∀ n : ℕ, ((1 + (3 * (n + 2)) + (2 * ((n + 2)).choose 2) + (2 * ((n + 2)).choose 3))) + ((1 + (3 * n) + (2 * (n).choose 2) + (2 * (n).choose 3))) = ((2 * (n + 1))) + 2 * ((1 + (3 * (n + 1)) + (2 * ((n + 1)).choose 2) + (2 * ((n + 1)).choose 3))) := by
    intro n
    simp only [Nat.add_assoc, Nat.choose_succ_succ, Nat.choose_one_right, Nat.choose_zero_right]
    ring
  have h := multiplicative_certificate (2 : ℚ) (fun n : ℕ => (1 + (3 * n) + (2 * (n).choose 2) + (2 * (n).choose 3))) (fun n : ℕ => (2 * (n + 1))) (by norm_num) he
  convert h.1 using 1 <;> norm_num [p135]
theorem p135_domain : ∀ n, p135 n ≠ 0 := by
  intro n; unfold p135; positivity
theorem p135_unique (a : ℕ → ℚ) (hi : a 0 = (2 : ℚ)) (hj : a 1 = (16 : ℚ))
    (ha : ∀ n : ℕ, a (n + 2) * a n = (2 : ℚ) ^ ((2 * (n + 1))) * a (n + 1) ^ 2) :
    ∀ n, a n = p135 n := by
  apply general_second_unique p135_valid
  apply multiplicative_from_relation a (2 : ℚ) (16 : ℚ) (fun n => (2 : ℚ) ^ ((2 * (n + 1)))) hi hj
  · norm_num
  · norm_num
  · intro n; positivity
  · exact ha
#print axioms p135_domain
#print axioms p135_valid
#print axioms p135_unique

def p151 (n : ℕ) : ℚ := ((3 : ℚ) ^ ((n + 1) + (n).choose 2))
theorem p151_valid : GeneralSecondCertificate p151 (3 : ℚ) (9 : ℚ) (fun n x y => (3 : ℚ) ^ (1) * y ^ 2 / x) := by
  have he : ∀ n : ℕ, ((((n + 2) + 1) + ((n + 2)).choose 2)) + (((n + 1) + (n).choose 2)) = (1) + 2 * ((((n + 1) + 1) + ((n + 1)).choose 2)) := by
    intro n
    simp only [Nat.add_assoc, Nat.choose_succ_succ, Nat.choose_one_right, Nat.choose_zero_right]
    ring
  have h := multiplicative_certificate (3 : ℚ) (fun n : ℕ => ((n + 1) + (n).choose 2)) (fun n : ℕ => 1) (by norm_num) he
  convert h.1 using 1 <;> norm_num [p151]
theorem p151_domain : ∀ n, p151 n ≠ 0 := by
  intro n; unfold p151; positivity
theorem p151_unique (a : ℕ → ℚ) (hi : a 0 = (3 : ℚ)) (hj : a 1 = (9 : ℚ))
    (ha : ∀ n : ℕ, a (n + 2) * a n = (3 : ℚ) ^ (1) * a (n + 1) ^ 2) :
    ∀ n, a n = p151 n := by
  apply general_second_unique p151_valid
  apply multiplicative_from_relation a (3 : ℚ) (9 : ℚ) (fun n => (3 : ℚ) ^ (1)) hi hj
  · norm_num
  · norm_num
  · intro n; positivity
  · exact ha
#print axioms p151_domain
#print axioms p151_valid
#print axioms p151_unique

def p143 (n : ℕ) : ℚ := ((2 : ℚ) ^ (1 + (3 * n) + (3 * (n).choose 2) + (2 * (n).choose 3)))
theorem p143_valid : GeneralSecondCertificate p143 (2 : ℚ) (16 : ℚ) (fun n x y => (2 : ℚ) ^ ((1 + (2 * (n + 1)))) * y ^ 2 / x) := by
  have he : ∀ n : ℕ, ((1 + (3 * (n + 2)) + (3 * ((n + 2)).choose 2) + (2 * ((n + 2)).choose 3))) + ((1 + (3 * n) + (3 * (n).choose 2) + (2 * (n).choose 3))) = ((1 + (2 * (n + 1)))) + 2 * ((1 + (3 * (n + 1)) + (3 * ((n + 1)).choose 2) + (2 * ((n + 1)).choose 3))) := by
    intro n
    simp only [Nat.add_assoc, Nat.choose_succ_succ, Nat.choose_one_right, Nat.choose_zero_right]
    ring
  have h := multiplicative_certificate (2 : ℚ) (fun n : ℕ => (1 + (3 * n) + (3 * (n).choose 2) + (2 * (n).choose 3))) (fun n : ℕ => (1 + (2 * (n + 1)))) (by norm_num) he
  convert h.1 using 1 <;> norm_num [p143]
theorem p143_domain : ∀ n, p143 n ≠ 0 := by
  intro n; unfold p143; positivity
theorem p143_unique (a : ℕ → ℚ) (hi : a 0 = (2 : ℚ)) (hj : a 1 = (16 : ℚ))
    (ha : ∀ n : ℕ, a (n + 2) * a n = (2 : ℚ) ^ ((1 + (2 * (n + 1)))) * a (n + 1) ^ 2) :
    ∀ n, a n = p143 n := by
  apply general_second_unique p143_valid
  apply multiplicative_from_relation a (2 : ℚ) (16 : ℚ) (fun n => (2 : ℚ) ^ ((1 + (2 * (n + 1))))) hi hj
  · norm_num
  · norm_num
  · intro n; positivity
  · exact ha
#print axioms p143_domain
#print axioms p143_valid
#print axioms p143_unique

def p127 (n : ℕ) : ℚ := ((3 : ℚ) ^ ((n + 1) + (2 * (n).choose 2) + (2 * (n).choose 3)))
theorem p127_valid : GeneralSecondCertificate p127 (3 : ℚ) (9 : ℚ) (fun n x y => (3 : ℚ) ^ ((2 * (n + 1))) * y ^ 2 / x) := by
  have he : ∀ n : ℕ, ((((n + 2) + 1) + (2 * ((n + 2)).choose 2) + (2 * ((n + 2)).choose 3))) + (((n + 1) + (2 * (n).choose 2) + (2 * (n).choose 3))) = ((2 * (n + 1))) + 2 * ((((n + 1) + 1) + (2 * ((n + 1)).choose 2) + (2 * ((n + 1)).choose 3))) := by
    intro n
    simp only [Nat.add_assoc, Nat.choose_succ_succ, Nat.choose_one_right, Nat.choose_zero_right]
    ring
  have h := multiplicative_certificate (3 : ℚ) (fun n : ℕ => ((n + 1) + (2 * (n).choose 2) + (2 * (n).choose 3))) (fun n : ℕ => (2 * (n + 1))) (by norm_num) he
  convert h.1 using 1 <;> norm_num [p127]
theorem p127_domain : ∀ n, p127 n ≠ 0 := by
  intro n; unfold p127; positivity
theorem p127_unique (a : ℕ → ℚ) (hi : a 0 = (3 : ℚ)) (hj : a 1 = (9 : ℚ))
    (ha : ∀ n : ℕ, a (n + 2) * a n = (3 : ℚ) ^ ((2 * (n + 1))) * a (n + 1) ^ 2) :
    ∀ n, a n = p127 n := by
  apply general_second_unique p127_valid
  apply multiplicative_from_relation a (3 : ℚ) (9 : ℚ) (fun n => (3 : ℚ) ^ ((2 * (n + 1)))) hi hj
  · norm_num
  · norm_num
  · intro n; positivity
  · exact ha
#print axioms p127_domain
#print axioms p127_valid
#print axioms p127_unique

def p141 (n : ℕ) : ℚ := ((2 : ℚ) ^ (1 + (3 * n) + (2 * (n).choose 2)))
theorem p141_valid : GeneralSecondCertificate p141 (2 : ℚ) (16 : ℚ) (fun n x y => (2 : ℚ) ^ (2) * y ^ 2 / x) := by
  have he : ∀ n : ℕ, ((1 + (3 * (n + 2)) + (2 * ((n + 2)).choose 2))) + ((1 + (3 * n) + (2 * (n).choose 2))) = (2) + 2 * ((1 + (3 * (n + 1)) + (2 * ((n + 1)).choose 2))) := by
    intro n
    simp only [Nat.add_assoc, Nat.choose_succ_succ, Nat.choose_one_right, Nat.choose_zero_right]
    ring
  have h := multiplicative_certificate (2 : ℚ) (fun n : ℕ => (1 + (3 * n) + (2 * (n).choose 2))) (fun n : ℕ => 2) (by norm_num) he
  convert h.1 using 1 <;> norm_num [p141]
theorem p141_domain : ∀ n, p141 n ≠ 0 := by
  intro n; unfold p141; positivity
theorem p141_unique (a : ℕ → ℚ) (hi : a 0 = (2 : ℚ)) (hj : a 1 = (16 : ℚ))
    (ha : ∀ n : ℕ, a (n + 2) * a n = (2 : ℚ) ^ (2) * a (n + 1) ^ 2) :
    ∀ n, a n = p141 n := by
  apply general_second_unique p141_valid
  apply multiplicative_from_relation a (2 : ℚ) (16 : ℚ) (fun n => (2 : ℚ) ^ (2)) hi hj
  · norm_num
  · norm_num
  · intro n; positivity
  · exact ha
#print axioms p141_domain
#print axioms p141_valid
#print axioms p141_unique

def p147 (n : ℕ) : ℚ := ((3 : ℚ) ^ ((n + 1) + (6 * (n).choose 2) + (4 * (n).choose 3)))
theorem p147_valid : GeneralSecondCertificate p147 (3 : ℚ) (9 : ℚ) (fun n x y => (3 : ℚ) ^ ((2 + (4 * (n + 1)))) * y ^ 2 / x) := by
  have he : ∀ n : ℕ, ((((n + 2) + 1) + (6 * ((n + 2)).choose 2) + (4 * ((n + 2)).choose 3))) + (((n + 1) + (6 * (n).choose 2) + (4 * (n).choose 3))) = ((2 + (4 * (n + 1)))) + 2 * ((((n + 1) + 1) + (6 * ((n + 1)).choose 2) + (4 * ((n + 1)).choose 3))) := by
    intro n
    simp only [Nat.add_assoc, Nat.choose_succ_succ, Nat.choose_one_right, Nat.choose_zero_right]
    ring
  have h := multiplicative_certificate (3 : ℚ) (fun n : ℕ => ((n + 1) + (6 * (n).choose 2) + (4 * (n).choose 3))) (fun n : ℕ => (2 + (4 * (n + 1)))) (by norm_num) he
  convert h.1 using 1 <;> norm_num [p147]
theorem p147_domain : ∀ n, p147 n ≠ 0 := by
  intro n; unfold p147; positivity
theorem p147_unique (a : ℕ → ℚ) (hi : a 0 = (3 : ℚ)) (hj : a 1 = (9 : ℚ))
    (ha : ∀ n : ℕ, a (n + 2) * a n = (3 : ℚ) ^ ((2 + (4 * (n + 1)))) * a (n + 1) ^ 2) :
    ∀ n, a n = p147 n := by
  apply general_second_unique p147_valid
  apply multiplicative_from_relation a (3 : ℚ) (9 : ℚ) (fun n => (3 : ℚ) ^ ((2 + (4 * (n + 1))))) hi hj
  · norm_num
  · norm_num
  · intro n; positivity
  · exact ha
#print axioms p147_domain
#print axioms p147_valid
#print axioms p147_unique

def p118 (n : ℕ) : ℚ := ((2 : ℚ) ^ (1 + (3 * n) + (3 * (n).choose 2) + (3 * (n).choose 3)))
theorem p118_valid : GeneralSecondCertificate p118 (2 : ℚ) (16 : ℚ) (fun n x y => (2 : ℚ) ^ ((3 * (n + 1))) * y ^ 2 / x) := by
  have he : ∀ n : ℕ, ((1 + (3 * (n + 2)) + (3 * ((n + 2)).choose 2) + (3 * ((n + 2)).choose 3))) + ((1 + (3 * n) + (3 * (n).choose 2) + (3 * (n).choose 3))) = ((3 * (n + 1))) + 2 * ((1 + (3 * (n + 1)) + (3 * ((n + 1)).choose 2) + (3 * ((n + 1)).choose 3))) := by
    intro n
    simp only [Nat.add_assoc, Nat.choose_succ_succ, Nat.choose_one_right, Nat.choose_zero_right]
    ring
  have h := multiplicative_certificate (2 : ℚ) (fun n : ℕ => (1 + (3 * n) + (3 * (n).choose 2) + (3 * (n).choose 3))) (fun n : ℕ => (3 * (n + 1))) (by norm_num) he
  convert h.1 using 1 <;> norm_num [p118]
theorem p118_domain : ∀ n, p118 n ≠ 0 := by
  intro n; unfold p118; positivity
theorem p118_unique (a : ℕ → ℚ) (hi : a 0 = (2 : ℚ)) (hj : a 1 = (16 : ℚ))
    (ha : ∀ n : ℕ, a (n + 2) * a n = (2 : ℚ) ^ ((3 * (n + 1))) * a (n + 1) ^ 2) :
    ∀ n, a n = p118 n := by
  apply general_second_unique p118_valid
  apply multiplicative_from_relation a (2 : ℚ) (16 : ℚ) (fun n => (2 : ℚ) ^ ((3 * (n + 1)))) hi hj
  · norm_num
  · norm_num
  · intro n; positivity
  · exact ha
#print axioms p118_domain
#print axioms p118_valid
#print axioms p118_unique

def p165 (n : ℕ) : ℚ := ((3 : ℚ) ^ ((n + 1) + (2 * (n).choose 2)))
theorem p165_valid : GeneralSecondCertificate p165 (3 : ℚ) (9 : ℚ) (fun n x y => (3 : ℚ) ^ (2) * y ^ 2 / x) := by
  have he : ∀ n : ℕ, ((((n + 2) + 1) + (2 * ((n + 2)).choose 2))) + (((n + 1) + (2 * (n).choose 2))) = (2) + 2 * ((((n + 1) + 1) + (2 * ((n + 1)).choose 2))) := by
    intro n
    simp only [Nat.add_assoc, Nat.choose_succ_succ, Nat.choose_one_right, Nat.choose_zero_right]
    ring
  have h := multiplicative_certificate (3 : ℚ) (fun n : ℕ => ((n + 1) + (2 * (n).choose 2))) (fun n : ℕ => 2) (by norm_num) he
  convert h.1 using 1 <;> norm_num [p165]
theorem p165_domain : ∀ n, p165 n ≠ 0 := by
  intro n; unfold p165; positivity
theorem p165_unique (a : ℕ → ℚ) (hi : a 0 = (3 : ℚ)) (hj : a 1 = (9 : ℚ))
    (ha : ∀ n : ℕ, a (n + 2) * a n = (3 : ℚ) ^ (2) * a (n + 1) ^ 2) :
    ∀ n, a n = p165 n := by
  apply general_second_unique p165_valid
  apply multiplicative_from_relation a (3 : ℚ) (9 : ℚ) (fun n => (3 : ℚ) ^ (2)) hi hj
  · norm_num
  · norm_num
  · intro n; positivity
  · exact ha
#print axioms p165_domain
#print axioms p165_valid
#print axioms p165_unique

def p160 (n : ℕ) : ℚ := ((2 : ℚ) ^ (1 + (3 * n) + (6 * (n).choose 2) + (4 * (n).choose 3)))
theorem p160_valid : GeneralSecondCertificate p160 (2 : ℚ) (16 : ℚ) (fun n x y => (2 : ℚ) ^ ((2 + (4 * (n + 1)))) * y ^ 2 / x) := by
  have he : ∀ n : ℕ, ((1 + (3 * (n + 2)) + (6 * ((n + 2)).choose 2) + (4 * ((n + 2)).choose 3))) + ((1 + (3 * n) + (6 * (n).choose 2) + (4 * (n).choose 3))) = ((2 + (4 * (n + 1)))) + 2 * ((1 + (3 * (n + 1)) + (6 * ((n + 1)).choose 2) + (4 * ((n + 1)).choose 3))) := by
    intro n
    simp only [Nat.add_assoc, Nat.choose_succ_succ, Nat.choose_one_right, Nat.choose_zero_right]
    ring
  have h := multiplicative_certificate (2 : ℚ) (fun n : ℕ => (1 + (3 * n) + (6 * (n).choose 2) + (4 * (n).choose 3))) (fun n : ℕ => (2 + (4 * (n + 1)))) (by norm_num) he
  convert h.1 using 1 <;> norm_num [p160]
theorem p160_domain : ∀ n, p160 n ≠ 0 := by
  intro n; unfold p160; positivity
theorem p160_unique (a : ℕ → ℚ) (hi : a 0 = (2 : ℚ)) (hj : a 1 = (16 : ℚ))
    (ha : ∀ n : ℕ, a (n + 2) * a n = (2 : ℚ) ^ ((2 + (4 * (n + 1)))) * a (n + 1) ^ 2) :
    ∀ n, a n = p160 n := by
  apply general_second_unique p160_valid
  apply multiplicative_from_relation a (2 : ℚ) (16 : ℚ) (fun n => (2 : ℚ) ^ ((2 + (4 * (n + 1))))) hi hj
  · norm_num
  · norm_num
  · intro n; positivity
  · exact ha
#print axioms p160_domain
#print axioms p160_valid
#print axioms p160_unique

def p162 (n : ℕ) : ℚ := ((3 : ℚ) ^ ((n + 1) + (3 * (n).choose 2) + (3 * (n).choose 3)))
theorem p162_valid : GeneralSecondCertificate p162 (3 : ℚ) (9 : ℚ) (fun n x y => (3 : ℚ) ^ ((3 * (n + 1))) * y ^ 2 / x) := by
  have he : ∀ n : ℕ, ((((n + 2) + 1) + (3 * ((n + 2)).choose 2) + (3 * ((n + 2)).choose 3))) + (((n + 1) + (3 * (n).choose 2) + (3 * (n).choose 3))) = ((3 * (n + 1))) + 2 * ((((n + 1) + 1) + (3 * ((n + 1)).choose 2) + (3 * ((n + 1)).choose 3))) := by
    intro n
    simp only [Nat.add_assoc, Nat.choose_succ_succ, Nat.choose_one_right, Nat.choose_zero_right]
    ring
  have h := multiplicative_certificate (3 : ℚ) (fun n : ℕ => ((n + 1) + (3 * (n).choose 2) + (3 * (n).choose 3))) (fun n : ℕ => (3 * (n + 1))) (by norm_num) he
  convert h.1 using 1 <;> norm_num [p162]
theorem p162_domain : ∀ n, p162 n ≠ 0 := by
  intro n; unfold p162; positivity
theorem p162_unique (a : ℕ → ℚ) (hi : a 0 = (3 : ℚ)) (hj : a 1 = (9 : ℚ))
    (ha : ∀ n : ℕ, a (n + 2) * a n = (3 : ℚ) ^ ((3 * (n + 1))) * a (n + 1) ^ 2) :
    ∀ n, a n = p162 n := by
  apply general_second_unique p162_valid
  apply multiplicative_from_relation a (3 : ℚ) (9 : ℚ) (fun n => (3 : ℚ) ^ ((3 * (n + 1)))) hi hj
  · norm_num
  · norm_num
  · intro n; positivity
  · exact ha
#print axioms p162_domain
#print axioms p162_valid
#print axioms p162_unique

def p167 (n : ℕ) : ℚ := ((n : ℚ) + 1)
theorem p167_base_valid : FirstCertificate p167 (1 : ℚ) (fun n x => ((1 : ℚ) * x + (1 : ℚ)) / (1 : ℚ)) := by
  apply linear_certificate p167 (1 : ℚ) (fun n : ℕ => (1 : ℚ)) (fun n : ℕ => (1 : ℚ)) (fun n : ℕ => (1 : ℚ))
  · norm_num [p167]
  · intro n; positivity
  · intro n
    simp only [p167, Nat.cast_add, Nat.cast_one, pow_succ, pow_add] at *
    ring
theorem p167_valid : FirstCertificate p167 (1 : ℚ) (fun n x => ((1 : ℚ) * x + (1 : ℚ)) / (1 : ℚ)) := p167_base_valid
theorem p167_unique (a : ℕ → ℚ) (ha : FirstCertificate a (1 : ℚ) (fun n x => ((1 : ℚ) * x + (1 : ℚ)) / (1 : ℚ))) :
    ∀ n, a n = p167 n := first_unique p167_valid ha
#print axioms p167_valid
#print axioms p167_unique

def p240 (n : ℕ) : ℚ := (((2 : ℚ) * ((n : ℚ) + 1)) + (-1 : ℚ))
theorem p240_base_valid : FirstCertificate p240 (1 : ℚ) (fun n x => ((1 : ℚ) * x + (2 : ℚ)) / (1 : ℚ)) := by
  apply linear_certificate p240 (1 : ℚ) (fun n : ℕ => (1 : ℚ)) (fun n : ℕ => (1 : ℚ)) (fun n : ℕ => (2 : ℚ))
  · norm_num [p240]
  · intro n; positivity
  · intro n
    simp only [p240, Nat.cast_add, Nat.cast_one, pow_succ, pow_add] at *
    ring
theorem p240_valid : FirstCertificate p240 (1 : ℚ) (fun n x => ((1 : ℚ) * x + (2 : ℚ)) / (1 : ℚ)) := p240_base_valid
theorem p240_unique (a : ℕ → ℚ) (ha : FirstCertificate a (1 : ℚ) (fun n x => ((1 : ℚ) * x + (2 : ℚ)) / (1 : ℚ))) :
    ∀ n, a n = p240 n := first_unique p240_valid ha
#print axioms p240_valid
#print axioms p240_unique

def p234 (n : ℕ) : ℚ := (((3 : ℚ) * ((n : ℚ) + 1)) + (-2 : ℚ))
theorem p234_base_valid : FirstCertificate p234 (1 : ℚ) (fun n x => ((1 : ℚ) * x + (3 : ℚ)) / (1 : ℚ)) := by
  apply linear_certificate p234 (1 : ℚ) (fun n : ℕ => (1 : ℚ)) (fun n : ℕ => (1 : ℚ)) (fun n : ℕ => (3 : ℚ))
  · norm_num [p234]
  · intro n; positivity
  · intro n
    simp only [p234, Nat.cast_add, Nat.cast_one, pow_succ, pow_add] at *
    ring
theorem p234_valid : FirstCertificate p234 (1 : ℚ) (fun n x => ((1 : ℚ) * x + (3 : ℚ)) / (1 : ℚ)) := p234_base_valid
theorem p234_unique (a : ℕ → ℚ) (ha : FirstCertificate a (1 : ℚ) (fun n x => ((1 : ℚ) * x + (3 : ℚ)) / (1 : ℚ))) :
    ∀ n, a n = p234 n := first_unique p234_valid ha
#print axioms p234_valid
#print axioms p234_unique

def p251 (n : ℕ) : ℚ := (((4 : ℚ) * ((n : ℚ) + 1)) + (-3 : ℚ))
theorem p251_base_valid : FirstCertificate p251 (1 : ℚ) (fun n x => ((1 : ℚ) * x + (4 : ℚ)) / (1 : ℚ)) := by
  apply linear_certificate p251 (1 : ℚ) (fun n : ℕ => (1 : ℚ)) (fun n : ℕ => (1 : ℚ)) (fun n : ℕ => (4 : ℚ))
  · norm_num [p251]
  · intro n; positivity
  · intro n
    simp only [p251, Nat.cast_add, Nat.cast_one, pow_succ, pow_add] at *
    ring
theorem p251_valid : FirstCertificate p251 (1 : ℚ) (fun n x => ((1 : ℚ) * x + (4 : ℚ)) / (1 : ℚ)) := p251_base_valid
theorem p251_unique (a : ℕ → ℚ) (ha : FirstCertificate a (1 : ℚ) (fun n x => ((1 : ℚ) * x + (4 : ℚ)) / (1 : ℚ))) :
    ∀ n, a n = p251 n := first_unique p251_valid ha
#print axioms p251_valid
#print axioms p251_unique

def p252 (n : ℕ) : ℚ := ((((1 : ℚ) / 2) * ((n : ℚ) + 1)) + ((1 : ℚ) / 2))
theorem p252_base_valid : FirstCertificate p252 (1 : ℚ) (fun n x => ((1 : ℚ) * x + ((1 : ℚ) / 2)) / (1 : ℚ)) := by
  apply linear_certificate p252 (1 : ℚ) (fun n : ℕ => (1 : ℚ)) (fun n : ℕ => (1 : ℚ)) (fun n : ℕ => ((1 : ℚ) / 2))
  · norm_num [p252]
  · intro n; positivity
  · intro n
    simp only [p252, Nat.cast_add, Nat.cast_one, pow_succ, pow_add] at *
    ring
theorem p252_valid : FirstCertificate p252 (1 : ℚ) (fun n x => ((1 : ℚ) * x + ((1 : ℚ) / 2)) / (1 : ℚ)) := p252_base_valid
theorem p252_unique (a : ℕ → ℚ) (ha : FirstCertificate a (1 : ℚ) (fun n x => ((1 : ℚ) * x + ((1 : ℚ) / 2)) / (1 : ℚ))) :
    ∀ n, a n = p252 n := first_unique p252_valid ha
#print axioms p252_valid
#print axioms p252_unique

def p250 (n : ℕ) : ℚ := (((-1 : ℚ) * ((n : ℚ) + 1)) + (2 : ℚ))
theorem p250_base_valid : FirstCertificate p250 (1 : ℚ) (fun n x => ((1 : ℚ) * x + (-1 : ℚ)) / (1 : ℚ)) := by
  apply linear_certificate p250 (1 : ℚ) (fun n : ℕ => (1 : ℚ)) (fun n : ℕ => (1 : ℚ)) (fun n : ℕ => (-1 : ℚ))
  · norm_num [p250]
  · intro n; positivity
  · intro n
    simp only [p250, Nat.cast_add, Nat.cast_one, pow_succ, pow_add] at *
    ring
theorem p250_valid : FirstCertificate p250 (1 : ℚ) (fun n x => ((1 : ℚ) * x + (-1 : ℚ)) / (1 : ℚ)) := p250_base_valid
theorem p250_unique (a : ℕ → ℚ) (ha : FirstCertificate a (1 : ℚ) (fun n x => ((1 : ℚ) * x + (-1 : ℚ)) / (1 : ℚ))) :
    ∀ n, a n = p250 n := first_unique p250_valid ha
#print axioms p250_valid
#print axioms p250_unique

def p210 (n : ℕ) : ℚ := (((2 : ℚ) * (((n : ℚ) + 1) ^ 2)) + (-1 : ℚ))
theorem p210_base_valid : FirstCertificate p210 (1 : ℚ) (fun n x => ((1 : ℚ) * x + ((2 : ℚ) * (((2 : ℚ) * ((n : ℚ) + 1)) + (1 : ℚ)))) / (1 : ℚ)) := by
  apply linear_certificate p210 (1 : ℚ) (fun n : ℕ => (1 : ℚ)) (fun n : ℕ => (1 : ℚ)) (fun n : ℕ => ((2 : ℚ) * (((2 : ℚ) * ((n : ℚ) + 1)) + (1 : ℚ))))
  · norm_num [p210]
  · intro n; positivity
  · intro n
    simp only [p210, Nat.cast_add, Nat.cast_one, pow_succ, pow_add] at *
    ring
theorem p210_valid : FirstCertificate p210 (1 : ℚ) (fun n x => ((1 : ℚ) * x + ((2 : ℚ) * (((2 : ℚ) * ((n : ℚ) + 1)) + (1 : ℚ)))) / (1 : ℚ)) := p210_base_valid
theorem p210_unique (a : ℕ → ℚ) (ha : FirstCertificate a (1 : ℚ) (fun n x => ((1 : ℚ) * x + ((2 : ℚ) * (((2 : ℚ) * ((n : ℚ) + 1)) + (1 : ℚ)))) / (1 : ℚ))) :
    ∀ n, a n = p210 n := first_unique p210_valid ha
#print axioms p210_valid
#print axioms p210_unique

def p215 (n : ℕ) : ℚ := ((((n : ℚ) + 1) ^ 2) + ((-1 : ℚ) * ((n : ℚ) + 1)) + (1 : ℚ))
theorem p215_base_valid : FirstCertificate p215 (1 : ℚ) (fun n x => ((1 : ℚ) * x + ((2 : ℚ) * ((n : ℚ) + 1))) / (1 : ℚ)) := by
  apply linear_certificate p215 (1 : ℚ) (fun n : ℕ => (1 : ℚ)) (fun n : ℕ => (1 : ℚ)) (fun n : ℕ => ((2 : ℚ) * ((n : ℚ) + 1)))
  · norm_num [p215]
  · intro n; positivity
  · intro n
    simp only [p215, Nat.cast_add, Nat.cast_one, pow_succ, pow_add] at *
    ring
theorem p215_valid : FirstCertificate p215 (1 : ℚ) (fun n x => ((1 : ℚ) * x + ((2 : ℚ) * ((n : ℚ) + 1))) / (1 : ℚ)) := p215_base_valid
theorem p215_unique (a : ℕ → ℚ) (ha : FirstCertificate a (1 : ℚ) (fun n x => ((1 : ℚ) * x + ((2 : ℚ) * ((n : ℚ) + 1))) / (1 : ℚ))) :
    ∀ n, a n = p215 n := first_unique p215_valid ha
#print axioms p215_valid
#print axioms p215_unique

def p241 (n : ℕ) : ℚ := ((((2 : ℚ) / 3) * (((n : ℚ) + 1) ^ 3)) + (((-2 : ℚ) / 3) * ((n : ℚ) + 1)) + (1 : ℚ))
theorem p241_base_valid : FirstCertificate p241 (1 : ℚ) (fun n x => ((1 : ℚ) * x + ((2 : ℚ) * ((n : ℚ) + 1) * (((n : ℚ) + 1) + (1 : ℚ)))) / (1 : ℚ)) := by
  apply linear_certificate p241 (1 : ℚ) (fun n : ℕ => (1 : ℚ)) (fun n : ℕ => (1 : ℚ)) (fun n : ℕ => ((2 : ℚ) * ((n : ℚ) + 1) * (((n : ℚ) + 1) + (1 : ℚ))))
  · norm_num [p241]
  · intro n; positivity
  · intro n
    simp only [p241, Nat.cast_add, Nat.cast_one, pow_succ, pow_add] at *
    ring
theorem p241_valid : FirstCertificate p241 (1 : ℚ) (fun n x => ((1 : ℚ) * x + ((2 : ℚ) * ((n : ℚ) + 1) * (((n : ℚ) + 1) + (1 : ℚ)))) / (1 : ℚ)) := p241_base_valid
theorem p241_unique (a : ℕ → ℚ) (ha : FirstCertificate a (1 : ℚ) (fun n x => ((1 : ℚ) * x + ((2 : ℚ) * ((n : ℚ) + 1) * (((n : ℚ) + 1) + (1 : ℚ)))) / (1 : ℚ))) :
    ∀ n, a n = p241 n := first_unique p241_valid ha
#print axioms p241_valid
#print axioms p241_unique

def p224 (n : ℕ) : ℚ := (((n : ℚ) + 1) ^ 2)
theorem p224_base_valid : FirstCertificate p224 (1 : ℚ) (fun n x => ((1 : ℚ) * x + (((2 : ℚ) * ((n : ℚ) + 1)) + (1 : ℚ))) / (1 : ℚ)) := by
  apply linear_certificate p224 (1 : ℚ) (fun n : ℕ => (1 : ℚ)) (fun n : ℕ => (1 : ℚ)) (fun n : ℕ => (((2 : ℚ) * ((n : ℚ) + 1)) + (1 : ℚ)))
  · norm_num [p224]
  · intro n; positivity
  · intro n
    simp only [p224, Nat.cast_add, Nat.cast_one, pow_succ, pow_add] at *
    ring
theorem p224_valid : FirstCertificate p224 (1 : ℚ) (fun n x => ((1 : ℚ) * x + (((2 : ℚ) * ((n : ℚ) + 1)) + (1 : ℚ))) / (1 : ℚ)) := p224_base_valid
theorem p224_unique (a : ℕ → ℚ) (ha : FirstCertificate a (1 : ℚ) (fun n x => ((1 : ℚ) * x + (((2 : ℚ) * ((n : ℚ) + 1)) + (1 : ℚ))) / (1 : ℚ))) :
    ∀ n, a n = p224 n := first_unique p224_valid ha
#print axioms p224_valid
#print axioms p224_unique

def p170 (n : ℕ) : ℚ := ((((1 : ℚ) / 2) * (((n : ℚ) + 1) ^ 2)) + (((-1 : ℚ) / 2) * ((n : ℚ) + 1)) + (1 : ℚ))
theorem p170_base_valid : FirstCertificate p170 (1 : ℚ) (fun n x => ((1 : ℚ) * x + ((n : ℚ) + 1)) / (1 : ℚ)) := by
  apply linear_certificate p170 (1 : ℚ) (fun n : ℕ => (1 : ℚ)) (fun n : ℕ => (1 : ℚ)) (fun n : ℕ => ((n : ℚ) + 1))
  · norm_num [p170]
  · intro n; positivity
  · intro n
    simp only [p170, Nat.cast_add, Nat.cast_one, pow_succ, pow_add] at *
    ring
theorem p170_valid : FirstCertificate p170 (1 : ℚ) (fun n x => ((1 : ℚ) * x + ((n : ℚ) + 1)) / (1 : ℚ)) := p170_base_valid
theorem p170_unique (a : ℕ → ℚ) (ha : FirstCertificate a (1 : ℚ) (fun n x => ((1 : ℚ) * x + ((n : ℚ) + 1)) / (1 : ℚ))) :
    ∀ n, a n = p170 n := first_unique p170_valid ha
#print axioms p170_valid
#print axioms p170_unique

def p175 (n : ℕ) : ℚ := ((((n : ℚ) + 1) ^ 3) + ((-1 : ℚ) * ((n : ℚ) + 1)) + (1 : ℚ))
theorem p175_base_valid : FirstCertificate p175 (1 : ℚ) (fun n x => ((1 : ℚ) * x + ((3 : ℚ) * ((n : ℚ) + 1) * (((n : ℚ) + 1) + (1 : ℚ)))) / (1 : ℚ)) := by
  apply linear_certificate p175 (1 : ℚ) (fun n : ℕ => (1 : ℚ)) (fun n : ℕ => (1 : ℚ)) (fun n : ℕ => ((3 : ℚ) * ((n : ℚ) + 1) * (((n : ℚ) + 1) + (1 : ℚ))))
  · norm_num [p175]
  · intro n; positivity
  · intro n
    simp only [p175, Nat.cast_add, Nat.cast_one, pow_succ, pow_add] at *
    ring
theorem p175_valid : FirstCertificate p175 (1 : ℚ) (fun n x => ((1 : ℚ) * x + ((3 : ℚ) * ((n : ℚ) + 1) * (((n : ℚ) + 1) + (1 : ℚ)))) / (1 : ℚ)) := p175_base_valid
theorem p175_unique (a : ℕ → ℚ) (ha : FirstCertificate a (1 : ℚ) (fun n x => ((1 : ℚ) * x + ((3 : ℚ) * ((n : ℚ) + 1) * (((n : ℚ) + 1) + (1 : ℚ)))) / (1 : ℚ))) :
    ∀ n, a n = p175 n := first_unique p175_valid ha
#print axioms p175_valid
#print axioms p175_unique

def p242 (n : ℕ) : ℚ := (((1 : ℚ) / 2) * (((3 : ℚ) ^ n) + ((1 : ℚ) ^ n)))
def p242_b (n : ℕ) : ℚ := (((1 : ℚ) / 2) * (((3 : ℚ) ^ n) + ((-1 : ℚ) * ((1 : ℚ) ^ n))))
theorem p242_valid : SystemCertificate p242 p242_b (1 : ℚ) (0 : ℚ) (fun n x y => (((2 : ℚ) * x) + y) / (1 : ℚ)) (fun n x y => (x + ((2 : ℚ) * y)) / (1 : ℚ)) := by
  constructor
  · norm_num [p242]
  · norm_num [p242_b]
  · intro n
    apply (eq_div_iff (show (1 : ℚ) ≠ 0 by positivity)).2
    simp only [p242, p242_b, Nat.cast_add, Nat.cast_one, pow_succ, pow_add]
    norm_num <;> ring
  · intro n
    apply (eq_div_iff (show (1 : ℚ) ≠ 0 by positivity)).2
    simp only [p242, p242_b, Nat.cast_add, Nat.cast_one, pow_succ, pow_add]
    norm_num <;> ring
theorem p242_unique (a b : ℕ → ℚ) (ha : SystemCertificate a b (1 : ℚ) (0 : ℚ) (fun n x y => (((2 : ℚ) * x) + y) / (1 : ℚ)) (fun n x y => (x + ((2 : ℚ) * y)) / (1 : ℚ))) :
    ∀ n, a n = p242 n ∧ b n = p242_b n := system_unique p242_valid ha
#print axioms p242_valid
#print axioms p242_unique

def p230 (n : ℕ) : ℚ := (((1 : ℚ) / 2) * (((2 : ℚ) ^ n) + ((-2 : ℚ) ^ n)))
def p230_b (n : ℕ) : ℚ := (((1 : ℚ) / 2) * (((2 : ℚ) ^ n) + ((-1 : ℚ) * ((-2 : ℚ) ^ n))))
theorem p230_valid : SystemCertificate p230 p230_b (1 : ℚ) (0 : ℚ) (fun n x y => ((2 : ℚ) * y) / (1 : ℚ)) (fun n x y => ((2 : ℚ) * x) / (1 : ℚ)) := by
  constructor
  · norm_num [p230]
  · norm_num [p230_b]
  · intro n
    apply (eq_div_iff (show (1 : ℚ) ≠ 0 by positivity)).2
    simp only [p230, p230_b, Nat.cast_add, Nat.cast_one, pow_succ, pow_add]
    norm_num <;> ring
  · intro n
    apply (eq_div_iff (show (1 : ℚ) ≠ 0 by positivity)).2
    simp only [p230, p230_b, Nat.cast_add, Nat.cast_one, pow_succ, pow_add]
    norm_num <;> ring
theorem p230_unique (a b : ℕ → ℚ) (ha : SystemCertificate a b (1 : ℚ) (0 : ℚ) (fun n x y => ((2 : ℚ) * y) / (1 : ℚ)) (fun n x y => ((2 : ℚ) * x) / (1 : ℚ))) :
    ∀ n, a n = p230 n ∧ b n = p230_b n := system_unique p230_valid ha
#print axioms p230_valid
#print axioms p230_unique

def p196 (n : ℕ) : ℚ := (((1 : ℚ) / 2) * (((2 : ℚ) ^ n) + ((4 : ℚ) ^ n)))
def p196_b (n : ℕ) : ℚ := (((1 : ℚ) / 2) * (((2 : ℚ) ^ n) + ((-1 : ℚ) * ((4 : ℚ) ^ n))))
theorem p196_valid : SystemCertificate p196 p196_b (1 : ℚ) (0 : ℚ) (fun n x y => (((3 : ℚ) * x) + ((-1 : ℚ) * y)) / (1 : ℚ)) (fun n x y => (((-1 : ℚ) * x) + ((3 : ℚ) * y)) / (1 : ℚ)) := by
  constructor
  · norm_num [p196]
  · norm_num [p196_b]
  · intro n
    apply (eq_div_iff (show (1 : ℚ) ≠ 0 by positivity)).2
    simp only [p196, p196_b, Nat.cast_add, Nat.cast_one, pow_succ, pow_add]
    norm_num <;> ring
  · intro n
    apply (eq_div_iff (show (1 : ℚ) ≠ 0 by positivity)).2
    simp only [p196, p196_b, Nat.cast_add, Nat.cast_one, pow_succ, pow_add]
    norm_num <;> ring
theorem p196_unique (a b : ℕ → ℚ) (ha : SystemCertificate a b (1 : ℚ) (0 : ℚ) (fun n x y => (((3 : ℚ) * x) + ((-1 : ℚ) * y)) / (1 : ℚ)) (fun n x y => (((-1 : ℚ) * x) + ((3 : ℚ) * y)) / (1 : ℚ))) :
    ∀ n, a n = p196 n ∧ b n = p196_b n := system_unique p196_valid ha
#print axioms p196_valid
#print axioms p196_unique

def p214 (n : ℕ) : ℚ := (((1 : ℚ) / 2) * (((2 : ℚ) ^ n) + ((-1 : ℚ) ^ n)))
def p214_b (n : ℕ) : ℚ := (((1 : ℚ) / 2) * (((2 : ℚ) ^ n) + ((-1 : ℚ) * ((-1 : ℚ) ^ n))))
theorem p214_valid : SystemCertificate p214 p214_b (1 : ℚ) (0 : ℚ) (fun n x y => ((((1 : ℚ) / 2) * x) + (((3 : ℚ) / 2) * y)) / (1 : ℚ)) (fun n x y => ((((3 : ℚ) / 2) * x) + (((1 : ℚ) / 2) * y)) / (1 : ℚ)) := by
  constructor
  · norm_num [p214]
  · norm_num [p214_b]
  · intro n
    apply (eq_div_iff (show (1 : ℚ) ≠ 0 by positivity)).2
    simp only [p214, p214_b, Nat.cast_add, Nat.cast_one, pow_succ, pow_add]
    norm_num <;> ring
  · intro n
    apply (eq_div_iff (show (1 : ℚ) ≠ 0 by positivity)).2
    simp only [p214, p214_b, Nat.cast_add, Nat.cast_one, pow_succ, pow_add]
    norm_num <;> ring
theorem p214_unique (a b : ℕ → ℚ) (ha : SystemCertificate a b (1 : ℚ) (0 : ℚ) (fun n x y => ((((1 : ℚ) / 2) * x) + (((3 : ℚ) / 2) * y)) / (1 : ℚ)) (fun n x y => ((((3 : ℚ) / 2) * x) + (((1 : ℚ) / 2) * y)) / (1 : ℚ))) :
    ∀ n, a n = p214 n ∧ b n = p214_b n := system_unique p214_valid ha
#print axioms p214_valid
#print axioms p214_unique

def p203 (n : ℕ) : ℚ := (((1 : ℚ) / 2) * (((3 : ℚ) ^ n) + ((-2 : ℚ) ^ n)))
def p203_b (n : ℕ) : ℚ := (((1 : ℚ) / 2) * (((3 : ℚ) ^ n) + ((-1 : ℚ) * ((-2 : ℚ) ^ n))))
theorem p203_valid : SystemCertificate p203 p203_b (1 : ℚ) (0 : ℚ) (fun n x y => ((((1 : ℚ) / 2) * x) + (((5 : ℚ) / 2) * y)) / (1 : ℚ)) (fun n x y => ((((5 : ℚ) / 2) * x) + (((1 : ℚ) / 2) * y)) / (1 : ℚ)) := by
  constructor
  · norm_num [p203]
  · norm_num [p203_b]
  · intro n
    apply (eq_div_iff (show (1 : ℚ) ≠ 0 by positivity)).2
    simp only [p203, p203_b, Nat.cast_add, Nat.cast_one, pow_succ, pow_add]
    norm_num <;> ring
  · intro n
    apply (eq_div_iff (show (1 : ℚ) ≠ 0 by positivity)).2
    simp only [p203, p203_b, Nat.cast_add, Nat.cast_one, pow_succ, pow_add]
    norm_num <;> ring
theorem p203_unique (a b : ℕ → ℚ) (ha : SystemCertificate a b (1 : ℚ) (0 : ℚ) (fun n x y => ((((1 : ℚ) / 2) * x) + (((5 : ℚ) / 2) * y)) / (1 : ℚ)) (fun n x y => ((((5 : ℚ) / 2) * x) + (((1 : ℚ) / 2) * y)) / (1 : ℚ))) :
    ∀ n, a n = p203 n ∧ b n = p203_b n := system_unique p203_valid ha
#print axioms p203_valid
#print axioms p203_unique

def p187 (n : ℕ) : ℚ := (((1 : ℚ) / 2) * (((2 : ℚ) ^ n) + ((1 : ℚ) ^ n)))
def p187_b (n : ℕ) : ℚ := (((1 : ℚ) / 2) * (((2 : ℚ) ^ n) + ((-1 : ℚ) * ((1 : ℚ) ^ n))))
theorem p187_valid : SystemCertificate p187 p187_b (1 : ℚ) (0 : ℚ) (fun n x y => ((((3 : ℚ) / 2) * x) + (((1 : ℚ) / 2) * y)) / (1 : ℚ)) (fun n x y => ((((1 : ℚ) / 2) * x) + (((3 : ℚ) / 2) * y)) / (1 : ℚ)) := by
  constructor
  · norm_num [p187]
  · norm_num [p187_b]
  · intro n
    apply (eq_div_iff (show (1 : ℚ) ≠ 0 by positivity)).2
    simp only [p187, p187_b, Nat.cast_add, Nat.cast_one, pow_succ, pow_add]
    norm_num <;> ring
  · intro n
    apply (eq_div_iff (show (1 : ℚ) ≠ 0 by positivity)).2
    simp only [p187, p187_b, Nat.cast_add, Nat.cast_one, pow_succ, pow_add]
    norm_num <;> ring
theorem p187_unique (a b : ℕ → ℚ) (ha : SystemCertificate a b (1 : ℚ) (0 : ℚ) (fun n x y => ((((3 : ℚ) / 2) * x) + (((1 : ℚ) / 2) * y)) / (1 : ℚ)) (fun n x y => ((((1 : ℚ) / 2) * x) + (((3 : ℚ) / 2) * y)) / (1 : ℚ))) :
    ∀ n, a n = p187 n ∧ b n = p187_b n := system_unique p187_valid ha
#print axioms p187_valid
#print axioms p187_unique

def p206 (n : ℕ) : ℚ := (((1 : ℚ) / 2) * (((3 : ℚ) ^ n) + ((2 : ℚ) ^ n)))
def p206_b (n : ℕ) : ℚ := (((1 : ℚ) / 2) * (((3 : ℚ) ^ n) + ((-1 : ℚ) * ((2 : ℚ) ^ n))))
theorem p206_valid : SystemCertificate p206 p206_b (1 : ℚ) (0 : ℚ) (fun n x y => ((((5 : ℚ) / 2) * x) + (((1 : ℚ) / 2) * y)) / (1 : ℚ)) (fun n x y => ((((1 : ℚ) / 2) * x) + (((5 : ℚ) / 2) * y)) / (1 : ℚ)) := by
  constructor
  · norm_num [p206]
  · norm_num [p206_b]
  · intro n
    apply (eq_div_iff (show (1 : ℚ) ≠ 0 by positivity)).2
    simp only [p206, p206_b, Nat.cast_add, Nat.cast_one, pow_succ, pow_add]
    norm_num <;> ring
  · intro n
    apply (eq_div_iff (show (1 : ℚ) ≠ 0 by positivity)).2
    simp only [p206, p206_b, Nat.cast_add, Nat.cast_one, pow_succ, pow_add]
    norm_num <;> ring
theorem p206_unique (a b : ℕ → ℚ) (ha : SystemCertificate a b (1 : ℚ) (0 : ℚ) (fun n x y => ((((5 : ℚ) / 2) * x) + (((1 : ℚ) / 2) * y)) / (1 : ℚ)) (fun n x y => ((((1 : ℚ) / 2) * x) + (((5 : ℚ) / 2) * y)) / (1 : ℚ))) :
    ∀ n, a n = p206 n ∧ b n = p206_b n := system_unique p206_valid ha
#print axioms p206_valid
#print axioms p206_unique

def p213 (n : ℕ) : ℚ := (((1 : ℚ) / 2) * (((2 : ℚ) ^ n) + ((3 : ℚ) ^ n)))
def p213_b (n : ℕ) : ℚ := (((1 : ℚ) / 2) * (((2 : ℚ) ^ n) + ((-1 : ℚ) * ((3 : ℚ) ^ n))))
theorem p213_valid : SystemCertificate p213 p213_b (1 : ℚ) (0 : ℚ) (fun n x y => ((((5 : ℚ) / 2) * x) + (((-1 : ℚ) / 2) * y)) / (1 : ℚ)) (fun n x y => ((((-1 : ℚ) / 2) * x) + (((5 : ℚ) / 2) * y)) / (1 : ℚ)) := by
  constructor
  · norm_num [p213]
  · norm_num [p213_b]
  · intro n
    apply (eq_div_iff (show (1 : ℚ) ≠ 0 by positivity)).2
    simp only [p213, p213_b, Nat.cast_add, Nat.cast_one, pow_succ, pow_add]
    norm_num <;> ring
  · intro n
    apply (eq_div_iff (show (1 : ℚ) ≠ 0 by positivity)).2
    simp only [p213, p213_b, Nat.cast_add, Nat.cast_one, pow_succ, pow_add]
    norm_num <;> ring
theorem p213_unique (a b : ℕ → ℚ) (ha : SystemCertificate a b (1 : ℚ) (0 : ℚ) (fun n x y => ((((5 : ℚ) / 2) * x) + (((-1 : ℚ) / 2) * y)) / (1 : ℚ)) (fun n x y => ((((-1 : ℚ) / 2) * x) + (((5 : ℚ) / 2) * y)) / (1 : ℚ))) :
    ∀ n, a n = p213 n ∧ b n = p213_b n := system_unique p213_valid ha
#print axioms p213_valid
#print axioms p213_unique

def p192 (n : ℕ) : ℚ := (((1 : ℚ) / 2) * (((2 : ℚ) * ((3 : ℚ) ^ n)) + ((2 : ℚ) * ((1 : ℚ) ^ n))))
def p192_b (n : ℕ) : ℚ := (((1 : ℚ) / 4) * (((2 : ℚ) * ((3 : ℚ) ^ n)) + ((-2 : ℚ) * ((1 : ℚ) ^ n))))
theorem p192_valid : SystemCertificate p192 p192_b (2 : ℚ) (0 : ℚ) (fun n x y => (((2 : ℚ) * x) + ((2 : ℚ) * y)) / (1 : ℚ)) (fun n x y => ((((1 : ℚ) / 2) * x) + ((2 : ℚ) * y)) / (1 : ℚ)) := by
  constructor
  · norm_num [p192]
  · norm_num [p192_b]
  · intro n
    apply (eq_div_iff (show (1 : ℚ) ≠ 0 by positivity)).2
    simp only [p192, p192_b, Nat.cast_add, Nat.cast_one, pow_succ, pow_add]
    norm_num <;> ring
  · intro n
    apply (eq_div_iff (show (1 : ℚ) ≠ 0 by positivity)).2
    simp only [p192, p192_b, Nat.cast_add, Nat.cast_one, pow_succ, pow_add]
    norm_num <;> ring
theorem p192_unique (a b : ℕ → ℚ) (ha : SystemCertificate a b (2 : ℚ) (0 : ℚ) (fun n x y => (((2 : ℚ) * x) + ((2 : ℚ) * y)) / (1 : ℚ)) (fun n x y => ((((1 : ℚ) / 2) * x) + ((2 : ℚ) * y)) / (1 : ℚ))) :
    ∀ n, a n = p192 n ∧ b n = p192_b n := system_unique p192_valid ha
#print axioms p192_valid
#print axioms p192_unique

def p169 (n : ℕ) : ℚ := (((1 : ℚ) / 2) * (((3 : ℚ) ^ n) + ((3 : ℚ) * ((1 : ℚ) ^ n))))
def p169_b (n : ℕ) : ℚ := (((1 : ℚ) / 6) * (((3 : ℚ) ^ n) + ((-3 : ℚ) * ((1 : ℚ) ^ n))))
theorem p169_valid : SystemCertificate p169 p169_b (2 : ℚ) ((-1 : ℚ) / 3) (fun n x y => (((2 : ℚ) * x) + ((3 : ℚ) * y)) / (1 : ℚ)) (fun n x y => ((((1 : ℚ) / 3) * x) + ((2 : ℚ) * y)) / (1 : ℚ)) := by
  constructor
  · norm_num [p169]
  · norm_num [p169_b]
  · intro n
    apply (eq_div_iff (show (1 : ℚ) ≠ 0 by positivity)).2
    simp only [p169, p169_b, Nat.cast_add, Nat.cast_one, pow_succ, pow_add]
    norm_num <;> ring
  · intro n
    apply (eq_div_iff (show (1 : ℚ) ≠ 0 by positivity)).2
    simp only [p169, p169_b, Nat.cast_add, Nat.cast_one, pow_succ, pow_add]
    norm_num <;> ring
theorem p169_unique (a b : ℕ → ℚ) (ha : SystemCertificate a b (2 : ℚ) ((-1 : ℚ) / 3) (fun n x y => (((2 : ℚ) * x) + ((3 : ℚ) * y)) / (1 : ℚ)) (fun n x y => ((((1 : ℚ) / 3) * x) + ((2 : ℚ) * y)) / (1 : ℚ))) :
    ∀ n, a n = p169 n ∧ b n = p169_b n := system_unique p169_valid ha
#print axioms p169_valid
#print axioms p169_unique

def p225 (n : ℕ) : ℚ := (((1 : ℚ) / 2) * (((2 : ℚ) * ((2 : ℚ) ^ n)) + ((2 : ℚ) * ((4 : ℚ) ^ n))))
def p225_b (n : ℕ) : ℚ := (((1 : ℚ) / 4) * (((2 : ℚ) * ((2 : ℚ) ^ n)) + ((-2 : ℚ) * ((4 : ℚ) ^ n))))
theorem p225_valid : SystemCertificate p225 p225_b (2 : ℚ) (0 : ℚ) (fun n x y => (((3 : ℚ) * x) + ((-2 : ℚ) * y)) / (1 : ℚ)) (fun n x y => ((((-1 : ℚ) / 2) * x) + ((3 : ℚ) * y)) / (1 : ℚ)) := by
  constructor
  · norm_num [p225]
  · norm_num [p225_b]
  · intro n
    apply (eq_div_iff (show (1 : ℚ) ≠ 0 by positivity)).2
    simp only [p225, p225_b, Nat.cast_add, Nat.cast_one, pow_succ, pow_add]
    norm_num <;> ring
  · intro n
    apply (eq_div_iff (show (1 : ℚ) ≠ 0 by positivity)).2
    simp only [p225, p225_b, Nat.cast_add, Nat.cast_one, pow_succ, pow_add]
    norm_num <;> ring
theorem p225_unique (a b : ℕ → ℚ) (ha : SystemCertificate a b (2 : ℚ) (0 : ℚ) (fun n x y => (((3 : ℚ) * x) + ((-2 : ℚ) * y)) / (1 : ℚ)) (fun n x y => ((((-1 : ℚ) / 2) * x) + ((3 : ℚ) * y)) / (1 : ℚ))) :
    ∀ n, a n = p225 n ∧ b n = p225_b n := system_unique p225_valid ha
#print axioms p225_valid
#print axioms p225_unique

def p197 (n : ℕ) : ℚ := (((1 : ℚ) / 2) * (((2 : ℚ) ^ n) + ((3 : ℚ) * ((4 : ℚ) ^ n))))
def p197_b (n : ℕ) : ℚ := (((1 : ℚ) / 6) * (((2 : ℚ) ^ n) + ((-3 : ℚ) * ((4 : ℚ) ^ n))))
theorem p197_valid : SystemCertificate p197 p197_b (2 : ℚ) ((-1 : ℚ) / 3) (fun n x y => (((3 : ℚ) * x) + ((-3 : ℚ) * y)) / (1 : ℚ)) (fun n x y => ((((-1 : ℚ) / 3) * x) + ((3 : ℚ) * y)) / (1 : ℚ)) := by
  constructor
  · norm_num [p197]
  · norm_num [p197_b]
  · intro n
    apply (eq_div_iff (show (1 : ℚ) ≠ 0 by positivity)).2
    simp only [p197, p197_b, Nat.cast_add, Nat.cast_one, pow_succ, pow_add]
    norm_num <;> ring
  · intro n
    apply (eq_div_iff (show (1 : ℚ) ≠ 0 by positivity)).2
    simp only [p197, p197_b, Nat.cast_add, Nat.cast_one, pow_succ, pow_add]
    norm_num <;> ring
theorem p197_unique (a b : ℕ → ℚ) (ha : SystemCertificate a b (2 : ℚ) ((-1 : ℚ) / 3) (fun n x y => (((3 : ℚ) * x) + ((-3 : ℚ) * y)) / (1 : ℚ)) (fun n x y => ((((-1 : ℚ) / 3) * x) + ((3 : ℚ) * y)) / (1 : ℚ))) :
    ∀ n, a n = p197 n ∧ b n = p197_b n := system_unique p197_valid ha
#print axioms p197_valid
#print axioms p197_unique

def p229 (n : ℕ) : ℚ := (((1 : ℚ) / 2) * (((2 : ℚ) * ((2 : ℚ) ^ n)) + ((2 : ℚ) * ((-2 : ℚ) ^ n))))
def p229_b (n : ℕ) : ℚ := (((1 : ℚ) / 4) * (((2 : ℚ) * ((2 : ℚ) ^ n)) + ((-2 : ℚ) * ((-2 : ℚ) ^ n))))
theorem p229_valid : SystemCertificate p229 p229_b (2 : ℚ) (0 : ℚ) (fun n x y => ((4 : ℚ) * y) / (1 : ℚ)) (fun n x y => x / (1 : ℚ)) := by
  constructor
  · norm_num [p229]
  · norm_num [p229_b]
  · intro n
    apply (eq_div_iff (show (1 : ℚ) ≠ 0 by positivity)).2
    simp only [p229, p229_b, Nat.cast_add, Nat.cast_one, pow_succ, pow_add]
    norm_num <;> ring
  · intro n
    apply (eq_div_iff (show (1 : ℚ) ≠ 0 by positivity)).2
    simp only [p229, p229_b, Nat.cast_add, Nat.cast_one, pow_succ, pow_add]
    norm_num <;> ring
theorem p229_unique (a b : ℕ → ℚ) (ha : SystemCertificate a b (2 : ℚ) (0 : ℚ) (fun n x y => ((4 : ℚ) * y) / (1 : ℚ)) (fun n x y => x / (1 : ℚ))) :
    ∀ n, a n = p229 n ∧ b n = p229_b n := system_unique p229_valid ha
#print axioms p229_valid
#print axioms p229_unique

def p202 (n : ℕ) : ℚ := (((1 : ℚ) / 2) * (((2 : ℚ) ^ n) + ((3 : ℚ) * ((-2 : ℚ) ^ n))))
def p202_b (n : ℕ) : ℚ := (((1 : ℚ) / 6) * (((2 : ℚ) ^ n) + ((-3 : ℚ) * ((-2 : ℚ) ^ n))))
theorem p202_valid : SystemCertificate p202 p202_b (2 : ℚ) ((-1 : ℚ) / 3) (fun n x y => ((6 : ℚ) * y) / (1 : ℚ)) (fun n x y => (((2 : ℚ) / 3) * x) / (1 : ℚ)) := by
  constructor
  · norm_num [p202]
  · norm_num [p202_b]
  · intro n
    apply (eq_div_iff (show (1 : ℚ) ≠ 0 by positivity)).2
    simp only [p202, p202_b, Nat.cast_add, Nat.cast_one, pow_succ, pow_add]
    norm_num <;> ring
  · intro n
    apply (eq_div_iff (show (1 : ℚ) ≠ 0 by positivity)).2
    simp only [p202, p202_b, Nat.cast_add, Nat.cast_one, pow_succ, pow_add]
    norm_num <;> ring
theorem p202_unique (a b : ℕ → ℚ) (ha : SystemCertificate a b (2 : ℚ) ((-1 : ℚ) / 3) (fun n x y => ((6 : ℚ) * y) / (1 : ℚ)) (fun n x y => (((2 : ℚ) / 3) * x) / (1 : ℚ))) :
    ∀ n, a n = p202 n ∧ b n = p202_b n := system_unique p202_valid ha
#print axioms p202_valid
#print axioms p202_unique

def p190 (n : ℕ) : ℚ := (((1 : ℚ) / 2) * (((2 : ℚ) * ((n : ℚ) + 1)) + (1 : ℚ)) * (((2 : ℚ) ^ n) + ((-2 : ℚ) ^ n)))
def p190_b (n : ℕ) : ℚ := (((1 : ℚ) / 2) * (((2 : ℚ) * ((n : ℚ) + 1)) + (1 : ℚ)) * (((2 : ℚ) ^ n) + ((-1 : ℚ) * ((-2 : ℚ) ^ n))))
theorem p190_valid : SystemCertificate p190 p190_b (3 : ℚ) (0 : ℚ) (fun n x y => ((2 : ℚ) * (((2 : ℚ) * ((n : ℚ) + 1)) + (3 : ℚ)) * y) / (((2 : ℚ) * ((n : ℚ) + 1)) + (1 : ℚ))) (fun n x y => ((2 : ℚ) * (((2 : ℚ) * ((n : ℚ) + 1)) + (3 : ℚ)) * x) / (((2 : ℚ) * ((n : ℚ) + 1)) + (1 : ℚ))) := by
  constructor
  · norm_num [p190]
  · norm_num [p190_b]
  · intro n
    apply (eq_div_iff (show (((2 : ℚ) * ((n : ℚ) + 1)) + (1 : ℚ)) ≠ 0 by positivity)).2
    simp only [p190, p190_b, Nat.cast_add, Nat.cast_one, pow_succ, pow_add]
    norm_num <;> ring
  · intro n
    apply (eq_div_iff (show (((2 : ℚ) * ((n : ℚ) + 1)) + (1 : ℚ)) ≠ 0 by positivity)).2
    simp only [p190, p190_b, Nat.cast_add, Nat.cast_one, pow_succ, pow_add]
    norm_num <;> ring
theorem p190_unique (a b : ℕ → ℚ) (ha : SystemCertificate a b (3 : ℚ) (0 : ℚ) (fun n x y => ((2 : ℚ) * (((2 : ℚ) * ((n : ℚ) + 1)) + (3 : ℚ)) * y) / (((2 : ℚ) * ((n : ℚ) + 1)) + (1 : ℚ))) (fun n x y => ((2 : ℚ) * (((2 : ℚ) * ((n : ℚ) + 1)) + (3 : ℚ)) * x) / (((2 : ℚ) * ((n : ℚ) + 1)) + (1 : ℚ)))) :
    ∀ n, a n = p190 n ∧ b n = p190_b n := system_unique p190_valid ha
#print axioms p190_valid
#print axioms p190_unique

def p246 (n : ℕ) : ℚ := (((1 : ℚ) / 2) * (((n : ℚ) + 1) + (1 : ℚ)) * (((3 : ℚ) ^ n) + ((1 : ℚ) ^ n)))
def p246_b (n : ℕ) : ℚ := (((1 : ℚ) / 2) * (((n : ℚ) + 1) + (1 : ℚ)) * (((3 : ℚ) ^ n) + ((-1 : ℚ) * ((1 : ℚ) ^ n))))
theorem p246_valid : SystemCertificate p246 p246_b (2 : ℚ) (0 : ℚ) (fun n x y => ((((n : ℚ) + 1) + (2 : ℚ)) * (((2 : ℚ) * x) + y)) / (((n : ℚ) + 1) + (1 : ℚ))) (fun n x y => ((((n : ℚ) + 1) + (2 : ℚ)) * (x + ((2 : ℚ) * y))) / (((n : ℚ) + 1) + (1 : ℚ))) := by
  constructor
  · norm_num [p246]
  · norm_num [p246_b]
  · intro n
    apply (eq_div_iff (show (((n : ℚ) + 1) + (1 : ℚ)) ≠ 0 by positivity)).2
    simp only [p246, p246_b, Nat.cast_add, Nat.cast_one, pow_succ, pow_add]
    norm_num <;> ring
  · intro n
    apply (eq_div_iff (show (((n : ℚ) + 1) + (1 : ℚ)) ≠ 0 by positivity)).2
    simp only [p246, p246_b, Nat.cast_add, Nat.cast_one, pow_succ, pow_add]
    norm_num <;> ring
theorem p246_unique (a b : ℕ → ℚ) (ha : SystemCertificate a b (2 : ℚ) (0 : ℚ) (fun n x y => ((((n : ℚ) + 1) + (2 : ℚ)) * (((2 : ℚ) * x) + y)) / (((n : ℚ) + 1) + (1 : ℚ))) (fun n x y => ((((n : ℚ) + 1) + (2 : ℚ)) * (x + ((2 : ℚ) * y))) / (((n : ℚ) + 1) + (1 : ℚ)))) :
    ∀ n, a n = p246 n ∧ b n = p246_b n := system_unique p246_valid ha
#print axioms p246_valid
#print axioms p246_unique

def p184 (n : ℕ) : ℚ := (((1 : ℚ) / 2) * ((n : ℚ) + 1) * (((2 : ℚ) ^ n) + ((4 : ℚ) ^ n)))
def p184_b (n : ℕ) : ℚ := (((1 : ℚ) / 2) * ((n : ℚ) + 1) * (((2 : ℚ) ^ n) + ((-1 : ℚ) * ((4 : ℚ) ^ n))))
theorem p184_valid : SystemCertificate p184 p184_b (1 : ℚ) (0 : ℚ) (fun n x y => ((((n : ℚ) + 1) + (1 : ℚ)) * (((3 : ℚ) * x) + ((-1 : ℚ) * y))) / ((n : ℚ) + 1)) (fun n x y => ((((n : ℚ) + 1) + (1 : ℚ)) * (((-1 : ℚ) * x) + ((3 : ℚ) * y))) / ((n : ℚ) + 1)) := by
  constructor
  · norm_num [p184]
  · norm_num [p184_b]
  · intro n
    apply (eq_div_iff (show ((n : ℚ) + 1) ≠ 0 by positivity)).2
    simp only [p184, p184_b, Nat.cast_add, Nat.cast_one, pow_succ, pow_add]
    norm_num <;> ring
  · intro n
    apply (eq_div_iff (show ((n : ℚ) + 1) ≠ 0 by positivity)).2
    simp only [p184, p184_b, Nat.cast_add, Nat.cast_one, pow_succ, pow_add]
    norm_num <;> ring
theorem p184_unique (a b : ℕ → ℚ) (ha : SystemCertificate a b (1 : ℚ) (0 : ℚ) (fun n x y => ((((n : ℚ) + 1) + (1 : ℚ)) * (((3 : ℚ) * x) + ((-1 : ℚ) * y))) / ((n : ℚ) + 1)) (fun n x y => ((((n : ℚ) + 1) + (1 : ℚ)) * (((-1 : ℚ) * x) + ((3 : ℚ) * y))) / ((n : ℚ) + 1))) :
    ∀ n, a n = p184 n ∧ b n = p184_b n := system_unique p184_valid ha
#print axioms p184_valid
#print axioms p184_unique

def p231 (n : ℕ) : ℚ := (((1 : ℚ) / 2) * (((2 : ℚ) * ((n : ℚ) + 1)) + (1 : ℚ)) * (((3 : ℚ) ^ n) + ((-1 : ℚ) ^ n)))
def p231_b (n : ℕ) : ℚ := (((1 : ℚ) / 2) * (((2 : ℚ) * ((n : ℚ) + 1)) + (1 : ℚ)) * (((3 : ℚ) ^ n) + ((-1 : ℚ) * ((-1 : ℚ) ^ n))))
theorem p231_valid : SystemCertificate p231 p231_b (3 : ℚ) (0 : ℚ) (fun n x y => ((((2 : ℚ) * ((n : ℚ) + 1)) + (3 : ℚ)) * (x + ((2 : ℚ) * y))) / (((2 : ℚ) * ((n : ℚ) + 1)) + (1 : ℚ))) (fun n x y => ((((2 : ℚ) * ((n : ℚ) + 1)) + (3 : ℚ)) * (((2 : ℚ) * x) + y)) / (((2 : ℚ) * ((n : ℚ) + 1)) + (1 : ℚ))) := by
  constructor
  · norm_num [p231]
  · norm_num [p231_b]
  · intro n
    apply (eq_div_iff (show (((2 : ℚ) * ((n : ℚ) + 1)) + (1 : ℚ)) ≠ 0 by positivity)).2
    simp only [p231, p231_b, Nat.cast_add, Nat.cast_one, pow_succ, pow_add]
    norm_num <;> ring
  · intro n
    apply (eq_div_iff (show (((2 : ℚ) * ((n : ℚ) + 1)) + (1 : ℚ)) ≠ 0 by positivity)).2
    simp only [p231, p231_b, Nat.cast_add, Nat.cast_one, pow_succ, pow_add]
    norm_num <;> ring
theorem p231_unique (a b : ℕ → ℚ) (ha : SystemCertificate a b (3 : ℚ) (0 : ℚ) (fun n x y => ((((2 : ℚ) * ((n : ℚ) + 1)) + (3 : ℚ)) * (x + ((2 : ℚ) * y))) / (((2 : ℚ) * ((n : ℚ) + 1)) + (1 : ℚ))) (fun n x y => ((((2 : ℚ) * ((n : ℚ) + 1)) + (3 : ℚ)) * (((2 : ℚ) * x) + y)) / (((2 : ℚ) * ((n : ℚ) + 1)) + (1 : ℚ)))) :
    ∀ n, a n = p231 n ∧ b n = p231_b n := system_unique p231_valid ha
#print axioms p231_valid
#print axioms p231_unique

def p209 (n : ℕ) : ℚ := (((1 : ℚ) / 2) * (((n : ℚ) + 1) + (1 : ℚ)) * (((2 : ℚ) ^ n) + ((-1 : ℚ) ^ n)))
def p209_b (n : ℕ) : ℚ := (((1 : ℚ) / 2) * (((n : ℚ) + 1) + (1 : ℚ)) * (((2 : ℚ) ^ n) + ((-1 : ℚ) * ((-1 : ℚ) ^ n))))
theorem p209_valid : SystemCertificate p209 p209_b (2 : ℚ) (0 : ℚ) (fun n x y => ((((n : ℚ) + 1) + (2 : ℚ)) * ((((1 : ℚ) / 2) * x) + (((3 : ℚ) / 2) * y))) / (((n : ℚ) + 1) + (1 : ℚ))) (fun n x y => ((((n : ℚ) + 1) + (2 : ℚ)) * ((((3 : ℚ) / 2) * x) + (((1 : ℚ) / 2) * y))) / (((n : ℚ) + 1) + (1 : ℚ))) := by
  constructor
  · norm_num [p209]
  · norm_num [p209_b]
  · intro n
    apply (eq_div_iff (show (((n : ℚ) + 1) + (1 : ℚ)) ≠ 0 by positivity)).2
    simp only [p209, p209_b, Nat.cast_add, Nat.cast_one, pow_succ, pow_add]
    norm_num <;> ring
  · intro n
    apply (eq_div_iff (show (((n : ℚ) + 1) + (1 : ℚ)) ≠ 0 by positivity)).2
    simp only [p209, p209_b, Nat.cast_add, Nat.cast_one, pow_succ, pow_add]
    norm_num <;> ring
theorem p209_unique (a b : ℕ → ℚ) (ha : SystemCertificate a b (2 : ℚ) (0 : ℚ) (fun n x y => ((((n : ℚ) + 1) + (2 : ℚ)) * ((((1 : ℚ) / 2) * x) + (((3 : ℚ) / 2) * y))) / (((n : ℚ) + 1) + (1 : ℚ))) (fun n x y => ((((n : ℚ) + 1) + (2 : ℚ)) * ((((3 : ℚ) / 2) * x) + (((1 : ℚ) / 2) * y))) / (((n : ℚ) + 1) + (1 : ℚ)))) :
    ∀ n, a n = p209 n ∧ b n = p209_b n := system_unique p209_valid ha
#print axioms p209_valid
#print axioms p209_unique

def p208 (n : ℕ) : ℚ := (((1 : ℚ) / 2) * ((n : ℚ) + 1) * (((3 : ℚ) ^ n) + ((-2 : ℚ) ^ n)))
def p208_b (n : ℕ) : ℚ := (((1 : ℚ) / 2) * ((n : ℚ) + 1) * (((3 : ℚ) ^ n) + ((-1 : ℚ) * ((-2 : ℚ) ^ n))))
theorem p208_valid : SystemCertificate p208 p208_b (1 : ℚ) (0 : ℚ) (fun n x y => ((((n : ℚ) + 1) + (1 : ℚ)) * ((((1 : ℚ) / 2) * x) + (((5 : ℚ) / 2) * y))) / ((n : ℚ) + 1)) (fun n x y => ((((n : ℚ) + 1) + (1 : ℚ)) * ((((5 : ℚ) / 2) * x) + (((1 : ℚ) / 2) * y))) / ((n : ℚ) + 1)) := by
  constructor
  · norm_num [p208]
  · norm_num [p208_b]
  · intro n
    apply (eq_div_iff (show ((n : ℚ) + 1) ≠ 0 by positivity)).2
    simp only [p208, p208_b, Nat.cast_add, Nat.cast_one, pow_succ, pow_add]
    norm_num <;> ring
  · intro n
    apply (eq_div_iff (show ((n : ℚ) + 1) ≠ 0 by positivity)).2
    simp only [p208, p208_b, Nat.cast_add, Nat.cast_one, pow_succ, pow_add]
    norm_num <;> ring
theorem p208_unique (a b : ℕ → ℚ) (ha : SystemCertificate a b (1 : ℚ) (0 : ℚ) (fun n x y => ((((n : ℚ) + 1) + (1 : ℚ)) * ((((1 : ℚ) / 2) * x) + (((5 : ℚ) / 2) * y))) / ((n : ℚ) + 1)) (fun n x y => ((((n : ℚ) + 1) + (1 : ℚ)) * ((((5 : ℚ) / 2) * x) + (((1 : ℚ) / 2) * y))) / ((n : ℚ) + 1))) :
    ∀ n, a n = p208 n ∧ b n = p208_b n := system_unique p208_valid ha
#print axioms p208_valid
#print axioms p208_unique

def p244 (n : ℕ) : ℚ := (((1 : ℚ) / 2) * (((2 : ℚ) * ((n : ℚ) + 1)) + (1 : ℚ)) * (((2 : ℚ) ^ n) + ((1 : ℚ) ^ n)))
def p244_b (n : ℕ) : ℚ := (((1 : ℚ) / 2) * (((2 : ℚ) * ((n : ℚ) + 1)) + (1 : ℚ)) * (((2 : ℚ) ^ n) + ((-1 : ℚ) * ((1 : ℚ) ^ n))))
theorem p244_valid : SystemCertificate p244 p244_b (3 : ℚ) (0 : ℚ) (fun n x y => ((((2 : ℚ) * ((n : ℚ) + 1)) + (3 : ℚ)) * ((((3 : ℚ) / 2) * x) + (((1 : ℚ) / 2) * y))) / (((2 : ℚ) * ((n : ℚ) + 1)) + (1 : ℚ))) (fun n x y => ((((2 : ℚ) * ((n : ℚ) + 1)) + (3 : ℚ)) * ((((1 : ℚ) / 2) * x) + (((3 : ℚ) / 2) * y))) / (((2 : ℚ) * ((n : ℚ) + 1)) + (1 : ℚ))) := by
  constructor
  · norm_num [p244]
  · norm_num [p244_b]
  · intro n
    apply (eq_div_iff (show (((2 : ℚ) * ((n : ℚ) + 1)) + (1 : ℚ)) ≠ 0 by positivity)).2
    simp only [p244, p244_b, Nat.cast_add, Nat.cast_one, pow_succ, pow_add]
    norm_num <;> ring
  · intro n
    apply (eq_div_iff (show (((2 : ℚ) * ((n : ℚ) + 1)) + (1 : ℚ)) ≠ 0 by positivity)).2
    simp only [p244, p244_b, Nat.cast_add, Nat.cast_one, pow_succ, pow_add]
    norm_num <;> ring
theorem p244_unique (a b : ℕ → ℚ) (ha : SystemCertificate a b (3 : ℚ) (0 : ℚ) (fun n x y => ((((2 : ℚ) * ((n : ℚ) + 1)) + (3 : ℚ)) * ((((3 : ℚ) / 2) * x) + (((1 : ℚ) / 2) * y))) / (((2 : ℚ) * ((n : ℚ) + 1)) + (1 : ℚ))) (fun n x y => ((((2 : ℚ) * ((n : ℚ) + 1)) + (3 : ℚ)) * ((((1 : ℚ) / 2) * x) + (((3 : ℚ) / 2) * y))) / (((2 : ℚ) * ((n : ℚ) + 1)) + (1 : ℚ)))) :
    ∀ n, a n = p244 n ∧ b n = p244_b n := system_unique p244_valid ha
#print axioms p244_valid
#print axioms p244_unique

def p178 (n : ℕ) : ℚ := (((1 : ℚ) / 2) * (((n : ℚ) + 1) + (1 : ℚ)) * (((3 : ℚ) ^ n) + ((2 : ℚ) ^ n)))
def p178_b (n : ℕ) : ℚ := (((1 : ℚ) / 2) * (((n : ℚ) + 1) + (1 : ℚ)) * (((3 : ℚ) ^ n) + ((-1 : ℚ) * ((2 : ℚ) ^ n))))
theorem p178_valid : SystemCertificate p178 p178_b (2 : ℚ) (0 : ℚ) (fun n x y => ((((n : ℚ) + 1) + (2 : ℚ)) * ((((5 : ℚ) / 2) * x) + (((1 : ℚ) / 2) * y))) / (((n : ℚ) + 1) + (1 : ℚ))) (fun n x y => ((((n : ℚ) + 1) + (2 : ℚ)) * ((((1 : ℚ) / 2) * x) + (((5 : ℚ) / 2) * y))) / (((n : ℚ) + 1) + (1 : ℚ))) := by
  constructor
  · norm_num [p178]
  · norm_num [p178_b]
  · intro n
    apply (eq_div_iff (show (((n : ℚ) + 1) + (1 : ℚ)) ≠ 0 by positivity)).2
    simp only [p178, p178_b, Nat.cast_add, Nat.cast_one, pow_succ, pow_add]
    norm_num <;> ring
  · intro n
    apply (eq_div_iff (show (((n : ℚ) + 1) + (1 : ℚ)) ≠ 0 by positivity)).2
    simp only [p178, p178_b, Nat.cast_add, Nat.cast_one, pow_succ, pow_add]
    norm_num <;> ring
theorem p178_unique (a b : ℕ → ℚ) (ha : SystemCertificate a b (2 : ℚ) (0 : ℚ) (fun n x y => ((((n : ℚ) + 1) + (2 : ℚ)) * ((((5 : ℚ) / 2) * x) + (((1 : ℚ) / 2) * y))) / (((n : ℚ) + 1) + (1 : ℚ))) (fun n x y => ((((n : ℚ) + 1) + (2 : ℚ)) * ((((1 : ℚ) / 2) * x) + (((5 : ℚ) / 2) * y))) / (((n : ℚ) + 1) + (1 : ℚ)))) :
    ∀ n, a n = p178 n ∧ b n = p178_b n := system_unique p178_valid ha
#print axioms p178_valid
#print axioms p178_unique

def p235 (n : ℕ) : ℚ := (((1 : ℚ) / 2) * (((2 : ℚ) * ((3 : ℚ) ^ n)) + ((1 : ℚ) ^ n) + (1 : ℚ)))
def p235_b (n : ℕ) : ℚ := (((1 : ℚ) / 2) * (((2 : ℚ) * ((3 : ℚ) ^ n)) + ((-1 : ℚ) * ((1 : ℚ) ^ n)) + (1 : ℚ)))
theorem p235_valid : SystemCertificate p235 p235_b (2 : ℚ) (1 : ℚ) (fun n x y => (((2 : ℚ) * x) + y + (-1 : ℚ)) / (1 : ℚ)) (fun n x y => (x + ((2 : ℚ) * y) + (-1 : ℚ)) / (1 : ℚ)) := by
  constructor
  · norm_num [p235]
  · norm_num [p235_b]
  · intro n
    apply (eq_div_iff (show (1 : ℚ) ≠ 0 by positivity)).2
    simp only [p235, p235_b, Nat.cast_add, Nat.cast_one, pow_succ, pow_add]
    norm_num <;> ring
  · intro n
    apply (eq_div_iff (show (1 : ℚ) ≠ 0 by positivity)).2
    simp only [p235, p235_b, Nat.cast_add, Nat.cast_one, pow_succ, pow_add]
    norm_num <;> ring
theorem p235_unique (a b : ℕ → ℚ) (ha : SystemCertificate a b (2 : ℚ) (1 : ℚ) (fun n x y => (((2 : ℚ) * x) + y + (-1 : ℚ)) / (1 : ℚ)) (fun n x y => (x + ((2 : ℚ) * y) + (-1 : ℚ)) / (1 : ℚ))) :
    ∀ n, a n = p235 n ∧ b n = p235_b n := system_unique p235_valid ha
#print axioms p235_valid
#print axioms p235_unique

def p236 (n : ℕ) : ℚ := (((1 : ℚ) / 2) * (((2 : ℚ) ^ n) + ((-1 : ℚ) * ((n : ℚ) + 1)) + ((-2 : ℚ) ^ n) + (-1 : ℚ)))
def p236_b (n : ℕ) : ℚ := (((1 : ℚ) / 2) * (((2 : ℚ) ^ n) + ((-1 : ℚ) * ((n : ℚ) + 1)) + ((-1 : ℚ) * ((-2 : ℚ) ^ n)) + (-1 : ℚ)))
theorem p236_valid : SystemCertificate p236 p236_b (0 : ℚ) (-1 : ℚ) (fun n x y => (((2 : ℚ) * y) + (((1 : ℚ) / 2) * ((n : ℚ) + 1))) / (1 : ℚ)) (fun n x y => (((2 : ℚ) * x) + (((1 : ℚ) / 2) * ((n : ℚ) + 1))) / (1 : ℚ)) := by
  constructor
  · norm_num [p236]
  · norm_num [p236_b]
  · intro n
    apply (eq_div_iff (show (1 : ℚ) ≠ 0 by positivity)).2
    simp only [p236, p236_b, Nat.cast_add, Nat.cast_one, pow_succ, pow_add]
    norm_num <;> ring
  · intro n
    apply (eq_div_iff (show (1 : ℚ) ≠ 0 by positivity)).2
    simp only [p236, p236_b, Nat.cast_add, Nat.cast_one, pow_succ, pow_add]
    norm_num <;> ring
theorem p236_unique (a b : ℕ → ℚ) (ha : SystemCertificate a b (0 : ℚ) (-1 : ℚ) (fun n x y => (((2 : ℚ) * y) + (((1 : ℚ) / 2) * ((n : ℚ) + 1))) / (1 : ℚ)) (fun n x y => (((2 : ℚ) * x) + (((1 : ℚ) / 2) * ((n : ℚ) + 1))) / (1 : ℚ))) :
    ∀ n, a n = p236 n ∧ b n = p236_b n := system_unique p236_valid ha
#print axioms p236_valid
#print axioms p236_unique

def p182 (n : ℕ) : ℚ := (((1 : ℚ) / 2) * (((2 : ℚ) * ((2 : ℚ) ^ n)) + ((2 : ℚ) * ((4 : ℚ) ^ n)) + (2 : ℚ)))
def p182_b (n : ℕ) : ℚ := (((1 : ℚ) / 2) * (((2 : ℚ) * ((2 : ℚ) ^ n)) + ((-2 : ℚ) * ((4 : ℚ) ^ n)) + (2 : ℚ)))
theorem p182_valid : SystemCertificate p182 p182_b (3 : ℚ) (1 : ℚ) (fun n x y => (((3 : ℚ) * x) + ((-1 : ℚ) * y) + (-1 : ℚ)) / (1 : ℚ)) (fun n x y => (((-1 : ℚ) * x) + ((3 : ℚ) * y) + (-1 : ℚ)) / (1 : ℚ)) := by
  constructor
  · norm_num [p182]
  · norm_num [p182_b]
  · intro n
    apply (eq_div_iff (show (1 : ℚ) ≠ 0 by positivity)).2
    simp only [p182, p182_b, Nat.cast_add, Nat.cast_one, pow_succ, pow_add]
    norm_num <;> ring
  · intro n
    apply (eq_div_iff (show (1 : ℚ) ≠ 0 by positivity)).2
    simp only [p182, p182_b, Nat.cast_add, Nat.cast_one, pow_succ, pow_add]
    norm_num <;> ring
theorem p182_unique (a b : ℕ → ℚ) (ha : SystemCertificate a b (3 : ℚ) (1 : ℚ) (fun n x y => (((3 : ℚ) * x) + ((-1 : ℚ) * y) + (-1 : ℚ)) / (1 : ℚ)) (fun n x y => (((-1 : ℚ) * x) + ((3 : ℚ) * y) + (-1 : ℚ)) / (1 : ℚ))) :
    ∀ n, a n = p182 n ∧ b n = p182_b n := system_unique p182_valid ha
#print axioms p182_valid
#print axioms p182_unique

def p172 (n : ℕ) : ℚ := (((1 : ℚ) / 2) * (((2 : ℚ) ^ n) + ((-1 : ℚ) * ((n : ℚ) + 1)) + ((-1 : ℚ) ^ n) + (-1 : ℚ)))
def p172_b (n : ℕ) : ℚ := (((1 : ℚ) / 2) * (((2 : ℚ) ^ n) + ((-1 : ℚ) * ((n : ℚ) + 1)) + ((-1 : ℚ) * ((-1 : ℚ) ^ n)) + (-1 : ℚ)))
theorem p172_valid : SystemCertificate p172 p172_b (0 : ℚ) (-1 : ℚ) (fun n x y => ((((1 : ℚ) / 2) * x) + (((3 : ℚ) / 2) * y) + (((1 : ℚ) / 2) * ((n : ℚ) + 1))) / (1 : ℚ)) (fun n x y => ((((3 : ℚ) / 2) * x) + (((1 : ℚ) / 2) * y) + (((1 : ℚ) / 2) * ((n : ℚ) + 1))) / (1 : ℚ)) := by
  constructor
  · norm_num [p172]
  · norm_num [p172_b]
  · intro n
    apply (eq_div_iff (show (1 : ℚ) ≠ 0 by positivity)).2
    simp only [p172, p172_b, Nat.cast_add, Nat.cast_one, pow_succ, pow_add]
    norm_num <;> ring
  · intro n
    apply (eq_div_iff (show (1 : ℚ) ≠ 0 by positivity)).2
    simp only [p172, p172_b, Nat.cast_add, Nat.cast_one, pow_succ, pow_add]
    norm_num <;> ring
theorem p172_unique (a b : ℕ → ℚ) (ha : SystemCertificate a b (0 : ℚ) (-1 : ℚ) (fun n x y => ((((1 : ℚ) / 2) * x) + (((3 : ℚ) / 2) * y) + (((1 : ℚ) / 2) * ((n : ℚ) + 1))) / (1 : ℚ)) (fun n x y => ((((3 : ℚ) / 2) * x) + (((1 : ℚ) / 2) * y) + (((1 : ℚ) / 2) * ((n : ℚ) + 1))) / (1 : ℚ))) :
    ∀ n, a n = p172 n ∧ b n = p172_b n := system_unique p172_valid ha
#print axioms p172_valid
#print axioms p172_unique

def p198 (n : ℕ) : ℚ := (((1 : ℚ) / 2) * (((2 : ℚ) * ((3 : ℚ) ^ n)) + ((-2 : ℚ) ^ n) + (1 : ℚ)))
def p198_b (n : ℕ) : ℚ := (((1 : ℚ) / 2) * (((2 : ℚ) * ((3 : ℚ) ^ n)) + ((-1 : ℚ) * ((-2 : ℚ) ^ n)) + (1 : ℚ)))
theorem p198_valid : SystemCertificate p198 p198_b (2 : ℚ) (1 : ℚ) (fun n x y => ((((1 : ℚ) / 2) * x) + (((5 : ℚ) / 2) * y) + (-1 : ℚ)) / (1 : ℚ)) (fun n x y => ((((5 : ℚ) / 2) * x) + (((1 : ℚ) / 2) * y) + (-1 : ℚ)) / (1 : ℚ)) := by
  constructor
  · norm_num [p198]
  · norm_num [p198_b]
  · intro n
    apply (eq_div_iff (show (1 : ℚ) ≠ 0 by positivity)).2
    simp only [p198, p198_b, Nat.cast_add, Nat.cast_one, pow_succ, pow_add]
    norm_num <;> ring
  · intro n
    apply (eq_div_iff (show (1 : ℚ) ≠ 0 by positivity)).2
    simp only [p198, p198_b, Nat.cast_add, Nat.cast_one, pow_succ, pow_add]
    norm_num <;> ring
theorem p198_unique (a b : ℕ → ℚ) (ha : SystemCertificate a b (2 : ℚ) (1 : ℚ) (fun n x y => ((((1 : ℚ) / 2) * x) + (((5 : ℚ) / 2) * y) + (-1 : ℚ)) / (1 : ℚ)) (fun n x y => ((((5 : ℚ) / 2) * x) + (((1 : ℚ) / 2) * y) + (-1 : ℚ)) / (1 : ℚ))) :
    ∀ n, a n = p198 n ∧ b n = p198_b n := system_unique p198_valid ha
#print axioms p198_valid
#print axioms p198_unique

def p223 (n : ℕ) : ℚ := (((1 : ℚ) / 2) * (((2 : ℚ) ^ n) + ((-1 : ℚ) * ((n : ℚ) + 1)) + ((1 : ℚ) ^ n) + (-1 : ℚ)))
def p223_b (n : ℕ) : ℚ := (((1 : ℚ) / 2) * (((2 : ℚ) ^ n) + ((-1 : ℚ) * ((n : ℚ) + 1)) + ((-1 : ℚ) * ((1 : ℚ) ^ n)) + (-1 : ℚ)))
theorem p223_valid : SystemCertificate p223 p223_b (0 : ℚ) (-1 : ℚ) (fun n x y => ((((3 : ℚ) / 2) * x) + (((1 : ℚ) / 2) * y) + (((1 : ℚ) / 2) * ((n : ℚ) + 1))) / (1 : ℚ)) (fun n x y => ((((1 : ℚ) / 2) * x) + (((3 : ℚ) / 2) * y) + (((1 : ℚ) / 2) * ((n : ℚ) + 1))) / (1 : ℚ)) := by
  constructor
  · norm_num [p223]
  · norm_num [p223_b]
  · intro n
    apply (eq_div_iff (show (1 : ℚ) ≠ 0 by positivity)).2
    simp only [p223, p223_b, Nat.cast_add, Nat.cast_one, pow_succ, pow_add]
    norm_num <;> ring
  · intro n
    apply (eq_div_iff (show (1 : ℚ) ≠ 0 by positivity)).2
    simp only [p223, p223_b, Nat.cast_add, Nat.cast_one, pow_succ, pow_add]
    norm_num <;> ring
theorem p223_unique (a b : ℕ → ℚ) (ha : SystemCertificate a b (0 : ℚ) (-1 : ℚ) (fun n x y => ((((3 : ℚ) / 2) * x) + (((1 : ℚ) / 2) * y) + (((1 : ℚ) / 2) * ((n : ℚ) + 1))) / (1 : ℚ)) (fun n x y => ((((1 : ℚ) / 2) * x) + (((3 : ℚ) / 2) * y) + (((1 : ℚ) / 2) * ((n : ℚ) + 1))) / (1 : ℚ))) :
    ∀ n, a n = p223 n ∧ b n = p223_b n := system_unique p223_valid ha
#print axioms p223_valid
#print axioms p223_unique

def p219 (n : ℕ) : ℚ := (((1 : ℚ) / 2) * (((2 : ℚ) * ((3 : ℚ) ^ n)) + ((2 : ℚ) ^ n) + (1 : ℚ)))
def p219_b (n : ℕ) : ℚ := (((1 : ℚ) / 2) * (((2 : ℚ) * ((3 : ℚ) ^ n)) + ((-1 : ℚ) * ((2 : ℚ) ^ n)) + (1 : ℚ)))
theorem p219_valid : SystemCertificate p219 p219_b (2 : ℚ) (1 : ℚ) (fun n x y => ((((5 : ℚ) / 2) * x) + (((1 : ℚ) / 2) * y) + (-1 : ℚ)) / (1 : ℚ)) (fun n x y => ((((1 : ℚ) / 2) * x) + (((5 : ℚ) / 2) * y) + (-1 : ℚ)) / (1 : ℚ)) := by
  constructor
  · norm_num [p219]
  · norm_num [p219_b]
  · intro n
    apply (eq_div_iff (show (1 : ℚ) ≠ 0 by positivity)).2
    simp only [p219, p219_b, Nat.cast_add, Nat.cast_one, pow_succ, pow_add]
    norm_num <;> ring
  · intro n
    apply (eq_div_iff (show (1 : ℚ) ≠ 0 by positivity)).2
    simp only [p219, p219_b, Nat.cast_add, Nat.cast_one, pow_succ, pow_add]
    norm_num <;> ring
theorem p219_unique (a b : ℕ → ℚ) (ha : SystemCertificate a b (2 : ℚ) (1 : ℚ) (fun n x y => ((((5 : ℚ) / 2) * x) + (((1 : ℚ) / 2) * y) + (-1 : ℚ)) / (1 : ℚ)) (fun n x y => ((((1 : ℚ) / 2) * x) + (((5 : ℚ) / 2) * y) + (-1 : ℚ)) / (1 : ℚ))) :
    ∀ n, a n = p219 n ∧ b n = p219_b n := system_unique p219_valid ha
#print axioms p219_valid
#print axioms p219_unique

def p226 (n : ℕ) : ℚ := (((1 : ℚ) / 2) * (((2 : ℚ) ^ n) + ((-1 : ℚ) * ((n : ℚ) + 1)) + ((3 : ℚ) ^ n) + (-1 : ℚ)))
def p226_b (n : ℕ) : ℚ := (((1 : ℚ) / 2) * (((2 : ℚ) ^ n) + ((-1 : ℚ) * ((n : ℚ) + 1)) + ((-1 : ℚ) * ((3 : ℚ) ^ n)) + (-1 : ℚ)))
theorem p226_valid : SystemCertificate p226 p226_b (0 : ℚ) (-1 : ℚ) (fun n x y => ((((5 : ℚ) / 2) * x) + (((-1 : ℚ) / 2) * y) + (((1 : ℚ) / 2) * ((n : ℚ) + 1))) / (1 : ℚ)) (fun n x y => ((((-1 : ℚ) / 2) * x) + (((5 : ℚ) / 2) * y) + (((1 : ℚ) / 2) * ((n : ℚ) + 1))) / (1 : ℚ)) := by
  constructor
  · norm_num [p226]
  · norm_num [p226_b]
  · intro n
    apply (eq_div_iff (show (1 : ℚ) ≠ 0 by positivity)).2
    simp only [p226, p226_b, Nat.cast_add, Nat.cast_one, pow_succ, pow_add]
    norm_num <;> ring
  · intro n
    apply (eq_div_iff (show (1 : ℚ) ≠ 0 by positivity)).2
    simp only [p226, p226_b, Nat.cast_add, Nat.cast_one, pow_succ, pow_add]
    norm_num <;> ring
theorem p226_unique (a b : ℕ → ℚ) (ha : SystemCertificate a b (0 : ℚ) (-1 : ℚ) (fun n x y => ((((5 : ℚ) / 2) * x) + (((-1 : ℚ) / 2) * y) + (((1 : ℚ) / 2) * ((n : ℚ) + 1))) / (1 : ℚ)) (fun n x y => ((((-1 : ℚ) / 2) * x) + (((5 : ℚ) / 2) * y) + (((1 : ℚ) / 2) * ((n : ℚ) + 1))) / (1 : ℚ))) :
    ∀ n, a n = p226 n ∧ b n = p226_b n := system_unique p226_valid ha
#print axioms p226_valid
#print axioms p226_unique

def p194_sum (n : ℕ) : ℚ := (((2 : ℚ) * ((2 : ℚ) ^ n)) + (-1 : ℚ))
theorem p194_sum_base_valid : FirstCertificate p194_sum (1 : ℚ) (fun n x => ((2 : ℚ) * x + (1 : ℚ)) / (1 : ℚ)) := by
  apply linear_certificate p194_sum (1 : ℚ) (fun n : ℕ => (1 : ℚ)) (fun n : ℕ => (2 : ℚ)) (fun n : ℕ => (1 : ℚ))
  · norm_num [p194_sum]
  · intro n; positivity
  · intro n
    simp only [p194_sum, Nat.cast_add, Nat.cast_one, pow_succ, pow_add] at *
    ring
theorem p194_sum_valid : FirstCertificate p194_sum (1 : ℚ) (fun n x => ((2 : ℚ) * x + (1 : ℚ)) / (1 : ℚ)) := p194_sum_base_valid
theorem p194_sum_unique (a : ℕ → ℚ) (ha : FirstCertificate a (1 : ℚ) (fun n x => ((2 : ℚ) * x + (1 : ℚ)) / (1 : ℚ))) :
    ∀ n, a n = p194_sum n := first_unique p194_sum_valid ha
#print axioms p194_sum_valid
#print axioms p194_sum_unique

def p194 (n : ℕ) : ℚ := (((2 : ℚ) * ((2 : ℚ) ^ n)) + ((-1 : ℚ) * ((((2 : ℚ) * ((2 : ℚ) ^ n)) / (2 : ℚ)) + (-1 : ℚ))) + (-1 : ℚ))
theorem p194_prefix : ∀ n, prefix p194 n = p194_sum n := by
  intro n
  induction n with
  | zero => norm_num [prefix, p194, p194_sum]
  | succ n ih =>
    rw [prefix_succ, ih]
    simp only [p194, p194_sum, Nat.cast_add, Nat.cast_one, pow_succ, pow_add]
    norm_num <;> ring
theorem p194_valid : PureSumCertificate p194 (1 : ℚ) (fun n x => ((2 : ℚ) * x + (1 : ℚ)) / (1 : ℚ)) := by
  have heq : prefix p194 = p194_sum := funext p194_prefix
  change FirstCertificate (prefix p194) (1 : ℚ) (fun n x => ((2 : ℚ) * x + (1 : ℚ)) / (1 : ℚ))
  rw [heq]
  exact p194_sum_valid
theorem p194_unique (a : ℕ → ℚ) (ha : PureSumCertificate a (1 : ℚ) (fun n x => ((2 : ℚ) * x + (1 : ℚ)) / (1 : ℚ))) :
    ∀ n, a n = p194 n := pure_sum_unique p194_valid ha
#print axioms p194_valid
#print axioms p194_unique

def p183_sum (n : ℕ) : ℚ := (((2 : ℚ) * ((2 : ℚ) ^ n)) + ((2 : ℚ) * ((n : ℚ) + 1)) + (-1 : ℚ))
theorem p183_sum_base_valid : FirstCertificate p183_sum (3 : ℚ) (fun n x => ((2 : ℚ) * x + (((-2 : ℚ) * ((n : ℚ) + 1)) + (3 : ℚ))) / (1 : ℚ)) := by
  apply linear_certificate p183_sum (3 : ℚ) (fun n : ℕ => (1 : ℚ)) (fun n : ℕ => (2 : ℚ)) (fun n : ℕ => (((-2 : ℚ) * ((n : ℚ) + 1)) + (3 : ℚ)))
  · norm_num [p183_sum]
  · intro n; positivity
  · intro n
    simp only [p183_sum, Nat.cast_add, Nat.cast_one, pow_succ, pow_add] at *
    ring
theorem p183_sum_valid : FirstCertificate p183_sum (3 : ℚ) (fun n x => ((2 : ℚ) * x + (((-2 : ℚ) * ((n : ℚ) + 1)) + (3 : ℚ))) / (1 : ℚ)) := p183_sum_base_valid
theorem p183_sum_unique (a : ℕ → ℚ) (ha : FirstCertificate a (3 : ℚ) (fun n x => ((2 : ℚ) * x + (((-2 : ℚ) * ((n : ℚ) + 1)) + (3 : ℚ))) / (1 : ℚ))) :
    ∀ n, a n = p183_sum n := first_unique p183_sum_valid ha
#print axioms p183_sum_valid
#print axioms p183_sum_unique

def p183 (n : ℕ) : ℚ := (((2 : ℚ) * ((2 : ℚ) ^ n)) + ((2 : ℚ) * ((n : ℚ) + 1)) + ((-1 : ℚ) * ((((2 : ℚ) * ((2 : ℚ) ^ n)) / (2 : ℚ)) + ((2 : ℚ) * (((n : ℚ) + 1) + (-1 : ℚ))) + (-1 : ℚ))) + (-1 : ℚ))
theorem p183_prefix : ∀ n, prefix p183 n = p183_sum n := by
  intro n
  induction n with
  | zero => norm_num [prefix, p183, p183_sum]
  | succ n ih =>
    rw [prefix_succ, ih]
    simp only [p183, p183_sum, Nat.cast_add, Nat.cast_one, pow_succ, pow_add]
    norm_num <;> ring
theorem p183_valid : PureSumCertificate p183 (3 : ℚ) (fun n x => ((2 : ℚ) * x + (((-2 : ℚ) * ((n : ℚ) + 1)) + (3 : ℚ))) / (1 : ℚ)) := by
  have heq : prefix p183 = p183_sum := funext p183_prefix
  change FirstCertificate (prefix p183) (3 : ℚ) (fun n x => ((2 : ℚ) * x + (((-2 : ℚ) * ((n : ℚ) + 1)) + (3 : ℚ))) / (1 : ℚ))
  rw [heq]
  exact p183_sum_valid
theorem p183_unique (a : ℕ → ℚ) (ha : PureSumCertificate a (3 : ℚ) (fun n x => ((2 : ℚ) * x + (((-2 : ℚ) * ((n : ℚ) + 1)) + (3 : ℚ))) / (1 : ℚ))) :
    ∀ n, a n = p183 n := pure_sum_unique p183_valid ha
#print axioms p183_valid
#print axioms p183_unique

def p179_sum (n : ℕ) : ℚ := (((4 : ℚ) * ((2 : ℚ) ^ n)) + (-2 : ℚ))
theorem p179_sum_base_valid : FirstCertificate p179_sum (2 : ℚ) (fun n x => ((2 : ℚ) * x + (2 : ℚ)) / (1 : ℚ)) := by
  apply linear_certificate p179_sum (2 : ℚ) (fun n : ℕ => (1 : ℚ)) (fun n : ℕ => (2 : ℚ)) (fun n : ℕ => (2 : ℚ))
  · norm_num [p179_sum]
  · intro n; positivity
  · intro n
    simp only [p179_sum, Nat.cast_add, Nat.cast_one, pow_succ, pow_add] at *
    ring
theorem p179_sum_valid : FirstCertificate p179_sum (2 : ℚ) (fun n x => ((2 : ℚ) * x + (2 : ℚ)) / (1 : ℚ)) := p179_sum_base_valid
theorem p179_sum_unique (a : ℕ → ℚ) (ha : FirstCertificate a (2 : ℚ) (fun n x => ((2 : ℚ) * x + (2 : ℚ)) / (1 : ℚ))) :
    ∀ n, a n = p179_sum n := first_unique p179_sum_valid ha
#print axioms p179_sum_valid
#print axioms p179_sum_unique

def p179 (n : ℕ) : ℚ := (((4 : ℚ) * ((2 : ℚ) ^ n)) + ((-1 : ℚ) * ((((4 : ℚ) * ((2 : ℚ) ^ n)) / (2 : ℚ)) + (-2 : ℚ))) + (-2 : ℚ))
theorem p179_prefix : ∀ n, prefix p179 n = p179_sum n := by
  intro n
  induction n with
  | zero => norm_num [prefix, p179, p179_sum]
  | succ n ih =>
    rw [prefix_succ, ih]
    simp only [p179, p179_sum, Nat.cast_add, Nat.cast_one, pow_succ, pow_add]
    norm_num <;> ring
theorem p179_valid : PureSumCertificate p179 (2 : ℚ) (fun n x => ((2 : ℚ) * x + (2 : ℚ)) / (1 : ℚ)) := by
  have heq : prefix p179 = p179_sum := funext p179_prefix
  change FirstCertificate (prefix p179) (2 : ℚ) (fun n x => ((2 : ℚ) * x + (2 : ℚ)) / (1 : ℚ))
  rw [heq]
  exact p179_sum_valid
theorem p179_unique (a : ℕ → ℚ) (ha : PureSumCertificate a (2 : ℚ) (fun n x => ((2 : ℚ) * x + (2 : ℚ)) / (1 : ℚ))) :
    ∀ n, a n = p179 n := pure_sum_unique p179_valid ha
#print axioms p179_valid
#print axioms p179_unique

def p211_sum (n : ℕ) : ℚ := (((2 : ℚ) ^ n) + ((n : ℚ) + 1) + ((-1 : ℚ) / 2))
theorem p211_sum_base_valid : FirstCertificate p211_sum ((3 : ℚ) / 2) (fun n x => ((2 : ℚ) * x + (((-1 : ℚ) * ((n : ℚ) + 1)) + ((3 : ℚ) / 2))) / (1 : ℚ)) := by
  apply linear_certificate p211_sum ((3 : ℚ) / 2) (fun n : ℕ => (1 : ℚ)) (fun n : ℕ => (2 : ℚ)) (fun n : ℕ => (((-1 : ℚ) * ((n : ℚ) + 1)) + ((3 : ℚ) / 2)))
  · norm_num [p211_sum]
  · intro n; positivity
  · intro n
    simp only [p211_sum, Nat.cast_add, Nat.cast_one, pow_succ, pow_add] at *
    ring
theorem p211_sum_valid : FirstCertificate p211_sum ((3 : ℚ) / 2) (fun n x => ((2 : ℚ) * x + (((-1 : ℚ) * ((n : ℚ) + 1)) + ((3 : ℚ) / 2))) / (1 : ℚ)) := p211_sum_base_valid
theorem p211_sum_unique (a : ℕ → ℚ) (ha : FirstCertificate a ((3 : ℚ) / 2) (fun n x => ((2 : ℚ) * x + (((-1 : ℚ) * ((n : ℚ) + 1)) + ((3 : ℚ) / 2))) / (1 : ℚ))) :
    ∀ n, a n = p211_sum n := first_unique p211_sum_valid ha
#print axioms p211_sum_valid
#print axioms p211_sum_unique

def p211 (n : ℕ) : ℚ := (((2 : ℚ) ^ n) + ((n : ℚ) + 1) + ((-1 : ℚ) * ((((2 : ℚ) ^ n) / (2 : ℚ)) + ((n : ℚ) + 1) + ((-3 : ℚ) / 2))) + ((-1 : ℚ) / 2))
theorem p211_prefix : ∀ n, prefix p211 n = p211_sum n := by
  intro n
  induction n with
  | zero => norm_num [prefix, p211, p211_sum]
  | succ n ih =>
    rw [prefix_succ, ih]
    simp only [p211, p211_sum, Nat.cast_add, Nat.cast_one, pow_succ, pow_add]
    norm_num <;> ring
theorem p211_valid : PureSumCertificate p211 ((3 : ℚ) / 2) (fun n x => ((2 : ℚ) * x + (((-1 : ℚ) * ((n : ℚ) + 1)) + ((3 : ℚ) / 2))) / (1 : ℚ)) := by
  have heq : prefix p211 = p211_sum := funext p211_prefix
  change FirstCertificate (prefix p211) ((3 : ℚ) / 2) (fun n x => ((2 : ℚ) * x + (((-1 : ℚ) * ((n : ℚ) + 1)) + ((3 : ℚ) / 2))) / (1 : ℚ))
  rw [heq]
  exact p211_sum_valid
theorem p211_unique (a : ℕ → ℚ) (ha : PureSumCertificate a ((3 : ℚ) / 2) (fun n x => ((2 : ℚ) * x + (((-1 : ℚ) * ((n : ℚ) + 1)) + ((3 : ℚ) / 2))) / (1 : ℚ))) :
    ∀ n, a n = p211 n := pure_sum_unique p211_valid ha
#print axioms p211_valid
#print axioms p211_unique

def p221_sum (n : ℕ) : ℚ := (((6 : ℚ) * ((2 : ℚ) ^ n)) + (-3 : ℚ))
theorem p221_sum_base_valid : FirstCertificate p221_sum (3 : ℚ) (fun n x => ((2 : ℚ) * x + (3 : ℚ)) / (1 : ℚ)) := by
  apply linear_certificate p221_sum (3 : ℚ) (fun n : ℕ => (1 : ℚ)) (fun n : ℕ => (2 : ℚ)) (fun n : ℕ => (3 : ℚ))
  · norm_num [p221_sum]
  · intro n; positivity
  · intro n
    simp only [p221_sum, Nat.cast_add, Nat.cast_one, pow_succ, pow_add] at *
    ring
theorem p221_sum_valid : FirstCertificate p221_sum (3 : ℚ) (fun n x => ((2 : ℚ) * x + (3 : ℚ)) / (1 : ℚ)) := p221_sum_base_valid
theorem p221_sum_unique (a : ℕ → ℚ) (ha : FirstCertificate a (3 : ℚ) (fun n x => ((2 : ℚ) * x + (3 : ℚ)) / (1 : ℚ))) :
    ∀ n, a n = p221_sum n := first_unique p221_sum_valid ha
#print axioms p221_sum_valid
#print axioms p221_sum_unique

def p221 (n : ℕ) : ℚ := (((6 : ℚ) * ((2 : ℚ) ^ n)) + ((-1 : ℚ) * ((((6 : ℚ) * ((2 : ℚ) ^ n)) / (2 : ℚ)) + (-3 : ℚ))) + (-3 : ℚ))
theorem p221_prefix : ∀ n, prefix p221 n = p221_sum n := by
  intro n
  induction n with
  | zero => norm_num [prefix, p221, p221_sum]
  | succ n ih =>
    rw [prefix_succ, ih]
    simp only [p221, p221_sum, Nat.cast_add, Nat.cast_one, pow_succ, pow_add]
    norm_num <;> ring
theorem p221_valid : PureSumCertificate p221 (3 : ℚ) (fun n x => ((2 : ℚ) * x + (3 : ℚ)) / (1 : ℚ)) := by
  have heq : prefix p221 = p221_sum := funext p221_prefix
  change FirstCertificate (prefix p221) (3 : ℚ) (fun n x => ((2 : ℚ) * x + (3 : ℚ)) / (1 : ℚ))
  rw [heq]
  exact p221_sum_valid
theorem p221_unique (a : ℕ → ℚ) (ha : PureSumCertificate a (3 : ℚ) (fun n x => ((2 : ℚ) * x + (3 : ℚ)) / (1 : ℚ))) :
    ∀ n, a n = p221 n := pure_sum_unique p221_valid ha
#print axioms p221_valid
#print axioms p221_unique

def p188_sum (n : ℕ) : ℚ := (((3 : ℚ) ^ n) + ((n : ℚ) + 1) + ((-1 : ℚ) / 3))
theorem p188_sum_base_valid : FirstCertificate p188_sum ((5 : ℚ) / 3) (fun n x => ((3 : ℚ) * x + (((-2 : ℚ) * ((n : ℚ) + 1)) + ((5 : ℚ) / 3))) / (1 : ℚ)) := by
  apply linear_certificate p188_sum ((5 : ℚ) / 3) (fun n : ℕ => (1 : ℚ)) (fun n : ℕ => (3 : ℚ)) (fun n : ℕ => (((-2 : ℚ) * ((n : ℚ) + 1)) + ((5 : ℚ) / 3)))
  · norm_num [p188_sum]
  · intro n; positivity
  · intro n
    simp only [p188_sum, Nat.cast_add, Nat.cast_one, pow_succ, pow_add] at *
    ring
theorem p188_sum_valid : FirstCertificate p188_sum ((5 : ℚ) / 3) (fun n x => ((3 : ℚ) * x + (((-2 : ℚ) * ((n : ℚ) + 1)) + ((5 : ℚ) / 3))) / (1 : ℚ)) := p188_sum_base_valid
theorem p188_sum_unique (a : ℕ → ℚ) (ha : FirstCertificate a ((5 : ℚ) / 3) (fun n x => ((3 : ℚ) * x + (((-2 : ℚ) * ((n : ℚ) + 1)) + ((5 : ℚ) / 3))) / (1 : ℚ))) :
    ∀ n, a n = p188_sum n := first_unique p188_sum_valid ha
#print axioms p188_sum_valid
#print axioms p188_sum_unique

def p188 (n : ℕ) : ℚ := (((3 : ℚ) ^ n) + ((n : ℚ) + 1) + ((-1 : ℚ) * ((((3 : ℚ) ^ n) / (3 : ℚ)) + ((n : ℚ) + 1) + ((-4 : ℚ) / 3))) + ((-1 : ℚ) / 3))
theorem p188_prefix : ∀ n, prefix p188 n = p188_sum n := by
  intro n
  induction n with
  | zero => norm_num [prefix, p188, p188_sum]
  | succ n ih =>
    rw [prefix_succ, ih]
    simp only [p188, p188_sum, Nat.cast_add, Nat.cast_one, pow_succ, pow_add]
    norm_num <;> ring
theorem p188_valid : PureSumCertificate p188 ((5 : ℚ) / 3) (fun n x => ((3 : ℚ) * x + (((-2 : ℚ) * ((n : ℚ) + 1)) + ((5 : ℚ) / 3))) / (1 : ℚ)) := by
  have heq : prefix p188 = p188_sum := funext p188_prefix
  change FirstCertificate (prefix p188) ((5 : ℚ) / 3) (fun n x => ((3 : ℚ) * x + (((-2 : ℚ) * ((n : ℚ) + 1)) + ((5 : ℚ) / 3))) / (1 : ℚ))
  rw [heq]
  exact p188_sum_valid
theorem p188_unique (a : ℕ → ℚ) (ha : PureSumCertificate a ((5 : ℚ) / 3) (fun n x => ((3 : ℚ) * x + (((-2 : ℚ) * ((n : ℚ) + 1)) + ((5 : ℚ) / 3))) / (1 : ℚ))) :
    ∀ n, a n = p188 n := pure_sum_unique p188_valid ha
#print axioms p188_valid
#print axioms p188_unique

def p222_sum (n : ℕ) : ℚ := (((n : ℚ) + 1) * (((2 : ℚ) ^ n) + ((-2 : ℚ) ^ n)))
theorem p222_sum_valid : GeneralSecondCertificate p222_sum (2 : ℚ) (0 : ℚ) (fun n x y => ((0 : ℚ) * y + (((4 : ℚ) * ((n : ℚ) + 1)) + (8 : ℚ)) * x) / ((n : ℚ) + 1)) := by
  apply linear_second_certificate p222_sum (2 : ℚ) (0 : ℚ) (fun n => ((n : ℚ) + 1)) (fun n => (0 : ℚ)) (fun n => (((4 : ℚ) * ((n : ℚ) + 1)) + (8 : ℚ)))
  · norm_num [p222_sum]
  · norm_num [p222_sum]
  · intro n; positivity
  · intro n
    simp only [p222_sum, Nat.cast_add, Nat.cast_one, pow_succ, pow_add] at *
    ring
theorem p222_sum_unique (a : ℕ → ℚ) (hi : a 0 = (2 : ℚ)) (hj : a 1 = (0 : ℚ))
    (ha : ∀ n : ℕ, ((n : ℚ) + 1) * a (n + 2) = (0 : ℚ) * a (n + 1) + (((4 : ℚ) * ((n : ℚ) + 1)) + (8 : ℚ)) * a n) :
    ∀ n, a n = p222_sum n := by
  apply general_second_unique p222_sum_valid
  exact linear_second_certificate a (2 : ℚ) (0 : ℚ) (fun n => ((n : ℚ) + 1)) (fun n => (0 : ℚ)) (fun n => (((4 : ℚ) * ((n : ℚ) + 1)) + (8 : ℚ))) hi hj (by intro n; positivity) ha
#print axioms p222_sum_valid
#print axioms p222_sum_unique

def p222 (n : ℕ) : ℚ := ((((n : ℚ) + 1) * (((2 : ℚ) ^ n) + ((-2 : ℚ) ^ n))) + ((-1 : ℚ) * (((n : ℚ) + 1) + (-1 : ℚ)) * ((((2 : ℚ) ^ n) / (2 : ℚ)) + (((-2 : ℚ) ^ n) / (-2 : ℚ)))))
theorem p222_prefix : ∀ n, prefix p222 n = p222_sum n := by
  intro n
  induction n with
  | zero => norm_num [prefix, p222, p222_sum]
  | succ n ih =>
    rw [prefix_succ, ih]
    simp only [p222, p222_sum, Nat.cast_add, Nat.cast_one, pow_succ, pow_add]
    norm_num <;> ring
theorem p222_valid : PureSecondSumCertificate p222 (2 : ℚ) (0 : ℚ) (fun n x y => ((0 : ℚ) * y + (((4 : ℚ) * ((n : ℚ) + 1)) + (8 : ℚ)) * x) / ((n : ℚ) + 1)) := by
  have heq : prefix p222 = p222_sum := funext p222_prefix
  change GeneralSecondCertificate (prefix p222) (2 : ℚ) (0 : ℚ) (fun n x y => ((0 : ℚ) * y + (((4 : ℚ) * ((n : ℚ) + 1)) + (8 : ℚ)) * x) / ((n : ℚ) + 1))
  rw [heq]
  exact p222_sum_valid
theorem p222_unique (a : ℕ → ℚ) (ha : PureSecondSumCertificate a (2 : ℚ) (0 : ℚ) (fun n x y => ((0 : ℚ) * y + (((4 : ℚ) * ((n : ℚ) + 1)) + (8 : ℚ)) * x) / ((n : ℚ) + 1))) :
    ∀ n, a n = p222 n := pure_second_sum_unique p222_valid ha
#print axioms p222_valid
#print axioms p222_unique

def p220_sum (n : ℕ) : ℚ := (((n : ℚ) + 1) * (((n : ℚ) + 1) + (1 : ℚ)) * (((2 : ℚ) * ((2 : ℚ) ^ n)) + ((3 : ℚ) * ((-1 : ℚ) ^ n))))
theorem p220_sum_valid : GeneralSecondCertificate p220_sum (10 : ℚ) (6 : ℚ) (fun n x y => (((((n : ℚ) + 1) ^ 2) + ((3 : ℚ) * ((n : ℚ) + 1))) * y + (((2 : ℚ) * (((n : ℚ) + 1) ^ 2)) + ((10 : ℚ) * ((n : ℚ) + 1)) + (12 : ℚ)) * x) / ((((n : ℚ) + 1) ^ 2) + ((n : ℚ) + 1))) := by
  apply linear_second_certificate p220_sum (10 : ℚ) (6 : ℚ) (fun n => ((((n : ℚ) + 1) ^ 2) + ((n : ℚ) + 1))) (fun n => ((((n : ℚ) + 1) ^ 2) + ((3 : ℚ) * ((n : ℚ) + 1)))) (fun n => (((2 : ℚ) * (((n : ℚ) + 1) ^ 2)) + ((10 : ℚ) * ((n : ℚ) + 1)) + (12 : ℚ)))
  · norm_num [p220_sum]
  · norm_num [p220_sum]
  · intro n; positivity
  · intro n
    simp only [p220_sum, Nat.cast_add, Nat.cast_one, pow_succ, pow_add] at *
    ring
theorem p220_sum_unique (a : ℕ → ℚ) (hi : a 0 = (10 : ℚ)) (hj : a 1 = (6 : ℚ))
    (ha : ∀ n : ℕ, ((((n : ℚ) + 1) ^ 2) + ((n : ℚ) + 1)) * a (n + 2) = ((((n : ℚ) + 1) ^ 2) + ((3 : ℚ) * ((n : ℚ) + 1))) * a (n + 1) + (((2 : ℚ) * (((n : ℚ) + 1) ^ 2)) + ((10 : ℚ) * ((n : ℚ) + 1)) + (12 : ℚ)) * a n) :
    ∀ n, a n = p220_sum n := by
  apply general_second_unique p220_sum_valid
  exact linear_second_certificate a (10 : ℚ) (6 : ℚ) (fun n => ((((n : ℚ) + 1) ^ 2) + ((n : ℚ) + 1))) (fun n => ((((n : ℚ) + 1) ^ 2) + ((3 : ℚ) * ((n : ℚ) + 1)))) (fun n => (((2 : ℚ) * (((n : ℚ) + 1) ^ 2)) + ((10 : ℚ) * ((n : ℚ) + 1)) + (12 : ℚ))) hi hj (by intro n; positivity) ha
#print axioms p220_sum_valid
#print axioms p220_sum_unique

def p220 (n : ℕ) : ℚ := ((((n : ℚ) + 1) * (((n : ℚ) + 1) + (1 : ℚ)) * (((2 : ℚ) * ((2 : ℚ) ^ n)) + ((3 : ℚ) * ((-1 : ℚ) ^ n)))) + ((-1 : ℚ) * (((n : ℚ) + 1) + (-1 : ℚ)) * ((n : ℚ) + 1) * ((((2 : ℚ) * ((2 : ℚ) ^ n)) / (2 : ℚ)) + (((3 : ℚ) * ((-1 : ℚ) ^ n)) / (-1 : ℚ)))))
theorem p220_prefix : ∀ n, prefix p220 n = p220_sum n := by
  intro n
  induction n with
  | zero => norm_num [prefix, p220, p220_sum]
  | succ n ih =>
    rw [prefix_succ, ih]
    simp only [p220, p220_sum, Nat.cast_add, Nat.cast_one, pow_succ, pow_add]
    norm_num <;> ring
theorem p220_valid : PureSecondSumCertificate p220 (10 : ℚ) (6 : ℚ) (fun n x y => (((((n : ℚ) + 1) ^ 2) + ((3 : ℚ) * ((n : ℚ) + 1))) * y + (((2 : ℚ) * (((n : ℚ) + 1) ^ 2)) + ((10 : ℚ) * ((n : ℚ) + 1)) + (12 : ℚ)) * x) / ((((n : ℚ) + 1) ^ 2) + ((n : ℚ) + 1))) := by
  have heq : prefix p220 = p220_sum := funext p220_prefix
  change GeneralSecondCertificate (prefix p220) (10 : ℚ) (6 : ℚ) (fun n x y => (((((n : ℚ) + 1) ^ 2) + ((3 : ℚ) * ((n : ℚ) + 1))) * y + (((2 : ℚ) * (((n : ℚ) + 1) ^ 2)) + ((10 : ℚ) * ((n : ℚ) + 1)) + (12 : ℚ)) * x) / ((((n : ℚ) + 1) ^ 2) + ((n : ℚ) + 1)))
  rw [heq]
  exact p220_sum_valid
theorem p220_unique (a : ℕ → ℚ) (ha : PureSecondSumCertificate a (10 : ℚ) (6 : ℚ) (fun n x y => (((((n : ℚ) + 1) ^ 2) + ((3 : ℚ) * ((n : ℚ) + 1))) * y + (((2 : ℚ) * (((n : ℚ) + 1) ^ 2)) + ((10 : ℚ) * ((n : ℚ) + 1)) + (12 : ℚ)) * x) / ((((n : ℚ) + 1) ^ 2) + ((n : ℚ) + 1)))) :
    ∀ n, a n = p220 n := pure_second_sum_unique p220_valid ha
#print axioms p220_valid
#print axioms p220_unique

def p177_sum (n : ℕ) : ℚ := (((n : ℚ) + 1) * (((3 : ℚ) ^ n) + ((-1 : ℚ) ^ n)))
theorem p177_sum_valid : GeneralSecondCertificate p177_sum (2 : ℚ) (4 : ℚ) (fun n x y => (((2 : ℚ) * ((n : ℚ) + 1) * (((n : ℚ) + 1) + (2 : ℚ))) * y + ((3 : ℚ) * (((n : ℚ) + 1) + (1 : ℚ)) * (((n : ℚ) + 1) + (2 : ℚ))) * x) / (((n : ℚ) + 1) * (((n : ℚ) + 1) + (1 : ℚ)))) := by
  apply linear_second_certificate p177_sum (2 : ℚ) (4 : ℚ) (fun n => (((n : ℚ) + 1) * (((n : ℚ) + 1) + (1 : ℚ)))) (fun n => ((2 : ℚ) * ((n : ℚ) + 1) * (((n : ℚ) + 1) + (2 : ℚ)))) (fun n => ((3 : ℚ) * (((n : ℚ) + 1) + (1 : ℚ)) * (((n : ℚ) + 1) + (2 : ℚ))))
  · norm_num [p177_sum]
  · norm_num [p177_sum]
  · intro n; positivity
  · intro n
    simp only [p177_sum, Nat.cast_add, Nat.cast_one, pow_succ, pow_add] at *
    ring
theorem p177_sum_unique (a : ℕ → ℚ) (hi : a 0 = (2 : ℚ)) (hj : a 1 = (4 : ℚ))
    (ha : ∀ n : ℕ, (((n : ℚ) + 1) * (((n : ℚ) + 1) + (1 : ℚ))) * a (n + 2) = ((2 : ℚ) * ((n : ℚ) + 1) * (((n : ℚ) + 1) + (2 : ℚ))) * a (n + 1) + ((3 : ℚ) * (((n : ℚ) + 1) + (1 : ℚ)) * (((n : ℚ) + 1) + (2 : ℚ))) * a n) :
    ∀ n, a n = p177_sum n := by
  apply general_second_unique p177_sum_valid
  exact linear_second_certificate a (2 : ℚ) (4 : ℚ) (fun n => (((n : ℚ) + 1) * (((n : ℚ) + 1) + (1 : ℚ)))) (fun n => ((2 : ℚ) * ((n : ℚ) + 1) * (((n : ℚ) + 1) + (2 : ℚ)))) (fun n => ((3 : ℚ) * (((n : ℚ) + 1) + (1 : ℚ)) * (((n : ℚ) + 1) + (2 : ℚ)))) hi hj (by intro n; positivity) ha
#print axioms p177_sum_valid
#print axioms p177_sum_unique

def p177 (n : ℕ) : ℚ := ((((n : ℚ) + 1) * (((3 : ℚ) ^ n) + ((-1 : ℚ) ^ n))) + ((-1 : ℚ) * (((n : ℚ) + 1) + (-1 : ℚ)) * ((((3 : ℚ) ^ n) / (3 : ℚ)) + (((-1 : ℚ) ^ n) / (-1 : ℚ)))))
theorem p177_prefix : ∀ n, prefix p177 n = p177_sum n := by
  intro n
  induction n with
  | zero => norm_num [prefix, p177, p177_sum]
  | succ n ih =>
    rw [prefix_succ, ih]
    simp only [p177, p177_sum, Nat.cast_add, Nat.cast_one, pow_succ, pow_add]
    norm_num <;> ring
theorem p177_valid : PureSecondSumCertificate p177 (2 : ℚ) (4 : ℚ) (fun n x y => (((2 : ℚ) * ((n : ℚ) + 1) * (((n : ℚ) + 1) + (2 : ℚ))) * y + ((3 : ℚ) * (((n : ℚ) + 1) + (1 : ℚ)) * (((n : ℚ) + 1) + (2 : ℚ))) * x) / (((n : ℚ) + 1) * (((n : ℚ) + 1) + (1 : ℚ)))) := by
  have heq : prefix p177 = p177_sum := funext p177_prefix
  change GeneralSecondCertificate (prefix p177) (2 : ℚ) (4 : ℚ) (fun n x y => (((2 : ℚ) * ((n : ℚ) + 1) * (((n : ℚ) + 1) + (2 : ℚ))) * y + ((3 : ℚ) * (((n : ℚ) + 1) + (1 : ℚ)) * (((n : ℚ) + 1) + (2 : ℚ))) * x) / (((n : ℚ) + 1) * (((n : ℚ) + 1) + (1 : ℚ))))
  rw [heq]
  exact p177_sum_valid
theorem p177_unique (a : ℕ → ℚ) (ha : PureSecondSumCertificate a (2 : ℚ) (4 : ℚ) (fun n x y => (((2 : ℚ) * ((n : ℚ) + 1) * (((n : ℚ) + 1) + (2 : ℚ))) * y + ((3 : ℚ) * (((n : ℚ) + 1) + (1 : ℚ)) * (((n : ℚ) + 1) + (2 : ℚ))) * x) / (((n : ℚ) + 1) * (((n : ℚ) + 1) + (1 : ℚ))))) :
    ∀ n, a n = p177 n := pure_second_sum_unique p177_valid ha
#print axioms p177_valid
#print axioms p177_unique

def p181_sum (n : ℕ) : ℚ := (((n : ℚ) + 1) * (((n : ℚ) + 1) + (1 : ℚ)) * (((5 : ℚ) * ((2 : ℚ) ^ n)) + ((3 : ℚ) * ((-2 : ℚ) ^ n))))
theorem p181_sum_valid : GeneralSecondCertificate p181_sum (16 : ℚ) (24 : ℚ) (fun n x y => ((0 : ℚ) * y + (((4 : ℚ) * (((n : ℚ) + 1) ^ 2)) + ((20 : ℚ) * ((n : ℚ) + 1)) + (24 : ℚ)) * x) / ((((n : ℚ) + 1) ^ 2) + ((n : ℚ) + 1))) := by
  apply linear_second_certificate p181_sum (16 : ℚ) (24 : ℚ) (fun n => ((((n : ℚ) + 1) ^ 2) + ((n : ℚ) + 1))) (fun n => (0 : ℚ)) (fun n => (((4 : ℚ) * (((n : ℚ) + 1) ^ 2)) + ((20 : ℚ) * ((n : ℚ) + 1)) + (24 : ℚ)))
  · norm_num [p181_sum]
  · norm_num [p181_sum]
  · intro n; positivity
  · intro n
    simp only [p181_sum, Nat.cast_add, Nat.cast_one, pow_succ, pow_add] at *
    ring
theorem p181_sum_unique (a : ℕ → ℚ) (hi : a 0 = (16 : ℚ)) (hj : a 1 = (24 : ℚ))
    (ha : ∀ n : ℕ, ((((n : ℚ) + 1) ^ 2) + ((n : ℚ) + 1)) * a (n + 2) = (0 : ℚ) * a (n + 1) + (((4 : ℚ) * (((n : ℚ) + 1) ^ 2)) + ((20 : ℚ) * ((n : ℚ) + 1)) + (24 : ℚ)) * a n) :
    ∀ n, a n = p181_sum n := by
  apply general_second_unique p181_sum_valid
  exact linear_second_certificate a (16 : ℚ) (24 : ℚ) (fun n => ((((n : ℚ) + 1) ^ 2) + ((n : ℚ) + 1))) (fun n => (0 : ℚ)) (fun n => (((4 : ℚ) * (((n : ℚ) + 1) ^ 2)) + ((20 : ℚ) * ((n : ℚ) + 1)) + (24 : ℚ))) hi hj (by intro n; positivity) ha
#print axioms p181_sum_valid
#print axioms p181_sum_unique

def p181 (n : ℕ) : ℚ := ((((n : ℚ) + 1) * (((n : ℚ) + 1) + (1 : ℚ)) * (((5 : ℚ) * ((2 : ℚ) ^ n)) + ((3 : ℚ) * ((-2 : ℚ) ^ n)))) + ((-1 : ℚ) * (((n : ℚ) + 1) + (-1 : ℚ)) * ((n : ℚ) + 1) * ((((5 : ℚ) * ((2 : ℚ) ^ n)) / (2 : ℚ)) + (((3 : ℚ) * ((-2 : ℚ) ^ n)) / (-2 : ℚ)))))
theorem p181_prefix : ∀ n, prefix p181 n = p181_sum n := by
  intro n
  induction n with
  | zero => norm_num [prefix, p181, p181_sum]
  | succ n ih =>
    rw [prefix_succ, ih]
    simp only [p181, p181_sum, Nat.cast_add, Nat.cast_one, pow_succ, pow_add]
    norm_num <;> ring
theorem p181_valid : PureSecondSumCertificate p181 (16 : ℚ) (24 : ℚ) (fun n x y => ((0 : ℚ) * y + (((4 : ℚ) * (((n : ℚ) + 1) ^ 2)) + ((20 : ℚ) * ((n : ℚ) + 1)) + (24 : ℚ)) * x) / ((((n : ℚ) + 1) ^ 2) + ((n : ℚ) + 1))) := by
  have heq : prefix p181 = p181_sum := funext p181_prefix
  change GeneralSecondCertificate (prefix p181) (16 : ℚ) (24 : ℚ) (fun n x y => ((0 : ℚ) * y + (((4 : ℚ) * (((n : ℚ) + 1) ^ 2)) + ((20 : ℚ) * ((n : ℚ) + 1)) + (24 : ℚ)) * x) / ((((n : ℚ) + 1) ^ 2) + ((n : ℚ) + 1)))
  rw [heq]
  exact p181_sum_valid
theorem p181_unique (a : ℕ → ℚ) (ha : PureSecondSumCertificate a (16 : ℚ) (24 : ℚ) (fun n x y => ((0 : ℚ) * y + (((4 : ℚ) * (((n : ℚ) + 1) ^ 2)) + ((20 : ℚ) * ((n : ℚ) + 1)) + (24 : ℚ)) * x) / ((((n : ℚ) + 1) ^ 2) + ((n : ℚ) + 1)))) :
    ∀ n, a n = p181 n := pure_second_sum_unique p181_valid ha
#print axioms p181_valid
#print axioms p181_unique

def p218_sum (n : ℕ) : ℚ := (((n : ℚ) + 1) * (((2 : ℚ) ^ n) + ((1 : ℚ) ^ n)))
theorem p218_sum_valid : GeneralSecondCertificate p218_sum (2 : ℚ) (6 : ℚ) (fun n x y => (((3 : ℚ) * ((n : ℚ) + 1) * (((n : ℚ) + 1) + (2 : ℚ))) * y + ((-2 : ℚ) * (((n : ℚ) + 1) + (1 : ℚ)) * (((n : ℚ) + 1) + (2 : ℚ))) * x) / (((n : ℚ) + 1) * (((n : ℚ) + 1) + (1 : ℚ)))) := by
  apply linear_second_certificate p218_sum (2 : ℚ) (6 : ℚ) (fun n => (((n : ℚ) + 1) * (((n : ℚ) + 1) + (1 : ℚ)))) (fun n => ((3 : ℚ) * ((n : ℚ) + 1) * (((n : ℚ) + 1) + (2 : ℚ)))) (fun n => ((-2 : ℚ) * (((n : ℚ) + 1) + (1 : ℚ)) * (((n : ℚ) + 1) + (2 : ℚ))))
  · norm_num [p218_sum]
  · norm_num [p218_sum]
  · intro n; positivity
  · intro n
    simp only [p218_sum, Nat.cast_add, Nat.cast_one, pow_succ, pow_add] at *
    ring
theorem p218_sum_unique (a : ℕ → ℚ) (hi : a 0 = (2 : ℚ)) (hj : a 1 = (6 : ℚ))
    (ha : ∀ n : ℕ, (((n : ℚ) + 1) * (((n : ℚ) + 1) + (1 : ℚ))) * a (n + 2) = ((3 : ℚ) * ((n : ℚ) + 1) * (((n : ℚ) + 1) + (2 : ℚ))) * a (n + 1) + ((-2 : ℚ) * (((n : ℚ) + 1) + (1 : ℚ)) * (((n : ℚ) + 1) + (2 : ℚ))) * a n) :
    ∀ n, a n = p218_sum n := by
  apply general_second_unique p218_sum_valid
  exact linear_second_certificate a (2 : ℚ) (6 : ℚ) (fun n => (((n : ℚ) + 1) * (((n : ℚ) + 1) + (1 : ℚ)))) (fun n => ((3 : ℚ) * ((n : ℚ) + 1) * (((n : ℚ) + 1) + (2 : ℚ)))) (fun n => ((-2 : ℚ) * (((n : ℚ) + 1) + (1 : ℚ)) * (((n : ℚ) + 1) + (2 : ℚ)))) hi hj (by intro n; positivity) ha
#print axioms p218_sum_valid
#print axioms p218_sum_unique

def p218 (n : ℕ) : ℚ := ((((n : ℚ) + 1) * (((2 : ℚ) ^ n) + ((1 : ℚ) ^ n))) + ((-1 : ℚ) * (((n : ℚ) + 1) + (-1 : ℚ)) * ((((2 : ℚ) ^ n) / (2 : ℚ)) + (((1 : ℚ) ^ n) / (1 : ℚ)))))
theorem p218_prefix : ∀ n, prefix p218 n = p218_sum n := by
  intro n
  induction n with
  | zero => norm_num [prefix, p218, p218_sum]
  | succ n ih =>
    rw [prefix_succ, ih]
    simp only [p218, p218_sum, Nat.cast_add, Nat.cast_one, pow_succ, pow_add]
    norm_num <;> ring
theorem p218_valid : PureSecondSumCertificate p218 (2 : ℚ) (6 : ℚ) (fun n x y => (((3 : ℚ) * ((n : ℚ) + 1) * (((n : ℚ) + 1) + (2 : ℚ))) * y + ((-2 : ℚ) * (((n : ℚ) + 1) + (1 : ℚ)) * (((n : ℚ) + 1) + (2 : ℚ))) * x) / (((n : ℚ) + 1) * (((n : ℚ) + 1) + (1 : ℚ)))) := by
  have heq : prefix p218 = p218_sum := funext p218_prefix
  change GeneralSecondCertificate (prefix p218) (2 : ℚ) (6 : ℚ) (fun n x y => (((3 : ℚ) * ((n : ℚ) + 1) * (((n : ℚ) + 1) + (2 : ℚ))) * y + ((-2 : ℚ) * (((n : ℚ) + 1) + (1 : ℚ)) * (((n : ℚ) + 1) + (2 : ℚ))) * x) / (((n : ℚ) + 1) * (((n : ℚ) + 1) + (1 : ℚ))))
  rw [heq]
  exact p218_sum_valid
theorem p218_unique (a : ℕ → ℚ) (ha : PureSecondSumCertificate a (2 : ℚ) (6 : ℚ) (fun n x y => (((3 : ℚ) * ((n : ℚ) + 1) * (((n : ℚ) + 1) + (2 : ℚ))) * y + ((-2 : ℚ) * (((n : ℚ) + 1) + (1 : ℚ)) * (((n : ℚ) + 1) + (2 : ℚ))) * x) / (((n : ℚ) + 1) * (((n : ℚ) + 1) + (1 : ℚ))))) :
    ∀ n, a n = p218 n := pure_second_sum_unique p218_valid ha
#print axioms p218_valid
#print axioms p218_unique

def p237_sum (n : ℕ) : ℚ := (((n : ℚ) + 1) * (((n : ℚ) + 1) + (1 : ℚ)) * (((3 : ℚ) ^ n) + ((2 : ℚ) * ((-1 : ℚ) ^ n))))
theorem p237_sum_valid : GeneralSecondCertificate p237_sum (6 : ℚ) (6 : ℚ) (fun n x y => ((((2 : ℚ) * (((n : ℚ) + 1) ^ 2)) + ((6 : ℚ) * ((n : ℚ) + 1))) * y + (((3 : ℚ) * (((n : ℚ) + 1) ^ 2)) + ((15 : ℚ) * ((n : ℚ) + 1)) + (18 : ℚ)) * x) / ((((n : ℚ) + 1) ^ 2) + ((n : ℚ) + 1))) := by
  apply linear_second_certificate p237_sum (6 : ℚ) (6 : ℚ) (fun n => ((((n : ℚ) + 1) ^ 2) + ((n : ℚ) + 1))) (fun n => (((2 : ℚ) * (((n : ℚ) + 1) ^ 2)) + ((6 : ℚ) * ((n : ℚ) + 1)))) (fun n => (((3 : ℚ) * (((n : ℚ) + 1) ^ 2)) + ((15 : ℚ) * ((n : ℚ) + 1)) + (18 : ℚ)))
  · norm_num [p237_sum]
  · norm_num [p237_sum]
  · intro n; positivity
  · intro n
    simp only [p237_sum, Nat.cast_add, Nat.cast_one, pow_succ, pow_add] at *
    ring
theorem p237_sum_unique (a : ℕ → ℚ) (hi : a 0 = (6 : ℚ)) (hj : a 1 = (6 : ℚ))
    (ha : ∀ n : ℕ, ((((n : ℚ) + 1) ^ 2) + ((n : ℚ) + 1)) * a (n + 2) = (((2 : ℚ) * (((n : ℚ) + 1) ^ 2)) + ((6 : ℚ) * ((n : ℚ) + 1))) * a (n + 1) + (((3 : ℚ) * (((n : ℚ) + 1) ^ 2)) + ((15 : ℚ) * ((n : ℚ) + 1)) + (18 : ℚ)) * a n) :
    ∀ n, a n = p237_sum n := by
  apply general_second_unique p237_sum_valid
  exact linear_second_certificate a (6 : ℚ) (6 : ℚ) (fun n => ((((n : ℚ) + 1) ^ 2) + ((n : ℚ) + 1))) (fun n => (((2 : ℚ) * (((n : ℚ) + 1) ^ 2)) + ((6 : ℚ) * ((n : ℚ) + 1)))) (fun n => (((3 : ℚ) * (((n : ℚ) + 1) ^ 2)) + ((15 : ℚ) * ((n : ℚ) + 1)) + (18 : ℚ))) hi hj (by intro n; positivity) ha
#print axioms p237_sum_valid
#print axioms p237_sum_unique

def p237 (n : ℕ) : ℚ := ((((n : ℚ) + 1) * (((n : ℚ) + 1) + (1 : ℚ)) * (((3 : ℚ) ^ n) + ((2 : ℚ) * ((-1 : ℚ) ^ n)))) + ((-1 : ℚ) * (((n : ℚ) + 1) + (-1 : ℚ)) * ((n : ℚ) + 1) * ((((3 : ℚ) ^ n) / (3 : ℚ)) + (((2 : ℚ) * ((-1 : ℚ) ^ n)) / (-1 : ℚ)))))
theorem p237_prefix : ∀ n, prefix p237 n = p237_sum n := by
  intro n
  induction n with
  | zero => norm_num [prefix, p237, p237_sum]
  | succ n ih =>
    rw [prefix_succ, ih]
    simp only [p237, p237_sum, Nat.cast_add, Nat.cast_one, pow_succ, pow_add]
    norm_num <;> ring
theorem p237_valid : PureSecondSumCertificate p237 (6 : ℚ) (6 : ℚ) (fun n x y => ((((2 : ℚ) * (((n : ℚ) + 1) ^ 2)) + ((6 : ℚ) * ((n : ℚ) + 1))) * y + (((3 : ℚ) * (((n : ℚ) + 1) ^ 2)) + ((15 : ℚ) * ((n : ℚ) + 1)) + (18 : ℚ)) * x) / ((((n : ℚ) + 1) ^ 2) + ((n : ℚ) + 1))) := by
  have heq : prefix p237 = p237_sum := funext p237_prefix
  change GeneralSecondCertificate (prefix p237) (6 : ℚ) (6 : ℚ) (fun n x y => ((((2 : ℚ) * (((n : ℚ) + 1) ^ 2)) + ((6 : ℚ) * ((n : ℚ) + 1))) * y + (((3 : ℚ) * (((n : ℚ) + 1) ^ 2)) + ((15 : ℚ) * ((n : ℚ) + 1)) + (18 : ℚ)) * x) / ((((n : ℚ) + 1) ^ 2) + ((n : ℚ) + 1)))
  rw [heq]
  exact p237_sum_valid
theorem p237_unique (a : ℕ → ℚ) (ha : PureSecondSumCertificate a (6 : ℚ) (6 : ℚ) (fun n x y => ((((2 : ℚ) * (((n : ℚ) + 1) ^ 2)) + ((6 : ℚ) * ((n : ℚ) + 1))) * y + (((3 : ℚ) * (((n : ℚ) + 1) ^ 2)) + ((15 : ℚ) * ((n : ℚ) + 1)) + (18 : ℚ)) * x) / ((((n : ℚ) + 1) ^ 2) + ((n : ℚ) + 1)))) :
    ∀ n, a n = p237 n := pure_second_sum_unique p237_valid ha
#print axioms p237_valid
#print axioms p237_unique

def p168_sum (n : ℕ) : ℚ := (((n : ℚ) + 1) * (((3 : ℚ) ^ n) + ((1 : ℚ) ^ n)))
theorem p168_sum_valid : GeneralSecondCertificate p168_sum (2 : ℚ) (8 : ℚ) (fun n x y => (((4 : ℚ) * ((n : ℚ) + 1) * (((n : ℚ) + 1) + (2 : ℚ))) * y + ((-3 : ℚ) * (((n : ℚ) + 1) + (1 : ℚ)) * (((n : ℚ) + 1) + (2 : ℚ))) * x) / (((n : ℚ) + 1) * (((n : ℚ) + 1) + (1 : ℚ)))) := by
  apply linear_second_certificate p168_sum (2 : ℚ) (8 : ℚ) (fun n => (((n : ℚ) + 1) * (((n : ℚ) + 1) + (1 : ℚ)))) (fun n => ((4 : ℚ) * ((n : ℚ) + 1) * (((n : ℚ) + 1) + (2 : ℚ)))) (fun n => ((-3 : ℚ) * (((n : ℚ) + 1) + (1 : ℚ)) * (((n : ℚ) + 1) + (2 : ℚ))))
  · norm_num [p168_sum]
  · norm_num [p168_sum]
  · intro n; positivity
  · intro n
    simp only [p168_sum, Nat.cast_add, Nat.cast_one, pow_succ, pow_add] at *
    ring
theorem p168_sum_unique (a : ℕ → ℚ) (hi : a 0 = (2 : ℚ)) (hj : a 1 = (8 : ℚ))
    (ha : ∀ n : ℕ, (((n : ℚ) + 1) * (((n : ℚ) + 1) + (1 : ℚ))) * a (n + 2) = ((4 : ℚ) * ((n : ℚ) + 1) * (((n : ℚ) + 1) + (2 : ℚ))) * a (n + 1) + ((-3 : ℚ) * (((n : ℚ) + 1) + (1 : ℚ)) * (((n : ℚ) + 1) + (2 : ℚ))) * a n) :
    ∀ n, a n = p168_sum n := by
  apply general_second_unique p168_sum_valid
  exact linear_second_certificate a (2 : ℚ) (8 : ℚ) (fun n => (((n : ℚ) + 1) * (((n : ℚ) + 1) + (1 : ℚ)))) (fun n => ((4 : ℚ) * ((n : ℚ) + 1) * (((n : ℚ) + 1) + (2 : ℚ)))) (fun n => ((-3 : ℚ) * (((n : ℚ) + 1) + (1 : ℚ)) * (((n : ℚ) + 1) + (2 : ℚ)))) hi hj (by intro n; positivity) ha
#print axioms p168_sum_valid
#print axioms p168_sum_unique

def p168 (n : ℕ) : ℚ := ((((n : ℚ) + 1) * (((3 : ℚ) ^ n) + ((1 : ℚ) ^ n))) + ((-1 : ℚ) * (((n : ℚ) + 1) + (-1 : ℚ)) * ((((3 : ℚ) ^ n) / (3 : ℚ)) + (((1 : ℚ) ^ n) / (1 : ℚ)))))
theorem p168_prefix : ∀ n, prefix p168 n = p168_sum n := by
  intro n
  induction n with
  | zero => norm_num [prefix, p168, p168_sum]
  | succ n ih =>
    rw [prefix_succ, ih]
    simp only [p168, p168_sum, Nat.cast_add, Nat.cast_one, pow_succ, pow_add]
    norm_num <;> ring
theorem p168_valid : PureSecondSumCertificate p168 (2 : ℚ) (8 : ℚ) (fun n x y => (((4 : ℚ) * ((n : ℚ) + 1) * (((n : ℚ) + 1) + (2 : ℚ))) * y + ((-3 : ℚ) * (((n : ℚ) + 1) + (1 : ℚ)) * (((n : ℚ) + 1) + (2 : ℚ))) * x) / (((n : ℚ) + 1) * (((n : ℚ) + 1) + (1 : ℚ)))) := by
  have heq : prefix p168 = p168_sum := funext p168_prefix
  change GeneralSecondCertificate (prefix p168) (2 : ℚ) (8 : ℚ) (fun n x y => (((4 : ℚ) * ((n : ℚ) + 1) * (((n : ℚ) + 1) + (2 : ℚ))) * y + ((-3 : ℚ) * (((n : ℚ) + 1) + (1 : ℚ)) * (((n : ℚ) + 1) + (2 : ℚ))) * x) / (((n : ℚ) + 1) * (((n : ℚ) + 1) + (1 : ℚ))))
  rw [heq]
  exact p168_sum_valid
theorem p168_unique (a : ℕ → ℚ) (ha : PureSecondSumCertificate a (2 : ℚ) (8 : ℚ) (fun n x y => (((4 : ℚ) * ((n : ℚ) + 1) * (((n : ℚ) + 1) + (2 : ℚ))) * y + ((-3 : ℚ) * (((n : ℚ) + 1) + (1 : ℚ)) * (((n : ℚ) + 1) + (2 : ℚ))) * x) / (((n : ℚ) + 1) * (((n : ℚ) + 1) + (1 : ℚ))))) :
    ∀ n, a n = p168 n := pure_second_sum_unique p168_valid ha
#print axioms p168_valid
#print axioms p168_unique

def p227_sum (n : ℕ) : ℚ := (((n : ℚ) + 1) * (((n : ℚ) + 1) + (1 : ℚ)) * (((3 : ℚ) ^ n) + ((-2 : ℚ) ^ n)))
theorem p227_sum_valid : GeneralSecondCertificate p227_sum (4 : ℚ) (6 : ℚ) (fun n x y => (((((n : ℚ) + 1) ^ 2) + ((3 : ℚ) * ((n : ℚ) + 1))) * y + (((6 : ℚ) * (((n : ℚ) + 1) ^ 2)) + ((30 : ℚ) * ((n : ℚ) + 1)) + (36 : ℚ)) * x) / ((((n : ℚ) + 1) ^ 2) + ((n : ℚ) + 1))) := by
  apply linear_second_certificate p227_sum (4 : ℚ) (6 : ℚ) (fun n => ((((n : ℚ) + 1) ^ 2) + ((n : ℚ) + 1))) (fun n => ((((n : ℚ) + 1) ^ 2) + ((3 : ℚ) * ((n : ℚ) + 1)))) (fun n => (((6 : ℚ) * (((n : ℚ) + 1) ^ 2)) + ((30 : ℚ) * ((n : ℚ) + 1)) + (36 : ℚ)))
  · norm_num [p227_sum]
  · norm_num [p227_sum]
  · intro n; positivity
  · intro n
    simp only [p227_sum, Nat.cast_add, Nat.cast_one, pow_succ, pow_add] at *
    ring
theorem p227_sum_unique (a : ℕ → ℚ) (hi : a 0 = (4 : ℚ)) (hj : a 1 = (6 : ℚ))
    (ha : ∀ n : ℕ, ((((n : ℚ) + 1) ^ 2) + ((n : ℚ) + 1)) * a (n + 2) = ((((n : ℚ) + 1) ^ 2) + ((3 : ℚ) * ((n : ℚ) + 1))) * a (n + 1) + (((6 : ℚ) * (((n : ℚ) + 1) ^ 2)) + ((30 : ℚ) * ((n : ℚ) + 1)) + (36 : ℚ)) * a n) :
    ∀ n, a n = p227_sum n := by
  apply general_second_unique p227_sum_valid
  exact linear_second_certificate a (4 : ℚ) (6 : ℚ) (fun n => ((((n : ℚ) + 1) ^ 2) + ((n : ℚ) + 1))) (fun n => ((((n : ℚ) + 1) ^ 2) + ((3 : ℚ) * ((n : ℚ) + 1)))) (fun n => (((6 : ℚ) * (((n : ℚ) + 1) ^ 2)) + ((30 : ℚ) * ((n : ℚ) + 1)) + (36 : ℚ))) hi hj (by intro n; positivity) ha
#print axioms p227_sum_valid
#print axioms p227_sum_unique

def p227 (n : ℕ) : ℚ := ((((n : ℚ) + 1) * (((n : ℚ) + 1) + (1 : ℚ)) * (((3 : ℚ) ^ n) + ((-2 : ℚ) ^ n))) + ((-1 : ℚ) * (((n : ℚ) + 1) + (-1 : ℚ)) * ((n : ℚ) + 1) * ((((3 : ℚ) ^ n) / (3 : ℚ)) + (((-2 : ℚ) ^ n) / (-2 : ℚ)))))
theorem p227_prefix : ∀ n, prefix p227 n = p227_sum n := by
  intro n
  induction n with
  | zero => norm_num [prefix, p227, p227_sum]
  | succ n ih =>
    rw [prefix_succ, ih]
    simp only [p227, p227_sum, Nat.cast_add, Nat.cast_one, pow_succ, pow_add]
    norm_num <;> ring
theorem p227_valid : PureSecondSumCertificate p227 (4 : ℚ) (6 : ℚ) (fun n x y => (((((n : ℚ) + 1) ^ 2) + ((3 : ℚ) * ((n : ℚ) + 1))) * y + (((6 : ℚ) * (((n : ℚ) + 1) ^ 2)) + ((30 : ℚ) * ((n : ℚ) + 1)) + (36 : ℚ)) * x) / ((((n : ℚ) + 1) ^ 2) + ((n : ℚ) + 1))) := by
  have heq : prefix p227 = p227_sum := funext p227_prefix
  change GeneralSecondCertificate (prefix p227) (4 : ℚ) (6 : ℚ) (fun n x y => (((((n : ℚ) + 1) ^ 2) + ((3 : ℚ) * ((n : ℚ) + 1))) * y + (((6 : ℚ) * (((n : ℚ) + 1) ^ 2)) + ((30 : ℚ) * ((n : ℚ) + 1)) + (36 : ℚ)) * x) / ((((n : ℚ) + 1) ^ 2) + ((n : ℚ) + 1)))
  rw [heq]
  exact p227_sum_valid
theorem p227_unique (a : ℕ → ℚ) (ha : PureSecondSumCertificate a (4 : ℚ) (6 : ℚ) (fun n x y => (((((n : ℚ) + 1) ^ 2) + ((3 : ℚ) * ((n : ℚ) + 1))) * y + (((6 : ℚ) * (((n : ℚ) + 1) ^ 2)) + ((30 : ℚ) * ((n : ℚ) + 1)) + (36 : ℚ)) * x) / ((((n : ℚ) + 1) ^ 2) + ((n : ℚ) + 1)))) :
    ∀ n, a n = p227 n := pure_second_sum_unique p227_valid ha
#print axioms p227_valid
#print axioms p227_unique

def p166 (n : ℕ) : ℚ := (((2 : ℚ) ^ n) + (2 : ℚ))
def p166_sum (n : ℕ) : ℚ := (((2 : ℚ) ^ (n + 1)) + ((2 : ℚ) * ((n : ℚ) + 1)) + (-1 : ℚ))
theorem p166_prefix : ∀ n, prefix p166 n = p166_sum n := by
  intro n
  induction n with
  | zero => norm_num [prefix, p166, p166_sum]
  | succ n ih =>
    rw [prefix_succ, ih]
    simp only [p166, p166_sum, Nat.cast_add, Nat.cast_one, pow_succ, pow_add]
    norm_num <;> ring
theorem p166_valid : SumRelationCertificate p166 (3 : ℚ) (2 : ℚ) (fun n => (((2 : ℚ) * ((n : ℚ) + 1)) + (-5 : ℚ))) := by
  constructor
  · norm_num [p166]
  · intro n
    rw [p166_prefix]
    simp only [p166, p166_sum, Nat.cast_add, Nat.cast_one, pow_succ, pow_add]
    norm_num <;> ring
theorem p166_unique (a : ℕ → ℚ) (ha : SumRelationCertificate a (3 : ℚ) (2 : ℚ) (fun n => (((2 : ℚ) * ((n : ℚ) + 1)) + (-5 : ℚ)))) :
    ∀ n, a n = p166 n := sum_relation_unique p166_valid ha (by norm_num)
#print axioms p166_valid
#print axioms p166_unique

def p245 (n : ℕ) : ℚ := (((2 : ℚ) ^ n) + ((n : ℚ) + 1))
def p245_sum (n : ℕ) : ℚ := (((2 : ℚ) ^ (n + 1)) + (((1 : ℚ) / 2) * ((((n : ℚ) + 1) + (1 : ℚ)) ^ 2)) + (((-1 : ℚ) / 2) * ((n : ℚ) + 1)) + ((-3 : ℚ) / 2))
theorem p245_prefix : ∀ n, prefix p245 n = p245_sum n := by
  intro n
  induction n with
  | zero => norm_num [prefix, p245, p245_sum]
  | succ n ih =>
    rw [prefix_succ, ih]
    simp only [p245, p245_sum, Nat.cast_add, Nat.cast_one, pow_succ, pow_add]
    norm_num <;> ring
theorem p245_valid : SumRelationCertificate p245 (2 : ℚ) (2 : ℚ) (fun n => ((((1 : ℚ) / 2) * (((n : ℚ) + 1) ^ 2)) + (((-3 : ℚ) / 2) * ((n : ℚ) + 1)) + (-1 : ℚ))) := by
  constructor
  · norm_num [p245]
  · intro n
    rw [p245_prefix]
    simp only [p245, p245_sum, Nat.cast_add, Nat.cast_one, pow_succ, pow_add]
    norm_num <;> ring
theorem p245_unique (a : ℕ → ℚ) (ha : SumRelationCertificate a (2 : ℚ) (2 : ℚ) (fun n => ((((1 : ℚ) / 2) * (((n : ℚ) + 1) ^ 2)) + (((-3 : ℚ) / 2) * ((n : ℚ) + 1)) + (-1 : ℚ)))) :
    ∀ n, a n = p245 n := sum_relation_unique p245_valid ha (by norm_num)
#print axioms p245_valid
#print axioms p245_unique

def p204 (n : ℕ) : ℚ := (((2 : ℚ) * ((2 : ℚ) ^ n)) + (2 : ℚ))
def p204_sum (n : ℕ) : ℚ := (((2 : ℚ) * (((2 : ℚ) ^ (n + 1)) + (-1 : ℚ))) + ((2 : ℚ) * ((n : ℚ) + 1)))
theorem p204_prefix : ∀ n, prefix p204 n = p204_sum n := by
  intro n
  induction n with
  | zero => norm_num [prefix, p204, p204_sum]
  | succ n ih =>
    rw [prefix_succ, ih]
    simp only [p204, p204_sum, Nat.cast_add, Nat.cast_one, pow_succ, pow_add]
    norm_num <;> ring
theorem p204_valid : SumRelationCertificate p204 (4 : ℚ) (2 : ℚ) (fun n => (((2 : ℚ) * ((n : ℚ) + 1)) + (-6 : ℚ))) := by
  constructor
  · norm_num [p204]
  · intro n
    rw [p204_prefix]
    simp only [p204, p204_sum, Nat.cast_add, Nat.cast_one, pow_succ, pow_add]
    norm_num <;> ring
theorem p204_unique (a : ℕ → ℚ) (ha : SumRelationCertificate a (4 : ℚ) (2 : ℚ) (fun n => (((2 : ℚ) * ((n : ℚ) + 1)) + (-6 : ℚ)))) :
    ∀ n, a n = p204 n := sum_relation_unique p204_valid ha (by norm_num)
#print axioms p204_valid
#print axioms p204_unique

def p207 (n : ℕ) : ℚ := (((2 : ℚ) * ((2 : ℚ) ^ n)) + ((n : ℚ) + 1))
def p207_sum (n : ℕ) : ℚ := (((2 : ℚ) * (((2 : ℚ) ^ (n + 1)) + (-1 : ℚ))) + (((1 : ℚ) / 2) * ((((n : ℚ) + 1) + (1 : ℚ)) ^ 2)) + (((-1 : ℚ) / 2) * ((n : ℚ) + 1)) + ((-1 : ℚ) / 2))
theorem p207_prefix : ∀ n, prefix p207 n = p207_sum n := by
  intro n
  induction n with
  | zero => norm_num [prefix, p207, p207_sum]
  | succ n ih =>
    rw [prefix_succ, ih]
    simp only [p207, p207_sum, Nat.cast_add, Nat.cast_one, pow_succ, pow_add]
    norm_num <;> ring
theorem p207_valid : SumRelationCertificate p207 (3 : ℚ) (2 : ℚ) (fun n => ((((1 : ℚ) / 2) * (((n : ℚ) + 1) ^ 2)) + (((-3 : ℚ) / 2) * ((n : ℚ) + 1)) + (-2 : ℚ))) := by
  constructor
  · norm_num [p207]
  · intro n
    rw [p207_prefix]
    simp only [p207, p207_sum, Nat.cast_add, Nat.cast_one, pow_succ, pow_add]
    norm_num <;> ring
theorem p207_unique (a : ℕ → ℚ) (ha : SumRelationCertificate a (3 : ℚ) (2 : ℚ) (fun n => ((((1 : ℚ) / 2) * (((n : ℚ) + 1) ^ 2)) + (((-3 : ℚ) / 2) * ((n : ℚ) + 1)) + (-2 : ℚ)))) :
    ∀ n, a n = p207 n := sum_relation_unique p207_valid ha (by norm_num)
#print axioms p207_valid
#print axioms p207_unique

def p228 (n : ℕ) : ℚ := (((4 : ℚ) * ((2 : ℚ) ^ n)) + (2 : ℚ))
def p228_sum (n : ℕ) : ℚ := (((4 : ℚ) * (((2 : ℚ) ^ (n + 1)) + (-1 : ℚ))) + ((2 : ℚ) * ((n : ℚ) + 1)))
theorem p228_prefix : ∀ n, prefix p228 n = p228_sum n := by
  intro n
  induction n with
  | zero => norm_num [prefix, p228, p228_sum]
  | succ n ih =>
    rw [prefix_succ, ih]
    simp only [p228, p228_sum, Nat.cast_add, Nat.cast_one, pow_succ, pow_add]
    norm_num <;> ring
theorem p228_valid : SumRelationCertificate p228 (6 : ℚ) (2 : ℚ) (fun n => (((2 : ℚ) * ((n : ℚ) + 1)) + (-8 : ℚ))) := by
  constructor
  · norm_num [p228]
  · intro n
    rw [p228_prefix]
    simp only [p228, p228_sum, Nat.cast_add, Nat.cast_one, pow_succ, pow_add]
    norm_num <;> ring
theorem p228_unique (a : ℕ → ℚ) (ha : SumRelationCertificate a (6 : ℚ) (2 : ℚ) (fun n => (((2 : ℚ) * ((n : ℚ) + 1)) + (-8 : ℚ)))) :
    ∀ n, a n = p228 n := sum_relation_unique p228_valid ha (by norm_num)
#print axioms p228_valid
#print axioms p228_unique

def p189 (n : ℕ) : ℚ := (((3 : ℚ) * ((2 : ℚ) ^ n)) + ((n : ℚ) + 1))
def p189_sum (n : ℕ) : ℚ := (((3 : ℚ) * (((2 : ℚ) ^ (n + 1)) + (-1 : ℚ))) + (((1 : ℚ) / 2) * ((((n : ℚ) + 1) + (1 : ℚ)) ^ 2)) + (((-1 : ℚ) / 2) * ((n : ℚ) + 1)) + ((-1 : ℚ) / 2))
theorem p189_prefix : ∀ n, prefix p189 n = p189_sum n := by
  intro n
  induction n with
  | zero => norm_num [prefix, p189, p189_sum]
  | succ n ih =>
    rw [prefix_succ, ih]
    simp only [p189, p189_sum, Nat.cast_add, Nat.cast_one, pow_succ, pow_add]
    norm_num <;> ring
theorem p189_valid : SumRelationCertificate p189 (4 : ℚ) (2 : ℚ) (fun n => ((((1 : ℚ) / 2) * (((n : ℚ) + 1) ^ 2)) + (((-3 : ℚ) / 2) * ((n : ℚ) + 1)) + (-3 : ℚ))) := by
  constructor
  · norm_num [p189]
  · intro n
    rw [p189_prefix]
    simp only [p189, p189_sum, Nat.cast_add, Nat.cast_one, pow_succ, pow_add]
    norm_num <;> ring
theorem p189_unique (a : ℕ → ℚ) (ha : SumRelationCertificate a (4 : ℚ) (2 : ℚ) (fun n => ((((1 : ℚ) / 2) * (((n : ℚ) + 1) ^ 2)) + (((-3 : ℚ) / 2) * ((n : ℚ) + 1)) + (-3 : ℚ)))) :
    ∀ n, a n = p189 n := sum_relation_unique p189_valid ha (by norm_num)
#print axioms p189_valid
#print axioms p189_unique

def p195 (n : ℕ) : ℚ := ((((1 : ℚ) / 2) * ((2 : ℚ) ^ n)) + (2 : ℚ))
def p195_sum (n : ℕ) : ℚ := ((((1 : ℚ) / 2) * (((2 : ℚ) ^ (n + 1)) + (-1 : ℚ))) + ((2 : ℚ) * ((n : ℚ) + 1)))
theorem p195_prefix : ∀ n, prefix p195 n = p195_sum n := by
  intro n
  induction n with
  | zero => norm_num [prefix, p195, p195_sum]
  | succ n ih =>
    rw [prefix_succ, ih]
    simp only [p195, p195_sum, Nat.cast_add, Nat.cast_one, pow_succ, pow_add]
    norm_num <;> ring
theorem p195_valid : SumRelationCertificate p195 ((5 : ℚ) / 2) (2 : ℚ) (fun n => (((2 : ℚ) * ((n : ℚ) + 1)) + ((-9 : ℚ) / 2))) := by
  constructor
  · norm_num [p195]
  · intro n
    rw [p195_prefix]
    simp only [p195, p195_sum, Nat.cast_add, Nat.cast_one, pow_succ, pow_add]
    norm_num <;> ring
theorem p195_unique (a : ℕ → ℚ) (ha : SumRelationCertificate a ((5 : ℚ) / 2) (2 : ℚ) (fun n => (((2 : ℚ) * ((n : ℚ) + 1)) + ((-9 : ℚ) / 2)))) :
    ∀ n, a n = p195 n := sum_relation_unique p195_valid ha (by norm_num)
#print axioms p195_valid
#print axioms p195_unique

def p171 (n : ℕ) : ℚ := (((4 : ℚ) * ((2 : ℚ) ^ n)) + ((n : ℚ) + 1))
def p171_sum (n : ℕ) : ℚ := (((4 : ℚ) * (((2 : ℚ) ^ (n + 1)) + (-1 : ℚ))) + (((1 : ℚ) / 2) * ((((n : ℚ) + 1) + (1 : ℚ)) ^ 2)) + (((-1 : ℚ) / 2) * ((n : ℚ) + 1)) + ((-1 : ℚ) / 2))
theorem p171_prefix : ∀ n, prefix p171 n = p171_sum n := by
  intro n
  induction n with
  | zero => norm_num [prefix, p171, p171_sum]
  | succ n ih =>
    rw [prefix_succ, ih]
    simp only [p171, p171_sum, Nat.cast_add, Nat.cast_one, pow_succ, pow_add]
    norm_num <;> ring
theorem p171_valid : SumRelationCertificate p171 (5 : ℚ) (2 : ℚ) (fun n => ((((1 : ℚ) / 2) * (((n : ℚ) + 1) ^ 2)) + (((-3 : ℚ) / 2) * ((n : ℚ) + 1)) + (-4 : ℚ))) := by
  constructor
  · norm_num [p171]
  · intro n
    rw [p171_prefix]
    simp only [p171, p171_sum, Nat.cast_add, Nat.cast_one, pow_succ, pow_add]
    norm_num <;> ring
theorem p171_unique (a : ℕ → ℚ) (ha : SumRelationCertificate a (5 : ℚ) (2 : ℚ) (fun n => ((((1 : ℚ) / 2) * (((n : ℚ) + 1) ^ 2)) + (((-3 : ℚ) / 2) * ((n : ℚ) + 1)) + (-4 : ℚ)))) :
    ∀ n, a n = p171 n := sum_relation_unique p171_valid ha (by norm_num)
#print axioms p171_valid
#print axioms p171_unique

end Recurrence
