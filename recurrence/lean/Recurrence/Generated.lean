import Recurrence.Theory

namespace Recurrence

def p003 (n : ℕ) : ℚ := (3 : ℚ)
theorem p003_base_valid : FirstCertificate p003 (3 : ℚ) (fun n x => ((1 : ℚ) * x + (0 : ℚ)) / (1 : ℚ)) := by
  apply linear_certificate p003 (3 : ℚ) (fun n : ℕ => (1 : ℚ)) (fun n : ℕ => (1 : ℚ)) (fun n : ℕ => (0 : ℚ))
  · norm_num [p003]
  · intro n; positivity
  · intro n
    simp only [p003, Nat.cast_add, Nat.cast_one, pow_succ, pow_add] at *
    ring
theorem p003_valid : FirstCertificate p003 (3 : ℚ) (fun n x => ((1 : ℚ) * x + (0 : ℚ)) / (1 : ℚ)) := p003_base_valid
theorem p003_unique (a : ℕ → ℚ) (ha : FirstCertificate a (3 : ℚ) (fun n x => ((1 : ℚ) * x + (0 : ℚ)) / (1 : ℚ))) :
    ∀ n, a n = p003 n := first_unique p003_valid ha
#print axioms p003_valid
#print axioms p003_unique

def p005 (n : ℕ) : ℚ := (2 : ℚ)
theorem p005_base_valid : FirstCertificate p005 (2 : ℚ) (fun n x => ((1 : ℚ) * x + (0 : ℚ)) / (1 : ℚ)) := by
  apply linear_certificate p005 (2 : ℚ) (fun n : ℕ => (1 : ℚ)) (fun n : ℕ => (1 : ℚ)) (fun n : ℕ => (0 : ℚ))
  · norm_num [p005]
  · intro n; positivity
  · intro n
    simp only [p005, Nat.cast_add, Nat.cast_one, pow_succ, pow_add] at *
    ring
theorem p005_valid : FirstCertificate p005 (2 : ℚ) (fun n x => ((1 : ℚ) * x + (0 : ℚ)) / (1 : ℚ)) := p005_base_valid
theorem p005_unique (a : ℕ → ℚ) (ha : FirstCertificate a (2 : ℚ) (fun n x => ((1 : ℚ) * x + (0 : ℚ)) / (1 : ℚ))) :
    ∀ n, a n = p005 n := first_unique p005_valid ha
#print axioms p005_valid
#print axioms p005_unique

def p051 (n : ℕ) : ℚ := (8 : ℚ)
theorem p051_base_valid : FirstCertificate p051 (8 : ℚ) (fun n x => ((1 : ℚ) * x + (0 : ℚ)) / (1 : ℚ)) := by
  apply linear_certificate p051 (8 : ℚ) (fun n : ℕ => (1 : ℚ)) (fun n : ℕ => (1 : ℚ)) (fun n : ℕ => (0 : ℚ))
  · norm_num [p051]
  · intro n; positivity
  · intro n
    simp only [p051, Nat.cast_add, Nat.cast_one, pow_succ, pow_add] at *
    ring
theorem p051_valid : FirstCertificate p051 (8 : ℚ) (fun n x => ((1 : ℚ) * x + (0 : ℚ)) / (1 : ℚ)) := p051_base_valid
theorem p051_unique (a : ℕ → ℚ) (ha : FirstCertificate a (8 : ℚ) (fun n x => ((1 : ℚ) * x + (0 : ℚ)) / (1 : ℚ))) :
    ∀ n, a n = p051 n := first_unique p051_valid ha
#print axioms p051_valid
#print axioms p051_unique

def p052 (n : ℕ) : ℚ := (5 : ℚ)
theorem p052_base_valid : FirstCertificate p052 (5 : ℚ) (fun n x => ((1 : ℚ) * x + (0 : ℚ)) / (1 : ℚ)) := by
  apply linear_certificate p052 (5 : ℚ) (fun n : ℕ => (1 : ℚ)) (fun n : ℕ => (1 : ℚ)) (fun n : ℕ => (0 : ℚ))
  · norm_num [p052]
  · intro n; positivity
  · intro n
    simp only [p052, Nat.cast_add, Nat.cast_one, pow_succ, pow_add] at *
    ring
theorem p052_valid : FirstCertificate p052 (5 : ℚ) (fun n x => ((1 : ℚ) * x + (0 : ℚ)) / (1 : ℚ)) := p052_base_valid
theorem p052_unique (a : ℕ → ℚ) (ha : FirstCertificate a (5 : ℚ) (fun n x => ((1 : ℚ) * x + (0 : ℚ)) / (1 : ℚ))) :
    ∀ n, a n = p052 n := first_unique p052_valid ha
#print axioms p052_valid
#print axioms p052_unique

def p001 (n : ℕ) : ℚ := (4 : ℚ)
theorem p001_base_valid : FirstCertificate p001 (4 : ℚ) (fun n x => ((1 : ℚ) * x + (0 : ℚ)) / (1 : ℚ)) := by
  apply linear_certificate p001 (4 : ℚ) (fun n : ℕ => (1 : ℚ)) (fun n : ℕ => (1 : ℚ)) (fun n : ℕ => (0 : ℚ))
  · norm_num [p001]
  · intro n; positivity
  · intro n
    simp only [p001, Nat.cast_add, Nat.cast_one, pow_succ, pow_add] at *
    ring
theorem p001_valid : FirstCertificate p001 (4 : ℚ) (fun n x => ((1 : ℚ) * x + (0 : ℚ)) / (1 : ℚ)) := p001_base_valid
theorem p001_unique (a : ℕ → ℚ) (ha : FirstCertificate a (4 : ℚ) (fun n x => ((1 : ℚ) * x + (0 : ℚ)) / (1 : ℚ))) :
    ∀ n, a n = p001 n := first_unique p001_valid ha
#print axioms p001_valid
#print axioms p001_unique

def p010 (n : ℕ) : ℚ := ((3 : ℚ) * ((2 : ℚ) ^ n))
theorem p010_base_valid : FirstCertificate p010 (3 : ℚ) (fun n x => ((2 : ℚ) * x + (0 : ℚ)) / (1 : ℚ)) := by
  apply linear_certificate p010 (3 : ℚ) (fun n : ℕ => (1 : ℚ)) (fun n : ℕ => (2 : ℚ)) (fun n : ℕ => (0 : ℚ))
  · norm_num [p010]
  · intro n; positivity
  · intro n
    simp only [p010, Nat.cast_add, Nat.cast_one, pow_succ, pow_add] at *
    ring
theorem p010_valid : FirstCertificate p010 (3 : ℚ) (fun n x => ((2 : ℚ) * x + (0 : ℚ)) / (1 : ℚ)) := p010_base_valid
theorem p010_unique (a : ℕ → ℚ) (ha : FirstCertificate a (3 : ℚ) (fun n x => ((2 : ℚ) * x + (0 : ℚ)) / (1 : ℚ))) :
    ∀ n, a n = p010 n := first_unique p010_valid ha
#print axioms p010_valid
#print axioms p010_unique

def p053 (n : ℕ) : ℚ := ((8 : ℚ) * ((3 : ℚ) ^ n))
theorem p053_base_valid : FirstCertificate p053 (8 : ℚ) (fun n x => ((3 : ℚ) * x + (0 : ℚ)) / (1 : ℚ)) := by
  apply linear_certificate p053 (8 : ℚ) (fun n : ℕ => (1 : ℚ)) (fun n : ℕ => (3 : ℚ)) (fun n : ℕ => (0 : ℚ))
  · norm_num [p053]
  · intro n; positivity
  · intro n
    simp only [p053, Nat.cast_add, Nat.cast_one, pow_succ, pow_add] at *
    ring
theorem p053_valid : FirstCertificate p053 (8 : ℚ) (fun n x => ((3 : ℚ) * x + (0 : ℚ)) / (1 : ℚ)) := p053_base_valid
theorem p053_unique (a : ℕ → ℚ) (ha : FirstCertificate a (8 : ℚ) (fun n x => ((3 : ℚ) * x + (0 : ℚ)) / (1 : ℚ))) :
    ∀ n, a n = p053 n := first_unique p053_valid ha
#print axioms p053_valid
#print axioms p053_unique

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

def p055 (n : ℕ) : ℚ := ((5 : ℚ) * ((3 : ℚ) ^ n))
theorem p055_base_valid : FirstCertificate p055 (5 : ℚ) (fun n x => ((3 : ℚ) * x + (0 : ℚ)) / (1 : ℚ)) := by
  apply linear_certificate p055 (5 : ℚ) (fun n : ℕ => (1 : ℚ)) (fun n : ℕ => (3 : ℚ)) (fun n : ℕ => (0 : ℚ))
  · norm_num [p055]
  · intro n; positivity
  · intro n
    simp only [p055, Nat.cast_add, Nat.cast_one, pow_succ, pow_add] at *
    ring
theorem p055_valid : FirstCertificate p055 (5 : ℚ) (fun n x => ((3 : ℚ) * x + (0 : ℚ)) / (1 : ℚ)) := p055_base_valid
theorem p055_unique (a : ℕ → ℚ) (ha : FirstCertificate a (5 : ℚ) (fun n x => ((3 : ℚ) * x + (0 : ℚ)) / (1 : ℚ))) :
    ∀ n, a n = p055 n := first_unique p055_valid ha
#print axioms p055_valid
#print axioms p055_unique

def p056 (n : ℕ) : ℚ := ((8 : ℚ) * ((2 : ℚ) ^ n))
theorem p056_base_valid : FirstCertificate p056 (8 : ℚ) (fun n x => ((2 : ℚ) * x + (0 : ℚ)) / (1 : ℚ)) := by
  apply linear_certificate p056 (8 : ℚ) (fun n : ℕ => (1 : ℚ)) (fun n : ℕ => (2 : ℚ)) (fun n : ℕ => (0 : ℚ))
  · norm_num [p056]
  · intro n; positivity
  · intro n
    simp only [p056, Nat.cast_add, Nat.cast_one, pow_succ, pow_add] at *
    ring
theorem p056_valid : FirstCertificate p056 (8 : ℚ) (fun n x => ((2 : ℚ) * x + (0 : ℚ)) / (1 : ℚ)) := p056_base_valid
theorem p056_unique (a : ℕ → ℚ) (ha : FirstCertificate a (8 : ℚ) (fun n x => ((2 : ℚ) * x + (0 : ℚ)) / (1 : ℚ))) :
    ∀ n, a n = p056 n := first_unique p056_valid ha
#print axioms p056_valid
#print axioms p056_unique

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

def p059 (n : ℕ) : ℚ := (((8 : ℚ) * ((3 : ℚ) ^ n)) + (1 : ℚ))
theorem p059_base_valid : FirstCertificate p059 (9 : ℚ) (fun n x => ((3 : ℚ) * x + (-2 : ℚ)) / (1 : ℚ)) := by
  apply linear_certificate p059 (9 : ℚ) (fun n : ℕ => (1 : ℚ)) (fun n : ℕ => (3 : ℚ)) (fun n : ℕ => (-2 : ℚ))
  · norm_num [p059]
  · intro n; positivity
  · intro n
    simp only [p059, Nat.cast_add, Nat.cast_one, pow_succ, pow_add] at *
    ring
theorem p059_valid : FirstCertificate p059 (9 : ℚ) (fun n x => ((3 : ℚ) * x + (-2 : ℚ)) / (1 : ℚ)) := p059_base_valid
theorem p059_unique (a : ℕ → ℚ) (ha : FirstCertificate a (9 : ℚ) (fun n x => ((3 : ℚ) * x + (-2 : ℚ)) / (1 : ℚ))) :
    ∀ n, a n = p059 n := first_unique p059_valid ha
#print axioms p059_valid
#print axioms p059_unique

def p060 (n : ℕ) : ℚ := ((((1 : ℚ) / 2) * ((3 : ℚ) ^ n)) + (2 : ℚ))
theorem p060_base_valid : FirstCertificate p060 ((5 : ℚ) / 2) (fun n x => ((3 : ℚ) * x + (-4 : ℚ)) / (1 : ℚ)) := by
  apply linear_certificate p060 ((5 : ℚ) / 2) (fun n : ℕ => (1 : ℚ)) (fun n : ℕ => (3 : ℚ)) (fun n : ℕ => (-4 : ℚ))
  · norm_num [p060]
  · intro n; positivity
  · intro n
    simp only [p060, Nat.cast_add, Nat.cast_one, pow_succ, pow_add] at *
    ring
theorem p060_valid : FirstCertificate p060 ((5 : ℚ) / 2) (fun n x => ((3 : ℚ) * x + (-4 : ℚ)) / (1 : ℚ)) := p060_base_valid
theorem p060_unique (a : ℕ → ℚ) (ha : FirstCertificate a ((5 : ℚ) / 2) (fun n x => ((3 : ℚ) * x + (-4 : ℚ)) / (1 : ℚ))) :
    ∀ n, a n = p060 n := first_unique p060_valid ha
#print axioms p060_valid
#print axioms p060_unique

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

def p017 (n : ℕ) : ℚ := ((3 : ℚ) * ((n : ℚ) + 1) * (((n : ℚ) + 1) + (2 : ℚ)))
theorem p017_base_valid : FirstCertificate p017 (9 : ℚ) (fun n x => (((((n : ℚ) + 1) + (1 : ℚ)) * (((n : ℚ) + 1) + (3 : ℚ))) * x + (0 : ℚ)) / (((n : ℚ) + 1) * (((n : ℚ) + 1) + (2 : ℚ)))) := by
  apply linear_certificate p017 (9 : ℚ) (fun n : ℕ => (((n : ℚ) + 1) * (((n : ℚ) + 1) + (2 : ℚ)))) (fun n : ℕ => ((((n : ℚ) + 1) + (1 : ℚ)) * (((n : ℚ) + 1) + (3 : ℚ)))) (fun n : ℕ => (0 : ℚ))
  · norm_num [p017]
  · intro n; positivity
  · intro n
    simp only [p017, Nat.cast_add, Nat.cast_one, pow_succ, pow_add] at *
    ring
theorem p017_valid : FirstCertificate p017 (9 : ℚ) (fun n x => (((((n : ℚ) + 1) + (1 : ℚ)) * (((n : ℚ) + 1) + (3 : ℚ))) * x + (0 : ℚ)) / (((n : ℚ) + 1) * (((n : ℚ) + 1) + (2 : ℚ)))) := p017_base_valid
theorem p017_unique (a : ℕ → ℚ) (ha : FirstCertificate a (9 : ℚ) (fun n x => (((((n : ℚ) + 1) + (1 : ℚ)) * (((n : ℚ) + 1) + (3 : ℚ))) * x + (0 : ℚ)) / (((n : ℚ) + 1) * (((n : ℚ) + 1) + (2 : ℚ))))) :
    ∀ n, a n = p017 n := first_unique p017_valid ha
#print axioms p017_valid
#print axioms p017_unique

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

def p079 (n : ℕ) : ℚ := (((n : ℚ) + 1) * (((3 : ℚ) * ((2 : ℚ) ^ n)) + (2 : ℚ)))
theorem p079_base_valid : FirstCertificate p079 (5 : ℚ) (fun n x => (((2 : ℚ) * (((n : ℚ) + 1) + (1 : ℚ))) * x + ((-2 : ℚ) * ((n : ℚ) + 1) * (((n : ℚ) + 1) + (1 : ℚ)))) / ((n : ℚ) + 1)) := by
  apply linear_certificate p079 (5 : ℚ) (fun n : ℕ => ((n : ℚ) + 1)) (fun n : ℕ => ((2 : ℚ) * (((n : ℚ) + 1) + (1 : ℚ)))) (fun n : ℕ => ((-2 : ℚ) * ((n : ℚ) + 1) * (((n : ℚ) + 1) + (1 : ℚ))))
  · norm_num [p079]
  · intro n; positivity
  · intro n
    simp only [p079, Nat.cast_add, Nat.cast_one, pow_succ, pow_add] at *
    ring
theorem p079_valid : FirstCertificate p079 (5 : ℚ) (fun n x => (((2 : ℚ) * (((n : ℚ) + 1) + (1 : ℚ))) * x + ((-2 : ℚ) * ((n : ℚ) + 1) * (((n : ℚ) + 1) + (1 : ℚ)))) / ((n : ℚ) + 1)) := p079_base_valid
theorem p079_unique (a : ℕ → ℚ) (ha : FirstCertificate a (5 : ℚ) (fun n x => (((2 : ℚ) * (((n : ℚ) + 1) + (1 : ℚ))) * x + ((-2 : ℚ) * ((n : ℚ) + 1) * (((n : ℚ) + 1) + (1 : ℚ)))) / ((n : ℚ) + 1))) :
    ∀ n, a n = p079 n := first_unique p079_valid ha
#print axioms p079_valid
#print axioms p079_unique

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

def p081 (n : ℕ) : ℚ := ((((8 : ℚ) * ((2 : ℚ) ^ n)) + (1 : ℚ)) / (((n : ℚ) + 1) * (((n : ℚ) + 1) + (1 : ℚ))))
theorem p081_base_valid : FirstCertificate p081 ((9 : ℚ) / 2) (fun n x => (((2 : ℚ) * ((n : ℚ) + 1) * (((n : ℚ) + 1) + (1 : ℚ))) * x + (-1 : ℚ)) / ((((n : ℚ) + 1) + (1 : ℚ)) * (((n : ℚ) + 1) + (2 : ℚ)))) := by
  apply linear_certificate p081 ((9 : ℚ) / 2) (fun n : ℕ => ((((n : ℚ) + 1) + (1 : ℚ)) * (((n : ℚ) + 1) + (2 : ℚ)))) (fun n : ℕ => ((2 : ℚ) * ((n : ℚ) + 1) * (((n : ℚ) + 1) + (1 : ℚ)))) (fun n : ℕ => (-1 : ℚ))
  · norm_num [p081]
  · intro n; positivity
  · intro n
    have hd0 : (((n : ℚ) + 1) * (((n : ℚ) + 1) + (1 : ℚ))) ≠ 0 := by positivity
    have he0 : ((((n + 1) : ℚ) + 1) * ((((n + 1) : ℚ) + 1) + (1 : ℚ))) ≠ 0 := by positivity
    simp only [p081, Nat.cast_add, Nat.cast_one, pow_succ, pow_add] at *
    field_simp [hd0, he0] <;> ring
theorem p081_valid : FirstCertificate p081 ((9 : ℚ) / 2) (fun n x => (((2 : ℚ) * ((n : ℚ) + 1) * (((n : ℚ) + 1) + (1 : ℚ))) * x + (-1 : ℚ)) / ((((n : ℚ) + 1) + (1 : ℚ)) * (((n : ℚ) + 1) + (2 : ℚ)))) := p081_base_valid
theorem p081_unique (a : ℕ → ℚ) (ha : FirstCertificate a ((9 : ℚ) / 2) (fun n x => (((2 : ℚ) * ((n : ℚ) + 1) * (((n : ℚ) + 1) + (1 : ℚ))) * x + (-1 : ℚ)) / ((((n : ℚ) + 1) + (1 : ℚ)) * (((n : ℚ) + 1) + (2 : ℚ))))) :
    ∀ n, a n = p081 n := first_unique p081_valid ha
#print axioms p081_valid
#print axioms p081_unique

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

def p083 (n : ℕ) : ℚ := ((((8 : ℚ) * ((2 : ℚ) ^ n)) + (1 : ℚ)) / (((n : ℚ) + 1) ^ 2))
theorem p083_base_valid : FirstCertificate p083 (9 : ℚ) (fun n x => (((2 : ℚ) * (((n : ℚ) + 1) ^ 2)) * x + (-1 : ℚ)) / ((((n : ℚ) + 1) + (1 : ℚ)) ^ 2)) := by
  apply linear_certificate p083 (9 : ℚ) (fun n : ℕ => ((((n : ℚ) + 1) + (1 : ℚ)) ^ 2)) (fun n : ℕ => ((2 : ℚ) * (((n : ℚ) + 1) ^ 2))) (fun n : ℕ => (-1 : ℚ))
  · norm_num [p083]
  · intro n; positivity
  · intro n
    have hd0 : (((n : ℚ) + 1) ^ 2) ≠ 0 := by positivity
    have he0 : ((((n + 1) : ℚ) + 1) ^ 2) ≠ 0 := by positivity
    simp only [p083, Nat.cast_add, Nat.cast_one, pow_succ, pow_add] at *
    field_simp [hd0, he0] <;> ring
theorem p083_valid : FirstCertificate p083 (9 : ℚ) (fun n x => (((2 : ℚ) * (((n : ℚ) + 1) ^ 2)) * x + (-1 : ℚ)) / ((((n : ℚ) + 1) + (1 : ℚ)) ^ 2)) := p083_base_valid
theorem p083_unique (a : ℕ → ℚ) (ha : FirstCertificate a (9 : ℚ) (fun n x => (((2 : ℚ) * (((n : ℚ) + 1) ^ 2)) * x + (-1 : ℚ)) / ((((n : ℚ) + 1) + (1 : ℚ)) ^ 2))) :
    ∀ n, a n = p083 n := first_unique p083_valid ha
#print axioms p083_valid
#print axioms p083_unique

def p034 (n : ℕ) : ℚ := (((3 : ℚ) * ((2 : ℚ) ^ n)) + ((3 : ℚ) ^ n))
theorem p034_valid : SecondCertificate p034 (4 : ℚ) (9 : ℚ) (5 : ℚ) (-6 : ℚ) := by
  constructor
  · norm_num [p034]
  · norm_num [p034]
  · intro n
    simp only [p034, pow_succ, pow_add] <;> ring
theorem p034_unique (a : ℕ → ℚ) (ha : SecondCertificate a (4 : ℚ) (9 : ℚ) (5 : ℚ) (-6 : ℚ)) :
    ∀ n, a n = p034 n := second_unique p034_valid ha
#print axioms p034_valid
#print axioms p034_unique

def p084 (n : ℕ) : ℚ := (((4 : ℚ) * ((2 : ℚ) ^ n)) + ((2 : ℚ) * ((4 : ℚ) ^ n)))
theorem p084_valid : SecondCertificate p084 (6 : ℚ) (16 : ℚ) (6 : ℚ) (-8 : ℚ) := by
  constructor
  · norm_num [p084]
  · norm_num [p084]
  · intro n
    simp only [p084, pow_succ, pow_add] <;> ring
theorem p084_unique (a : ℕ → ℚ) (ha : SecondCertificate a (6 : ℚ) (16 : ℚ) (6 : ℚ) (-8 : ℚ)) :
    ∀ n, a n = p084 n := second_unique p084_valid ha
#print axioms p084_valid
#print axioms p084_unique

def p085 (n : ℕ) : ℚ := (((3 : ℚ) ^ n) + ((4 : ℚ) ^ n))
theorem p085_valid : SecondCertificate p085 (2 : ℚ) (7 : ℚ) (7 : ℚ) (-12 : ℚ) := by
  constructor
  · norm_num [p085]
  · norm_num [p085]
  · intro n
    simp only [p085, pow_succ, pow_add] <;> ring
theorem p085_unique (a : ℕ → ℚ) (ha : SecondCertificate a (2 : ℚ) (7 : ℚ) (7 : ℚ) (-12 : ℚ)) :
    ∀ n, a n = p085 n := second_unique p085_valid ha
#print axioms p085_valid
#print axioms p085_unique

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

def p033 (n : ℕ) : ℚ := ((((1 : ℚ) / 2) * ((2 : ℚ) ^ n)) + ((4 : ℚ) ^ n))
theorem p033_valid : SecondCertificate p033 ((3 : ℚ) / 2) (5 : ℚ) (6 : ℚ) (-8 : ℚ) := by
  constructor
  · norm_num [p033]
  · norm_num [p033]
  · intro n
    simp only [p033, pow_succ, pow_add] <;> ring
theorem p033_unique (a : ℕ → ℚ) (ha : SecondCertificate a ((3 : ℚ) / 2) (5 : ℚ) (6 : ℚ) (-8 : ℚ)) :
    ∀ n, a n = p033 n := second_unique p033_valid ha
#print axioms p033_valid
#print axioms p033_unique

def p087 (n : ℕ) : ℚ := ((3 : ℚ) * ((2 : ℚ) ^ (n * (n + 2))))
theorem p087_base_valid : FirstCertificate p087 (3 : ℚ) (fun n x => (((2 : ℚ) ^ ((2 * (n + 1)) + 1)) * x + (0 : ℚ)) / (1 : ℚ)) := by
  apply linear_certificate p087 (3 : ℚ) (fun n : ℕ => (1 : ℚ)) (fun n : ℕ => ((2 : ℚ) ^ ((2 * (n + 1)) + 1))) (fun n : ℕ => (0 : ℚ))
  · norm_num [p087]
  · intro n; positivity
  · intro n
    have he : (n + 1) * (n + 3) = n * (n + 2) + (2 * (n + 1) + 1) := by ring
    simp only [p087, Nat.add_assoc]
    rw [he]
    simp only [pow_add] <;> ring
theorem p087_valid : FirstCertificate p087 (3 : ℚ) (fun n x => (((2 : ℚ) ^ ((2 * (n + 1)) + 1)) * x + (0 : ℚ)) / (1 : ℚ)) := p087_base_valid
theorem p087_unique (a : ℕ → ℚ) (ha : FirstCertificate a (3 : ℚ) (fun n x => (((2 : ℚ) ^ ((2 * (n + 1)) + 1)) * x + (0 : ℚ)) / (1 : ℚ))) :
    ∀ n, a n = p087 n := first_unique p087_valid ha
#print axioms p087_valid
#print axioms p087_unique

def p040 (n : ℕ) : ℚ := ((3 : ℚ) * ((2 : ℚ) ^ ((n + 1).choose 2)))
theorem p040_base_valid : FirstCertificate p040 (3 : ℚ) (fun n x => (((2 : ℚ) ^ (n + 1)) * x + (0 : ℚ)) / (1 : ℚ)) := by
  apply linear_certificate p040 (3 : ℚ) (fun n : ℕ => (1 : ℚ)) (fun n : ℕ => ((2 : ℚ) ^ (n + 1))) (fun n : ℕ => (0 : ℚ))
  · norm_num [p040]
  · intro n; positivity
  · intro n
    have he : (n + 2).choose 2 = (n + 1).choose 2 + (n + 1) := by
      have hs := Nat.choose_succ_succ (n + 1) 1
      simp only [Nat.add_assoc, Nat.choose_one_right] at hs
      omega
    simp only [p040, Nat.add_assoc]
    rw [he]
    simp only [pow_add] <;> ring
theorem p040_valid : FirstCertificate p040 (3 : ℚ) (fun n x => (((2 : ℚ) ^ (n + 1)) * x + (0 : ℚ)) / (1 : ℚ)) := p040_base_valid
theorem p040_unique (a : ℕ → ℚ) (ha : FirstCertificate a (3 : ℚ) (fun n x => (((2 : ℚ) ^ (n + 1)) * x + (0 : ℚ)) / (1 : ℚ))) :
    ∀ n, a n = p040 n := first_unique p040_valid ha
#print axioms p040_valid
#print axioms p040_unique

def p088 (n : ℕ) : ℚ := ((3 : ℚ) * ((2 : ℚ) ^ ((n + 2)).choose 3))
theorem p088_base_valid : FirstCertificate p088 (3 : ℚ) (fun n x => (((2 : ℚ) ^ ((n + 2)).choose 2) * x + (0 : ℚ)) / (1 : ℚ)) := by
  apply linear_certificate p088 (3 : ℚ) (fun n : ℕ => (1 : ℚ)) (fun n : ℕ => ((2 : ℚ) ^ ((n + 2)).choose 2)) (fun n : ℕ => (0 : ℚ))
  · norm_num [p088]
  · intro n; positivity
  · intro n
    have he : (n + 3).choose 3 = (n + 2).choose 3 + (n + 2).choose 2 := by
      have hs := Nat.choose_succ_succ (n + 2) 2
      simp only [Nat.add_assoc] at hs
      omega
    simp only [p088, Nat.add_assoc]
    rw [he]
    simp only [pow_add] <;> ring
theorem p088_valid : FirstCertificate p088 (3 : ℚ) (fun n x => (((2 : ℚ) ^ ((n + 2)).choose 2) * x + (0 : ℚ)) / (1 : ℚ)) := p088_base_valid
theorem p088_unique (a : ℕ → ℚ) (ha : FirstCertificate a (3 : ℚ) (fun n x => (((2 : ℚ) ^ ((n + 2)).choose 2) * x + (0 : ℚ)) / (1 : ℚ))) :
    ∀ n, a n = p088 n := first_unique p088_valid ha
#print axioms p088_valid
#print axioms p088_unique

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

def p090 (n : ℕ) : ℚ := ((2 : ℚ) * ((2 : ℚ) ^ ((n + 1).choose 2)))
theorem p090_base_valid : FirstCertificate p090 (2 : ℚ) (fun n x => (((2 : ℚ) ^ (n + 1)) * x + (0 : ℚ)) / (1 : ℚ)) := by
  apply linear_certificate p090 (2 : ℚ) (fun n : ℕ => (1 : ℚ)) (fun n : ℕ => ((2 : ℚ) ^ (n + 1))) (fun n : ℕ => (0 : ℚ))
  · norm_num [p090]
  · intro n; positivity
  · intro n
    have he : (n + 2).choose 2 = (n + 1).choose 2 + (n + 1) := by
      have hs := Nat.choose_succ_succ (n + 1) 1
      simp only [Nat.add_assoc, Nat.choose_one_right] at hs
      omega
    simp only [p090, Nat.add_assoc]
    rw [he]
    simp only [pow_add] <;> ring
theorem p090_valid : FirstCertificate p090 (2 : ℚ) (fun n x => (((2 : ℚ) ^ (n + 1)) * x + (0 : ℚ)) / (1 : ℚ)) := p090_base_valid
theorem p090_unique (a : ℕ → ℚ) (ha : FirstCertificate a (2 : ℚ) (fun n x => (((2 : ℚ) ^ (n + 1)) * x + (0 : ℚ)) / (1 : ℚ))) :
    ∀ n, a n = p090 n := first_unique p090_valid ha
#print axioms p090_valid
#print axioms p090_unique

def p091 (n : ℕ) : ℚ := ((2 : ℚ) * ((2 : ℚ) ^ ((n + 2)).choose 3))
theorem p091_base_valid : FirstCertificate p091 (2 : ℚ) (fun n x => (((2 : ℚ) ^ ((n + 2)).choose 2) * x + (0 : ℚ)) / (1 : ℚ)) := by
  apply linear_certificate p091 (2 : ℚ) (fun n : ℕ => (1 : ℚ)) (fun n : ℕ => ((2 : ℚ) ^ ((n + 2)).choose 2)) (fun n : ℕ => (0 : ℚ))
  · norm_num [p091]
  · intro n; positivity
  · intro n
    have he : (n + 3).choose 3 = (n + 2).choose 3 + (n + 2).choose 2 := by
      have hs := Nat.choose_succ_succ (n + 2) 2
      simp only [Nat.add_assoc] at hs
      omega
    simp only [p091, Nat.add_assoc]
    rw [he]
    simp only [pow_add] <;> ring
theorem p091_valid : FirstCertificate p091 (2 : ℚ) (fun n x => (((2 : ℚ) ^ ((n + 2)).choose 2) * x + (0 : ℚ)) / (1 : ℚ)) := p091_base_valid
theorem p091_unique (a : ℕ → ℚ) (ha : FirstCertificate a (2 : ℚ) (fun n x => (((2 : ℚ) ^ ((n + 2)).choose 2) * x + (0 : ℚ)) / (1 : ℚ))) :
    ∀ n, a n = p091 n := first_unique p091_valid ha
#print axioms p091_valid
#print axioms p091_unique

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

def p092 (n : ℕ) : ℚ := ((1 : ℚ) / (((8 : ℚ) * ((3 : ℚ) ^ n)) + (1 : ℚ)))
def p092_base (n : ℕ) : ℚ := (((8 : ℚ) * ((3 : ℚ) ^ n)) + (1 : ℚ))
theorem p092_base_valid : FirstCertificate p092_base (9 : ℚ) (fun n x => ((3 : ℚ) * x + (-2 : ℚ)) / (1 : ℚ)) := by
  apply linear_certificate p092_base (9 : ℚ) (fun n : ℕ => (1 : ℚ)) (fun n : ℕ => (3 : ℚ)) (fun n : ℕ => (-2 : ℚ))
  · norm_num [p092_base]
  · intro n; positivity
  · intro n
    simp only [p092_base, Nat.cast_add, Nat.cast_one, pow_succ, pow_add] at *
    ring
theorem p092_positive (n : ℕ) : 0 < p092_base n := by
  unfold p092_base
  positivity
theorem p092_valid : FirstCertificate p092 ((1 : ℚ) / 9) (fun n x => (1 : ℚ) * x / ((3 : ℚ) + (-2 : ℚ) * x)) := by
  have h := reciprocal_certificate p092_base_valid p092_positive (by intro n; positivity)
  have heq : p092 = (fun n => 1 / p092_base n) := by
    funext n
    simp [p092, p092_base, div_eq_mul_inv] <;> ring
  rw [heq]
  convert h.1 using 1 <;> norm_num
theorem p092_domain : (∀ n : ℕ, (3 : ℚ) + (-2 : ℚ) * p092 n ≠ 0) ∧ (∀ n, p092 n ≠ 0) := by
  have h := reciprocal_certificate p092_base_valid p092_positive (by intro n; positivity)
  simpa [p092, p092_base, div_eq_mul_inv] using h.2
#print axioms p092_domain
theorem p092_unique (a : ℕ → ℚ) (ha : FirstCertificate a ((1 : ℚ) / 9) (fun n x => (1 : ℚ) * x / ((3 : ℚ) + (-2 : ℚ) * x))) :
    ∀ n, a n = p092 n := first_unique p092_valid ha
#print axioms p092_valid
#print axioms p092_unique

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

def p094 (n : ℕ) : ℚ := ((1 : ℚ) / (((2 : ℚ) * ((3 : ℚ) ^ n)) + (2 : ℚ)))
def p094_base (n : ℕ) : ℚ := (((2 : ℚ) * ((3 : ℚ) ^ n)) + (2 : ℚ))
theorem p094_base_valid : FirstCertificate p094_base (4 : ℚ) (fun n x => ((3 : ℚ) * x + (-4 : ℚ)) / (1 : ℚ)) := by
  apply linear_certificate p094_base (4 : ℚ) (fun n : ℕ => (1 : ℚ)) (fun n : ℕ => (3 : ℚ)) (fun n : ℕ => (-4 : ℚ))
  · norm_num [p094_base]
  · intro n; positivity
  · intro n
    simp only [p094_base, Nat.cast_add, Nat.cast_one, pow_succ, pow_add] at *
    ring
theorem p094_positive (n : ℕ) : 0 < p094_base n := by
  unfold p094_base
  positivity
theorem p094_valid : FirstCertificate p094 ((1 : ℚ) / 4) (fun n x => (1 : ℚ) * x / ((3 : ℚ) + (-4 : ℚ) * x)) := by
  have h := reciprocal_certificate p094_base_valid p094_positive (by intro n; positivity)
  have heq : p094 = (fun n => 1 / p094_base n) := by
    funext n
    simp [p094, p094_base, div_eq_mul_inv] <;> ring
  rw [heq]
  convert h.1 using 1 <;> norm_num
theorem p094_domain : (∀ n : ℕ, (3 : ℚ) + (-4 : ℚ) * p094 n ≠ 0) ∧ (∀ n, p094 n ≠ 0) := by
  have h := reciprocal_certificate p094_base_valid p094_positive (by intro n; positivity)
  simpa [p094, p094_base, div_eq_mul_inv] using h.2
#print axioms p094_domain
theorem p094_unique (a : ℕ → ℚ) (ha : FirstCertificate a ((1 : ℚ) / 4) (fun n x => (1 : ℚ) * x / ((3 : ℚ) + (-4 : ℚ) * x))) :
    ∀ n, a n = p094 n := first_unique p094_valid ha
#print axioms p094_valid
#print axioms p094_unique

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

def p097 (n : ℕ) : ℚ := ((((n : ℚ) + 1) + (1 : ℚ)) / (((3 : ℚ) * ((2 : ℚ) ^ n)) + (2 : ℚ)))
def p097_base (n : ℕ) : ℚ := ((((3 : ℚ) * ((2 : ℚ) ^ n)) + (2 : ℚ)) / (((n : ℚ) + 1) + (1 : ℚ)))
theorem p097_base_valid : FirstCertificate p097_base ((5 : ℚ) / 2) (fun n x => (((2 : ℚ) * (((n : ℚ) + 1) + (1 : ℚ))) * x + (-2 : ℚ)) / (((n : ℚ) + 1) + (2 : ℚ))) := by
  apply linear_certificate p097_base ((5 : ℚ) / 2) (fun n : ℕ => (((n : ℚ) + 1) + (2 : ℚ))) (fun n : ℕ => ((2 : ℚ) * (((n : ℚ) + 1) + (1 : ℚ)))) (fun n : ℕ => (-2 : ℚ))
  · norm_num [p097_base]
  · intro n; positivity
  · intro n
    have hd0 : (((n : ℚ) + 1) + (1 : ℚ)) ≠ 0 := by positivity
    have he0 : ((((n + 1) : ℚ) + 1) + (1 : ℚ)) ≠ 0 := by positivity
    simp only [p097_base, Nat.cast_add, Nat.cast_one, pow_succ, pow_add] at *
    field_simp [hd0, he0] <;> ring
theorem p097_positive (n : ℕ) : 0 < p097_base n := by
  unfold p097_base
  positivity
theorem p097_valid : FirstCertificate p097 ((2 : ℚ) / 5) (fun n x => (((n : ℚ) + 1) + (2 : ℚ)) * x / (((2 : ℚ) * (((n : ℚ) + 1) + (1 : ℚ))) + (-2 : ℚ) * x)) := by
  have h := reciprocal_certificate p097_base_valid p097_positive (by intro n; positivity)
  have heq : p097 = (fun n => 1 / p097_base n) := by
    funext n
    simp [p097, p097_base, div_eq_mul_inv] <;> ring
  rw [heq]
  convert h.1 using 1 <;> norm_num
theorem p097_domain : (∀ n : ℕ, ((2 : ℚ) * (((n : ℚ) + 1) + (1 : ℚ))) + (-2 : ℚ) * p097 n ≠ 0) ∧ (∀ n, p097 n ≠ 0) := by
  have h := reciprocal_certificate p097_base_valid p097_positive (by intro n; positivity)
  simpa [p097, p097_base, div_eq_mul_inv] using h.2
#print axioms p097_domain
theorem p097_unique (a : ℕ → ℚ) (ha : FirstCertificate a ((2 : ℚ) / 5) (fun n x => (((n : ℚ) + 1) + (2 : ℚ)) * x / (((2 : ℚ) * (((n : ℚ) + 1) + (1 : ℚ))) + (-2 : ℚ) * x))) :
    ∀ n, a n = p097 n := first_unique p097_valid ha
#print axioms p097_valid
#print axioms p097_unique

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

def p099 (n : ℕ) : ℚ := ((((n : ℚ) + 1) ^ 2) / (((3 : ℚ) * ((2 : ℚ) ^ n)) + (2 : ℚ)))
def p099_base (n : ℕ) : ℚ := ((((3 : ℚ) * ((2 : ℚ) ^ n)) + (2 : ℚ)) / (((n : ℚ) + 1) ^ 2))
theorem p099_base_valid : FirstCertificate p099_base (5 : ℚ) (fun n x => (((2 : ℚ) * (((n : ℚ) + 1) ^ 2)) * x + (-2 : ℚ)) / ((((n : ℚ) + 1) + (1 : ℚ)) ^ 2)) := by
  apply linear_certificate p099_base (5 : ℚ) (fun n : ℕ => ((((n : ℚ) + 1) + (1 : ℚ)) ^ 2)) (fun n : ℕ => ((2 : ℚ) * (((n : ℚ) + 1) ^ 2))) (fun n : ℕ => (-2 : ℚ))
  · norm_num [p099_base]
  · intro n; positivity
  · intro n
    have hd0 : (((n : ℚ) + 1) ^ 2) ≠ 0 := by positivity
    have he0 : ((((n + 1) : ℚ) + 1) ^ 2) ≠ 0 := by positivity
    simp only [p099_base, Nat.cast_add, Nat.cast_one, pow_succ, pow_add] at *
    field_simp [hd0, he0] <;> ring
theorem p099_positive (n : ℕ) : 0 < p099_base n := by
  unfold p099_base
  positivity
theorem p099_valid : FirstCertificate p099 ((1 : ℚ) / 5) (fun n x => ((((n : ℚ) + 1) + (1 : ℚ)) ^ 2) * x / (((2 : ℚ) * (((n : ℚ) + 1) ^ 2)) + (-2 : ℚ) * x)) := by
  have h := reciprocal_certificate p099_base_valid p099_positive (by intro n; positivity)
  have heq : p099 = (fun n => 1 / p099_base n) := by
    funext n
    simp [p099, p099_base, div_eq_mul_inv] <;> ring
  rw [heq]
  convert h.1 using 1 <;> norm_num
theorem p099_domain : (∀ n : ℕ, ((2 : ℚ) * (((n : ℚ) + 1) ^ 2)) + (-2 : ℚ) * p099 n ≠ 0) ∧ (∀ n, p099 n ≠ 0) := by
  have h := reciprocal_certificate p099_base_valid p099_positive (by intro n; positivity)
  simpa [p099, p099_base, div_eq_mul_inv] using h.2
#print axioms p099_domain
theorem p099_unique (a : ℕ → ℚ) (ha : FirstCertificate a ((1 : ℚ) / 5) (fun n x => ((((n : ℚ) + 1) + (1 : ℚ)) ^ 2) * x / (((2 : ℚ) * (((n : ℚ) + 1) ^ 2)) + (-2 : ℚ) * x))) :
    ∀ n, a n = p099 n := first_unique p099_valid ha
#print axioms p099_valid
#print axioms p099_unique

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

end Recurrence
