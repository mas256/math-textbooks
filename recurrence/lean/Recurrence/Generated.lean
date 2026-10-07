import Recurrence.Theory

namespace Recurrence

def p001 (n : ℕ) : ℚ := (4 : ℚ)
theorem p001_base_valid : FirstCertificate p001 (4 : ℚ) (fun n x => ((1 : ℚ) * x + (0 : ℚ)) / (1 : ℚ)) := by
  apply linear_certificate p001 (4 : ℚ) (fun n : ℕ => (1 : ℚ)) (fun n : ℕ => (1 : ℚ)) (fun n : ℕ => (0 : ℚ))
  · norm_num [p001]
  · intro n; positivity
  · intro n
    simp only [p001, Nat.cast_add, Nat.cast_one, pow_succ, Nat.choose_succ_succ, Nat.choose_one_right, pow_add]
    ring
theorem p001_valid : FirstCertificate p001 (4 : ℚ) (fun n x => ((1 : ℚ) * x + (0 : ℚ)) / (1 : ℚ)) := p001_base_valid
theorem p001_unique (a : ℕ → ℚ) (ha : FirstCertificate a (4 : ℚ) (fun n x => ((1 : ℚ) * x + (0 : ℚ)) / (1 : ℚ))) :
    ∀ n, a n = p001 n := first_unique p001_valid ha
#print axioms p001_valid
#print axioms p001_unique

def p002 (n : ℕ) : ℚ := (1 : ℚ)
theorem p002_base_valid : FirstCertificate p002 (1 : ℚ) (fun n x => ((1 : ℚ) * x + (0 : ℚ)) / (1 : ℚ)) := by
  apply linear_certificate p002 (1 : ℚ) (fun n : ℕ => (1 : ℚ)) (fun n : ℕ => (1 : ℚ)) (fun n : ℕ => (0 : ℚ))
  · norm_num [p002]
  · intro n; positivity
  · intro n
    simp only [p002, Nat.cast_add, Nat.cast_one, pow_succ, Nat.choose_succ_succ, Nat.choose_one_right, pow_add]
    ring
theorem p002_valid : FirstCertificate p002 (1 : ℚ) (fun n x => ((1 : ℚ) * x + (0 : ℚ)) / (1 : ℚ)) := p002_base_valid
theorem p002_unique (a : ℕ → ℚ) (ha : FirstCertificate a (1 : ℚ) (fun n x => ((1 : ℚ) * x + (0 : ℚ)) / (1 : ℚ))) :
    ∀ n, a n = p002 n := first_unique p002_valid ha
#print axioms p002_valid
#print axioms p002_unique

def p003 (n : ℕ) : ℚ := (3 : ℚ)
theorem p003_base_valid : FirstCertificate p003 (3 : ℚ) (fun n x => ((1 : ℚ) * x + (0 : ℚ)) / (1 : ℚ)) := by
  apply linear_certificate p003 (3 : ℚ) (fun n : ℕ => (1 : ℚ)) (fun n : ℕ => (1 : ℚ)) (fun n : ℕ => (0 : ℚ))
  · norm_num [p003]
  · intro n; positivity
  · intro n
    simp only [p003, Nat.cast_add, Nat.cast_one, pow_succ, Nat.choose_succ_succ, Nat.choose_one_right, pow_add]
    ring
theorem p003_valid : FirstCertificate p003 (3 : ℚ) (fun n x => ((1 : ℚ) * x + (0 : ℚ)) / (1 : ℚ)) := p003_base_valid
theorem p003_unique (a : ℕ → ℚ) (ha : FirstCertificate a (3 : ℚ) (fun n x => ((1 : ℚ) * x + (0 : ℚ)) / (1 : ℚ))) :
    ∀ n, a n = p003 n := first_unique p003_valid ha
#print axioms p003_valid
#print axioms p003_unique

def p004 (n : ℕ) : ℚ := ((1 : ℚ) / 2)
theorem p004_base_valid : FirstCertificate p004 ((1 : ℚ) / 2) (fun n x => ((1 : ℚ) * x + (0 : ℚ)) / (1 : ℚ)) := by
  apply linear_certificate p004 ((1 : ℚ) / 2) (fun n : ℕ => (1 : ℚ)) (fun n : ℕ => (1 : ℚ)) (fun n : ℕ => (0 : ℚ))
  · norm_num [p004]
  · intro n; positivity
  · intro n
    simp only [p004, Nat.cast_add, Nat.cast_one, pow_succ, Nat.choose_succ_succ, Nat.choose_one_right, pow_add]
    ring
theorem p004_valid : FirstCertificate p004 ((1 : ℚ) / 2) (fun n x => ((1 : ℚ) * x + (0 : ℚ)) / (1 : ℚ)) := p004_base_valid
theorem p004_unique (a : ℕ → ℚ) (ha : FirstCertificate a ((1 : ℚ) / 2) (fun n x => ((1 : ℚ) * x + (0 : ℚ)) / (1 : ℚ))) :
    ∀ n, a n = p004 n := first_unique p004_valid ha
#print axioms p004_valid
#print axioms p004_unique

def p005 (n : ℕ) : ℚ := (2 : ℚ)
theorem p005_base_valid : FirstCertificate p005 (2 : ℚ) (fun n x => ((1 : ℚ) * x + (0 : ℚ)) / (1 : ℚ)) := by
  apply linear_certificate p005 (2 : ℚ) (fun n : ℕ => (1 : ℚ)) (fun n : ℕ => (1 : ℚ)) (fun n : ℕ => (0 : ℚ))
  · norm_num [p005]
  · intro n; positivity
  · intro n
    simp only [p005, Nat.cast_add, Nat.cast_one, pow_succ, Nat.choose_succ_succ, Nat.choose_one_right, pow_add]
    ring
theorem p005_valid : FirstCertificate p005 (2 : ℚ) (fun n x => ((1 : ℚ) * x + (0 : ℚ)) / (1 : ℚ)) := p005_base_valid
theorem p005_unique (a : ℕ → ℚ) (ha : FirstCertificate a (2 : ℚ) (fun n x => ((1 : ℚ) * x + (0 : ℚ)) / (1 : ℚ))) :
    ∀ n, a n = p005 n := first_unique p005_valid ha
#print axioms p005_valid
#print axioms p005_unique

def p006 (n : ℕ) : ℚ := ((4 : ℚ) * ((3 : ℚ) ^ n))
theorem p006_base_valid : FirstCertificate p006 (4 : ℚ) (fun n x => ((3 : ℚ) * x + (0 : ℚ)) / (1 : ℚ)) := by
  apply linear_certificate p006 (4 : ℚ) (fun n : ℕ => (1 : ℚ)) (fun n : ℕ => (3 : ℚ)) (fun n : ℕ => (0 : ℚ))
  · norm_num [p006]
  · intro n; positivity
  · intro n
    simp only [p006, Nat.cast_add, Nat.cast_one, pow_succ, Nat.choose_succ_succ, Nat.choose_one_right, pow_add]
    ring
theorem p006_valid : FirstCertificate p006 (4 : ℚ) (fun n x => ((3 : ℚ) * x + (0 : ℚ)) / (1 : ℚ)) := p006_base_valid
theorem p006_unique (a : ℕ → ℚ) (ha : FirstCertificate a (4 : ℚ) (fun n x => ((3 : ℚ) * x + (0 : ℚ)) / (1 : ℚ))) :
    ∀ n, a n = p006 n := first_unique p006_valid ha
#print axioms p006_valid
#print axioms p006_unique

def p007 (n : ℕ) : ℚ := ((3 : ℚ) ^ n)
theorem p007_base_valid : FirstCertificate p007 (1 : ℚ) (fun n x => ((3 : ℚ) * x + (0 : ℚ)) / (1 : ℚ)) := by
  apply linear_certificate p007 (1 : ℚ) (fun n : ℕ => (1 : ℚ)) (fun n : ℕ => (3 : ℚ)) (fun n : ℕ => (0 : ℚ))
  · norm_num [p007]
  · intro n; positivity
  · intro n
    simp only [p007, Nat.cast_add, Nat.cast_one, pow_succ, Nat.choose_succ_succ, Nat.choose_one_right, pow_add]
    ring
theorem p007_valid : FirstCertificate p007 (1 : ℚ) (fun n x => ((3 : ℚ) * x + (0 : ℚ)) / (1 : ℚ)) := p007_base_valid
theorem p007_unique (a : ℕ → ℚ) (ha : FirstCertificate a (1 : ℚ) (fun n x => ((3 : ℚ) * x + (0 : ℚ)) / (1 : ℚ))) :
    ∀ n, a n = p007 n := first_unique p007_valid ha
#print axioms p007_valid
#print axioms p007_unique

def p008 (n : ℕ) : ℚ := ((3 : ℚ) * ((3 : ℚ) ^ n))
theorem p008_base_valid : FirstCertificate p008 (3 : ℚ) (fun n x => ((3 : ℚ) * x + (0 : ℚ)) / (1 : ℚ)) := by
  apply linear_certificate p008 (3 : ℚ) (fun n : ℕ => (1 : ℚ)) (fun n : ℕ => (3 : ℚ)) (fun n : ℕ => (0 : ℚ))
  · norm_num [p008]
  · intro n; positivity
  · intro n
    simp only [p008, Nat.cast_add, Nat.cast_one, pow_succ, Nat.choose_succ_succ, Nat.choose_one_right, pow_add]
    ring
theorem p008_valid : FirstCertificate p008 (3 : ℚ) (fun n x => ((3 : ℚ) * x + (0 : ℚ)) / (1 : ℚ)) := p008_base_valid
theorem p008_unique (a : ℕ → ℚ) (ha : FirstCertificate a (3 : ℚ) (fun n x => ((3 : ℚ) * x + (0 : ℚ)) / (1 : ℚ))) :
    ∀ n, a n = p008 n := first_unique p008_valid ha
#print axioms p008_valid
#print axioms p008_unique

def p009 (n : ℕ) : ℚ := (((1 : ℚ) / 2) * ((2 : ℚ) ^ n))
theorem p009_base_valid : FirstCertificate p009 ((1 : ℚ) / 2) (fun n x => ((2 : ℚ) * x + (0 : ℚ)) / (1 : ℚ)) := by
  apply linear_certificate p009 ((1 : ℚ) / 2) (fun n : ℕ => (1 : ℚ)) (fun n : ℕ => (2 : ℚ)) (fun n : ℕ => (0 : ℚ))
  · norm_num [p009]
  · intro n; positivity
  · intro n
    simp only [p009, Nat.cast_add, Nat.cast_one, pow_succ, Nat.choose_succ_succ, Nat.choose_one_right, pow_add]
    ring
theorem p009_valid : FirstCertificate p009 ((1 : ℚ) / 2) (fun n x => ((2 : ℚ) * x + (0 : ℚ)) / (1 : ℚ)) := p009_base_valid
theorem p009_unique (a : ℕ → ℚ) (ha : FirstCertificate a ((1 : ℚ) / 2) (fun n x => ((2 : ℚ) * x + (0 : ℚ)) / (1 : ℚ))) :
    ∀ n, a n = p009 n := first_unique p009_valid ha
#print axioms p009_valid
#print axioms p009_unique

def p010 (n : ℕ) : ℚ := ((3 : ℚ) * ((2 : ℚ) ^ n))
theorem p010_base_valid : FirstCertificate p010 (3 : ℚ) (fun n x => ((2 : ℚ) * x + (0 : ℚ)) / (1 : ℚ)) := by
  apply linear_certificate p010 (3 : ℚ) (fun n : ℕ => (1 : ℚ)) (fun n : ℕ => (2 : ℚ)) (fun n : ℕ => (0 : ℚ))
  · norm_num [p010]
  · intro n; positivity
  · intro n
    simp only [p010, Nat.cast_add, Nat.cast_one, pow_succ, Nat.choose_succ_succ, Nat.choose_one_right, pow_add]
    ring
theorem p010_valid : FirstCertificate p010 (3 : ℚ) (fun n x => ((2 : ℚ) * x + (0 : ℚ)) / (1 : ℚ)) := p010_base_valid
theorem p010_unique (a : ℕ → ℚ) (ha : FirstCertificate a (3 : ℚ) (fun n x => ((2 : ℚ) * x + (0 : ℚ)) / (1 : ℚ))) :
    ∀ n, a n = p010 n := first_unique p010_valid ha
#print axioms p010_valid
#print axioms p010_unique

def p011 (n : ℕ) : ℚ := ((1 : ℚ) + ((4 : ℚ) * ((3 : ℚ) ^ n)))
theorem p011_base_valid : FirstCertificate p011 (5 : ℚ) (fun n x => ((3 : ℚ) * x + (-2 : ℚ)) / (1 : ℚ)) := by
  apply linear_certificate p011 (5 : ℚ) (fun n : ℕ => (1 : ℚ)) (fun n : ℕ => (3 : ℚ)) (fun n : ℕ => (-2 : ℚ))
  · norm_num [p011]
  · intro n; positivity
  · intro n
    simp only [p011, Nat.cast_add, Nat.cast_one, pow_succ, Nat.choose_succ_succ, Nat.choose_one_right, pow_add]
    ring
theorem p011_valid : FirstCertificate p011 (5 : ℚ) (fun n x => ((3 : ℚ) * x + (-2 : ℚ)) / (1 : ℚ)) := p011_base_valid
theorem p011_unique (a : ℕ → ℚ) (ha : FirstCertificate a (5 : ℚ) (fun n x => ((3 : ℚ) * x + (-2 : ℚ)) / (1 : ℚ))) :
    ∀ n, a n = p011 n := first_unique p011_valid ha
#print axioms p011_valid
#print axioms p011_unique

def p012 (n : ℕ) : ℚ := ((2 : ℚ) + ((3 : ℚ) ^ n))
theorem p012_base_valid : FirstCertificate p012 (3 : ℚ) (fun n x => ((3 : ℚ) * x + (-4 : ℚ)) / (1 : ℚ)) := by
  apply linear_certificate p012 (3 : ℚ) (fun n : ℕ => (1 : ℚ)) (fun n : ℕ => (3 : ℚ)) (fun n : ℕ => (-4 : ℚ))
  · norm_num [p012]
  · intro n; positivity
  · intro n
    simp only [p012, Nat.cast_add, Nat.cast_one, pow_succ, Nat.choose_succ_succ, Nat.choose_one_right, pow_add]
    ring
theorem p012_valid : FirstCertificate p012 (3 : ℚ) (fun n x => ((3 : ℚ) * x + (-4 : ℚ)) / (1 : ℚ)) := p012_base_valid
theorem p012_unique (a : ℕ → ℚ) (ha : FirstCertificate a (3 : ℚ) (fun n x => ((3 : ℚ) * x + (-4 : ℚ)) / (1 : ℚ))) :
    ∀ n, a n = p012 n := first_unique p012_valid ha
#print axioms p012_valid
#print axioms p012_unique

def p013 (n : ℕ) : ℚ := ((2 : ℚ) + ((3 : ℚ) * ((3 : ℚ) ^ n)))
theorem p013_base_valid : FirstCertificate p013 (5 : ℚ) (fun n x => ((3 : ℚ) * x + (-4 : ℚ)) / (1 : ℚ)) := by
  apply linear_certificate p013 (5 : ℚ) (fun n : ℕ => (1 : ℚ)) (fun n : ℕ => (3 : ℚ)) (fun n : ℕ => (-4 : ℚ))
  · norm_num [p013]
  · intro n; positivity
  · intro n
    simp only [p013, Nat.cast_add, Nat.cast_one, pow_succ, Nat.choose_succ_succ, Nat.choose_one_right, pow_add]
    ring
theorem p013_valid : FirstCertificate p013 (5 : ℚ) (fun n x => ((3 : ℚ) * x + (-4 : ℚ)) / (1 : ℚ)) := p013_base_valid
theorem p013_unique (a : ℕ → ℚ) (ha : FirstCertificate a (5 : ℚ) (fun n x => ((3 : ℚ) * x + (-4 : ℚ)) / (1 : ℚ))) :
    ∀ n, a n = p013 n := first_unique p013_valid ha
#print axioms p013_valid
#print axioms p013_unique

def p014 (n : ℕ) : ℚ := ((1 : ℚ) + (((1 : ℚ) / 2) * ((2 : ℚ) ^ n)))
theorem p014_base_valid : FirstCertificate p014 ((3 : ℚ) / 2) (fun n x => ((2 : ℚ) * x + (-1 : ℚ)) / (1 : ℚ)) := by
  apply linear_certificate p014 ((3 : ℚ) / 2) (fun n : ℕ => (1 : ℚ)) (fun n : ℕ => (2 : ℚ)) (fun n : ℕ => (-1 : ℚ))
  · norm_num [p014]
  · intro n; positivity
  · intro n
    simp only [p014, Nat.cast_add, Nat.cast_one, pow_succ, Nat.choose_succ_succ, Nat.choose_one_right, pow_add]
    ring
theorem p014_valid : FirstCertificate p014 ((3 : ℚ) / 2) (fun n x => ((2 : ℚ) * x + (-1 : ℚ)) / (1 : ℚ)) := p014_base_valid
theorem p014_unique (a : ℕ → ℚ) (ha : FirstCertificate a ((3 : ℚ) / 2) (fun n x => ((2 : ℚ) * x + (-1 : ℚ)) / (1 : ℚ))) :
    ∀ n, a n = p014 n := first_unique p014_valid ha
#print axioms p014_valid
#print axioms p014_unique

def p015 (n : ℕ) : ℚ := ((2 : ℚ) + ((3 : ℚ) * ((2 : ℚ) ^ n)))
theorem p015_base_valid : FirstCertificate p015 (5 : ℚ) (fun n x => ((2 : ℚ) * x + (-2 : ℚ)) / (1 : ℚ)) := by
  apply linear_certificate p015 (5 : ℚ) (fun n : ℕ => (1 : ℚ)) (fun n : ℕ => (2 : ℚ)) (fun n : ℕ => (-2 : ℚ))
  · norm_num [p015]
  · intro n; positivity
  · intro n
    simp only [p015, Nat.cast_add, Nat.cast_one, pow_succ, Nat.choose_succ_succ, Nat.choose_one_right, pow_add]
    ring
theorem p015_valid : FirstCertificate p015 (5 : ℚ) (fun n x => ((2 : ℚ) * x + (-2 : ℚ)) / (1 : ℚ)) := p015_base_valid
theorem p015_unique (a : ℕ → ℚ) (ha : FirstCertificate a (5 : ℚ) (fun n x => ((2 : ℚ) * x + (-2 : ℚ)) / (1 : ℚ))) :
    ∀ n, a n = p015 n := first_unique p015_valid ha
#print axioms p015_valid
#print axioms p015_unique

def p016 (n : ℕ) : ℚ := (((n : ℚ) + 1) * (((n : ℚ) + 1) + (2 : ℚ)))
theorem p016_base_valid : FirstCertificate p016 (3 : ℚ) (fun n x => (((((n : ℚ) + 1) + (1 : ℚ)) * ((((n : ℚ) + 1) + (1 : ℚ)) + (2 : ℚ))) * x + (0 : ℚ)) / (((n : ℚ) + 1) * (((n : ℚ) + 1) + (2 : ℚ)))) := by
  apply linear_certificate p016 (3 : ℚ) (fun n : ℕ => (((n : ℚ) + 1) * (((n : ℚ) + 1) + (2 : ℚ)))) (fun n : ℕ => ((((n : ℚ) + 1) + (1 : ℚ)) * ((((n : ℚ) + 1) + (1 : ℚ)) + (2 : ℚ)))) (fun n : ℕ => (0 : ℚ))
  · norm_num [p016]
  · intro n; positivity
  · intro n
    simp only [p016, Nat.cast_add, Nat.cast_one, pow_succ, Nat.choose_succ_succ, Nat.choose_one_right, pow_add]
    ring
theorem p016_valid : FirstCertificate p016 (3 : ℚ) (fun n x => (((((n : ℚ) + 1) + (1 : ℚ)) * ((((n : ℚ) + 1) + (1 : ℚ)) + (2 : ℚ))) * x + (0 : ℚ)) / (((n : ℚ) + 1) * (((n : ℚ) + 1) + (2 : ℚ)))) := p016_base_valid
theorem p016_unique (a : ℕ → ℚ) (ha : FirstCertificate a (3 : ℚ) (fun n x => (((((n : ℚ) + 1) + (1 : ℚ)) * ((((n : ℚ) + 1) + (1 : ℚ)) + (2 : ℚ))) * x + (0 : ℚ)) / (((n : ℚ) + 1) * (((n : ℚ) + 1) + (2 : ℚ))))) :
    ∀ n, a n = p016 n := first_unique p016_valid ha
#print axioms p016_valid
#print axioms p016_unique

def p017 (n : ℕ) : ℚ := ((((n : ℚ) + 1) * (((n : ℚ) + 1) + (2 : ℚ))) * (3 : ℚ))
theorem p017_base_valid : FirstCertificate p017 (9 : ℚ) (fun n x => (((((n : ℚ) + 1) + (1 : ℚ)) * ((((n : ℚ) + 1) + (1 : ℚ)) + (2 : ℚ))) * x + (0 : ℚ)) / (((n : ℚ) + 1) * (((n : ℚ) + 1) + (2 : ℚ)))) := by
  apply linear_certificate p017 (9 : ℚ) (fun n : ℕ => (((n : ℚ) + 1) * (((n : ℚ) + 1) + (2 : ℚ)))) (fun n : ℕ => ((((n : ℚ) + 1) + (1 : ℚ)) * ((((n : ℚ) + 1) + (1 : ℚ)) + (2 : ℚ)))) (fun n : ℕ => (0 : ℚ))
  · norm_num [p017]
  · intro n; positivity
  · intro n
    simp only [p017, Nat.cast_add, Nat.cast_one, pow_succ, Nat.choose_succ_succ, Nat.choose_one_right, pow_add]
    ring
theorem p017_valid : FirstCertificate p017 (9 : ℚ) (fun n x => (((((n : ℚ) + 1) + (1 : ℚ)) * ((((n : ℚ) + 1) + (1 : ℚ)) + (2 : ℚ))) * x + (0 : ℚ)) / (((n : ℚ) + 1) * (((n : ℚ) + 1) + (2 : ℚ)))) := p017_base_valid
theorem p017_unique (a : ℕ → ℚ) (ha : FirstCertificate a (9 : ℚ) (fun n x => (((((n : ℚ) + 1) + (1 : ℚ)) * ((((n : ℚ) + 1) + (1 : ℚ)) + (2 : ℚ))) * x + (0 : ℚ)) / (((n : ℚ) + 1) * (((n : ℚ) + 1) + (2 : ℚ))))) :
    ∀ n, a n = p017 n := first_unique p017_valid ha
#print axioms p017_valid
#print axioms p017_unique

def p018 (n : ℕ) : ℚ := ((((n : ℚ) + 1) * (((n : ℚ) + 1) + (2 : ℚ))) * ((1 : ℚ) / 2))
theorem p018_base_valid : FirstCertificate p018 ((3 : ℚ) / 2) (fun n x => (((((n : ℚ) + 1) + (1 : ℚ)) * ((((n : ℚ) + 1) + (1 : ℚ)) + (2 : ℚ))) * x + (0 : ℚ)) / (((n : ℚ) + 1) * (((n : ℚ) + 1) + (2 : ℚ)))) := by
  apply linear_certificate p018 ((3 : ℚ) / 2) (fun n : ℕ => (((n : ℚ) + 1) * (((n : ℚ) + 1) + (2 : ℚ)))) (fun n : ℕ => ((((n : ℚ) + 1) + (1 : ℚ)) * ((((n : ℚ) + 1) + (1 : ℚ)) + (2 : ℚ)))) (fun n : ℕ => (0 : ℚ))
  · norm_num [p018]
  · intro n; positivity
  · intro n
    simp only [p018, Nat.cast_add, Nat.cast_one, pow_succ, Nat.choose_succ_succ, Nat.choose_one_right, pow_add]
    ring
theorem p018_valid : FirstCertificate p018 ((3 : ℚ) / 2) (fun n x => (((((n : ℚ) + 1) + (1 : ℚ)) * ((((n : ℚ) + 1) + (1 : ℚ)) + (2 : ℚ))) * x + (0 : ℚ)) / (((n : ℚ) + 1) * (((n : ℚ) + 1) + (2 : ℚ)))) := p018_base_valid
theorem p018_unique (a : ℕ → ℚ) (ha : FirstCertificate a ((3 : ℚ) / 2) (fun n x => (((((n : ℚ) + 1) + (1 : ℚ)) * ((((n : ℚ) + 1) + (1 : ℚ)) + (2 : ℚ))) * x + (0 : ℚ)) / (((n : ℚ) + 1) * (((n : ℚ) + 1) + (2 : ℚ))))) :
    ∀ n, a n = p018 n := first_unique p018_valid ha
#print axioms p018_valid
#print axioms p018_unique

def p019 (n : ℕ) : ℚ := ((((n : ℚ) + 1) * (((n : ℚ) + 1) + (2 : ℚ))) * (2 : ℚ))
theorem p019_base_valid : FirstCertificate p019 (6 : ℚ) (fun n x => (((((n : ℚ) + 1) + (1 : ℚ)) * ((((n : ℚ) + 1) + (1 : ℚ)) + (2 : ℚ))) * x + (0 : ℚ)) / (((n : ℚ) + 1) * (((n : ℚ) + 1) + (2 : ℚ)))) := by
  apply linear_certificate p019 (6 : ℚ) (fun n : ℕ => (((n : ℚ) + 1) * (((n : ℚ) + 1) + (2 : ℚ)))) (fun n : ℕ => ((((n : ℚ) + 1) + (1 : ℚ)) * ((((n : ℚ) + 1) + (1 : ℚ)) + (2 : ℚ)))) (fun n : ℕ => (0 : ℚ))
  · norm_num [p019]
  · intro n; positivity
  · intro n
    simp only [p019, Nat.cast_add, Nat.cast_one, pow_succ, Nat.choose_succ_succ, Nat.choose_one_right, pow_add]
    ring
theorem p019_valid : FirstCertificate p019 (6 : ℚ) (fun n x => (((((n : ℚ) + 1) + (1 : ℚ)) * ((((n : ℚ) + 1) + (1 : ℚ)) + (2 : ℚ))) * x + (0 : ℚ)) / (((n : ℚ) + 1) * (((n : ℚ) + 1) + (2 : ℚ)))) := p019_base_valid
theorem p019_unique (a : ℕ → ℚ) (ha : FirstCertificate a (6 : ℚ) (fun n x => (((((n : ℚ) + 1) + (1 : ℚ)) * ((((n : ℚ) + 1) + (1 : ℚ)) + (2 : ℚ))) * x + (0 : ℚ)) / (((n : ℚ) + 1) * (((n : ℚ) + 1) + (2 : ℚ))))) :
    ∀ n, a n = p019 n := first_unique p019_valid ha
#print axioms p019_valid
#print axioms p019_unique

def p020 (n : ℕ) : ℚ := ((((n : ℚ) + 1) * (((n : ℚ) + 1) + (2 : ℚ))) * (4 : ℚ))
theorem p020_base_valid : FirstCertificate p020 (12 : ℚ) (fun n x => (((((n : ℚ) + 1) + (1 : ℚ)) * ((((n : ℚ) + 1) + (1 : ℚ)) + (2 : ℚ))) * x + (0 : ℚ)) / (((n : ℚ) + 1) * (((n : ℚ) + 1) + (2 : ℚ)))) := by
  apply linear_certificate p020 (12 : ℚ) (fun n : ℕ => (((n : ℚ) + 1) * (((n : ℚ) + 1) + (2 : ℚ)))) (fun n : ℕ => ((((n : ℚ) + 1) + (1 : ℚ)) * ((((n : ℚ) + 1) + (1 : ℚ)) + (2 : ℚ)))) (fun n : ℕ => (0 : ℚ))
  · norm_num [p020]
  · intro n; positivity
  · intro n
    simp only [p020, Nat.cast_add, Nat.cast_one, pow_succ, Nat.choose_succ_succ, Nat.choose_one_right, pow_add]
    ring
theorem p020_valid : FirstCertificate p020 (12 : ℚ) (fun n x => (((((n : ℚ) + 1) + (1 : ℚ)) * ((((n : ℚ) + 1) + (1 : ℚ)) + (2 : ℚ))) * x + (0 : ℚ)) / (((n : ℚ) + 1) * (((n : ℚ) + 1) + (2 : ℚ)))) := p020_base_valid
theorem p020_unique (a : ℕ → ℚ) (ha : FirstCertificate a (12 : ℚ) (fun n x => (((((n : ℚ) + 1) + (1 : ℚ)) * ((((n : ℚ) + 1) + (1 : ℚ)) + (2 : ℚ))) * x + (0 : ℚ)) / (((n : ℚ) + 1) * (((n : ℚ) + 1) + (2 : ℚ))))) :
    ∀ n, a n = p020 n := first_unique p020_valid ha
#print axioms p020_valid
#print axioms p020_unique

def p021 (n : ℕ) : ℚ := ((((n : ℚ) + 1) * (((n : ℚ) + 1) + (2 : ℚ))) + ((-1 : ℚ) * (2 : ℚ)))
theorem p021_base_valid : FirstCertificate p021 (1 : ℚ) (fun n x => (((((n : ℚ) + 1) + (1 : ℚ)) * ((((n : ℚ) + 1) + (1 : ℚ)) + (2 : ℚ))) * x + (((-1 : ℚ) * (2 : ℚ)) * ((((n : ℚ) + 1) * (((n : ℚ) + 1) + (2 : ℚ))) + ((-1 : ℚ) * ((((n : ℚ) + 1) + (1 : ℚ)) * ((((n : ℚ) + 1) + (1 : ℚ)) + (2 : ℚ))))))) / (((n : ℚ) + 1) * (((n : ℚ) + 1) + (2 : ℚ)))) := by
  apply linear_certificate p021 (1 : ℚ) (fun n : ℕ => (((n : ℚ) + 1) * (((n : ℚ) + 1) + (2 : ℚ)))) (fun n : ℕ => ((((n : ℚ) + 1) + (1 : ℚ)) * ((((n : ℚ) + 1) + (1 : ℚ)) + (2 : ℚ)))) (fun n : ℕ => (((-1 : ℚ) * (2 : ℚ)) * ((((n : ℚ) + 1) * (((n : ℚ) + 1) + (2 : ℚ))) + ((-1 : ℚ) * ((((n : ℚ) + 1) + (1 : ℚ)) * ((((n : ℚ) + 1) + (1 : ℚ)) + (2 : ℚ)))))))
  · norm_num [p021]
  · intro n; positivity
  · intro n
    simp only [p021, Nat.cast_add, Nat.cast_one, pow_succ, Nat.choose_succ_succ, Nat.choose_one_right, pow_add]
    ring
theorem p021_valid : FirstCertificate p021 (1 : ℚ) (fun n x => (((((n : ℚ) + 1) + (1 : ℚ)) * ((((n : ℚ) + 1) + (1 : ℚ)) + (2 : ℚ))) * x + (((-1 : ℚ) * (2 : ℚ)) * ((((n : ℚ) + 1) * (((n : ℚ) + 1) + (2 : ℚ))) + ((-1 : ℚ) * ((((n : ℚ) + 1) + (1 : ℚ)) * ((((n : ℚ) + 1) + (1 : ℚ)) + (2 : ℚ))))))) / (((n : ℚ) + 1) * (((n : ℚ) + 1) + (2 : ℚ)))) := p021_base_valid
theorem p021_unique (a : ℕ → ℚ) (ha : FirstCertificate a (1 : ℚ) (fun n x => (((((n : ℚ) + 1) + (1 : ℚ)) * ((((n : ℚ) + 1) + (1 : ℚ)) + (2 : ℚ))) * x + (((-1 : ℚ) * (2 : ℚ)) * ((((n : ℚ) + 1) * (((n : ℚ) + 1) + (2 : ℚ))) + ((-1 : ℚ) * ((((n : ℚ) + 1) + (1 : ℚ)) * ((((n : ℚ) + 1) + (1 : ℚ)) + (2 : ℚ))))))) / (((n : ℚ) + 1) * (((n : ℚ) + 1) + (2 : ℚ))))) :
    ∀ n, a n = p021 n := first_unique p021_valid ha
#print axioms p021_valid
#print axioms p021_unique

def p022 (n : ℕ) : ℚ := (((((n : ℚ) + 1) * (((n : ℚ) + 1) + (2 : ℚ))) * ((1 : ℚ) / 2)) + (-1 : ℚ))
theorem p022_base_valid : FirstCertificate p022 ((1 : ℚ) / 2) (fun n x => (((((n : ℚ) + 1) + (1 : ℚ)) * ((((n : ℚ) + 1) + (1 : ℚ)) + (2 : ℚ))) * x + ((-1 : ℚ) * ((((n : ℚ) + 1) * (((n : ℚ) + 1) + (2 : ℚ))) + ((-1 : ℚ) * ((((n : ℚ) + 1) + (1 : ℚ)) * ((((n : ℚ) + 1) + (1 : ℚ)) + (2 : ℚ))))))) / (((n : ℚ) + 1) * (((n : ℚ) + 1) + (2 : ℚ)))) := by
  apply linear_certificate p022 ((1 : ℚ) / 2) (fun n : ℕ => (((n : ℚ) + 1) * (((n : ℚ) + 1) + (2 : ℚ)))) (fun n : ℕ => ((((n : ℚ) + 1) + (1 : ℚ)) * ((((n : ℚ) + 1) + (1 : ℚ)) + (2 : ℚ)))) (fun n : ℕ => ((-1 : ℚ) * ((((n : ℚ) + 1) * (((n : ℚ) + 1) + (2 : ℚ))) + ((-1 : ℚ) * ((((n : ℚ) + 1) + (1 : ℚ)) * ((((n : ℚ) + 1) + (1 : ℚ)) + (2 : ℚ)))))))
  · norm_num [p022]
  · intro n; positivity
  · intro n
    simp only [p022, Nat.cast_add, Nat.cast_one, pow_succ, Nat.choose_succ_succ, Nat.choose_one_right, pow_add]
    ring
theorem p022_valid : FirstCertificate p022 ((1 : ℚ) / 2) (fun n x => (((((n : ℚ) + 1) + (1 : ℚ)) * ((((n : ℚ) + 1) + (1 : ℚ)) + (2 : ℚ))) * x + ((-1 : ℚ) * ((((n : ℚ) + 1) * (((n : ℚ) + 1) + (2 : ℚ))) + ((-1 : ℚ) * ((((n : ℚ) + 1) + (1 : ℚ)) * ((((n : ℚ) + 1) + (1 : ℚ)) + (2 : ℚ))))))) / (((n : ℚ) + 1) * (((n : ℚ) + 1) + (2 : ℚ)))) := p022_base_valid
theorem p022_unique (a : ℕ → ℚ) (ha : FirstCertificate a ((1 : ℚ) / 2) (fun n x => (((((n : ℚ) + 1) + (1 : ℚ)) * ((((n : ℚ) + 1) + (1 : ℚ)) + (2 : ℚ))) * x + ((-1 : ℚ) * ((((n : ℚ) + 1) * (((n : ℚ) + 1) + (2 : ℚ))) + ((-1 : ℚ) * ((((n : ℚ) + 1) + (1 : ℚ)) * ((((n : ℚ) + 1) + (1 : ℚ)) + (2 : ℚ))))))) / (((n : ℚ) + 1) * (((n : ℚ) + 1) + (2 : ℚ))))) :
    ∀ n, a n = p022 n := first_unique p022_valid ha
#print axioms p022_valid
#print axioms p022_unique

def p023 (n : ℕ) : ℚ := (((((n : ℚ) + 1) * (((n : ℚ) + 1) + (2 : ℚ))) * (3 : ℚ)) + ((-1 : ℚ) * (3 : ℚ)))
theorem p023_base_valid : FirstCertificate p023 (6 : ℚ) (fun n x => (((((n : ℚ) + 1) + (1 : ℚ)) * ((((n : ℚ) + 1) + (1 : ℚ)) + (2 : ℚ))) * x + (((-1 : ℚ) * (3 : ℚ)) * ((((n : ℚ) + 1) * (((n : ℚ) + 1) + (2 : ℚ))) + ((-1 : ℚ) * ((((n : ℚ) + 1) + (1 : ℚ)) * ((((n : ℚ) + 1) + (1 : ℚ)) + (2 : ℚ))))))) / (((n : ℚ) + 1) * (((n : ℚ) + 1) + (2 : ℚ)))) := by
  apply linear_certificate p023 (6 : ℚ) (fun n : ℕ => (((n : ℚ) + 1) * (((n : ℚ) + 1) + (2 : ℚ)))) (fun n : ℕ => ((((n : ℚ) + 1) + (1 : ℚ)) * ((((n : ℚ) + 1) + (1 : ℚ)) + (2 : ℚ)))) (fun n : ℕ => (((-1 : ℚ) * (3 : ℚ)) * ((((n : ℚ) + 1) * (((n : ℚ) + 1) + (2 : ℚ))) + ((-1 : ℚ) * ((((n : ℚ) + 1) + (1 : ℚ)) * ((((n : ℚ) + 1) + (1 : ℚ)) + (2 : ℚ)))))))
  · norm_num [p023]
  · intro n; positivity
  · intro n
    simp only [p023, Nat.cast_add, Nat.cast_one, pow_succ, Nat.choose_succ_succ, Nat.choose_one_right, pow_add]
    ring
theorem p023_valid : FirstCertificate p023 (6 : ℚ) (fun n x => (((((n : ℚ) + 1) + (1 : ℚ)) * ((((n : ℚ) + 1) + (1 : ℚ)) + (2 : ℚ))) * x + (((-1 : ℚ) * (3 : ℚ)) * ((((n : ℚ) + 1) * (((n : ℚ) + 1) + (2 : ℚ))) + ((-1 : ℚ) * ((((n : ℚ) + 1) + (1 : ℚ)) * ((((n : ℚ) + 1) + (1 : ℚ)) + (2 : ℚ))))))) / (((n : ℚ) + 1) * (((n : ℚ) + 1) + (2 : ℚ)))) := p023_base_valid
theorem p023_unique (a : ℕ → ℚ) (ha : FirstCertificate a (6 : ℚ) (fun n x => (((((n : ℚ) + 1) + (1 : ℚ)) * ((((n : ℚ) + 1) + (1 : ℚ)) + (2 : ℚ))) * x + (((-1 : ℚ) * (3 : ℚ)) * ((((n : ℚ) + 1) * (((n : ℚ) + 1) + (2 : ℚ))) + ((-1 : ℚ) * ((((n : ℚ) + 1) + (1 : ℚ)) * ((((n : ℚ) + 1) + (1 : ℚ)) + (2 : ℚ))))))) / (((n : ℚ) + 1) * (((n : ℚ) + 1) + (2 : ℚ))))) :
    ∀ n, a n = p023 n := first_unique p023_valid ha
#print axioms p023_valid
#print axioms p023_unique

def p024 (n : ℕ) : ℚ := ((((n : ℚ) + 1) * (((n : ℚ) + 1) + (2 : ℚ))) + ((-1 : ℚ) * (3 : ℚ)))
theorem p024_base_valid : FirstCertificate p024 (0 : ℚ) (fun n x => (((((n : ℚ) + 1) + (1 : ℚ)) * ((((n : ℚ) + 1) + (1 : ℚ)) + (2 : ℚ))) * x + (((-1 : ℚ) * (3 : ℚ)) * ((((n : ℚ) + 1) * (((n : ℚ) + 1) + (2 : ℚ))) + ((-1 : ℚ) * ((((n : ℚ) + 1) + (1 : ℚ)) * ((((n : ℚ) + 1) + (1 : ℚ)) + (2 : ℚ))))))) / (((n : ℚ) + 1) * (((n : ℚ) + 1) + (2 : ℚ)))) := by
  apply linear_certificate p024 (0 : ℚ) (fun n : ℕ => (((n : ℚ) + 1) * (((n : ℚ) + 1) + (2 : ℚ)))) (fun n : ℕ => ((((n : ℚ) + 1) + (1 : ℚ)) * ((((n : ℚ) + 1) + (1 : ℚ)) + (2 : ℚ)))) (fun n : ℕ => (((-1 : ℚ) * (3 : ℚ)) * ((((n : ℚ) + 1) * (((n : ℚ) + 1) + (2 : ℚ))) + ((-1 : ℚ) * ((((n : ℚ) + 1) + (1 : ℚ)) * ((((n : ℚ) + 1) + (1 : ℚ)) + (2 : ℚ)))))))
  · norm_num [p024]
  · intro n; positivity
  · intro n
    simp only [p024, Nat.cast_add, Nat.cast_one, pow_succ, Nat.choose_succ_succ, Nat.choose_one_right, pow_add]
    ring
theorem p024_valid : FirstCertificate p024 (0 : ℚ) (fun n x => (((((n : ℚ) + 1) + (1 : ℚ)) * ((((n : ℚ) + 1) + (1 : ℚ)) + (2 : ℚ))) * x + (((-1 : ℚ) * (3 : ℚ)) * ((((n : ℚ) + 1) * (((n : ℚ) + 1) + (2 : ℚ))) + ((-1 : ℚ) * ((((n : ℚ) + 1) + (1 : ℚ)) * ((((n : ℚ) + 1) + (1 : ℚ)) + (2 : ℚ))))))) / (((n : ℚ) + 1) * (((n : ℚ) + 1) + (2 : ℚ)))) := p024_base_valid
theorem p024_unique (a : ℕ → ℚ) (ha : FirstCertificate a (0 : ℚ) (fun n x => (((((n : ℚ) + 1) + (1 : ℚ)) * ((((n : ℚ) + 1) + (1 : ℚ)) + (2 : ℚ))) * x + (((-1 : ℚ) * (3 : ℚ)) * ((((n : ℚ) + 1) * (((n : ℚ) + 1) + (2 : ℚ))) + ((-1 : ℚ) * ((((n : ℚ) + 1) + (1 : ℚ)) * ((((n : ℚ) + 1) + (1 : ℚ)) + (2 : ℚ))))))) / (((n : ℚ) + 1) * (((n : ℚ) + 1) + (2 : ℚ))))) :
    ∀ n, a n = p024 n := first_unique p024_valid ha
#print axioms p024_valid
#print axioms p024_unique

def p025 (n : ℕ) : ℚ := (((((n : ℚ) + 1) * (((n : ℚ) + 1) + (2 : ℚ))) * ((1 : ℚ) / 2)) + ((-1 : ℚ) * (3 : ℚ)))
theorem p025_base_valid : FirstCertificate p025 ((-3 : ℚ) / 2) (fun n x => (((((n : ℚ) + 1) + (1 : ℚ)) * ((((n : ℚ) + 1) + (1 : ℚ)) + (2 : ℚ))) * x + (((-1 : ℚ) * (3 : ℚ)) * ((((n : ℚ) + 1) * (((n : ℚ) + 1) + (2 : ℚ))) + ((-1 : ℚ) * ((((n : ℚ) + 1) + (1 : ℚ)) * ((((n : ℚ) + 1) + (1 : ℚ)) + (2 : ℚ))))))) / (((n : ℚ) + 1) * (((n : ℚ) + 1) + (2 : ℚ)))) := by
  apply linear_certificate p025 ((-3 : ℚ) / 2) (fun n : ℕ => (((n : ℚ) + 1) * (((n : ℚ) + 1) + (2 : ℚ)))) (fun n : ℕ => ((((n : ℚ) + 1) + (1 : ℚ)) * ((((n : ℚ) + 1) + (1 : ℚ)) + (2 : ℚ)))) (fun n : ℕ => (((-1 : ℚ) * (3 : ℚ)) * ((((n : ℚ) + 1) * (((n : ℚ) + 1) + (2 : ℚ))) + ((-1 : ℚ) * ((((n : ℚ) + 1) + (1 : ℚ)) * ((((n : ℚ) + 1) + (1 : ℚ)) + (2 : ℚ)))))))
  · norm_num [p025]
  · intro n; positivity
  · intro n
    simp only [p025, Nat.cast_add, Nat.cast_one, pow_succ, Nat.choose_succ_succ, Nat.choose_one_right, pow_add]
    ring
theorem p025_valid : FirstCertificate p025 ((-3 : ℚ) / 2) (fun n x => (((((n : ℚ) + 1) + (1 : ℚ)) * ((((n : ℚ) + 1) + (1 : ℚ)) + (2 : ℚ))) * x + (((-1 : ℚ) * (3 : ℚ)) * ((((n : ℚ) + 1) * (((n : ℚ) + 1) + (2 : ℚ))) + ((-1 : ℚ) * ((((n : ℚ) + 1) + (1 : ℚ)) * ((((n : ℚ) + 1) + (1 : ℚ)) + (2 : ℚ))))))) / (((n : ℚ) + 1) * (((n : ℚ) + 1) + (2 : ℚ)))) := p025_base_valid
theorem p025_unique (a : ℕ → ℚ) (ha : FirstCertificate a ((-3 : ℚ) / 2) (fun n x => (((((n : ℚ) + 1) + (1 : ℚ)) * ((((n : ℚ) + 1) + (1 : ℚ)) + (2 : ℚ))) * x + (((-1 : ℚ) * (3 : ℚ)) * ((((n : ℚ) + 1) * (((n : ℚ) + 1) + (2 : ℚ))) + ((-1 : ℚ) * ((((n : ℚ) + 1) + (1 : ℚ)) * ((((n : ℚ) + 1) + (1 : ℚ)) + (2 : ℚ))))))) / (((n : ℚ) + 1) * (((n : ℚ) + 1) + (2 : ℚ))))) :
    ∀ n, a n = p025 n := first_unique p025_valid ha
#print axioms p025_valid
#print axioms p025_unique

def p026 (n : ℕ) : ℚ := ((((n : ℚ) + 1) * (((n : ℚ) + 1) + (2 : ℚ))) * ((2 : ℚ) + ((3 : ℚ) ^ n)))
theorem p026_base_valid : FirstCertificate p026 (9 : ℚ) (fun n x => (((3 : ℚ) * ((((n : ℚ) + 1) + (1 : ℚ)) * ((((n : ℚ) + 1) + (1 : ℚ)) + (2 : ℚ)))) * x + ((-4 : ℚ) * (((n : ℚ) + 1) * (((n : ℚ) + 1) + (2 : ℚ))) * ((((n : ℚ) + 1) + (1 : ℚ)) * ((((n : ℚ) + 1) + (1 : ℚ)) + (2 : ℚ))))) / (((n : ℚ) + 1) * (((n : ℚ) + 1) + (2 : ℚ)))) := by
  apply linear_certificate p026 (9 : ℚ) (fun n : ℕ => (((n : ℚ) + 1) * (((n : ℚ) + 1) + (2 : ℚ)))) (fun n : ℕ => ((3 : ℚ) * ((((n : ℚ) + 1) + (1 : ℚ)) * ((((n : ℚ) + 1) + (1 : ℚ)) + (2 : ℚ))))) (fun n : ℕ => ((-4 : ℚ) * (((n : ℚ) + 1) * (((n : ℚ) + 1) + (2 : ℚ))) * ((((n : ℚ) + 1) + (1 : ℚ)) * ((((n : ℚ) + 1) + (1 : ℚ)) + (2 : ℚ)))))
  · norm_num [p026]
  · intro n; positivity
  · intro n
    simp only [p026, Nat.cast_add, Nat.cast_one, pow_succ, Nat.choose_succ_succ, Nat.choose_one_right, pow_add]
    ring
theorem p026_valid : FirstCertificate p026 (9 : ℚ) (fun n x => (((3 : ℚ) * ((((n : ℚ) + 1) + (1 : ℚ)) * ((((n : ℚ) + 1) + (1 : ℚ)) + (2 : ℚ)))) * x + ((-4 : ℚ) * (((n : ℚ) + 1) * (((n : ℚ) + 1) + (2 : ℚ))) * ((((n : ℚ) + 1) + (1 : ℚ)) * ((((n : ℚ) + 1) + (1 : ℚ)) + (2 : ℚ))))) / (((n : ℚ) + 1) * (((n : ℚ) + 1) + (2 : ℚ)))) := p026_base_valid
theorem p026_unique (a : ℕ → ℚ) (ha : FirstCertificate a (9 : ℚ) (fun n x => (((3 : ℚ) * ((((n : ℚ) + 1) + (1 : ℚ)) * ((((n : ℚ) + 1) + (1 : ℚ)) + (2 : ℚ)))) * x + ((-4 : ℚ) * (((n : ℚ) + 1) * (((n : ℚ) + 1) + (2 : ℚ))) * ((((n : ℚ) + 1) + (1 : ℚ)) * ((((n : ℚ) + 1) + (1 : ℚ)) + (2 : ℚ))))) / (((n : ℚ) + 1) * (((n : ℚ) + 1) + (2 : ℚ))))) :
    ∀ n, a n = p026 n := first_unique p026_valid ha
#print axioms p026_valid
#print axioms p026_unique

def p027 (n : ℕ) : ℚ := ((((n : ℚ) + 1) * (((n : ℚ) + 1) + (2 : ℚ))) * ((1 : ℚ) + (((1 : ℚ) / 2) * ((2 : ℚ) ^ n))))
theorem p027_base_valid : FirstCertificate p027 ((9 : ℚ) / 2) (fun n x => (((2 : ℚ) * ((((n : ℚ) + 1) + (1 : ℚ)) * ((((n : ℚ) + 1) + (1 : ℚ)) + (2 : ℚ)))) * x + ((-1 : ℚ) * (((n : ℚ) + 1) * (((n : ℚ) + 1) + (2 : ℚ))) * ((((n : ℚ) + 1) + (1 : ℚ)) * ((((n : ℚ) + 1) + (1 : ℚ)) + (2 : ℚ))))) / (((n : ℚ) + 1) * (((n : ℚ) + 1) + (2 : ℚ)))) := by
  apply linear_certificate p027 ((9 : ℚ) / 2) (fun n : ℕ => (((n : ℚ) + 1) * (((n : ℚ) + 1) + (2 : ℚ)))) (fun n : ℕ => ((2 : ℚ) * ((((n : ℚ) + 1) + (1 : ℚ)) * ((((n : ℚ) + 1) + (1 : ℚ)) + (2 : ℚ))))) (fun n : ℕ => ((-1 : ℚ) * (((n : ℚ) + 1) * (((n : ℚ) + 1) + (2 : ℚ))) * ((((n : ℚ) + 1) + (1 : ℚ)) * ((((n : ℚ) + 1) + (1 : ℚ)) + (2 : ℚ)))))
  · norm_num [p027]
  · intro n; positivity
  · intro n
    simp only [p027, Nat.cast_add, Nat.cast_one, pow_succ, Nat.choose_succ_succ, Nat.choose_one_right, pow_add]
    ring
theorem p027_valid : FirstCertificate p027 ((9 : ℚ) / 2) (fun n x => (((2 : ℚ) * ((((n : ℚ) + 1) + (1 : ℚ)) * ((((n : ℚ) + 1) + (1 : ℚ)) + (2 : ℚ)))) * x + ((-1 : ℚ) * (((n : ℚ) + 1) * (((n : ℚ) + 1) + (2 : ℚ))) * ((((n : ℚ) + 1) + (1 : ℚ)) * ((((n : ℚ) + 1) + (1 : ℚ)) + (2 : ℚ))))) / (((n : ℚ) + 1) * (((n : ℚ) + 1) + (2 : ℚ)))) := p027_base_valid
theorem p027_unique (a : ℕ → ℚ) (ha : FirstCertificate a ((9 : ℚ) / 2) (fun n x => (((2 : ℚ) * ((((n : ℚ) + 1) + (1 : ℚ)) * ((((n : ℚ) + 1) + (1 : ℚ)) + (2 : ℚ)))) * x + ((-1 : ℚ) * (((n : ℚ) + 1) * (((n : ℚ) + 1) + (2 : ℚ))) * ((((n : ℚ) + 1) + (1 : ℚ)) * ((((n : ℚ) + 1) + (1 : ℚ)) + (2 : ℚ))))) / (((n : ℚ) + 1) * (((n : ℚ) + 1) + (2 : ℚ))))) :
    ∀ n, a n = p027 n := first_unique p027_valid ha
#print axioms p027_valid
#print axioms p027_unique

def p028 (n : ℕ) : ℚ := ((((n : ℚ) + 1) * (((n : ℚ) + 1) + (2 : ℚ))) * ((1 : ℚ) + ((2 : ℚ) ^ n)))
theorem p028_base_valid : FirstCertificate p028 (6 : ℚ) (fun n x => (((2 : ℚ) * ((((n : ℚ) + 1) + (1 : ℚ)) * ((((n : ℚ) + 1) + (1 : ℚ)) + (2 : ℚ)))) * x + ((-1 : ℚ) * (((n : ℚ) + 1) * (((n : ℚ) + 1) + (2 : ℚ))) * ((((n : ℚ) + 1) + (1 : ℚ)) * ((((n : ℚ) + 1) + (1 : ℚ)) + (2 : ℚ))))) / (((n : ℚ) + 1) * (((n : ℚ) + 1) + (2 : ℚ)))) := by
  apply linear_certificate p028 (6 : ℚ) (fun n : ℕ => (((n : ℚ) + 1) * (((n : ℚ) + 1) + (2 : ℚ)))) (fun n : ℕ => ((2 : ℚ) * ((((n : ℚ) + 1) + (1 : ℚ)) * ((((n : ℚ) + 1) + (1 : ℚ)) + (2 : ℚ))))) (fun n : ℕ => ((-1 : ℚ) * (((n : ℚ) + 1) * (((n : ℚ) + 1) + (2 : ℚ))) * ((((n : ℚ) + 1) + (1 : ℚ)) * ((((n : ℚ) + 1) + (1 : ℚ)) + (2 : ℚ)))))
  · norm_num [p028]
  · intro n; positivity
  · intro n
    simp only [p028, Nat.cast_add, Nat.cast_one, pow_succ, Nat.choose_succ_succ, Nat.choose_one_right, pow_add]
    ring
theorem p028_valid : FirstCertificate p028 (6 : ℚ) (fun n x => (((2 : ℚ) * ((((n : ℚ) + 1) + (1 : ℚ)) * ((((n : ℚ) + 1) + (1 : ℚ)) + (2 : ℚ)))) * x + ((-1 : ℚ) * (((n : ℚ) + 1) * (((n : ℚ) + 1) + (2 : ℚ))) * ((((n : ℚ) + 1) + (1 : ℚ)) * ((((n : ℚ) + 1) + (1 : ℚ)) + (2 : ℚ))))) / (((n : ℚ) + 1) * (((n : ℚ) + 1) + (2 : ℚ)))) := p028_base_valid
theorem p028_unique (a : ℕ → ℚ) (ha : FirstCertificate a (6 : ℚ) (fun n x => (((2 : ℚ) * ((((n : ℚ) + 1) + (1 : ℚ)) * ((((n : ℚ) + 1) + (1 : ℚ)) + (2 : ℚ)))) * x + ((-1 : ℚ) * (((n : ℚ) + 1) * (((n : ℚ) + 1) + (2 : ℚ))) * ((((n : ℚ) + 1) + (1 : ℚ)) * ((((n : ℚ) + 1) + (1 : ℚ)) + (2 : ℚ))))) / (((n : ℚ) + 1) * (((n : ℚ) + 1) + (2 : ℚ))))) :
    ∀ n, a n = p028 n := first_unique p028_valid ha
#print axioms p028_valid
#print axioms p028_unique

def p029 (n : ℕ) : ℚ := ((((n : ℚ) + 1) * (((n : ℚ) + 1) + (2 : ℚ))) * ((1 : ℚ) + ((3 : ℚ) ^ n)))
theorem p029_base_valid : FirstCertificate p029 (6 : ℚ) (fun n x => (((3 : ℚ) * ((((n : ℚ) + 1) + (1 : ℚ)) * ((((n : ℚ) + 1) + (1 : ℚ)) + (2 : ℚ)))) * x + ((-2 : ℚ) * (((n : ℚ) + 1) * (((n : ℚ) + 1) + (2 : ℚ))) * ((((n : ℚ) + 1) + (1 : ℚ)) * ((((n : ℚ) + 1) + (1 : ℚ)) + (2 : ℚ))))) / (((n : ℚ) + 1) * (((n : ℚ) + 1) + (2 : ℚ)))) := by
  apply linear_certificate p029 (6 : ℚ) (fun n : ℕ => (((n : ℚ) + 1) * (((n : ℚ) + 1) + (2 : ℚ)))) (fun n : ℕ => ((3 : ℚ) * ((((n : ℚ) + 1) + (1 : ℚ)) * ((((n : ℚ) + 1) + (1 : ℚ)) + (2 : ℚ))))) (fun n : ℕ => ((-2 : ℚ) * (((n : ℚ) + 1) * (((n : ℚ) + 1) + (2 : ℚ))) * ((((n : ℚ) + 1) + (1 : ℚ)) * ((((n : ℚ) + 1) + (1 : ℚ)) + (2 : ℚ)))))
  · norm_num [p029]
  · intro n; positivity
  · intro n
    simp only [p029, Nat.cast_add, Nat.cast_one, pow_succ, Nat.choose_succ_succ, Nat.choose_one_right, pow_add]
    ring
theorem p029_valid : FirstCertificate p029 (6 : ℚ) (fun n x => (((3 : ℚ) * ((((n : ℚ) + 1) + (1 : ℚ)) * ((((n : ℚ) + 1) + (1 : ℚ)) + (2 : ℚ)))) * x + ((-2 : ℚ) * (((n : ℚ) + 1) * (((n : ℚ) + 1) + (2 : ℚ))) * ((((n : ℚ) + 1) + (1 : ℚ)) * ((((n : ℚ) + 1) + (1 : ℚ)) + (2 : ℚ))))) / (((n : ℚ) + 1) * (((n : ℚ) + 1) + (2 : ℚ)))) := p029_base_valid
theorem p029_unique (a : ℕ → ℚ) (ha : FirstCertificate a (6 : ℚ) (fun n x => (((3 : ℚ) * ((((n : ℚ) + 1) + (1 : ℚ)) * ((((n : ℚ) + 1) + (1 : ℚ)) + (2 : ℚ)))) * x + ((-2 : ℚ) * (((n : ℚ) + 1) * (((n : ℚ) + 1) + (2 : ℚ))) * ((((n : ℚ) + 1) + (1 : ℚ)) * ((((n : ℚ) + 1) + (1 : ℚ)) + (2 : ℚ))))) / (((n : ℚ) + 1) * (((n : ℚ) + 1) + (2 : ℚ))))) :
    ∀ n, a n = p029 n := first_unique p029_valid ha
#print axioms p029_valid
#print axioms p029_unique

def p030 (n : ℕ) : ℚ := ((((n : ℚ) + 1) * (((n : ℚ) + 1) + (2 : ℚ))) * ((2 : ℚ) + ((2 : ℚ) ^ n)))
theorem p030_base_valid : FirstCertificate p030 (9 : ℚ) (fun n x => (((2 : ℚ) * ((((n : ℚ) + 1) + (1 : ℚ)) * ((((n : ℚ) + 1) + (1 : ℚ)) + (2 : ℚ)))) * x + ((-2 : ℚ) * (((n : ℚ) + 1) * (((n : ℚ) + 1) + (2 : ℚ))) * ((((n : ℚ) + 1) + (1 : ℚ)) * ((((n : ℚ) + 1) + (1 : ℚ)) + (2 : ℚ))))) / (((n : ℚ) + 1) * (((n : ℚ) + 1) + (2 : ℚ)))) := by
  apply linear_certificate p030 (9 : ℚ) (fun n : ℕ => (((n : ℚ) + 1) * (((n : ℚ) + 1) + (2 : ℚ)))) (fun n : ℕ => ((2 : ℚ) * ((((n : ℚ) + 1) + (1 : ℚ)) * ((((n : ℚ) + 1) + (1 : ℚ)) + (2 : ℚ))))) (fun n : ℕ => ((-2 : ℚ) * (((n : ℚ) + 1) * (((n : ℚ) + 1) + (2 : ℚ))) * ((((n : ℚ) + 1) + (1 : ℚ)) * ((((n : ℚ) + 1) + (1 : ℚ)) + (2 : ℚ)))))
  · norm_num [p030]
  · intro n; positivity
  · intro n
    simp only [p030, Nat.cast_add, Nat.cast_one, pow_succ, Nat.choose_succ_succ, Nat.choose_one_right, pow_add]
    ring
theorem p030_valid : FirstCertificate p030 (9 : ℚ) (fun n x => (((2 : ℚ) * ((((n : ℚ) + 1) + (1 : ℚ)) * ((((n : ℚ) + 1) + (1 : ℚ)) + (2 : ℚ)))) * x + ((-2 : ℚ) * (((n : ℚ) + 1) * (((n : ℚ) + 1) + (2 : ℚ))) * ((((n : ℚ) + 1) + (1 : ℚ)) * ((((n : ℚ) + 1) + (1 : ℚ)) + (2 : ℚ))))) / (((n : ℚ) + 1) * (((n : ℚ) + 1) + (2 : ℚ)))) := p030_base_valid
theorem p030_unique (a : ℕ → ℚ) (ha : FirstCertificate a (9 : ℚ) (fun n x => (((2 : ℚ) * ((((n : ℚ) + 1) + (1 : ℚ)) * ((((n : ℚ) + 1) + (1 : ℚ)) + (2 : ℚ)))) * x + ((-2 : ℚ) * (((n : ℚ) + 1) * (((n : ℚ) + 1) + (2 : ℚ))) * ((((n : ℚ) + 1) + (1 : ℚ)) * ((((n : ℚ) + 1) + (1 : ℚ)) + (2 : ℚ))))) / (((n : ℚ) + 1) * (((n : ℚ) + 1) + (2 : ℚ))))) :
    ∀ n, a n = p030 n := first_unique p030_valid ha
#print axioms p030_valid
#print axioms p030_unique

def p031 (n : ℕ) : ℚ := (((4 : ℚ) * ((3 : ℚ) ^ n)) + ((4 : ℚ) ^ n))
theorem p031_valid : SecondCertificate p031 (5 : ℚ) (16 : ℚ) (7 : ℚ) (-12 : ℚ) := by
  constructor
  · norm_num [p031]
  · norm_num [p031]
  · intro n
    simp only [p031, pow_succ, pow_add]
    ring
theorem p031_unique (a : ℕ → ℚ) (ha : SecondCertificate a (5 : ℚ) (16 : ℚ) (7 : ℚ) (-12 : ℚ)) :
    ∀ n, a n = p031 n := second_unique p031_valid ha
#print axioms p031_valid
#print axioms p031_unique

def p032 (n : ℕ) : ℚ := ((((1 : ℚ) / 2) * ((2 : ℚ) ^ n)) + ((3 : ℚ) ^ n))
theorem p032_valid : SecondCertificate p032 ((3 : ℚ) / 2) (4 : ℚ) (5 : ℚ) (-6 : ℚ) := by
  constructor
  · norm_num [p032]
  · norm_num [p032]
  · intro n
    simp only [p032, pow_succ, pow_add]
    ring
theorem p032_unique (a : ℕ → ℚ) (ha : SecondCertificate a ((3 : ℚ) / 2) (4 : ℚ) (5 : ℚ) (-6 : ℚ)) :
    ∀ n, a n = p032 n := second_unique p032_valid ha
#print axioms p032_valid
#print axioms p032_unique

def p033 (n : ℕ) : ℚ := ((((1 : ℚ) / 2) * ((2 : ℚ) ^ n)) + ((4 : ℚ) ^ n))
theorem p033_valid : SecondCertificate p033 ((3 : ℚ) / 2) (5 : ℚ) (6 : ℚ) (-8 : ℚ) := by
  constructor
  · norm_num [p033]
  · norm_num [p033]
  · intro n
    simp only [p033, pow_succ, pow_add]
    ring
theorem p033_unique (a : ℕ → ℚ) (ha : SecondCertificate a ((3 : ℚ) / 2) (5 : ℚ) (6 : ℚ) (-8 : ℚ)) :
    ∀ n, a n = p033 n := second_unique p033_valid ha
#print axioms p033_valid
#print axioms p033_unique

def p034 (n : ℕ) : ℚ := (((3 : ℚ) * ((2 : ℚ) ^ n)) + ((3 : ℚ) ^ n))
theorem p034_valid : SecondCertificate p034 (4 : ℚ) (9 : ℚ) (5 : ℚ) (-6 : ℚ) := by
  constructor
  · norm_num [p034]
  · norm_num [p034]
  · intro n
    simp only [p034, pow_succ, pow_add]
    ring
theorem p034_unique (a : ℕ → ℚ) (ha : SecondCertificate a (4 : ℚ) (9 : ℚ) (5 : ℚ) (-6 : ℚ)) :
    ∀ n, a n = p034 n := second_unique p034_valid ha
#print axioms p034_valid
#print axioms p034_unique

def p035 (n : ℕ) : ℚ := (((2 : ℚ) ^ n) + ((4 : ℚ) ^ n))
theorem p035_valid : SecondCertificate p035 (2 : ℚ) (6 : ℚ) (6 : ℚ) (-8 : ℚ) := by
  constructor
  · norm_num [p035]
  · norm_num [p035]
  · intro n
    simp only [p035, pow_succ, pow_add]
    ring
theorem p035_unique (a : ℕ → ℚ) (ha : SecondCertificate a (2 : ℚ) (6 : ℚ) (6 : ℚ) (-8 : ℚ)) :
    ∀ n, a n = p035 n := second_unique p035_valid ha
#print axioms p035_valid
#print axioms p035_unique

def p036 (n : ℕ) : ℚ := ((4 : ℚ) * ((3 : ℚ) ^ ((n + 1).choose 2)))
theorem p036_base_valid : FirstCertificate p036 (4 : ℚ) (fun n x => (((3 : ℚ) ^ (n + 1)) * x + (0 : ℚ)) / (1 : ℚ)) := by
  apply linear_certificate p036 (4 : ℚ) (fun n : ℕ => (1 : ℚ)) (fun n : ℕ => ((3 : ℚ) ^ (n + 1))) (fun n : ℕ => (0 : ℚ))
  · norm_num [p036]
  · intro n; positivity
  · intro n
    simp only [p036, Nat.cast_add, Nat.cast_one, pow_succ, Nat.choose_succ_succ, Nat.choose_one_right, pow_add]
    ring
theorem p036_valid : FirstCertificate p036 (4 : ℚ) (fun n x => (((3 : ℚ) ^ (n + 1)) * x + (0 : ℚ)) / (1 : ℚ)) := p036_base_valid
theorem p036_unique (a : ℕ → ℚ) (ha : FirstCertificate a (4 : ℚ) (fun n x => (((3 : ℚ) ^ (n + 1)) * x + (0 : ℚ)) / (1 : ℚ))) :
    ∀ n, a n = p036 n := first_unique p036_valid ha
#print axioms p036_valid
#print axioms p036_unique

def p037 (n : ℕ) : ℚ := ((3 : ℚ) ^ ((n + 1).choose 2))
theorem p037_base_valid : FirstCertificate p037 (1 : ℚ) (fun n x => (((3 : ℚ) ^ (n + 1)) * x + (0 : ℚ)) / (1 : ℚ)) := by
  apply linear_certificate p037 (1 : ℚ) (fun n : ℕ => (1 : ℚ)) (fun n : ℕ => ((3 : ℚ) ^ (n + 1))) (fun n : ℕ => (0 : ℚ))
  · norm_num [p037]
  · intro n; positivity
  · intro n
    simp only [p037, Nat.cast_add, Nat.cast_one, pow_succ, Nat.choose_succ_succ, Nat.choose_one_right, pow_add]
    ring
theorem p037_valid : FirstCertificate p037 (1 : ℚ) (fun n x => (((3 : ℚ) ^ (n + 1)) * x + (0 : ℚ)) / (1 : ℚ)) := p037_base_valid
theorem p037_unique (a : ℕ → ℚ) (ha : FirstCertificate a (1 : ℚ) (fun n x => (((3 : ℚ) ^ (n + 1)) * x + (0 : ℚ)) / (1 : ℚ))) :
    ∀ n, a n = p037 n := first_unique p037_valid ha
#print axioms p037_valid
#print axioms p037_unique

def p038 (n : ℕ) : ℚ := ((3 : ℚ) * ((3 : ℚ) ^ ((n + 1).choose 2)))
theorem p038_base_valid : FirstCertificate p038 (3 : ℚ) (fun n x => (((3 : ℚ) ^ (n + 1)) * x + (0 : ℚ)) / (1 : ℚ)) := by
  apply linear_certificate p038 (3 : ℚ) (fun n : ℕ => (1 : ℚ)) (fun n : ℕ => ((3 : ℚ) ^ (n + 1))) (fun n : ℕ => (0 : ℚ))
  · norm_num [p038]
  · intro n; positivity
  · intro n
    simp only [p038, Nat.cast_add, Nat.cast_one, pow_succ, Nat.choose_succ_succ, Nat.choose_one_right, pow_add]
    ring
theorem p038_valid : FirstCertificate p038 (3 : ℚ) (fun n x => (((3 : ℚ) ^ (n + 1)) * x + (0 : ℚ)) / (1 : ℚ)) := p038_base_valid
theorem p038_unique (a : ℕ → ℚ) (ha : FirstCertificate a (3 : ℚ) (fun n x => (((3 : ℚ) ^ (n + 1)) * x + (0 : ℚ)) / (1 : ℚ))) :
    ∀ n, a n = p038 n := first_unique p038_valid ha
#print axioms p038_valid
#print axioms p038_unique

def p039 (n : ℕ) : ℚ := (((1 : ℚ) / 2) * ((2 : ℚ) ^ ((n + 1).choose 2)))
theorem p039_base_valid : FirstCertificate p039 ((1 : ℚ) / 2) (fun n x => (((2 : ℚ) ^ (n + 1)) * x + (0 : ℚ)) / (1 : ℚ)) := by
  apply linear_certificate p039 ((1 : ℚ) / 2) (fun n : ℕ => (1 : ℚ)) (fun n : ℕ => ((2 : ℚ) ^ (n + 1))) (fun n : ℕ => (0 : ℚ))
  · norm_num [p039]
  · intro n; positivity
  · intro n
    simp only [p039, Nat.cast_add, Nat.cast_one, pow_succ, Nat.choose_succ_succ, Nat.choose_one_right, pow_add]
    ring
theorem p039_valid : FirstCertificate p039 ((1 : ℚ) / 2) (fun n x => (((2 : ℚ) ^ (n + 1)) * x + (0 : ℚ)) / (1 : ℚ)) := p039_base_valid
theorem p039_unique (a : ℕ → ℚ) (ha : FirstCertificate a ((1 : ℚ) / 2) (fun n x => (((2 : ℚ) ^ (n + 1)) * x + (0 : ℚ)) / (1 : ℚ))) :
    ∀ n, a n = p039 n := first_unique p039_valid ha
#print axioms p039_valid
#print axioms p039_unique

def p040 (n : ℕ) : ℚ := ((3 : ℚ) * ((2 : ℚ) ^ ((n + 1).choose 2)))
theorem p040_base_valid : FirstCertificate p040 (3 : ℚ) (fun n x => (((2 : ℚ) ^ (n + 1)) * x + (0 : ℚ)) / (1 : ℚ)) := by
  apply linear_certificate p040 (3 : ℚ) (fun n : ℕ => (1 : ℚ)) (fun n : ℕ => ((2 : ℚ) ^ (n + 1))) (fun n : ℕ => (0 : ℚ))
  · norm_num [p040]
  · intro n; positivity
  · intro n
    simp only [p040, Nat.cast_add, Nat.cast_one, pow_succ, Nat.choose_succ_succ, Nat.choose_one_right, pow_add]
    ring
theorem p040_valid : FirstCertificate p040 (3 : ℚ) (fun n x => (((2 : ℚ) ^ (n + 1)) * x + (0 : ℚ)) / (1 : ℚ)) := p040_base_valid
theorem p040_unique (a : ℕ → ℚ) (ha : FirstCertificate a (3 : ℚ) (fun n x => (((2 : ℚ) ^ (n + 1)) * x + (0 : ℚ)) / (1 : ℚ))) :
    ∀ n, a n = p040 n := first_unique p040_valid ha
#print axioms p040_valid
#print axioms p040_unique

def p041 (n : ℕ) : ℚ := ((1 : ℚ) / ((1 : ℚ) + ((4 : ℚ) * ((3 : ℚ) ^ n))))
def p041_base (n : ℕ) : ℚ := ((1 : ℚ) + ((4 : ℚ) * ((3 : ℚ) ^ n)))
theorem p041_base_valid : FirstCertificate p041_base (5 : ℚ) (fun n x => ((3 : ℚ) * x + (-2 : ℚ)) / (1 : ℚ)) := by
  apply linear_certificate p041_base (5 : ℚ) (fun n : ℕ => (1 : ℚ)) (fun n : ℕ => (3 : ℚ)) (fun n : ℕ => (-2 : ℚ))
  · norm_num [p041_base]
  · intro n; positivity
  · intro n
    simp only [p041_base, Nat.cast_add, Nat.cast_one, pow_succ, Nat.choose_succ_succ, Nat.choose_one_right, pow_add]
    ring
theorem p041_positive (n : ℕ) : 0 < p041_base n := by
  unfold p041_base
  positivity
theorem p041_valid : FirstCertificate p041 ((1 : ℚ) / 5) (fun n x => (1 : ℚ) * x / ((3 : ℚ) + (-2 : ℚ) * x)) := by
  have h := reciprocal_certificate p041_base_valid p041_positive (by intro n; positivity)
  simpa only [p041, p041_base] using h.1
theorem p041_domain : (∀ n : ℕ, (3 : ℚ) + (-2 : ℚ) * p041 n ≠ 0) ∧ (∀ n, p041 n ≠ 0) := by
  have h := reciprocal_certificate p041_base_valid p041_positive (by intro n; positivity)
  simpa only [p041, p041_base] using h.2
#print axioms p041_domain
theorem p041_unique (a : ℕ → ℚ) (ha : FirstCertificate a ((1 : ℚ) / 5) (fun n x => (1 : ℚ) * x / ((3 : ℚ) + (-2 : ℚ) * x))) :
    ∀ n, a n = p041 n := first_unique p041_valid ha
#print axioms p041_valid
#print axioms p041_unique

def p042 (n : ℕ) : ℚ := ((1 : ℚ) / ((2 : ℚ) + ((3 : ℚ) ^ n)))
def p042_base (n : ℕ) : ℚ := ((2 : ℚ) + ((3 : ℚ) ^ n))
theorem p042_base_valid : FirstCertificate p042_base (3 : ℚ) (fun n x => ((3 : ℚ) * x + (-4 : ℚ)) / (1 : ℚ)) := by
  apply linear_certificate p042_base (3 : ℚ) (fun n : ℕ => (1 : ℚ)) (fun n : ℕ => (3 : ℚ)) (fun n : ℕ => (-4 : ℚ))
  · norm_num [p042_base]
  · intro n; positivity
  · intro n
    simp only [p042_base, Nat.cast_add, Nat.cast_one, pow_succ, Nat.choose_succ_succ, Nat.choose_one_right, pow_add]
    ring
theorem p042_positive (n : ℕ) : 0 < p042_base n := by
  unfold p042_base
  positivity
theorem p042_valid : FirstCertificate p042 ((1 : ℚ) / 3) (fun n x => (1 : ℚ) * x / ((3 : ℚ) + (-4 : ℚ) * x)) := by
  have h := reciprocal_certificate p042_base_valid p042_positive (by intro n; positivity)
  simpa only [p042, p042_base] using h.1
theorem p042_domain : (∀ n : ℕ, (3 : ℚ) + (-4 : ℚ) * p042 n ≠ 0) ∧ (∀ n, p042 n ≠ 0) := by
  have h := reciprocal_certificate p042_base_valid p042_positive (by intro n; positivity)
  simpa only [p042, p042_base] using h.2
#print axioms p042_domain
theorem p042_unique (a : ℕ → ℚ) (ha : FirstCertificate a ((1 : ℚ) / 3) (fun n x => (1 : ℚ) * x / ((3 : ℚ) + (-4 : ℚ) * x))) :
    ∀ n, a n = p042 n := first_unique p042_valid ha
#print axioms p042_valid
#print axioms p042_unique

def p043 (n : ℕ) : ℚ := ((1 : ℚ) / ((2 : ℚ) + ((3 : ℚ) * ((3 : ℚ) ^ n))))
def p043_base (n : ℕ) : ℚ := ((2 : ℚ) + ((3 : ℚ) * ((3 : ℚ) ^ n)))
theorem p043_base_valid : FirstCertificate p043_base (5 : ℚ) (fun n x => ((3 : ℚ) * x + (-4 : ℚ)) / (1 : ℚ)) := by
  apply linear_certificate p043_base (5 : ℚ) (fun n : ℕ => (1 : ℚ)) (fun n : ℕ => (3 : ℚ)) (fun n : ℕ => (-4 : ℚ))
  · norm_num [p043_base]
  · intro n; positivity
  · intro n
    simp only [p043_base, Nat.cast_add, Nat.cast_one, pow_succ, Nat.choose_succ_succ, Nat.choose_one_right, pow_add]
    ring
theorem p043_positive (n : ℕ) : 0 < p043_base n := by
  unfold p043_base
  positivity
theorem p043_valid : FirstCertificate p043 ((1 : ℚ) / 5) (fun n x => (1 : ℚ) * x / ((3 : ℚ) + (-4 : ℚ) * x)) := by
  have h := reciprocal_certificate p043_base_valid p043_positive (by intro n; positivity)
  simpa only [p043, p043_base] using h.1
theorem p043_domain : (∀ n : ℕ, (3 : ℚ) + (-4 : ℚ) * p043 n ≠ 0) ∧ (∀ n, p043 n ≠ 0) := by
  have h := reciprocal_certificate p043_base_valid p043_positive (by intro n; positivity)
  simpa only [p043, p043_base] using h.2
#print axioms p043_domain
theorem p043_unique (a : ℕ → ℚ) (ha : FirstCertificate a ((1 : ℚ) / 5) (fun n x => (1 : ℚ) * x / ((3 : ℚ) + (-4 : ℚ) * x))) :
    ∀ n, a n = p043 n := first_unique p043_valid ha
#print axioms p043_valid
#print axioms p043_unique

def p044 (n : ℕ) : ℚ := ((1 : ℚ) / ((1 : ℚ) + (((1 : ℚ) / 2) * ((2 : ℚ) ^ n))))
def p044_base (n : ℕ) : ℚ := ((1 : ℚ) + (((1 : ℚ) / 2) * ((2 : ℚ) ^ n)))
theorem p044_base_valid : FirstCertificate p044_base ((3 : ℚ) / 2) (fun n x => ((2 : ℚ) * x + (-1 : ℚ)) / (1 : ℚ)) := by
  apply linear_certificate p044_base ((3 : ℚ) / 2) (fun n : ℕ => (1 : ℚ)) (fun n : ℕ => (2 : ℚ)) (fun n : ℕ => (-1 : ℚ))
  · norm_num [p044_base]
  · intro n; positivity
  · intro n
    simp only [p044_base, Nat.cast_add, Nat.cast_one, pow_succ, Nat.choose_succ_succ, Nat.choose_one_right, pow_add]
    ring
theorem p044_positive (n : ℕ) : 0 < p044_base n := by
  unfold p044_base
  positivity
theorem p044_valid : FirstCertificate p044 ((2 : ℚ) / 3) (fun n x => (1 : ℚ) * x / ((2 : ℚ) + (-1 : ℚ) * x)) := by
  have h := reciprocal_certificate p044_base_valid p044_positive (by intro n; positivity)
  simpa only [p044, p044_base] using h.1
theorem p044_domain : (∀ n : ℕ, (2 : ℚ) + (-1 : ℚ) * p044 n ≠ 0) ∧ (∀ n, p044 n ≠ 0) := by
  have h := reciprocal_certificate p044_base_valid p044_positive (by intro n; positivity)
  simpa only [p044, p044_base] using h.2
#print axioms p044_domain
theorem p044_unique (a : ℕ → ℚ) (ha : FirstCertificate a ((2 : ℚ) / 3) (fun n x => (1 : ℚ) * x / ((2 : ℚ) + (-1 : ℚ) * x))) :
    ∀ n, a n = p044 n := first_unique p044_valid ha
#print axioms p044_valid
#print axioms p044_unique

def p045 (n : ℕ) : ℚ := ((1 : ℚ) / ((2 : ℚ) + ((3 : ℚ) * ((2 : ℚ) ^ n))))
def p045_base (n : ℕ) : ℚ := ((2 : ℚ) + ((3 : ℚ) * ((2 : ℚ) ^ n)))
theorem p045_base_valid : FirstCertificate p045_base (5 : ℚ) (fun n x => ((2 : ℚ) * x + (-2 : ℚ)) / (1 : ℚ)) := by
  apply linear_certificate p045_base (5 : ℚ) (fun n : ℕ => (1 : ℚ)) (fun n : ℕ => (2 : ℚ)) (fun n : ℕ => (-2 : ℚ))
  · norm_num [p045_base]
  · intro n; positivity
  · intro n
    simp only [p045_base, Nat.cast_add, Nat.cast_one, pow_succ, Nat.choose_succ_succ, Nat.choose_one_right, pow_add]
    ring
theorem p045_positive (n : ℕ) : 0 < p045_base n := by
  unfold p045_base
  positivity
theorem p045_valid : FirstCertificate p045 ((1 : ℚ) / 5) (fun n x => (1 : ℚ) * x / ((2 : ℚ) + (-2 : ℚ) * x)) := by
  have h := reciprocal_certificate p045_base_valid p045_positive (by intro n; positivity)
  simpa only [p045, p045_base] using h.1
theorem p045_domain : (∀ n : ℕ, (2 : ℚ) + (-2 : ℚ) * p045 n ≠ 0) ∧ (∀ n, p045 n ≠ 0) := by
  have h := reciprocal_certificate p045_base_valid p045_positive (by intro n; positivity)
  simpa only [p045, p045_base] using h.2
#print axioms p045_domain
theorem p045_unique (a : ℕ → ℚ) (ha : FirstCertificate a ((1 : ℚ) / 5) (fun n x => (1 : ℚ) * x / ((2 : ℚ) + (-2 : ℚ) * x))) :
    ∀ n, a n = p045 n := first_unique p045_valid ha
#print axioms p045_valid
#print axioms p045_unique

def p046 (n : ℕ) : ℚ := ((1 : ℚ) / (((((n : ℚ) + 1) * (((n : ℚ) + 1) + (2 : ℚ))) * ((1 : ℚ) + ((3 : ℚ) ^ n))) + (2 : ℚ)))
def p046_base (n : ℕ) : ℚ := (((((n : ℚ) + 1) * (((n : ℚ) + 1) + (2 : ℚ))) * ((1 : ℚ) + ((3 : ℚ) ^ n))) + (2 : ℚ))
theorem p046_base_valid : FirstCertificate p046_base (8 : ℚ) (fun n x => (((3 : ℚ) * ((((n : ℚ) + 1) + (1 : ℚ)) * ((((n : ℚ) + 1) + (1 : ℚ)) + (2 : ℚ)))) * x + (((-2 : ℚ) * (((n : ℚ) + 1) * (((n : ℚ) + 1) + (2 : ℚ))) * ((((n : ℚ) + 1) + (1 : ℚ)) * ((((n : ℚ) + 1) + (1 : ℚ)) + (2 : ℚ)))) + ((2 : ℚ) * ((((n : ℚ) + 1) * (((n : ℚ) + 1) + (2 : ℚ))) + ((-1 : ℚ) * ((3 : ℚ) * ((((n : ℚ) + 1) + (1 : ℚ)) * ((((n : ℚ) + 1) + (1 : ℚ)) + (2 : ℚ))))))))) / (((n : ℚ) + 1) * (((n : ℚ) + 1) + (2 : ℚ)))) := by
  apply linear_certificate p046_base (8 : ℚ) (fun n : ℕ => (((n : ℚ) + 1) * (((n : ℚ) + 1) + (2 : ℚ)))) (fun n : ℕ => ((3 : ℚ) * ((((n : ℚ) + 1) + (1 : ℚ)) * ((((n : ℚ) + 1) + (1 : ℚ)) + (2 : ℚ))))) (fun n : ℕ => (((-2 : ℚ) * (((n : ℚ) + 1) * (((n : ℚ) + 1) + (2 : ℚ))) * ((((n : ℚ) + 1) + (1 : ℚ)) * ((((n : ℚ) + 1) + (1 : ℚ)) + (2 : ℚ)))) + ((2 : ℚ) * ((((n : ℚ) + 1) * (((n : ℚ) + 1) + (2 : ℚ))) + ((-1 : ℚ) * ((3 : ℚ) * ((((n : ℚ) + 1) + (1 : ℚ)) * ((((n : ℚ) + 1) + (1 : ℚ)) + (2 : ℚ)))))))))
  · norm_num [p046_base]
  · intro n; positivity
  · intro n
    simp only [p046_base, Nat.cast_add, Nat.cast_one, pow_succ, Nat.choose_succ_succ, Nat.choose_one_right, pow_add]
    ring
theorem p046_positive (n : ℕ) : 0 < p046_base n := by
  unfold p046_base
  positivity
theorem p046_valid : FirstCertificate p046 ((1 : ℚ) / 8) (fun n x => (((n : ℚ) + 1) * (((n : ℚ) + 1) + (2 : ℚ))) * x / (((3 : ℚ) * ((((n : ℚ) + 1) + (1 : ℚ)) * ((((n : ℚ) + 1) + (1 : ℚ)) + (2 : ℚ)))) + (((-2 : ℚ) * (((n : ℚ) + 1) * (((n : ℚ) + 1) + (2 : ℚ))) * ((((n : ℚ) + 1) + (1 : ℚ)) * ((((n : ℚ) + 1) + (1 : ℚ)) + (2 : ℚ)))) + ((2 : ℚ) * ((((n : ℚ) + 1) * (((n : ℚ) + 1) + (2 : ℚ))) + ((-1 : ℚ) * ((3 : ℚ) * ((((n : ℚ) + 1) + (1 : ℚ)) * ((((n : ℚ) + 1) + (1 : ℚ)) + (2 : ℚ)))))))) * x)) := by
  have h := reciprocal_certificate p046_base_valid p046_positive (by intro n; positivity)
  simpa only [p046, p046_base] using h.1
theorem p046_domain : (∀ n : ℕ, ((3 : ℚ) * ((((n : ℚ) + 1) + (1 : ℚ)) * ((((n : ℚ) + 1) + (1 : ℚ)) + (2 : ℚ)))) + (((-2 : ℚ) * (((n : ℚ) + 1) * (((n : ℚ) + 1) + (2 : ℚ))) * ((((n : ℚ) + 1) + (1 : ℚ)) * ((((n : ℚ) + 1) + (1 : ℚ)) + (2 : ℚ)))) + ((2 : ℚ) * ((((n : ℚ) + 1) * (((n : ℚ) + 1) + (2 : ℚ))) + ((-1 : ℚ) * ((3 : ℚ) * ((((n : ℚ) + 1) + (1 : ℚ)) * ((((n : ℚ) + 1) + (1 : ℚ)) + (2 : ℚ)))))))) * p046 n ≠ 0) ∧ (∀ n, p046 n ≠ 0) := by
  have h := reciprocal_certificate p046_base_valid p046_positive (by intro n; positivity)
  simpa only [p046, p046_base] using h.2
#print axioms p046_domain
theorem p046_unique (a : ℕ → ℚ) (ha : FirstCertificate a ((1 : ℚ) / 8) (fun n x => (((n : ℚ) + 1) * (((n : ℚ) + 1) + (2 : ℚ))) * x / (((3 : ℚ) * ((((n : ℚ) + 1) + (1 : ℚ)) * ((((n : ℚ) + 1) + (1 : ℚ)) + (2 : ℚ)))) + (((-2 : ℚ) * (((n : ℚ) + 1) * (((n : ℚ) + 1) + (2 : ℚ))) * ((((n : ℚ) + 1) + (1 : ℚ)) * ((((n : ℚ) + 1) + (1 : ℚ)) + (2 : ℚ)))) + ((2 : ℚ) * ((((n : ℚ) + 1) * (((n : ℚ) + 1) + (2 : ℚ))) + ((-1 : ℚ) * ((3 : ℚ) * ((((n : ℚ) + 1) + (1 : ℚ)) * ((((n : ℚ) + 1) + (1 : ℚ)) + (2 : ℚ)))))))) * x))) :
    ∀ n, a n = p046 n := first_unique p046_valid ha
#print axioms p046_valid
#print axioms p046_unique

def p047 (n : ℕ) : ℚ := ((1 : ℚ) / (((((n : ℚ) + 1) * (((n : ℚ) + 1) + (2 : ℚ))) * ((1 : ℚ) + ((2 : ℚ) ^ n))) + (2 : ℚ)))
def p047_base (n : ℕ) : ℚ := (((((n : ℚ) + 1) * (((n : ℚ) + 1) + (2 : ℚ))) * ((1 : ℚ) + ((2 : ℚ) ^ n))) + (2 : ℚ))
theorem p047_base_valid : FirstCertificate p047_base (8 : ℚ) (fun n x => (((2 : ℚ) * ((((n : ℚ) + 1) + (1 : ℚ)) * ((((n : ℚ) + 1) + (1 : ℚ)) + (2 : ℚ)))) * x + (((-1 : ℚ) * (((n : ℚ) + 1) * (((n : ℚ) + 1) + (2 : ℚ))) * ((((n : ℚ) + 1) + (1 : ℚ)) * ((((n : ℚ) + 1) + (1 : ℚ)) + (2 : ℚ)))) + ((2 : ℚ) * ((((n : ℚ) + 1) * (((n : ℚ) + 1) + (2 : ℚ))) + ((-1 : ℚ) * ((2 : ℚ) * ((((n : ℚ) + 1) + (1 : ℚ)) * ((((n : ℚ) + 1) + (1 : ℚ)) + (2 : ℚ))))))))) / (((n : ℚ) + 1) * (((n : ℚ) + 1) + (2 : ℚ)))) := by
  apply linear_certificate p047_base (8 : ℚ) (fun n : ℕ => (((n : ℚ) + 1) * (((n : ℚ) + 1) + (2 : ℚ)))) (fun n : ℕ => ((2 : ℚ) * ((((n : ℚ) + 1) + (1 : ℚ)) * ((((n : ℚ) + 1) + (1 : ℚ)) + (2 : ℚ))))) (fun n : ℕ => (((-1 : ℚ) * (((n : ℚ) + 1) * (((n : ℚ) + 1) + (2 : ℚ))) * ((((n : ℚ) + 1) + (1 : ℚ)) * ((((n : ℚ) + 1) + (1 : ℚ)) + (2 : ℚ)))) + ((2 : ℚ) * ((((n : ℚ) + 1) * (((n : ℚ) + 1) + (2 : ℚ))) + ((-1 : ℚ) * ((2 : ℚ) * ((((n : ℚ) + 1) + (1 : ℚ)) * ((((n : ℚ) + 1) + (1 : ℚ)) + (2 : ℚ)))))))))
  · norm_num [p047_base]
  · intro n; positivity
  · intro n
    simp only [p047_base, Nat.cast_add, Nat.cast_one, pow_succ, Nat.choose_succ_succ, Nat.choose_one_right, pow_add]
    ring
theorem p047_positive (n : ℕ) : 0 < p047_base n := by
  unfold p047_base
  positivity
theorem p047_valid : FirstCertificate p047 ((1 : ℚ) / 8) (fun n x => (((n : ℚ) + 1) * (((n : ℚ) + 1) + (2 : ℚ))) * x / (((2 : ℚ) * ((((n : ℚ) + 1) + (1 : ℚ)) * ((((n : ℚ) + 1) + (1 : ℚ)) + (2 : ℚ)))) + (((-1 : ℚ) * (((n : ℚ) + 1) * (((n : ℚ) + 1) + (2 : ℚ))) * ((((n : ℚ) + 1) + (1 : ℚ)) * ((((n : ℚ) + 1) + (1 : ℚ)) + (2 : ℚ)))) + ((2 : ℚ) * ((((n : ℚ) + 1) * (((n : ℚ) + 1) + (2 : ℚ))) + ((-1 : ℚ) * ((2 : ℚ) * ((((n : ℚ) + 1) + (1 : ℚ)) * ((((n : ℚ) + 1) + (1 : ℚ)) + (2 : ℚ)))))))) * x)) := by
  have h := reciprocal_certificate p047_base_valid p047_positive (by intro n; positivity)
  simpa only [p047, p047_base] using h.1
theorem p047_domain : (∀ n : ℕ, ((2 : ℚ) * ((((n : ℚ) + 1) + (1 : ℚ)) * ((((n : ℚ) + 1) + (1 : ℚ)) + (2 : ℚ)))) + (((-1 : ℚ) * (((n : ℚ) + 1) * (((n : ℚ) + 1) + (2 : ℚ))) * ((((n : ℚ) + 1) + (1 : ℚ)) * ((((n : ℚ) + 1) + (1 : ℚ)) + (2 : ℚ)))) + ((2 : ℚ) * ((((n : ℚ) + 1) * (((n : ℚ) + 1) + (2 : ℚ))) + ((-1 : ℚ) * ((2 : ℚ) * ((((n : ℚ) + 1) + (1 : ℚ)) * ((((n : ℚ) + 1) + (1 : ℚ)) + (2 : ℚ)))))))) * p047 n ≠ 0) ∧ (∀ n, p047 n ≠ 0) := by
  have h := reciprocal_certificate p047_base_valid p047_positive (by intro n; positivity)
  simpa only [p047, p047_base] using h.2
#print axioms p047_domain
theorem p047_unique (a : ℕ → ℚ) (ha : FirstCertificate a ((1 : ℚ) / 8) (fun n x => (((n : ℚ) + 1) * (((n : ℚ) + 1) + (2 : ℚ))) * x / (((2 : ℚ) * ((((n : ℚ) + 1) + (1 : ℚ)) * ((((n : ℚ) + 1) + (1 : ℚ)) + (2 : ℚ)))) + (((-1 : ℚ) * (((n : ℚ) + 1) * (((n : ℚ) + 1) + (2 : ℚ))) * ((((n : ℚ) + 1) + (1 : ℚ)) * ((((n : ℚ) + 1) + (1 : ℚ)) + (2 : ℚ)))) + ((2 : ℚ) * ((((n : ℚ) + 1) * (((n : ℚ) + 1) + (2 : ℚ))) + ((-1 : ℚ) * ((2 : ℚ) * ((((n : ℚ) + 1) + (1 : ℚ)) * ((((n : ℚ) + 1) + (1 : ℚ)) + (2 : ℚ)))))))) * x))) :
    ∀ n, a n = p047 n := first_unique p047_valid ha
#print axioms p047_valid
#print axioms p047_unique

def p048 (n : ℕ) : ℚ := ((1 : ℚ) / (((((n : ℚ) + 1) * (((n : ℚ) + 1) + (2 : ℚ))) * ((1 : ℚ) + ((2 : ℚ) ^ n))) + (1 : ℚ)))
def p048_base (n : ℕ) : ℚ := (((((n : ℚ) + 1) * (((n : ℚ) + 1) + (2 : ℚ))) * ((1 : ℚ) + ((2 : ℚ) ^ n))) + (1 : ℚ))
theorem p048_base_valid : FirstCertificate p048_base (7 : ℚ) (fun n x => (((2 : ℚ) * ((((n : ℚ) + 1) + (1 : ℚ)) * ((((n : ℚ) + 1) + (1 : ℚ)) + (2 : ℚ)))) * x + (((-1 : ℚ) * (((n : ℚ) + 1) * (((n : ℚ) + 1) + (2 : ℚ))) * ((((n : ℚ) + 1) + (1 : ℚ)) * ((((n : ℚ) + 1) + (1 : ℚ)) + (2 : ℚ)))) + ((((n : ℚ) + 1) * (((n : ℚ) + 1) + (2 : ℚ))) + ((-1 : ℚ) * ((2 : ℚ) * ((((n : ℚ) + 1) + (1 : ℚ)) * ((((n : ℚ) + 1) + (1 : ℚ)) + (2 : ℚ)))))))) / (((n : ℚ) + 1) * (((n : ℚ) + 1) + (2 : ℚ)))) := by
  apply linear_certificate p048_base (7 : ℚ) (fun n : ℕ => (((n : ℚ) + 1) * (((n : ℚ) + 1) + (2 : ℚ)))) (fun n : ℕ => ((2 : ℚ) * ((((n : ℚ) + 1) + (1 : ℚ)) * ((((n : ℚ) + 1) + (1 : ℚ)) + (2 : ℚ))))) (fun n : ℕ => (((-1 : ℚ) * (((n : ℚ) + 1) * (((n : ℚ) + 1) + (2 : ℚ))) * ((((n : ℚ) + 1) + (1 : ℚ)) * ((((n : ℚ) + 1) + (1 : ℚ)) + (2 : ℚ)))) + ((((n : ℚ) + 1) * (((n : ℚ) + 1) + (2 : ℚ))) + ((-1 : ℚ) * ((2 : ℚ) * ((((n : ℚ) + 1) + (1 : ℚ)) * ((((n : ℚ) + 1) + (1 : ℚ)) + (2 : ℚ))))))))
  · norm_num [p048_base]
  · intro n; positivity
  · intro n
    simp only [p048_base, Nat.cast_add, Nat.cast_one, pow_succ, Nat.choose_succ_succ, Nat.choose_one_right, pow_add]
    ring
theorem p048_positive (n : ℕ) : 0 < p048_base n := by
  unfold p048_base
  positivity
theorem p048_valid : FirstCertificate p048 ((1 : ℚ) / 7) (fun n x => (((n : ℚ) + 1) * (((n : ℚ) + 1) + (2 : ℚ))) * x / (((2 : ℚ) * ((((n : ℚ) + 1) + (1 : ℚ)) * ((((n : ℚ) + 1) + (1 : ℚ)) + (2 : ℚ)))) + (((-1 : ℚ) * (((n : ℚ) + 1) * (((n : ℚ) + 1) + (2 : ℚ))) * ((((n : ℚ) + 1) + (1 : ℚ)) * ((((n : ℚ) + 1) + (1 : ℚ)) + (2 : ℚ)))) + ((((n : ℚ) + 1) * (((n : ℚ) + 1) + (2 : ℚ))) + ((-1 : ℚ) * ((2 : ℚ) * ((((n : ℚ) + 1) + (1 : ℚ)) * ((((n : ℚ) + 1) + (1 : ℚ)) + (2 : ℚ))))))) * x)) := by
  have h := reciprocal_certificate p048_base_valid p048_positive (by intro n; positivity)
  simpa only [p048, p048_base] using h.1
theorem p048_domain : (∀ n : ℕ, ((2 : ℚ) * ((((n : ℚ) + 1) + (1 : ℚ)) * ((((n : ℚ) + 1) + (1 : ℚ)) + (2 : ℚ)))) + (((-1 : ℚ) * (((n : ℚ) + 1) * (((n : ℚ) + 1) + (2 : ℚ))) * ((((n : ℚ) + 1) + (1 : ℚ)) * ((((n : ℚ) + 1) + (1 : ℚ)) + (2 : ℚ)))) + ((((n : ℚ) + 1) * (((n : ℚ) + 1) + (2 : ℚ))) + ((-1 : ℚ) * ((2 : ℚ) * ((((n : ℚ) + 1) + (1 : ℚ)) * ((((n : ℚ) + 1) + (1 : ℚ)) + (2 : ℚ))))))) * p048 n ≠ 0) ∧ (∀ n, p048 n ≠ 0) := by
  have h := reciprocal_certificate p048_base_valid p048_positive (by intro n; positivity)
  simpa only [p048, p048_base] using h.2
#print axioms p048_domain
theorem p048_unique (a : ℕ → ℚ) (ha : FirstCertificate a ((1 : ℚ) / 7) (fun n x => (((n : ℚ) + 1) * (((n : ℚ) + 1) + (2 : ℚ))) * x / (((2 : ℚ) * ((((n : ℚ) + 1) + (1 : ℚ)) * ((((n : ℚ) + 1) + (1 : ℚ)) + (2 : ℚ)))) + (((-1 : ℚ) * (((n : ℚ) + 1) * (((n : ℚ) + 1) + (2 : ℚ))) * ((((n : ℚ) + 1) + (1 : ℚ)) * ((((n : ℚ) + 1) + (1 : ℚ)) + (2 : ℚ)))) + ((((n : ℚ) + 1) * (((n : ℚ) + 1) + (2 : ℚ))) + ((-1 : ℚ) * ((2 : ℚ) * ((((n : ℚ) + 1) + (1 : ℚ)) * ((((n : ℚ) + 1) + (1 : ℚ)) + (2 : ℚ))))))) * x))) :
    ∀ n, a n = p048 n := first_unique p048_valid ha
#print axioms p048_valid
#print axioms p048_unique

def p049 (n : ℕ) : ℚ := ((1 : ℚ) / (((((n : ℚ) + 1) * (((n : ℚ) + 1) + (2 : ℚ))) * ((2 : ℚ) + ((3 : ℚ) ^ n))) + (1 : ℚ)))
def p049_base (n : ℕ) : ℚ := (((((n : ℚ) + 1) * (((n : ℚ) + 1) + (2 : ℚ))) * ((2 : ℚ) + ((3 : ℚ) ^ n))) + (1 : ℚ))
theorem p049_base_valid : FirstCertificate p049_base (10 : ℚ) (fun n x => (((3 : ℚ) * ((((n : ℚ) + 1) + (1 : ℚ)) * ((((n : ℚ) + 1) + (1 : ℚ)) + (2 : ℚ)))) * x + (((-4 : ℚ) * (((n : ℚ) + 1) * (((n : ℚ) + 1) + (2 : ℚ))) * ((((n : ℚ) + 1) + (1 : ℚ)) * ((((n : ℚ) + 1) + (1 : ℚ)) + (2 : ℚ)))) + ((((n : ℚ) + 1) * (((n : ℚ) + 1) + (2 : ℚ))) + ((-1 : ℚ) * ((3 : ℚ) * ((((n : ℚ) + 1) + (1 : ℚ)) * ((((n : ℚ) + 1) + (1 : ℚ)) + (2 : ℚ)))))))) / (((n : ℚ) + 1) * (((n : ℚ) + 1) + (2 : ℚ)))) := by
  apply linear_certificate p049_base (10 : ℚ) (fun n : ℕ => (((n : ℚ) + 1) * (((n : ℚ) + 1) + (2 : ℚ)))) (fun n : ℕ => ((3 : ℚ) * ((((n : ℚ) + 1) + (1 : ℚ)) * ((((n : ℚ) + 1) + (1 : ℚ)) + (2 : ℚ))))) (fun n : ℕ => (((-4 : ℚ) * (((n : ℚ) + 1) * (((n : ℚ) + 1) + (2 : ℚ))) * ((((n : ℚ) + 1) + (1 : ℚ)) * ((((n : ℚ) + 1) + (1 : ℚ)) + (2 : ℚ)))) + ((((n : ℚ) + 1) * (((n : ℚ) + 1) + (2 : ℚ))) + ((-1 : ℚ) * ((3 : ℚ) * ((((n : ℚ) + 1) + (1 : ℚ)) * ((((n : ℚ) + 1) + (1 : ℚ)) + (2 : ℚ))))))))
  · norm_num [p049_base]
  · intro n; positivity
  · intro n
    simp only [p049_base, Nat.cast_add, Nat.cast_one, pow_succ, Nat.choose_succ_succ, Nat.choose_one_right, pow_add]
    ring
theorem p049_positive (n : ℕ) : 0 < p049_base n := by
  unfold p049_base
  positivity
theorem p049_valid : FirstCertificate p049 ((1 : ℚ) / 10) (fun n x => (((n : ℚ) + 1) * (((n : ℚ) + 1) + (2 : ℚ))) * x / (((3 : ℚ) * ((((n : ℚ) + 1) + (1 : ℚ)) * ((((n : ℚ) + 1) + (1 : ℚ)) + (2 : ℚ)))) + (((-4 : ℚ) * (((n : ℚ) + 1) * (((n : ℚ) + 1) + (2 : ℚ))) * ((((n : ℚ) + 1) + (1 : ℚ)) * ((((n : ℚ) + 1) + (1 : ℚ)) + (2 : ℚ)))) + ((((n : ℚ) + 1) * (((n : ℚ) + 1) + (2 : ℚ))) + ((-1 : ℚ) * ((3 : ℚ) * ((((n : ℚ) + 1) + (1 : ℚ)) * ((((n : ℚ) + 1) + (1 : ℚ)) + (2 : ℚ))))))) * x)) := by
  have h := reciprocal_certificate p049_base_valid p049_positive (by intro n; positivity)
  simpa only [p049, p049_base] using h.1
theorem p049_domain : (∀ n : ℕ, ((3 : ℚ) * ((((n : ℚ) + 1) + (1 : ℚ)) * ((((n : ℚ) + 1) + (1 : ℚ)) + (2 : ℚ)))) + (((-4 : ℚ) * (((n : ℚ) + 1) * (((n : ℚ) + 1) + (2 : ℚ))) * ((((n : ℚ) + 1) + (1 : ℚ)) * ((((n : ℚ) + 1) + (1 : ℚ)) + (2 : ℚ)))) + ((((n : ℚ) + 1) * (((n : ℚ) + 1) + (2 : ℚ))) + ((-1 : ℚ) * ((3 : ℚ) * ((((n : ℚ) + 1) + (1 : ℚ)) * ((((n : ℚ) + 1) + (1 : ℚ)) + (2 : ℚ))))))) * p049 n ≠ 0) ∧ (∀ n, p049 n ≠ 0) := by
  have h := reciprocal_certificate p049_base_valid p049_positive (by intro n; positivity)
  simpa only [p049, p049_base] using h.2
#print axioms p049_domain
theorem p049_unique (a : ℕ → ℚ) (ha : FirstCertificate a ((1 : ℚ) / 10) (fun n x => (((n : ℚ) + 1) * (((n : ℚ) + 1) + (2 : ℚ))) * x / (((3 : ℚ) * ((((n : ℚ) + 1) + (1 : ℚ)) * ((((n : ℚ) + 1) + (1 : ℚ)) + (2 : ℚ)))) + (((-4 : ℚ) * (((n : ℚ) + 1) * (((n : ℚ) + 1) + (2 : ℚ))) * ((((n : ℚ) + 1) + (1 : ℚ)) * ((((n : ℚ) + 1) + (1 : ℚ)) + (2 : ℚ)))) + ((((n : ℚ) + 1) * (((n : ℚ) + 1) + (2 : ℚ))) + ((-1 : ℚ) * ((3 : ℚ) * ((((n : ℚ) + 1) + (1 : ℚ)) * ((((n : ℚ) + 1) + (1 : ℚ)) + (2 : ℚ))))))) * x))) :
    ∀ n, a n = p049 n := first_unique p049_valid ha
#print axioms p049_valid
#print axioms p049_unique

def p050 (n : ℕ) : ℚ := ((1 : ℚ) / (((((n : ℚ) + 1) * (((n : ℚ) + 1) + (2 : ℚ))) * ((3 : ℚ) + ((2 : ℚ) * ((2 : ℚ) ^ n)))) + (1 : ℚ)))
def p050_base (n : ℕ) : ℚ := (((((n : ℚ) + 1) * (((n : ℚ) + 1) + (2 : ℚ))) * ((3 : ℚ) + ((2 : ℚ) * ((2 : ℚ) ^ n)))) + (1 : ℚ))
theorem p050_base_valid : FirstCertificate p050_base (16 : ℚ) (fun n x => (((2 : ℚ) * ((((n : ℚ) + 1) + (1 : ℚ)) * ((((n : ℚ) + 1) + (1 : ℚ)) + (2 : ℚ)))) * x + (((-3 : ℚ) * (((n : ℚ) + 1) * (((n : ℚ) + 1) + (2 : ℚ))) * ((((n : ℚ) + 1) + (1 : ℚ)) * ((((n : ℚ) + 1) + (1 : ℚ)) + (2 : ℚ)))) + ((((n : ℚ) + 1) * (((n : ℚ) + 1) + (2 : ℚ))) + ((-1 : ℚ) * ((2 : ℚ) * ((((n : ℚ) + 1) + (1 : ℚ)) * ((((n : ℚ) + 1) + (1 : ℚ)) + (2 : ℚ)))))))) / (((n : ℚ) + 1) * (((n : ℚ) + 1) + (2 : ℚ)))) := by
  apply linear_certificate p050_base (16 : ℚ) (fun n : ℕ => (((n : ℚ) + 1) * (((n : ℚ) + 1) + (2 : ℚ)))) (fun n : ℕ => ((2 : ℚ) * ((((n : ℚ) + 1) + (1 : ℚ)) * ((((n : ℚ) + 1) + (1 : ℚ)) + (2 : ℚ))))) (fun n : ℕ => (((-3 : ℚ) * (((n : ℚ) + 1) * (((n : ℚ) + 1) + (2 : ℚ))) * ((((n : ℚ) + 1) + (1 : ℚ)) * ((((n : ℚ) + 1) + (1 : ℚ)) + (2 : ℚ)))) + ((((n : ℚ) + 1) * (((n : ℚ) + 1) + (2 : ℚ))) + ((-1 : ℚ) * ((2 : ℚ) * ((((n : ℚ) + 1) + (1 : ℚ)) * ((((n : ℚ) + 1) + (1 : ℚ)) + (2 : ℚ))))))))
  · norm_num [p050_base]
  · intro n; positivity
  · intro n
    simp only [p050_base, Nat.cast_add, Nat.cast_one, pow_succ, Nat.choose_succ_succ, Nat.choose_one_right, pow_add]
    ring
theorem p050_positive (n : ℕ) : 0 < p050_base n := by
  unfold p050_base
  positivity
theorem p050_valid : FirstCertificate p050 ((1 : ℚ) / 16) (fun n x => (((n : ℚ) + 1) * (((n : ℚ) + 1) + (2 : ℚ))) * x / (((2 : ℚ) * ((((n : ℚ) + 1) + (1 : ℚ)) * ((((n : ℚ) + 1) + (1 : ℚ)) + (2 : ℚ)))) + (((-3 : ℚ) * (((n : ℚ) + 1) * (((n : ℚ) + 1) + (2 : ℚ))) * ((((n : ℚ) + 1) + (1 : ℚ)) * ((((n : ℚ) + 1) + (1 : ℚ)) + (2 : ℚ)))) + ((((n : ℚ) + 1) * (((n : ℚ) + 1) + (2 : ℚ))) + ((-1 : ℚ) * ((2 : ℚ) * ((((n : ℚ) + 1) + (1 : ℚ)) * ((((n : ℚ) + 1) + (1 : ℚ)) + (2 : ℚ))))))) * x)) := by
  have h := reciprocal_certificate p050_base_valid p050_positive (by intro n; positivity)
  simpa only [p050, p050_base] using h.1
theorem p050_domain : (∀ n : ℕ, ((2 : ℚ) * ((((n : ℚ) + 1) + (1 : ℚ)) * ((((n : ℚ) + 1) + (1 : ℚ)) + (2 : ℚ)))) + (((-3 : ℚ) * (((n : ℚ) + 1) * (((n : ℚ) + 1) + (2 : ℚ))) * ((((n : ℚ) + 1) + (1 : ℚ)) * ((((n : ℚ) + 1) + (1 : ℚ)) + (2 : ℚ)))) + ((((n : ℚ) + 1) * (((n : ℚ) + 1) + (2 : ℚ))) + ((-1 : ℚ) * ((2 : ℚ) * ((((n : ℚ) + 1) + (1 : ℚ)) * ((((n : ℚ) + 1) + (1 : ℚ)) + (2 : ℚ))))))) * p050 n ≠ 0) ∧ (∀ n, p050 n ≠ 0) := by
  have h := reciprocal_certificate p050_base_valid p050_positive (by intro n; positivity)
  simpa only [p050, p050_base] using h.2
#print axioms p050_domain
theorem p050_unique (a : ℕ → ℚ) (ha : FirstCertificate a ((1 : ℚ) / 16) (fun n x => (((n : ℚ) + 1) * (((n : ℚ) + 1) + (2 : ℚ))) * x / (((2 : ℚ) * ((((n : ℚ) + 1) + (1 : ℚ)) * ((((n : ℚ) + 1) + (1 : ℚ)) + (2 : ℚ)))) + (((-3 : ℚ) * (((n : ℚ) + 1) * (((n : ℚ) + 1) + (2 : ℚ))) * ((((n : ℚ) + 1) + (1 : ℚ)) * ((((n : ℚ) + 1) + (1 : ℚ)) + (2 : ℚ)))) + ((((n : ℚ) + 1) * (((n : ℚ) + 1) + (2 : ℚ))) + ((-1 : ℚ) * ((2 : ℚ) * ((((n : ℚ) + 1) + (1 : ℚ)) * ((((n : ℚ) + 1) + (1 : ℚ)) + (2 : ℚ))))))) * x))) :
    ∀ n, a n = p050 n := first_unique p050_valid ha
#print axioms p050_valid
#print axioms p050_unique

end Recurrence
