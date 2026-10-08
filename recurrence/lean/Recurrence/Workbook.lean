import Recurrence.Theory

namespace Recurrence

def w101 (n : ℕ) : ℚ := (9 : ℚ)
theorem w101_base_valid : FirstCertificate w101 (9 : ℚ) (fun n x => ((1 : ℚ) * x + (0 : ℚ)) / (1 : ℚ)) := by
  apply linear_certificate w101 (9 : ℚ) (fun n : ℕ => (1 : ℚ)) (fun n : ℕ => (1 : ℚ)) (fun n : ℕ => (0 : ℚ))
  · norm_num [w101]
  · intro n; positivity
  · intro n
    simp only [w101, Nat.cast_add, Nat.cast_one, pow_succ, pow_add] at *
    ring
theorem w101_valid : FirstCertificate w101 (9 : ℚ) (fun n x => ((1 : ℚ) * x + (0 : ℚ)) / (1 : ℚ)) := w101_base_valid
theorem w101_unique (a : ℕ → ℚ) (ha : FirstCertificate a (9 : ℚ) (fun n x => ((1 : ℚ) * x + (0 : ℚ)) / (1 : ℚ))) :
    ∀ n, a n = w101 n := first_unique w101_valid ha
#print axioms w101_valid
#print axioms w101_unique

def w102 (n : ℕ) : ℚ := (6 : ℚ)
theorem w102_base_valid : FirstCertificate w102 (6 : ℚ) (fun n x => ((1 : ℚ) * x + (0 : ℚ)) / (1 : ℚ)) := by
  apply linear_certificate w102 (6 : ℚ) (fun n : ℕ => (1 : ℚ)) (fun n : ℕ => (1 : ℚ)) (fun n : ℕ => (0 : ℚ))
  · norm_num [w102]
  · intro n; positivity
  · intro n
    simp only [w102, Nat.cast_add, Nat.cast_one, pow_succ, pow_add] at *
    ring
theorem w102_valid : FirstCertificate w102 (6 : ℚ) (fun n x => ((1 : ℚ) * x + (0 : ℚ)) / (1 : ℚ)) := w102_base_valid
theorem w102_unique (a : ℕ → ℚ) (ha : FirstCertificate a (6 : ℚ) (fun n x => ((1 : ℚ) * x + (0 : ℚ)) / (1 : ℚ))) :
    ∀ n, a n = w102 n := first_unique w102_valid ha
#print axioms w102_valid
#print axioms w102_unique

def w103 (n : ℕ) : ℚ := (8 : ℚ)
theorem w103_base_valid : FirstCertificate w103 (8 : ℚ) (fun n x => ((1 : ℚ) * x + (0 : ℚ)) / (1 : ℚ)) := by
  apply linear_certificate w103 (8 : ℚ) (fun n : ℕ => (1 : ℚ)) (fun n : ℕ => (1 : ℚ)) (fun n : ℕ => (0 : ℚ))
  · norm_num [w103]
  · intro n; positivity
  · intro n
    simp only [w103, Nat.cast_add, Nat.cast_one, pow_succ, pow_add] at *
    ring
theorem w103_valid : FirstCertificate w103 (8 : ℚ) (fun n x => ((1 : ℚ) * x + (0 : ℚ)) / (1 : ℚ)) := w103_base_valid
theorem w103_unique (a : ℕ → ℚ) (ha : FirstCertificate a (8 : ℚ) (fun n x => ((1 : ℚ) * x + (0 : ℚ)) / (1 : ℚ))) :
    ∀ n, a n = w103 n := first_unique w103_valid ha
#print axioms w103_valid
#print axioms w103_unique

def w104 (n : ℕ) : ℚ := ((6 : ℚ) * ((-2 : ℚ) ^ n))
theorem w104_base_valid : FirstCertificate w104 (6 : ℚ) (fun n x => ((-2 : ℚ) * x + (0 : ℚ)) / (1 : ℚ)) := by
  apply linear_certificate w104 (6 : ℚ) (fun n : ℕ => (1 : ℚ)) (fun n : ℕ => (-2 : ℚ)) (fun n : ℕ => (0 : ℚ))
  · norm_num [w104]
  · intro n; positivity
  · intro n
    simp only [w104, Nat.cast_add, Nat.cast_one, pow_succ, pow_add] at *
    ring
theorem w104_valid : FirstCertificate w104 (6 : ℚ) (fun n x => ((-2 : ℚ) * x + (0 : ℚ)) / (1 : ℚ)) := w104_base_valid
theorem w104_unique (a : ℕ → ℚ) (ha : FirstCertificate a (6 : ℚ) (fun n x => ((-2 : ℚ) * x + (0 : ℚ)) / (1 : ℚ))) :
    ∀ n, a n = w104 n := first_unique w104_valid ha
#print axioms w104_valid
#print axioms w104_unique

def w105 (n : ℕ) : ℚ := ((4 : ℚ) * ((-2 : ℚ) ^ n))
theorem w105_base_valid : FirstCertificate w105 (4 : ℚ) (fun n x => ((-2 : ℚ) * x + (0 : ℚ)) / (1 : ℚ)) := by
  apply linear_certificate w105 (4 : ℚ) (fun n : ℕ => (1 : ℚ)) (fun n : ℕ => (-2 : ℚ)) (fun n : ℕ => (0 : ℚ))
  · norm_num [w105]
  · intro n; positivity
  · intro n
    simp only [w105, Nat.cast_add, Nat.cast_one, pow_succ, pow_add] at *
    ring
theorem w105_valid : FirstCertificate w105 (4 : ℚ) (fun n x => ((-2 : ℚ) * x + (0 : ℚ)) / (1 : ℚ)) := w105_base_valid
theorem w105_unique (a : ℕ → ℚ) (ha : FirstCertificate a (4 : ℚ) (fun n x => ((-2 : ℚ) * x + (0 : ℚ)) / (1 : ℚ))) :
    ∀ n, a n = w105 n := first_unique w105_valid ha
#print axioms w105_valid
#print axioms w105_unique

def w106 (n : ℕ) : ℚ := ((9 : ℚ) * ((-1 : ℚ) ^ n))
theorem w106_base_valid : FirstCertificate w106 (9 : ℚ) (fun n x => ((-1 : ℚ) * x + (0 : ℚ)) / (1 : ℚ)) := by
  apply linear_certificate w106 (9 : ℚ) (fun n : ℕ => (1 : ℚ)) (fun n : ℕ => (-1 : ℚ)) (fun n : ℕ => (0 : ℚ))
  · norm_num [w106]
  · intro n; positivity
  · intro n
    simp only [w106, Nat.cast_add, Nat.cast_one, pow_succ, pow_add] at *
    ring
theorem w106_valid : FirstCertificate w106 (9 : ℚ) (fun n x => ((-1 : ℚ) * x + (0 : ℚ)) / (1 : ℚ)) := w106_base_valid
theorem w106_unique (a : ℕ → ℚ) (ha : FirstCertificate a (9 : ℚ) (fun n x => ((-1 : ℚ) * x + (0 : ℚ)) / (1 : ℚ))) :
    ∀ n, a n = w106 n := first_unique w106_valid ha
#print axioms w106_valid
#print axioms w106_unique

def w107 (n : ℕ) : ℚ := ((5 : ℚ) * ((-1 : ℚ) ^ n))
theorem w107_base_valid : FirstCertificate w107 (5 : ℚ) (fun n x => ((-1 : ℚ) * x + (0 : ℚ)) / (1 : ℚ)) := by
  apply linear_certificate w107 (5 : ℚ) (fun n : ℕ => (1 : ℚ)) (fun n : ℕ => (-1 : ℚ)) (fun n : ℕ => (0 : ℚ))
  · norm_num [w107]
  · intro n; positivity
  · intro n
    simp only [w107, Nat.cast_add, Nat.cast_one, pow_succ, pow_add] at *
    ring
theorem w107_valid : FirstCertificate w107 (5 : ℚ) (fun n x => ((-1 : ℚ) * x + (0 : ℚ)) / (1 : ℚ)) := w107_base_valid
theorem w107_unique (a : ℕ → ℚ) (ha : FirstCertificate a (5 : ℚ) (fun n x => ((-1 : ℚ) * x + (0 : ℚ)) / (1 : ℚ))) :
    ∀ n, a n = w107 n := first_unique w107_valid ha
#print axioms w107_valid
#print axioms w107_unique

def w108 (n : ℕ) : ℚ := ((4 : ℚ) * ((2 : ℚ) ^ n))
theorem w108_base_valid : FirstCertificate w108 (4 : ℚ) (fun n x => ((2 : ℚ) * x + (0 : ℚ)) / (1 : ℚ)) := by
  apply linear_certificate w108 (4 : ℚ) (fun n : ℕ => (1 : ℚ)) (fun n : ℕ => (2 : ℚ)) (fun n : ℕ => (0 : ℚ))
  · norm_num [w108]
  · intro n; positivity
  · intro n
    simp only [w108, Nat.cast_add, Nat.cast_one, pow_succ, pow_add] at *
    ring
theorem w108_valid : FirstCertificate w108 (4 : ℚ) (fun n x => ((2 : ℚ) * x + (0 : ℚ)) / (1 : ℚ)) := w108_base_valid
theorem w108_unique (a : ℕ → ℚ) (ha : FirstCertificate a (4 : ℚ) (fun n x => ((2 : ℚ) * x + (0 : ℚ)) / (1 : ℚ))) :
    ∀ n, a n = w108 n := first_unique w108_valid ha
#print axioms w108_valid
#print axioms w108_unique

def w109 (n : ℕ) : ℚ := ((6 : ℚ) * ((2 : ℚ) ^ n))
theorem w109_base_valid : FirstCertificate w109 (6 : ℚ) (fun n x => ((2 : ℚ) * x + (0 : ℚ)) / (1 : ℚ)) := by
  apply linear_certificate w109 (6 : ℚ) (fun n : ℕ => (1 : ℚ)) (fun n : ℕ => (2 : ℚ)) (fun n : ℕ => (0 : ℚ))
  · norm_num [w109]
  · intro n; positivity
  · intro n
    simp only [w109, Nat.cast_add, Nat.cast_one, pow_succ, pow_add] at *
    ring
theorem w109_valid : FirstCertificate w109 (6 : ℚ) (fun n x => ((2 : ℚ) * x + (0 : ℚ)) / (1 : ℚ)) := w109_base_valid
theorem w109_unique (a : ℕ → ℚ) (ha : FirstCertificate a (6 : ℚ) (fun n x => ((2 : ℚ) * x + (0 : ℚ)) / (1 : ℚ))) :
    ∀ n, a n = w109 n := first_unique w109_valid ha
#print axioms w109_valid
#print axioms w109_unique

def w110 (n : ℕ) : ℚ := ((6 : ℚ) * ((3 : ℚ) ^ n))
theorem w110_base_valid : FirstCertificate w110 (6 : ℚ) (fun n x => ((3 : ℚ) * x + (0 : ℚ)) / (1 : ℚ)) := by
  apply linear_certificate w110 (6 : ℚ) (fun n : ℕ => (1 : ℚ)) (fun n : ℕ => (3 : ℚ)) (fun n : ℕ => (0 : ℚ))
  · norm_num [w110]
  · intro n; positivity
  · intro n
    simp only [w110, Nat.cast_add, Nat.cast_one, pow_succ, pow_add] at *
    ring
theorem w110_valid : FirstCertificate w110 (6 : ℚ) (fun n x => ((3 : ℚ) * x + (0 : ℚ)) / (1 : ℚ)) := w110_base_valid
theorem w110_unique (a : ℕ → ℚ) (ha : FirstCertificate a (6 : ℚ) (fun n x => ((3 : ℚ) * x + (0 : ℚ)) / (1 : ℚ))) :
    ∀ n, a n = w110 n := first_unique w110_valid ha
#print axioms w110_valid
#print axioms w110_unique

def w111 (n : ℕ) : ℚ := ((5 : ℚ) * ((3 : ℚ) ^ n))
theorem w111_base_valid : FirstCertificate w111 (5 : ℚ) (fun n x => ((3 : ℚ) * x + (0 : ℚ)) / (1 : ℚ)) := by
  apply linear_certificate w111 (5 : ℚ) (fun n : ℕ => (1 : ℚ)) (fun n : ℕ => (3 : ℚ)) (fun n : ℕ => (0 : ℚ))
  · norm_num [w111]
  · intro n; positivity
  · intro n
    simp only [w111, Nat.cast_add, Nat.cast_one, pow_succ, pow_add] at *
    ring
theorem w111_valid : FirstCertificate w111 (5 : ℚ) (fun n x => ((3 : ℚ) * x + (0 : ℚ)) / (1 : ℚ)) := w111_base_valid
theorem w111_unique (a : ℕ → ℚ) (ha : FirstCertificate a (5 : ℚ) (fun n x => ((3 : ℚ) * x + (0 : ℚ)) / (1 : ℚ))) :
    ∀ n, a n = w111 n := first_unique w111_valid ha
#print axioms w111_valid
#print axioms w111_unique

def w112 (n : ℕ) : ℚ := ((8 : ℚ) * (((1 : ℚ) / 2) ^ n))
theorem w112_base_valid : FirstCertificate w112 (8 : ℚ) (fun n x => (((1 : ℚ) / 2) * x + (0 : ℚ)) / (1 : ℚ)) := by
  apply linear_certificate w112 (8 : ℚ) (fun n : ℕ => (1 : ℚ)) (fun n : ℕ => ((1 : ℚ) / 2)) (fun n : ℕ => (0 : ℚ))
  · norm_num [w112]
  · intro n; positivity
  · intro n
    simp only [w112, Nat.cast_add, Nat.cast_one, pow_succ, pow_add] at *
    ring
theorem w112_valid : FirstCertificate w112 (8 : ℚ) (fun n x => (((1 : ℚ) / 2) * x + (0 : ℚ)) / (1 : ℚ)) := w112_base_valid
theorem w112_unique (a : ℕ → ℚ) (ha : FirstCertificate a (8 : ℚ) (fun n x => (((1 : ℚ) / 2) * x + (0 : ℚ)) / (1 : ℚ))) :
    ∀ n, a n = w112 n := first_unique w112_valid ha
#print axioms w112_valid
#print axioms w112_unique

def w113 (n : ℕ) : ℚ := ((6 : ℚ) * (((1 : ℚ) / 2) ^ n))
theorem w113_base_valid : FirstCertificate w113 (6 : ℚ) (fun n x => (((1 : ℚ) / 2) * x + (0 : ℚ)) / (1 : ℚ)) := by
  apply linear_certificate w113 (6 : ℚ) (fun n : ℕ => (1 : ℚ)) (fun n : ℕ => ((1 : ℚ) / 2)) (fun n : ℕ => (0 : ℚ))
  · norm_num [w113]
  · intro n; positivity
  · intro n
    simp only [w113, Nat.cast_add, Nat.cast_one, pow_succ, pow_add] at *
    ring
theorem w113_valid : FirstCertificate w113 (6 : ℚ) (fun n x => (((1 : ℚ) / 2) * x + (0 : ℚ)) / (1 : ℚ)) := w113_base_valid
theorem w113_unique (a : ℕ → ℚ) (ha : FirstCertificate a (6 : ℚ) (fun n x => (((1 : ℚ) / 2) * x + (0 : ℚ)) / (1 : ℚ))) :
    ∀ n, a n = w113 n := first_unique w113_valid ha
#print axioms w113_valid
#print axioms w113_unique

def w114 (n : ℕ) : ℚ := ((8 : ℚ) * (((2 : ℚ) / 3) ^ n))
theorem w114_base_valid : FirstCertificate w114 (8 : ℚ) (fun n x => (((2 : ℚ) / 3) * x + (0 : ℚ)) / (1 : ℚ)) := by
  apply linear_certificate w114 (8 : ℚ) (fun n : ℕ => (1 : ℚ)) (fun n : ℕ => ((2 : ℚ) / 3)) (fun n : ℕ => (0 : ℚ))
  · norm_num [w114]
  · intro n; positivity
  · intro n
    simp only [w114, Nat.cast_add, Nat.cast_one, pow_succ, pow_add] at *
    ring
theorem w114_valid : FirstCertificate w114 (8 : ℚ) (fun n x => (((2 : ℚ) / 3) * x + (0 : ℚ)) / (1 : ℚ)) := w114_base_valid
theorem w114_unique (a : ℕ → ℚ) (ha : FirstCertificate a (8 : ℚ) (fun n x => (((2 : ℚ) / 3) * x + (0 : ℚ)) / (1 : ℚ))) :
    ∀ n, a n = w114 n := first_unique w114_valid ha
#print axioms w114_valid
#print axioms w114_unique

def w115 (n : ℕ) : ℚ := ((5 : ℚ) * (((2 : ℚ) / 3) ^ n))
theorem w115_base_valid : FirstCertificate w115 (5 : ℚ) (fun n x => (((2 : ℚ) / 3) * x + (0 : ℚ)) / (1 : ℚ)) := by
  apply linear_certificate w115 (5 : ℚ) (fun n : ℕ => (1 : ℚ)) (fun n : ℕ => ((2 : ℚ) / 3)) (fun n : ℕ => (0 : ℚ))
  · norm_num [w115]
  · intro n; positivity
  · intro n
    simp only [w115, Nat.cast_add, Nat.cast_one, pow_succ, pow_add] at *
    ring
theorem w115_valid : FirstCertificate w115 (5 : ℚ) (fun n x => (((2 : ℚ) / 3) * x + (0 : ℚ)) / (1 : ℚ)) := w115_base_valid
theorem w115_unique (a : ℕ → ℚ) (ha : FirstCertificate a (5 : ℚ) (fun n x => (((2 : ℚ) / 3) * x + (0 : ℚ)) / (1 : ℚ))) :
    ∀ n, a n = w115 n := first_unique w115_valid ha
#print axioms w115_valid
#print axioms w115_unique

def w201 (n : ℕ) : ℚ := ((4 : ℚ) / (((n : ℚ) + 1) * (((n : ℚ) + 1) + (2 : ℚ))))
theorem w201_base_valid : FirstCertificate w201 ((4 : ℚ) / 3) (fun n x => ((((n : ℚ) + 1) * (((n : ℚ) + 1) + (2 : ℚ))) * x + (0 : ℚ)) / ((((n : ℚ) + 1) + (1 : ℚ)) * (((n : ℚ) + 1) + (3 : ℚ)))) := by
  apply linear_certificate w201 ((4 : ℚ) / 3) (fun n : ℕ => ((((n : ℚ) + 1) + (1 : ℚ)) * (((n : ℚ) + 1) + (3 : ℚ)))) (fun n : ℕ => (((n : ℚ) + 1) * (((n : ℚ) + 1) + (2 : ℚ)))) (fun n : ℕ => (0 : ℚ))
  · norm_num [w201]
  · intro n; positivity
  · intro n
    have hd0 : (((n : ℚ) + 1) * (((n : ℚ) + 1) + (2 : ℚ))) ≠ 0 := by positivity
    have he0 : ((((n + 1) : ℚ) + 1) * ((((n + 1) : ℚ) + 1) + (2 : ℚ))) ≠ 0 := by positivity
    simp only [w201, Nat.cast_add, Nat.cast_one, pow_succ, pow_add] at *
    field_simp [hd0, he0] <;> ring
theorem w201_valid : FirstCertificate w201 ((4 : ℚ) / 3) (fun n x => ((((n : ℚ) + 1) * (((n : ℚ) + 1) + (2 : ℚ))) * x + (0 : ℚ)) / ((((n : ℚ) + 1) + (1 : ℚ)) * (((n : ℚ) + 1) + (3 : ℚ)))) := w201_base_valid
theorem w201_unique (a : ℕ → ℚ) (ha : FirstCertificate a ((4 : ℚ) / 3) (fun n x => ((((n : ℚ) + 1) * (((n : ℚ) + 1) + (2 : ℚ))) * x + (0 : ℚ)) / ((((n : ℚ) + 1) + (1 : ℚ)) * (((n : ℚ) + 1) + (3 : ℚ))))) :
    ∀ n, a n = w201 n := first_unique w201_valid ha
#print axioms w201_valid
#print axioms w201_unique

def w202 (n : ℕ) : ℚ := (((1 : ℚ) / 2) / (((n : ℚ) + 1) ^ 2))
theorem w202_base_valid : FirstCertificate w202 ((1 : ℚ) / 2) (fun n x => ((((n : ℚ) + 1) ^ 2) * x + (0 : ℚ)) / ((((n : ℚ) + 1) + (1 : ℚ)) ^ 2)) := by
  apply linear_certificate w202 ((1 : ℚ) / 2) (fun n : ℕ => ((((n : ℚ) + 1) + (1 : ℚ)) ^ 2)) (fun n : ℕ => (((n : ℚ) + 1) ^ 2)) (fun n : ℕ => (0 : ℚ))
  · norm_num [w202]
  · intro n; positivity
  · intro n
    have hd0 : (((n : ℚ) + 1) ^ 2) ≠ 0 := by positivity
    have he0 : ((((n + 1) : ℚ) + 1) ^ 2) ≠ 0 := by positivity
    simp only [w202, Nat.cast_add, Nat.cast_one, pow_succ, pow_add] at *
    field_simp [hd0, he0] <;> ring
theorem w202_valid : FirstCertificate w202 ((1 : ℚ) / 2) (fun n x => ((((n : ℚ) + 1) ^ 2) * x + (0 : ℚ)) / ((((n : ℚ) + 1) + (1 : ℚ)) ^ 2)) := w202_base_valid
theorem w202_unique (a : ℕ → ℚ) (ha : FirstCertificate a ((1 : ℚ) / 2) (fun n x => ((((n : ℚ) + 1) ^ 2) * x + (0 : ℚ)) / ((((n : ℚ) + 1) + (1 : ℚ)) ^ 2))) :
    ∀ n, a n = w202 n := first_unique w202_valid ha
#print axioms w202_valid
#print axioms w202_unique

def w203 (n : ℕ) : ℚ := (((1 : ℚ) / 2) / (((n : ℚ) + 1) * (((n : ℚ) + 1) + (1 : ℚ))))
theorem w203_base_valid : FirstCertificate w203 ((1 : ℚ) / 4) (fun n x => (((n : ℚ) + 1) * x + (0 : ℚ)) / (((n : ℚ) + 1) + (2 : ℚ))) := by
  apply linear_certificate w203 ((1 : ℚ) / 4) (fun n : ℕ => (((n : ℚ) + 1) + (2 : ℚ))) (fun n : ℕ => ((n : ℚ) + 1)) (fun n : ℕ => (0 : ℚ))
  · norm_num [w203]
  · intro n; positivity
  · intro n
    have hd0 : (((n : ℚ) + 1) * (((n : ℚ) + 1) + (1 : ℚ))) ≠ 0 := by positivity
    have he0 : ((((n + 1) : ℚ) + 1) * ((((n + 1) : ℚ) + 1) + (1 : ℚ))) ≠ 0 := by positivity
    simp only [w203, Nat.cast_add, Nat.cast_one, pow_succ, pow_add] at *
    field_simp [hd0, he0] <;> ring
theorem w203_valid : FirstCertificate w203 ((1 : ℚ) / 4) (fun n x => (((n : ℚ) + 1) * x + (0 : ℚ)) / (((n : ℚ) + 1) + (2 : ℚ))) := w203_base_valid
theorem w203_unique (a : ℕ → ℚ) (ha : FirstCertificate a ((1 : ℚ) / 4) (fun n x => (((n : ℚ) + 1) * x + (0 : ℚ)) / (((n : ℚ) + 1) + (2 : ℚ)))) :
    ∀ n, a n = w203 n := first_unique w203_valid ha
#print axioms w203_valid
#print axioms w203_unique

def w204 (n : ℕ) : ℚ := ((2 : ℚ) * ((n : ℚ) + 1) * (((n : ℚ) + 1) + (2 : ℚ)))
theorem w204_base_valid : FirstCertificate w204 (6 : ℚ) (fun n x => (((((n : ℚ) + 1) + (1 : ℚ)) * (((n : ℚ) + 1) + (3 : ℚ))) * x + (0 : ℚ)) / (((n : ℚ) + 1) * (((n : ℚ) + 1) + (2 : ℚ)))) := by
  apply linear_certificate w204 (6 : ℚ) (fun n : ℕ => (((n : ℚ) + 1) * (((n : ℚ) + 1) + (2 : ℚ)))) (fun n : ℕ => ((((n : ℚ) + 1) + (1 : ℚ)) * (((n : ℚ) + 1) + (3 : ℚ)))) (fun n : ℕ => (0 : ℚ))
  · norm_num [w204]
  · intro n; positivity
  · intro n
    simp only [w204, Nat.cast_add, Nat.cast_one, pow_succ, pow_add] at *
    ring
theorem w204_valid : FirstCertificate w204 (6 : ℚ) (fun n x => (((((n : ℚ) + 1) + (1 : ℚ)) * (((n : ℚ) + 1) + (3 : ℚ))) * x + (0 : ℚ)) / (((n : ℚ) + 1) * (((n : ℚ) + 1) + (2 : ℚ)))) := w204_base_valid
theorem w204_unique (a : ℕ → ℚ) (ha : FirstCertificate a (6 : ℚ) (fun n x => (((((n : ℚ) + 1) + (1 : ℚ)) * (((n : ℚ) + 1) + (3 : ℚ))) * x + (0 : ℚ)) / (((n : ℚ) + 1) * (((n : ℚ) + 1) + (2 : ℚ))))) :
    ∀ n, a n = w204 n := first_unique w204_valid ha
#print axioms w204_valid
#print axioms w204_unique

def w205 (n : ℕ) : ℚ := (((1 : ℚ) / 2) * (((n : ℚ) + 1) ^ 2))
theorem w205_base_valid : FirstCertificate w205 ((1 : ℚ) / 2) (fun n x => (((((n : ℚ) + 1) + (1 : ℚ)) ^ 2) * x + (0 : ℚ)) / (((n : ℚ) + 1) ^ 2)) := by
  apply linear_certificate w205 ((1 : ℚ) / 2) (fun n : ℕ => (((n : ℚ) + 1) ^ 2)) (fun n : ℕ => ((((n : ℚ) + 1) + (1 : ℚ)) ^ 2)) (fun n : ℕ => (0 : ℚ))
  · norm_num [w205]
  · intro n; positivity
  · intro n
    simp only [w205, Nat.cast_add, Nat.cast_one, pow_succ, pow_add] at *
    ring
theorem w205_valid : FirstCertificate w205 ((1 : ℚ) / 2) (fun n x => (((((n : ℚ) + 1) + (1 : ℚ)) ^ 2) * x + (0 : ℚ)) / (((n : ℚ) + 1) ^ 2)) := w205_base_valid
theorem w205_unique (a : ℕ → ℚ) (ha : FirstCertificate a ((1 : ℚ) / 2) (fun n x => (((((n : ℚ) + 1) + (1 : ℚ)) ^ 2) * x + (0 : ℚ)) / (((n : ℚ) + 1) ^ 2))) :
    ∀ n, a n = w205 n := first_unique w205_valid ha
#print axioms w205_valid
#print axioms w205_unique

def w206 (n : ℕ) : ℚ := (((2 : ℚ) / (((2 : ℚ) * ((n : ℚ) + 1)) + (1 : ℚ))) + (-2 : ℚ))
theorem w206_base_valid : FirstCertificate w206 ((-4 : ℚ) / 3) (fun n x => ((((2 : ℚ) * ((n : ℚ) + 1)) + (1 : ℚ)) * x + (-4 : ℚ)) / (((2 : ℚ) * ((n : ℚ) + 1)) + (3 : ℚ))) := by
  apply linear_certificate w206 ((-4 : ℚ) / 3) (fun n : ℕ => (((2 : ℚ) * ((n : ℚ) + 1)) + (3 : ℚ))) (fun n : ℕ => (((2 : ℚ) * ((n : ℚ) + 1)) + (1 : ℚ))) (fun n : ℕ => (-4 : ℚ))
  · norm_num [w206]
  · intro n; positivity
  · intro n
    have hd0 : (((2 : ℚ) * ((n : ℚ) + 1)) + (1 : ℚ)) ≠ 0 := by positivity
    have he0 : (((2 : ℚ) * (((n + 1) : ℚ) + 1)) + (1 : ℚ)) ≠ 0 := by positivity
    simp only [w206, Nat.cast_add, Nat.cast_one, pow_succ, pow_add] at *
    field_simp [hd0, he0] <;> ring
theorem w206_valid : FirstCertificate w206 ((-4 : ℚ) / 3) (fun n x => ((((2 : ℚ) * ((n : ℚ) + 1)) + (1 : ℚ)) * x + (-4 : ℚ)) / (((2 : ℚ) * ((n : ℚ) + 1)) + (3 : ℚ))) := w206_base_valid
theorem w206_unique (a : ℕ → ℚ) (ha : FirstCertificate a ((-4 : ℚ) / 3) (fun n x => ((((2 : ℚ) * ((n : ℚ) + 1)) + (1 : ℚ)) * x + (-4 : ℚ)) / (((2 : ℚ) * ((n : ℚ) + 1)) + (3 : ℚ)))) :
    ∀ n, a n = w206 n := first_unique w206_valid ha
#print axioms w206_valid
#print axioms w206_unique

def w207 (n : ℕ) : ℚ := (((2 : ℚ) / ((n : ℚ) + 1)) + (-2 : ℚ))
theorem w207_base_valid : FirstCertificate w207 (0 : ℚ) (fun n x => (((n : ℚ) + 1) * x + (-2 : ℚ)) / (((n : ℚ) + 1) + (1 : ℚ))) := by
  apply linear_certificate w207 (0 : ℚ) (fun n : ℕ => (((n : ℚ) + 1) + (1 : ℚ))) (fun n : ℕ => ((n : ℚ) + 1)) (fun n : ℕ => (-2 : ℚ))
  · norm_num [w207]
  · intro n; positivity
  · intro n
    have hd0 : ((n : ℚ) + 1) ≠ 0 := by positivity
    have he0 : (((n + 1) : ℚ) + 1) ≠ 0 := by positivity
    simp only [w207, Nat.cast_add, Nat.cast_one, pow_succ, pow_add] at *
    field_simp [hd0, he0] <;> ring
theorem w207_valid : FirstCertificate w207 (0 : ℚ) (fun n x => (((n : ℚ) + 1) * x + (-2 : ℚ)) / (((n : ℚ) + 1) + (1 : ℚ))) := w207_base_valid
theorem w207_unique (a : ℕ → ℚ) (ha : FirstCertificate a (0 : ℚ) (fun n x => (((n : ℚ) + 1) * x + (-2 : ℚ)) / (((n : ℚ) + 1) + (1 : ℚ)))) :
    ∀ n, a n = w207 n := first_unique w207_valid ha
#print axioms w207_valid
#print axioms w207_unique

def w208 (n : ℕ) : ℚ := (((1 : ℚ) / (((n : ℚ) + 1) + (1 : ℚ))) + (-1 : ℚ))
theorem w208_base_valid : FirstCertificate w208 ((-1 : ℚ) / 2) (fun n x => ((((n : ℚ) + 1) + (1 : ℚ)) * x + (-1 : ℚ)) / (((n : ℚ) + 1) + (2 : ℚ))) := by
  apply linear_certificate w208 ((-1 : ℚ) / 2) (fun n : ℕ => (((n : ℚ) + 1) + (2 : ℚ))) (fun n : ℕ => (((n : ℚ) + 1) + (1 : ℚ))) (fun n : ℕ => (-1 : ℚ))
  · norm_num [w208]
  · intro n; positivity
  · intro n
    have hd0 : (((n : ℚ) + 1) + (1 : ℚ)) ≠ 0 := by positivity
    have he0 : ((((n + 1) : ℚ) + 1) + (1 : ℚ)) ≠ 0 := by positivity
    simp only [w208, Nat.cast_add, Nat.cast_one, pow_succ, pow_add] at *
    field_simp [hd0, he0] <;> ring
theorem w208_valid : FirstCertificate w208 ((-1 : ℚ) / 2) (fun n x => ((((n : ℚ) + 1) + (1 : ℚ)) * x + (-1 : ℚ)) / (((n : ℚ) + 1) + (2 : ℚ))) := w208_base_valid
theorem w208_unique (a : ℕ → ℚ) (ha : FirstCertificate a ((-1 : ℚ) / 2) (fun n x => ((((n : ℚ) + 1) + (1 : ℚ)) * x + (-1 : ℚ)) / (((n : ℚ) + 1) + (2 : ℚ)))) :
    ∀ n, a n = w208 n := first_unique w208_valid ha
#print axioms w208_valid
#print axioms w208_unique

def w209 (n : ℕ) : ℚ := (((6 : ℚ) * ((2 : ℚ) ^ n)) + (3 : ℚ))
theorem w209_base_valid : FirstCertificate w209 (9 : ℚ) (fun n x => ((2 : ℚ) * x + (-3 : ℚ)) / (1 : ℚ)) := by
  apply linear_certificate w209 (9 : ℚ) (fun n : ℕ => (1 : ℚ)) (fun n : ℕ => (2 : ℚ)) (fun n : ℕ => (-3 : ℚ))
  · norm_num [w209]
  · intro n; positivity
  · intro n
    simp only [w209, Nat.cast_add, Nat.cast_one, pow_succ, pow_add] at *
    ring
theorem w209_valid : FirstCertificate w209 (9 : ℚ) (fun n x => ((2 : ℚ) * x + (-3 : ℚ)) / (1 : ℚ)) := w209_base_valid
theorem w209_unique (a : ℕ → ℚ) (ha : FirstCertificate a (9 : ℚ) (fun n x => ((2 : ℚ) * x + (-3 : ℚ)) / (1 : ℚ))) :
    ∀ n, a n = w209 n := first_unique w209_valid ha
#print axioms w209_valid
#print axioms w209_unique

def w210 (n : ℕ) : ℚ := (((3 : ℚ) * ((3 : ℚ) ^ n)) + (1 : ℚ))
theorem w210_base_valid : FirstCertificate w210 (4 : ℚ) (fun n x => ((3 : ℚ) * x + (-2 : ℚ)) / (1 : ℚ)) := by
  apply linear_certificate w210 (4 : ℚ) (fun n : ℕ => (1 : ℚ)) (fun n : ℕ => (3 : ℚ)) (fun n : ℕ => (-2 : ℚ))
  · norm_num [w210]
  · intro n; positivity
  · intro n
    simp only [w210, Nat.cast_add, Nat.cast_one, pow_succ, pow_add] at *
    ring
theorem w210_valid : FirstCertificate w210 (4 : ℚ) (fun n x => ((3 : ℚ) * x + (-2 : ℚ)) / (1 : ℚ)) := w210_base_valid
theorem w210_unique (a : ℕ → ℚ) (ha : FirstCertificate a (4 : ℚ) (fun n x => ((3 : ℚ) * x + (-2 : ℚ)) / (1 : ℚ))) :
    ∀ n, a n = w210 n := first_unique w210_valid ha
#print axioms w210_valid
#print axioms w210_unique

def w211 (n : ℕ) : ℚ := (((5 : ℚ) * ((3 : ℚ) ^ n)) + (3 : ℚ))
theorem w211_base_valid : FirstCertificate w211 (8 : ℚ) (fun n x => ((3 : ℚ) * x + (-6 : ℚ)) / (1 : ℚ)) := by
  apply linear_certificate w211 (8 : ℚ) (fun n : ℕ => (1 : ℚ)) (fun n : ℕ => (3 : ℚ)) (fun n : ℕ => (-6 : ℚ))
  · norm_num [w211]
  · intro n; positivity
  · intro n
    simp only [w211, Nat.cast_add, Nat.cast_one, pow_succ, pow_add] at *
    ring
theorem w211_valid : FirstCertificate w211 (8 : ℚ) (fun n x => ((3 : ℚ) * x + (-6 : ℚ)) / (1 : ℚ)) := w211_base_valid
theorem w211_unique (a : ℕ → ℚ) (ha : FirstCertificate a (8 : ℚ) (fun n x => ((3 : ℚ) * x + (-6 : ℚ)) / (1 : ℚ))) :
    ∀ n, a n = w211 n := first_unique w211_valid ha
#print axioms w211_valid
#print axioms w211_unique

def w212 (n : ℕ) : ℚ := (((1 : ℚ) / 2) * ((2 : ℚ) ^ ((n + 1).choose 2)))
theorem w212_base_valid : FirstCertificate w212 ((1 : ℚ) / 2) (fun n x => (((2 : ℚ) ^ (n + 1)) * x + (0 : ℚ)) / (1 : ℚ)) := by
  apply linear_certificate w212 ((1 : ℚ) / 2) (fun n : ℕ => (1 : ℚ)) (fun n : ℕ => ((2 : ℚ) ^ (n + 1))) (fun n : ℕ => (0 : ℚ))
  · norm_num [w212]
  · intro n; positivity
  · intro n
    simp only [w212, Nat.choose_succ_succ, Nat.choose_one_right, Nat.choose_zero_right, pow_succ, pow_add] <;> ring
theorem w212_valid : FirstCertificate w212 ((1 : ℚ) / 2) (fun n x => (((2 : ℚ) ^ (n + 1)) * x + (0 : ℚ)) / (1 : ℚ)) := w212_base_valid
theorem w212_unique (a : ℕ → ℚ) (ha : FirstCertificate a ((1 : ℚ) / 2) (fun n x => (((2 : ℚ) ^ (n + 1)) * x + (0 : ℚ)) / (1 : ℚ))) :
    ∀ n, a n = w212 n := first_unique w212_valid ha
#print axioms w212_valid
#print axioms w212_unique

def w213 (n : ℕ) : ℚ := ((2 : ℚ) * ((3 : ℚ) ^ (n * (n + 2))))
theorem w213_base_valid : FirstCertificate w213 (2 : ℚ) (fun n x => (((3 : ℚ) ^ ((2 * (n + 1)) + 1)) * x + (0 : ℚ)) / (1 : ℚ)) := by
  apply linear_certificate w213 (2 : ℚ) (fun n : ℕ => (1 : ℚ)) (fun n : ℕ => ((3 : ℚ) ^ ((2 * (n + 1)) + 1))) (fun n : ℕ => (0 : ℚ))
  · norm_num [w213]
  · intro n; positivity
  · intro n
    have he : (n + 1) * (n + 3) = n * (n + 2) + (2 * (n + 1) + 1) := by ring
    simp only [w213, Nat.add_assoc]
    rw [he]
    simp only [pow_add] <;> ring
theorem w213_valid : FirstCertificate w213 (2 : ℚ) (fun n x => (((3 : ℚ) ^ ((2 * (n + 1)) + 1)) * x + (0 : ℚ)) / (1 : ℚ)) := w213_base_valid
theorem w213_unique (a : ℕ → ℚ) (ha : FirstCertificate a (2 : ℚ) (fun n x => (((3 : ℚ) ^ ((2 * (n + 1)) + 1)) * x + (0 : ℚ)) / (1 : ℚ))) :
    ∀ n, a n = w213 n := first_unique w213_valid ha
#print axioms w213_valid
#print axioms w213_unique

def w214 (n : ℕ) : ℚ := ((((1 : ℚ) / 2) * ((2 : ℚ) ^ n)) + ((3 : ℚ) ^ n))
theorem w214_valid : SecondCertificate w214 ((3 : ℚ) / 2) (4 : ℚ) (5 : ℚ) (-6 : ℚ) := by
  constructor
  · norm_num [w214]
  · norm_num [w214]
  · intro n
    simp only [w214, pow_succ, pow_add] <;> ring
theorem w214_unique (a : ℕ → ℚ) (ha : SecondCertificate a ((3 : ℚ) / 2) (4 : ℚ) (5 : ℚ) (-6 : ℚ)) :
    ∀ n, a n = w214 n := second_unique w214_valid ha
#print axioms w214_valid
#print axioms w214_unique

def w215 (n : ℕ) : ℚ := (((2 : ℚ) * ((2 : ℚ) ^ n)) + ((3 : ℚ) * ((4 : ℚ) ^ n)))
theorem w215_valid : SecondCertificate w215 (5 : ℚ) (16 : ℚ) (6 : ℚ) (-8 : ℚ) := by
  constructor
  · norm_num [w215]
  · norm_num [w215]
  · intro n
    simp only [w215, pow_succ, pow_add] <;> ring
theorem w215_unique (a : ℕ → ℚ) (ha : SecondCertificate a (5 : ℚ) (16 : ℚ) (6 : ℚ) (-8 : ℚ)) :
    ∀ n, a n = w215 n := second_unique w215_valid ha
#print axioms w215_valid
#print axioms w215_unique

def w301 (n : ℕ) : ℚ := ((((2 : ℚ) * ((2 : ℚ) ^ n)) + ((3 : ℚ) * ((4 : ℚ) ^ n))) / ((n : ℚ) + 1))
theorem w301_valid : GeneralSecondCertificate w301 (5 : ℚ) (8 : ℚ) (fun n x y => (((6 : ℚ) * (((n : ℚ) + 1) + (1 : ℚ))) * y + ((-8 : ℚ) * ((n : ℚ) + 1)) * x) / (((n : ℚ) + 1) + (2 : ℚ))) := by
  apply linear_second_certificate w301 (5 : ℚ) (8 : ℚ) (fun n => (((n : ℚ) + 1) + (2 : ℚ))) (fun n => ((6 : ℚ) * (((n : ℚ) + 1) + (1 : ℚ)))) (fun n => ((-8 : ℚ) * ((n : ℚ) + 1)))
  · norm_num [w301]
  · norm_num [w301]
  · intro n; positivity
  · intro n
    have h0_0 : ((n : ℚ) + 1) ≠ 0 := by positivity
    have h1_0 : (((n + 1) : ℚ) + 1) ≠ 0 := by positivity
    have h2_0 : (((n + 2) : ℚ) + 1) ≠ 0 := by positivity
    simp only [w301, Nat.cast_add, Nat.cast_one, pow_succ, pow_add] at *
    field_simp [h0_0, h1_0, h2_0] <;> ring
theorem w301_unique (a : ℕ → ℚ) (hi : a 0 = (5 : ℚ)) (hj : a 1 = (8 : ℚ))
    (ha : ∀ n : ℕ, (((n : ℚ) + 1) + (2 : ℚ)) * a (n + 2) = ((6 : ℚ) * (((n : ℚ) + 1) + (1 : ℚ))) * a (n + 1) + ((-8 : ℚ) * ((n : ℚ) + 1)) * a n) :
    ∀ n, a n = w301 n := by
  apply general_second_unique w301_valid
  exact linear_second_certificate a (5 : ℚ) (8 : ℚ) (fun n => (((n : ℚ) + 1) + (2 : ℚ))) (fun n => ((6 : ℚ) * (((n : ℚ) + 1) + (1 : ℚ)))) (fun n => ((-8 : ℚ) * ((n : ℚ) + 1))) hi hj (by intro n; positivity) ha
#print axioms w301_valid
#print axioms w301_unique

def w302 (n : ℕ) : ℚ := ((((3 : ℚ) * ((2 : ℚ) ^ n)) + ((3 : ℚ) ^ n)) / (((n : ℚ) + 1) + (1 : ℚ)))
theorem w302_valid : GeneralSecondCertificate w302 (2 : ℚ) (3 : ℚ) (fun n x y => (((5 : ℚ) * (((n : ℚ) + 1) + (2 : ℚ))) * y + ((-6 : ℚ) * (((n : ℚ) + 1) + (1 : ℚ))) * x) / (((n : ℚ) + 1) + (3 : ℚ))) := by
  apply linear_second_certificate w302 (2 : ℚ) (3 : ℚ) (fun n => (((n : ℚ) + 1) + (3 : ℚ))) (fun n => ((5 : ℚ) * (((n : ℚ) + 1) + (2 : ℚ)))) (fun n => ((-6 : ℚ) * (((n : ℚ) + 1) + (1 : ℚ))))
  · norm_num [w302]
  · norm_num [w302]
  · intro n; positivity
  · intro n
    have h0_0 : (((n : ℚ) + 1) + (1 : ℚ)) ≠ 0 := by positivity
    have h1_0 : ((((n + 1) : ℚ) + 1) + (1 : ℚ)) ≠ 0 := by positivity
    have h2_0 : ((((n + 2) : ℚ) + 1) + (1 : ℚ)) ≠ 0 := by positivity
    simp only [w302, Nat.cast_add, Nat.cast_one, pow_succ, pow_add] at *
    field_simp [h0_0, h1_0, h2_0] <;> ring
theorem w302_unique (a : ℕ → ℚ) (hi : a 0 = (2 : ℚ)) (hj : a 1 = (3 : ℚ))
    (ha : ∀ n : ℕ, (((n : ℚ) + 1) + (3 : ℚ)) * a (n + 2) = ((5 : ℚ) * (((n : ℚ) + 1) + (2 : ℚ))) * a (n + 1) + ((-6 : ℚ) * (((n : ℚ) + 1) + (1 : ℚ))) * a n) :
    ∀ n, a n = w302 n := by
  apply general_second_unique w302_valid
  exact linear_second_certificate a (2 : ℚ) (3 : ℚ) (fun n => (((n : ℚ) + 1) + (3 : ℚ))) (fun n => ((5 : ℚ) * (((n : ℚ) + 1) + (2 : ℚ)))) (fun n => ((-6 : ℚ) * (((n : ℚ) + 1) + (1 : ℚ)))) hi hj (by intro n; positivity) ha
#print axioms w302_valid
#print axioms w302_unique

def w303 (n : ℕ) : ℚ := (((((1 : ℚ) / 2) * ((2 : ℚ) ^ n)) + ((3 : ℚ) ^ n)) / (((2 : ℚ) * ((n : ℚ) + 1)) + (1 : ℚ)))
theorem w303_valid : GeneralSecondCertificate w303 ((1 : ℚ) / 2) ((4 : ℚ) / 5) (fun n x y => (((5 : ℚ) * (((2 : ℚ) * ((n : ℚ) + 1)) + (3 : ℚ))) * y + ((-6 : ℚ) * (((2 : ℚ) * ((n : ℚ) + 1)) + (1 : ℚ))) * x) / (((2 : ℚ) * ((n : ℚ) + 1)) + (5 : ℚ))) := by
  apply linear_second_certificate w303 ((1 : ℚ) / 2) ((4 : ℚ) / 5) (fun n => (((2 : ℚ) * ((n : ℚ) + 1)) + (5 : ℚ))) (fun n => ((5 : ℚ) * (((2 : ℚ) * ((n : ℚ) + 1)) + (3 : ℚ)))) (fun n => ((-6 : ℚ) * (((2 : ℚ) * ((n : ℚ) + 1)) + (1 : ℚ))))
  · norm_num [w303]
  · norm_num [w303]
  · intro n; positivity
  · intro n
    have h0_0 : (((2 : ℚ) * ((n : ℚ) + 1)) + (1 : ℚ)) ≠ 0 := by positivity
    have h1_0 : (((2 : ℚ) * (((n + 1) : ℚ) + 1)) + (1 : ℚ)) ≠ 0 := by positivity
    have h2_0 : (((2 : ℚ) * (((n + 2) : ℚ) + 1)) + (1 : ℚ)) ≠ 0 := by positivity
    simp only [w303, Nat.cast_add, Nat.cast_one, pow_succ, pow_add] at *
    field_simp [h0_0, h1_0, h2_0] <;> ring
theorem w303_unique (a : ℕ → ℚ) (hi : a 0 = ((1 : ℚ) / 2)) (hj : a 1 = ((4 : ℚ) / 5))
    (ha : ∀ n : ℕ, (((2 : ℚ) * ((n : ℚ) + 1)) + (5 : ℚ)) * a (n + 2) = ((5 : ℚ) * (((2 : ℚ) * ((n : ℚ) + 1)) + (3 : ℚ))) * a (n + 1) + ((-6 : ℚ) * (((2 : ℚ) * ((n : ℚ) + 1)) + (1 : ℚ))) * a n) :
    ∀ n, a n = w303 n := by
  apply general_second_unique w303_valid
  exact linear_second_certificate a ((1 : ℚ) / 2) ((4 : ℚ) / 5) (fun n => (((2 : ℚ) * ((n : ℚ) + 1)) + (5 : ℚ))) (fun n => ((5 : ℚ) * (((2 : ℚ) * ((n : ℚ) + 1)) + (3 : ℚ)))) (fun n => ((-6 : ℚ) * (((2 : ℚ) * ((n : ℚ) + 1)) + (1 : ℚ)))) hi hj (by intro n; positivity) ha
#print axioms w303_valid
#print axioms w303_unique

def w304 (n : ℕ) : ℚ := (((-2 : ℚ) * ((2 : ℚ) ^ n)) + ((4 : ℚ) * ((3 : ℚ) ^ n)))
def w304_base (n : ℕ) : ℚ := (((-2 : ℚ) * ((2 : ℚ) ^ n)) + ((4 : ℚ) * ((3 : ℚ) ^ n)))
theorem w304_base_valid : SecondCertificate w304_base (2 : ℚ) (8 : ℚ) (5 : ℚ) (-6 : ℚ) := by
  constructor
  · norm_num [w304_base]
  · norm_num [w304_base]
  · intro n
    simp only [w304_base, Nat.cast_add, Nat.cast_one, pow_succ, pow_add] at *
    ring
theorem w304_valid : WeightedSumCertificate w304 (2 : ℚ) (fun n : ℕ => (1 : ℚ)) (6 : ℚ) (-2 : ℚ) := by
  apply weighted_sum_from_second w304 w304_base (fun n : ℕ => (1 : ℚ)) (2 : ℚ) (2 : ℚ) (8 : ℚ) (6 : ℚ) (-2 : ℚ)
  · convert w304_base_valid using 1 <;> norm_num
  · norm_num
  · intro n; positivity
  · intro n; simp only [w304, w304_base] <;> ring
  · norm_num [w304]
theorem w304_unique (a : ℕ → ℚ) (ha : WeightedSumCertificate a (2 : ℚ) (fun n : ℕ => (1 : ℚ)) (6 : ℚ) (-2 : ℚ)) :
    ∀ n, a n = w304 n := weighted_sum_unique w304_valid ha
#print axioms w304_valid
#print axioms w304_unique

def w305 (n : ℕ) : ℚ := (((((1 : ℚ) / 4) * (((n : ℚ) + 1) + (-1 : ℚ))) + ((1 : ℚ) / 2)) * ((2 : ℚ) ^ n))
def w305_base (n : ℕ) : ℚ := (((((1 : ℚ) / 4) * (((n : ℚ) + 1) + (-1 : ℚ))) + ((1 : ℚ) / 2)) * ((2 : ℚ) ^ n))
theorem w305_base_valid : SecondCertificate w305_base ((1 : ℚ) / 2) ((3 : ℚ) / 2) (4 : ℚ) (-4 : ℚ) := by
  constructor
  · norm_num [w305_base]
  · norm_num [w305_base]
  · intro n
    simp only [w305_base, Nat.cast_add, Nat.cast_one, pow_succ, pow_add] at *
    ring
theorem w305_valid : WeightedSumCertificate w305 ((1 : ℚ) / 2) (fun n : ℕ => (1 : ℚ)) (4 : ℚ) (-1 : ℚ) := by
  apply weighted_sum_from_second w305 w305_base (fun n : ℕ => (1 : ℚ)) ((1 : ℚ) / 2) ((1 : ℚ) / 2) ((3 : ℚ) / 2) (4 : ℚ) (-1 : ℚ)
  · convert w305_base_valid using 1 <;> norm_num
  · norm_num
  · intro n; positivity
  · intro n; simp only [w305, w305_base] <;> ring
  · norm_num [w305]
theorem w305_unique (a : ℕ → ℚ) (ha : WeightedSumCertificate a ((1 : ℚ) / 2) (fun n : ℕ => (1 : ℚ)) (4 : ℚ) (-1 : ℚ)) :
    ∀ n, a n = w305 n := weighted_sum_unique w305_valid ha
#print axioms w305_valid
#print axioms w305_unique

def w306 (n : ℕ) : ℚ := (((((1 : ℚ) / 3) * (((n : ℚ) + 1) + (-1 : ℚ))) + ((1 : ℚ) / 2)) * ((3 : ℚ) ^ n))
def w306_base (n : ℕ) : ℚ := (((((1 : ℚ) / 3) * (((n : ℚ) + 1) + (-1 : ℚ))) + ((1 : ℚ) / 2)) * ((3 : ℚ) ^ n))
theorem w306_base_valid : SecondCertificate w306_base ((1 : ℚ) / 2) ((5 : ℚ) / 2) (6 : ℚ) (-9 : ℚ) := by
  constructor
  · norm_num [w306_base]
  · norm_num [w306_base]
  · intro n
    simp only [w306_base, Nat.cast_add, Nat.cast_one, pow_succ, pow_add] at *
    ring
theorem w306_valid : WeightedSumCertificate w306 ((1 : ℚ) / 2) (fun n : ℕ => (1 : ℚ)) (9 : ℚ) (-4 : ℚ) := by
  apply weighted_sum_from_second w306 w306_base (fun n : ℕ => (1 : ℚ)) ((1 : ℚ) / 2) ((1 : ℚ) / 2) ((5 : ℚ) / 2) (9 : ℚ) (-4 : ℚ)
  · convert w306_base_valid using 1 <;> norm_num
  · norm_num
  · intro n; positivity
  · intro n; simp only [w306, w306_base] <;> ring
  · norm_num [w306]
theorem w306_unique (a : ℕ → ℚ) (ha : WeightedSumCertificate a ((1 : ℚ) / 2) (fun n : ℕ => (1 : ℚ)) (9 : ℚ) (-4 : ℚ)) :
    ∀ n, a n = w306 n := weighted_sum_unique w306_valid ha
#print axioms w306_valid
#print axioms w306_unique

def w307 (n : ℕ) : ℚ := ((2 : ℚ) ^ ((n + 2)).choose 3)
theorem w307_base_valid : FirstCertificate w307 (1 : ℚ) (fun n x => (((2 : ℚ) ^ ((n + 2)).choose 2) * x + (0 : ℚ)) / (1 : ℚ)) := by
  apply linear_certificate w307 (1 : ℚ) (fun n : ℕ => (1 : ℚ)) (fun n : ℕ => ((2 : ℚ) ^ ((n + 2)).choose 2)) (fun n : ℕ => (0 : ℚ))
  · norm_num [w307]
  · intro n; positivity
  · intro n
    simp only [w307, Nat.choose_succ_succ, Nat.choose_one_right, Nat.choose_zero_right, pow_succ, pow_add] <;> ring
theorem w307_valid : FirstCertificate w307 (1 : ℚ) (fun n x => (((2 : ℚ) ^ ((n + 2)).choose 2) * x + (0 : ℚ)) / (1 : ℚ)) := w307_base_valid
theorem w307_unique (a : ℕ → ℚ) (ha : FirstCertificate a (1 : ℚ) (fun n x => (((2 : ℚ) ^ ((n + 2)).choose 2) * x + (0 : ℚ)) / (1 : ℚ))) :
    ∀ n, a n = w307 n := first_unique w307_valid ha
#print axioms w307_valid
#print axioms w307_unique

def w308 (n : ℕ) : ℚ := ((4 : ℚ) * ((3 : ℚ) ^ ((n + 2)).choose 3))
theorem w308_base_valid : FirstCertificate w308 (4 : ℚ) (fun n x => (((3 : ℚ) ^ ((n + 2)).choose 2) * x + (0 : ℚ)) / (1 : ℚ)) := by
  apply linear_certificate w308 (4 : ℚ) (fun n : ℕ => (1 : ℚ)) (fun n : ℕ => ((3 : ℚ) ^ ((n + 2)).choose 2)) (fun n : ℕ => (0 : ℚ))
  · norm_num [w308]
  · intro n; positivity
  · intro n
    simp only [w308, Nat.choose_succ_succ, Nat.choose_one_right, Nat.choose_zero_right, pow_succ, pow_add] <;> ring
theorem w308_valid : FirstCertificate w308 (4 : ℚ) (fun n x => (((3 : ℚ) ^ ((n + 2)).choose 2) * x + (0 : ℚ)) / (1 : ℚ)) := w308_base_valid
theorem w308_unique (a : ℕ → ℚ) (ha : FirstCertificate a (4 : ℚ) (fun n x => (((3 : ℚ) ^ ((n + 2)).choose 2) * x + (0 : ℚ)) / (1 : ℚ))) :
    ∀ n, a n = w308 n := first_unique w308_valid ha
#print axioms w308_valid
#print axioms w308_unique

def w309 (n : ℕ) : ℚ := ((((5 : ℚ) * ((2 : ℚ) ^ n)) + (3 : ℚ)) / (((n : ℚ) + 1) ^ 2))
theorem w309_base_valid : FirstCertificate w309 (8 : ℚ) (fun n x => (((2 : ℚ) * (((n : ℚ) + 1) ^ 2)) * x + (-3 : ℚ)) / ((((n : ℚ) + 1) + (1 : ℚ)) ^ 2)) := by
  apply linear_certificate w309 (8 : ℚ) (fun n : ℕ => ((((n : ℚ) + 1) + (1 : ℚ)) ^ 2)) (fun n : ℕ => ((2 : ℚ) * (((n : ℚ) + 1) ^ 2))) (fun n : ℕ => (-3 : ℚ))
  · norm_num [w309]
  · intro n; positivity
  · intro n
    have hd0 : (((n : ℚ) + 1) ^ 2) ≠ 0 := by positivity
    have he0 : ((((n + 1) : ℚ) + 1) ^ 2) ≠ 0 := by positivity
    simp only [w309, Nat.cast_add, Nat.cast_one, pow_succ, pow_add] at *
    field_simp [hd0, he0] <;> ring
theorem w309_valid : FirstCertificate w309 (8 : ℚ) (fun n x => (((2 : ℚ) * (((n : ℚ) + 1) ^ 2)) * x + (-3 : ℚ)) / ((((n : ℚ) + 1) + (1 : ℚ)) ^ 2)) := w309_base_valid
theorem w309_unique (a : ℕ → ℚ) (ha : FirstCertificate a (8 : ℚ) (fun n x => (((2 : ℚ) * (((n : ℚ) + 1) ^ 2)) * x + (-3 : ℚ)) / ((((n : ℚ) + 1) + (1 : ℚ)) ^ 2))) :
    ∀ n, a n = w309 n := first_unique w309_valid ha
#print axioms w309_valid
#print axioms w309_unique

def w310 (n : ℕ) : ℚ := (((n : ℚ) + 1) * (((4 : ℚ) * ((3 : ℚ) ^ n)) + (1 : ℚ)))
theorem w310_base_valid : FirstCertificate w310 (5 : ℚ) (fun n x => (((3 : ℚ) * (((n : ℚ) + 1) + (1 : ℚ))) * x + ((-2 : ℚ) * ((n : ℚ) + 1) * (((n : ℚ) + 1) + (1 : ℚ)))) / ((n : ℚ) + 1)) := by
  apply linear_certificate w310 (5 : ℚ) (fun n : ℕ => ((n : ℚ) + 1)) (fun n : ℕ => ((3 : ℚ) * (((n : ℚ) + 1) + (1 : ℚ)))) (fun n : ℕ => ((-2 : ℚ) * ((n : ℚ) + 1) * (((n : ℚ) + 1) + (1 : ℚ))))
  · norm_num [w310]
  · intro n; positivity
  · intro n
    simp only [w310, Nat.cast_add, Nat.cast_one, pow_succ, pow_add] at *
    ring
theorem w310_valid : FirstCertificate w310 (5 : ℚ) (fun n x => (((3 : ℚ) * (((n : ℚ) + 1) + (1 : ℚ))) * x + ((-2 : ℚ) * ((n : ℚ) + 1) * (((n : ℚ) + 1) + (1 : ℚ)))) / ((n : ℚ) + 1)) := w310_base_valid
theorem w310_unique (a : ℕ → ℚ) (ha : FirstCertificate a (5 : ℚ) (fun n x => (((3 : ℚ) * (((n : ℚ) + 1) + (1 : ℚ))) * x + ((-2 : ℚ) * ((n : ℚ) + 1) * (((n : ℚ) + 1) + (1 : ℚ)))) / ((n : ℚ) + 1))) :
    ∀ n, a n = w310 n := first_unique w310_valid ha
#print axioms w310_valid
#print axioms w310_unique

def w311 (n : ℕ) : ℚ := (((5 : ℚ) * ((2 : ℚ) ^ n)) + ((-1 : ℚ) * ((n : ℚ) + 1)) + (-1 : ℚ))
theorem w311_base_valid : FirstCertificate w311 (3 : ℚ) (fun n x => ((2 : ℚ) * x + ((n : ℚ) + 1)) / (1 : ℚ)) := by
  apply linear_certificate w311 (3 : ℚ) (fun n : ℕ => (1 : ℚ)) (fun n : ℕ => (2 : ℚ)) (fun n : ℕ => ((n : ℚ) + 1))
  · norm_num [w311]
  · intro n; positivity
  · intro n
    simp only [w311, Nat.cast_add, Nat.cast_one, pow_succ, pow_add] at *
    ring
theorem w311_valid : FirstCertificate w311 (3 : ℚ) (fun n x => ((2 : ℚ) * x + ((n : ℚ) + 1)) / (1 : ℚ)) := w311_base_valid
theorem w311_unique (a : ℕ → ℚ) (ha : FirstCertificate a (3 : ℚ) (fun n x => ((2 : ℚ) * x + ((n : ℚ) + 1)) / (1 : ℚ))) :
    ∀ n, a n = w311 n := first_unique w311_valid ha
#print axioms w311_valid
#print axioms w311_unique

def w312 (n : ℕ) : ℚ := (((4 : ℚ) * ((3 : ℚ) ^ n)) + ((-2 : ℚ) * ((n : ℚ) + 1)) + (-1 : ℚ))
theorem w312_base_valid : FirstCertificate w312 (1 : ℚ) (fun n x => ((3 : ℚ) * x + ((4 : ℚ) * ((n : ℚ) + 1))) / (1 : ℚ)) := by
  apply linear_certificate w312 (1 : ℚ) (fun n : ℕ => (1 : ℚ)) (fun n : ℕ => (3 : ℚ)) (fun n : ℕ => ((4 : ℚ) * ((n : ℚ) + 1)))
  · norm_num [w312]
  · intro n; positivity
  · intro n
    simp only [w312, Nat.cast_add, Nat.cast_one, pow_succ, pow_add] at *
    ring
theorem w312_valid : FirstCertificate w312 (1 : ℚ) (fun n x => ((3 : ℚ) * x + ((4 : ℚ) * ((n : ℚ) + 1))) / (1 : ℚ)) := w312_base_valid
theorem w312_unique (a : ℕ → ℚ) (ha : FirstCertificate a (1 : ℚ) (fun n x => ((3 : ℚ) * x + ((4 : ℚ) * ((n : ℚ) + 1))) / (1 : ℚ))) :
    ∀ n, a n = w312 n := first_unique w312_valid ha
#print axioms w312_valid
#print axioms w312_unique

def w313 (n : ℕ) : ℚ := ((1 : ℚ) / (((2 : ℚ) ^ n) + (2 : ℚ)))
def w313_base (n : ℕ) : ℚ := (((2 : ℚ) ^ n) + (2 : ℚ))
theorem w313_base_valid : FirstCertificate w313_base (3 : ℚ) (fun n x => ((2 : ℚ) * x + (-2 : ℚ)) / (1 : ℚ)) := by
  apply linear_certificate w313_base (3 : ℚ) (fun n : ℕ => (1 : ℚ)) (fun n : ℕ => (2 : ℚ)) (fun n : ℕ => (-2 : ℚ))
  · norm_num [w313_base]
  · intro n; positivity
  · intro n
    simp only [w313_base, Nat.cast_add, Nat.cast_one, pow_succ, pow_add] at *
    ring
theorem w313_positive (n : ℕ) : 0 < w313_base n := by
  unfold w313_base
  positivity
theorem w313_valid : FirstCertificate w313 ((1 : ℚ) / 3) (fun n x => (1 : ℚ) * x / ((2 : ℚ) + (-2 : ℚ) * x)) := by
  have h := reciprocal_certificate w313_base_valid w313_positive (by intro n; positivity)
  have heq : w313 = (fun n => 1 / w313_base n) := by
    funext n
    simp [w313, w313_base, div_eq_mul_inv] <;> ring
  rw [heq]
  convert h.1 using 1 <;> norm_num
theorem w313_domain : (∀ n : ℕ, (2 : ℚ) + (-2 : ℚ) * w313 n ≠ 0) ∧ (∀ n, w313 n ≠ 0) := by
  have h := reciprocal_certificate w313_base_valid w313_positive (by intro n; positivity)
  simpa [w313, w313_base, div_eq_mul_inv] using h.2
#print axioms w313_domain
theorem w313_unique (a : ℕ → ℚ) (ha : FirstCertificate a ((1 : ℚ) / 3) (fun n x => (1 : ℚ) * x / ((2 : ℚ) + (-2 : ℚ) * x))) :
    ∀ n, a n = w313 n := first_unique w313_valid ha
#print axioms w313_valid
#print axioms w313_unique

def w314 (n : ℕ) : ℚ := ((1 : ℚ) / (((2 : ℚ) * ((3 : ℚ) ^ n)) + (2 : ℚ)))
def w314_base (n : ℕ) : ℚ := (((2 : ℚ) * ((3 : ℚ) ^ n)) + (2 : ℚ))
theorem w314_base_valid : FirstCertificate w314_base (4 : ℚ) (fun n x => ((3 : ℚ) * x + (-4 : ℚ)) / (1 : ℚ)) := by
  apply linear_certificate w314_base (4 : ℚ) (fun n : ℕ => (1 : ℚ)) (fun n : ℕ => (3 : ℚ)) (fun n : ℕ => (-4 : ℚ))
  · norm_num [w314_base]
  · intro n; positivity
  · intro n
    simp only [w314_base, Nat.cast_add, Nat.cast_one, pow_succ, pow_add] at *
    ring
theorem w314_positive (n : ℕ) : 0 < w314_base n := by
  unfold w314_base
  positivity
theorem w314_valid : FirstCertificate w314 ((1 : ℚ) / 4) (fun n x => (1 : ℚ) * x / ((3 : ℚ) + (-4 : ℚ) * x)) := by
  have h := reciprocal_certificate w314_base_valid w314_positive (by intro n; positivity)
  have heq : w314 = (fun n => 1 / w314_base n) := by
    funext n
    simp [w314, w314_base, div_eq_mul_inv] <;> ring
  rw [heq]
  convert h.1 using 1 <;> norm_num
theorem w314_domain : (∀ n : ℕ, (3 : ℚ) + (-4 : ℚ) * w314 n ≠ 0) ∧ (∀ n, w314 n ≠ 0) := by
  have h := reciprocal_certificate w314_base_valid w314_positive (by intro n; positivity)
  simpa [w314, w314_base, div_eq_mul_inv] using h.2
#print axioms w314_domain
theorem w314_unique (a : ℕ → ℚ) (ha : FirstCertificate a ((1 : ℚ) / 4) (fun n x => (1 : ℚ) * x / ((3 : ℚ) + (-4 : ℚ) * x))) :
    ∀ n, a n = w314 n := first_unique w314_valid ha
#print axioms w314_valid
#print axioms w314_unique

def w315 (n : ℕ) : ℚ := (((8 : ℚ) * ((2 : ℚ) ^ n)) + ((3 : ℚ) * ((3 : ℚ) ^ n)))
theorem w315_valid : SecondCertificate w315 (11 : ℚ) (25 : ℚ) (5 : ℚ) (-6 : ℚ) := by
  constructor
  · norm_num [w315]
  · norm_num [w315]
  · intro n
    simp only [w315, pow_succ, pow_add] <;> ring
theorem w315_unique (a : ℕ → ℚ) (ha : SecondCertificate a (11 : ℚ) (25 : ℚ) (5 : ℚ) (-6 : ℚ)) :
    ∀ n, a n = w315 n := second_unique w315_valid ha
#print axioms w315_valid
#print axioms w315_unique

def w401 (n : ℕ) : ℚ := ((((((1 : ℚ) / 2) * ((n : ℚ) + 1)) + ((-3 : ℚ) / 4)) * ((3 : ℚ) ^ n)) + ((9 : ℚ) / 4))
theorem w401_valid : GeneralSecondCertificate w401 (2 : ℚ) (3 : ℚ) (fun n x y => ((((4 : ℚ) * ((n : ℚ) + 1)) + (3 : ℚ)) * y + ((-3 : ℚ) * (((n : ℚ) + 1) + (1 : ℚ))) * x) / ((n : ℚ) + 1)) := by
  apply linear_second_certificate w401 (2 : ℚ) (3 : ℚ) (fun n => ((n : ℚ) + 1)) (fun n => (((4 : ℚ) * ((n : ℚ) + 1)) + (3 : ℚ))) (fun n => ((-3 : ℚ) * (((n : ℚ) + 1) + (1 : ℚ))))
  · norm_num [w401]
  · norm_num [w401]
  · intro n; positivity
  · intro n
    simp only [w401, Nat.cast_add, Nat.cast_one, pow_succ, pow_add] at *
    ring
theorem w401_unique (a : ℕ → ℚ) (hi : a 0 = (2 : ℚ)) (hj : a 1 = (3 : ℚ))
    (ha : ∀ n : ℕ, ((n : ℚ) + 1) * a (n + 2) = (((4 : ℚ) * ((n : ℚ) + 1)) + (3 : ℚ)) * a (n + 1) + ((-3 : ℚ) * (((n : ℚ) + 1) + (1 : ℚ))) * a n) :
    ∀ n, a n = w401 n := by
  apply general_second_unique w401_valid
  exact linear_second_certificate a (2 : ℚ) (3 : ℚ) (fun n => ((n : ℚ) + 1)) (fun n => (((4 : ℚ) * ((n : ℚ) + 1)) + (3 : ℚ))) (fun n => ((-3 : ℚ) * (((n : ℚ) + 1) + (1 : ℚ)))) hi hj (by intro n; positivity) ha
#print axioms w401_valid
#print axioms w401_unique

def w402 (n : ℕ) : ℚ := (((((3 : ℚ) * ((n : ℚ) + 1)) + (-3 : ℚ)) * ((2 : ℚ) ^ n)) + (3 : ℚ))
theorem w402_valid : GeneralSecondCertificate w402 (3 : ℚ) (9 : ℚ) (fun n x y => ((((3 : ℚ) * ((n : ℚ) + 1)) + (5 : ℚ)) * y + ((-2 : ℚ) * (((n : ℚ) + 1) + (2 : ℚ))) * x) / (((n : ℚ) + 1) + (1 : ℚ))) := by
  apply linear_second_certificate w402 (3 : ℚ) (9 : ℚ) (fun n => (((n : ℚ) + 1) + (1 : ℚ))) (fun n => (((3 : ℚ) * ((n : ℚ) + 1)) + (5 : ℚ))) (fun n => ((-2 : ℚ) * (((n : ℚ) + 1) + (2 : ℚ))))
  · norm_num [w402]
  · norm_num [w402]
  · intro n; positivity
  · intro n
    simp only [w402, Nat.cast_add, Nat.cast_one, pow_succ, pow_add] at *
    ring
theorem w402_unique (a : ℕ → ℚ) (hi : a 0 = (3 : ℚ)) (hj : a 1 = (9 : ℚ))
    (ha : ∀ n : ℕ, (((n : ℚ) + 1) + (1 : ℚ)) * a (n + 2) = (((3 : ℚ) * ((n : ℚ) + 1)) + (5 : ℚ)) * a (n + 1) + ((-2 : ℚ) * (((n : ℚ) + 1) + (2 : ℚ))) * a n) :
    ∀ n, a n = w402 n := by
  apply general_second_unique w402_valid
  exact linear_second_certificate a (3 : ℚ) (9 : ℚ) (fun n => (((n : ℚ) + 1) + (1 : ℚ))) (fun n => (((3 : ℚ) * ((n : ℚ) + 1)) + (5 : ℚ))) (fun n => ((-2 : ℚ) * (((n : ℚ) + 1) + (2 : ℚ)))) hi hj (by intro n; positivity) ha
#print axioms w402_valid
#print axioms w402_unique

def w403 (n : ℕ) : ℚ := ((((((n : ℚ) + 1) ^ 2) + ((-4 : ℚ) * ((n : ℚ) + 1)) + (6 : ℚ)) * ((2 : ℚ) ^ n)) + (-1 : ℚ))
theorem w403_valid : GeneralSecondCertificate w403 (2 : ℚ) (3 : ℚ) (fun n x y => ((((3 : ℚ) * (((n : ℚ) + 1) ^ 2)) + ((4 : ℚ) * ((n : ℚ) + 1)) + (2 : ℚ)) * y + ((-2 : ℚ) * ((((n : ℚ) + 1) + (1 : ℚ)) ^ 2)) * x) / (((n : ℚ) + 1) ^ 2)) := by
  apply linear_second_certificate w403 (2 : ℚ) (3 : ℚ) (fun n => (((n : ℚ) + 1) ^ 2)) (fun n => (((3 : ℚ) * (((n : ℚ) + 1) ^ 2)) + ((4 : ℚ) * ((n : ℚ) + 1)) + (2 : ℚ))) (fun n => ((-2 : ℚ) * ((((n : ℚ) + 1) + (1 : ℚ)) ^ 2)))
  · norm_num [w403]
  · norm_num [w403]
  · intro n; positivity
  · intro n
    simp only [w403, Nat.cast_add, Nat.cast_one, pow_succ, pow_add] at *
    ring
theorem w403_unique (a : ℕ → ℚ) (hi : a 0 = (2 : ℚ)) (hj : a 1 = (3 : ℚ))
    (ha : ∀ n : ℕ, (((n : ℚ) + 1) ^ 2) * a (n + 2) = (((3 : ℚ) * (((n : ℚ) + 1) ^ 2)) + ((4 : ℚ) * ((n : ℚ) + 1)) + (2 : ℚ)) * a (n + 1) + ((-2 : ℚ) * ((((n : ℚ) + 1) + (1 : ℚ)) ^ 2)) * a n) :
    ∀ n, a n = w403 n := by
  apply general_second_unique w403_valid
  exact linear_second_certificate a (2 : ℚ) (3 : ℚ) (fun n => (((n : ℚ) + 1) ^ 2)) (fun n => (((3 : ℚ) * (((n : ℚ) + 1) ^ 2)) + ((4 : ℚ) * ((n : ℚ) + 1)) + (2 : ℚ))) (fun n => ((-2 : ℚ) * ((((n : ℚ) + 1) + (1 : ℚ)) ^ 2))) hi hj (by intro n; positivity) ha
#print axioms w403_valid
#print axioms w403_unique

def w404 (n : ℕ) : ℚ := ((2 : ℚ) ^ (1 + (3 * n) + (3 * (n).choose 2)))
theorem w404_valid : GeneralSecondCertificate w404 (2 : ℚ) (16 : ℚ) (fun n x y => (2 : ℚ) ^ (3) * y ^ 2 / x) := by
  have he : ∀ n : ℕ, ((1 + (3 * (n + 2)) + (3 * ((n + 2)).choose 2))) + ((1 + (3 * n) + (3 * (n).choose 2))) = (3) + 2 * ((1 + (3 * (n + 1)) + (3 * ((n + 1)).choose 2))) := by
    intro n
    simp only [Nat.add_assoc, Nat.choose_succ_succ, Nat.choose_one_right, Nat.choose_zero_right]
    ring
  have h := multiplicative_certificate (2 : ℚ) (fun n : ℕ => (1 + (3 * n) + (3 * (n).choose 2))) (fun n : ℕ => 3) (by norm_num) he
  convert h.1 using 1 <;> norm_num [w404]
theorem w404_domain : ∀ n, w404 n ≠ 0 := by
  intro n; unfold w404; positivity
theorem w404_unique (a : ℕ → ℚ) (hi : a 0 = (2 : ℚ)) (hj : a 1 = (16 : ℚ))
    (ha : ∀ n : ℕ, a (n + 2) * a n = (2 : ℚ) ^ (3) * a (n + 1) ^ 2) :
    ∀ n, a n = w404 n := by
  apply general_second_unique w404_valid
  apply multiplicative_from_relation a (2 : ℚ) (16 : ℚ) (fun n => (2 : ℚ) ^ (3)) hi hj
  · norm_num
  · norm_num
  · intro n; positivity
  · exact ha
#print axioms w404_domain
#print axioms w404_valid
#print axioms w404_unique

def w405 (n : ℕ) : ℚ := ((2 : ℚ) ^ ((2 * (n + 1)) + (3 * (n).choose 2) + (3 * (n).choose 3)))
theorem w405_valid : GeneralSecondCertificate w405 (4 : ℚ) (16 : ℚ) (fun n x y => (2 : ℚ) ^ ((3 * (n + 1))) * y ^ 2 / x) := by
  have he : ∀ n : ℕ, (((2 * ((n + 2) + 1)) + (3 * ((n + 2)).choose 2) + (3 * ((n + 2)).choose 3))) + (((2 * (n + 1)) + (3 * (n).choose 2) + (3 * (n).choose 3))) = ((3 * (n + 1))) + 2 * (((2 * ((n + 1) + 1)) + (3 * ((n + 1)).choose 2) + (3 * ((n + 1)).choose 3))) := by
    intro n
    simp only [Nat.add_assoc, Nat.choose_succ_succ, Nat.choose_one_right, Nat.choose_zero_right]
    ring
  have h := multiplicative_certificate (2 : ℚ) (fun n : ℕ => ((2 * (n + 1)) + (3 * (n).choose 2) + (3 * (n).choose 3))) (fun n : ℕ => (3 * (n + 1))) (by norm_num) he
  convert h.1 using 1 <;> norm_num [w405]
theorem w405_domain : ∀ n, w405 n ≠ 0 := by
  intro n; unfold w405; positivity
theorem w405_unique (a : ℕ → ℚ) (hi : a 0 = (4 : ℚ)) (hj : a 1 = (16 : ℚ))
    (ha : ∀ n : ℕ, a (n + 2) * a n = (2 : ℚ) ^ ((3 * (n + 1))) * a (n + 1) ^ 2) :
    ∀ n, a n = w405 n := by
  apply general_second_unique w405_valid
  apply multiplicative_from_relation a (4 : ℚ) (16 : ℚ) (fun n => (2 : ℚ) ^ ((3 * (n + 1)))) hi hj
  · norm_num
  · norm_num
  · intro n; positivity
  · exact ha
#print axioms w405_domain
#print axioms w405_valid
#print axioms w405_unique

def w406 (n : ℕ) : ℚ := ((3 : ℚ) ^ ((n + 1) + (9 * (n).choose 2) + (6 * (n).choose 3)))
theorem w406_valid : GeneralSecondCertificate w406 (3 : ℚ) (9 : ℚ) (fun n x y => (3 : ℚ) ^ ((3 + (6 * (n + 1)))) * y ^ 2 / x) := by
  have he : ∀ n : ℕ, ((((n + 2) + 1) + (9 * ((n + 2)).choose 2) + (6 * ((n + 2)).choose 3))) + (((n + 1) + (9 * (n).choose 2) + (6 * (n).choose 3))) = ((3 + (6 * (n + 1)))) + 2 * ((((n + 1) + 1) + (9 * ((n + 1)).choose 2) + (6 * ((n + 1)).choose 3))) := by
    intro n
    simp only [Nat.add_assoc, Nat.choose_succ_succ, Nat.choose_one_right, Nat.choose_zero_right]
    ring
  have h := multiplicative_certificate (3 : ℚ) (fun n : ℕ => ((n + 1) + (9 * (n).choose 2) + (6 * (n).choose 3))) (fun n : ℕ => (3 + (6 * (n + 1)))) (by norm_num) he
  convert h.1 using 1 <;> norm_num [w406]
theorem w406_domain : ∀ n, w406 n ≠ 0 := by
  intro n; unfold w406; positivity
theorem w406_unique (a : ℕ → ℚ) (hi : a 0 = (3 : ℚ)) (hj : a 1 = (9 : ℚ))
    (ha : ∀ n : ℕ, a (n + 2) * a n = (3 : ℚ) ^ ((3 + (6 * (n + 1)))) * a (n + 1) ^ 2) :
    ∀ n, a n = w406 n := by
  apply general_second_unique w406_valid
  apply multiplicative_from_relation a (3 : ℚ) (9 : ℚ) (fun n => (3 : ℚ) ^ ((3 + (6 * (n + 1))))) hi hj
  · norm_num
  · norm_num
  · intro n; positivity
  · exact ha
#print axioms w406_domain
#print axioms w406_valid
#print axioms w406_unique

def w407 (n : ℕ) : ℚ := ((((2 : ℚ) * ((n : ℚ) + 1)) + (1 : ℚ)) * ((((2 : ℚ) / 3) * (((n : ℚ) + 1) + (-1 : ℚ))) + (1 : ℚ)) * ((3 : ℚ) ^ n))
def w407_base (n : ℕ) : ℚ := (((((2 : ℚ) / 3) * (((n : ℚ) + 1) + (-1 : ℚ))) + (1 : ℚ)) * ((3 : ℚ) ^ n))
theorem w407_base_valid : SecondCertificate w407_base (1 : ℚ) (5 : ℚ) (6 : ℚ) (-9 : ℚ) := by
  constructor
  · norm_num [w407_base]
  · norm_num [w407_base]
  · intro n
    simp only [w407_base, Nat.cast_add, Nat.cast_one, pow_succ, pow_add] at *
    ring
theorem w407_valid : WeightedSumCertificate w407 (3 : ℚ) (fun n : ℕ => (((2 : ℚ) * ((n : ℚ) + 1)) + (1 : ℚ))) (9 : ℚ) (-4 : ℚ) := by
  apply weighted_sum_from_second w407 w407_base (fun n : ℕ => (((2 : ℚ) * ((n : ℚ) + 1)) + (1 : ℚ))) (3 : ℚ) (1 : ℚ) (5 : ℚ) (9 : ℚ) (-4 : ℚ)
  · convert w407_base_valid using 1 <;> norm_num
  · norm_num
  · intro n; positivity
  · intro n; simp only [w407, w407_base] <;> ring
  · norm_num [w407]
theorem w407_unique (a : ℕ → ℚ) (ha : WeightedSumCertificate a (3 : ℚ) (fun n : ℕ => (((2 : ℚ) * ((n : ℚ) + 1)) + (1 : ℚ))) (9 : ℚ) (-4 : ℚ)) :
    ∀ n, a n = w407 n := weighted_sum_unique w407_valid ha
#print axioms w407_valid
#print axioms w407_unique

def w408 (n : ℕ) : ℚ := ((((n : ℚ) + 1) ^ 2) * ((((-1 : ℚ) / 2) * ((2 : ℚ) ^ n)) + ((3 : ℚ) ^ n)))
def w408_base (n : ℕ) : ℚ := ((((-1 : ℚ) / 2) * ((2 : ℚ) ^ n)) + ((3 : ℚ) ^ n))
theorem w408_base_valid : SecondCertificate w408_base ((1 : ℚ) / 2) (2 : ℚ) (5 : ℚ) (-6 : ℚ) := by
  constructor
  · norm_num [w408_base]
  · norm_num [w408_base]
  · intro n
    simp only [w408_base, Nat.cast_add, Nat.cast_one, pow_succ, pow_add] at *
    ring
theorem w408_valid : WeightedSumCertificate w408 ((1 : ℚ) / 2) (fun n : ℕ => (((n : ℚ) + 1) ^ 2)) (6 : ℚ) (-2 : ℚ) := by
  apply weighted_sum_from_second w408 w408_base (fun n : ℕ => (((n : ℚ) + 1) ^ 2)) ((1 : ℚ) / 2) ((1 : ℚ) / 2) (2 : ℚ) (6 : ℚ) (-2 : ℚ)
  · convert w408_base_valid using 1 <;> norm_num
  · norm_num
  · intro n; positivity
  · intro n; simp only [w408, w408_base] <;> ring
  · norm_num [w408]
theorem w408_unique (a : ℕ → ℚ) (ha : WeightedSumCertificate a ((1 : ℚ) / 2) (fun n : ℕ => (((n : ℚ) + 1) ^ 2)) (6 : ℚ) (-2 : ℚ)) :
    ∀ n, a n = w408 n := weighted_sum_unique w408_valid ha
#print axioms w408_valid
#print axioms w408_unique

def w409 (n : ℕ) : ℚ := ((((n : ℚ) + 1) + (1 : ℚ)) * ((((3 : ℚ) / 2) * (((n : ℚ) + 1) + (-1 : ℚ))) + (3 : ℚ)) * ((2 : ℚ) ^ n))
def w409_base (n : ℕ) : ℚ := (((((3 : ℚ) / 2) * (((n : ℚ) + 1) + (-1 : ℚ))) + (3 : ℚ)) * ((2 : ℚ) ^ n))
theorem w409_base_valid : SecondCertificate w409_base (3 : ℚ) (9 : ℚ) (4 : ℚ) (-4 : ℚ) := by
  constructor
  · norm_num [w409_base]
  · norm_num [w409_base]
  · intro n
    simp only [w409_base, Nat.cast_add, Nat.cast_one, pow_succ, pow_add] at *
    ring
theorem w409_valid : WeightedSumCertificate w409 (6 : ℚ) (fun n : ℕ => (((n : ℚ) + 1) + (1 : ℚ))) (4 : ℚ) (-1 : ℚ) := by
  apply weighted_sum_from_second w409 w409_base (fun n : ℕ => (((n : ℚ) + 1) + (1 : ℚ))) (6 : ℚ) (3 : ℚ) (9 : ℚ) (4 : ℚ) (-1 : ℚ)
  · convert w409_base_valid using 1 <;> norm_num
  · norm_num
  · intro n; positivity
  · intro n; simp only [w409, w409_base] <;> ring
  · norm_num [w409]
theorem w409_unique (a : ℕ → ℚ) (ha : WeightedSumCertificate a (6 : ℚ) (fun n : ℕ => (((n : ℚ) + 1) + (1 : ℚ))) (4 : ℚ) (-1 : ℚ)) :
    ∀ n, a n = w409 n := weighted_sum_unique w409_valid ha
#print axioms w409_valid
#print axioms w409_unique

def w410 (n : ℕ) : ℚ := ((((3 : ℚ) * ((2 : ℚ) ^ n)) + ((4 : ℚ) ^ n)) / (((n : ℚ) + 1) * (((n : ℚ) + 1) + (1 : ℚ))))
theorem w410_valid : GeneralSecondCertificate w410 (2 : ℚ) ((5 : ℚ) / 3) (fun n x y => (((6 : ℚ) * (((n : ℚ) + 1) + (1 : ℚ)) * (((n : ℚ) + 1) + (2 : ℚ))) * y + ((-8 : ℚ) * ((n : ℚ) + 1) * (((n : ℚ) + 1) + (1 : ℚ))) * x) / ((((n : ℚ) + 1) + (2 : ℚ)) * (((n : ℚ) + 1) + (3 : ℚ)))) := by
  apply linear_second_certificate w410 (2 : ℚ) ((5 : ℚ) / 3) (fun n => ((((n : ℚ) + 1) + (2 : ℚ)) * (((n : ℚ) + 1) + (3 : ℚ)))) (fun n => ((6 : ℚ) * (((n : ℚ) + 1) + (1 : ℚ)) * (((n : ℚ) + 1) + (2 : ℚ)))) (fun n => ((-8 : ℚ) * ((n : ℚ) + 1) * (((n : ℚ) + 1) + (1 : ℚ))))
  · norm_num [w410]
  · norm_num [w410]
  · intro n; positivity
  · intro n
    have h0_0 : (((n : ℚ) + 1) * (((n : ℚ) + 1) + (1 : ℚ))) ≠ 0 := by positivity
    have h1_0 : ((((n + 1) : ℚ) + 1) * ((((n + 1) : ℚ) + 1) + (1 : ℚ))) ≠ 0 := by positivity
    have h2_0 : ((((n + 2) : ℚ) + 1) * ((((n + 2) : ℚ) + 1) + (1 : ℚ))) ≠ 0 := by positivity
    simp only [w410, Nat.cast_add, Nat.cast_one, pow_succ, pow_add] at *
    field_simp [h0_0, h1_0, h2_0] <;> ring
theorem w410_unique (a : ℕ → ℚ) (hi : a 0 = (2 : ℚ)) (hj : a 1 = ((5 : ℚ) / 3))
    (ha : ∀ n : ℕ, ((((n : ℚ) + 1) + (2 : ℚ)) * (((n : ℚ) + 1) + (3 : ℚ))) * a (n + 2) = ((6 : ℚ) * (((n : ℚ) + 1) + (1 : ℚ)) * (((n : ℚ) + 1) + (2 : ℚ))) * a (n + 1) + ((-8 : ℚ) * ((n : ℚ) + 1) * (((n : ℚ) + 1) + (1 : ℚ))) * a n) :
    ∀ n, a n = w410 n := by
  apply general_second_unique w410_valid
  exact linear_second_certificate a (2 : ℚ) ((5 : ℚ) / 3) (fun n => ((((n : ℚ) + 1) + (2 : ℚ)) * (((n : ℚ) + 1) + (3 : ℚ)))) (fun n => ((6 : ℚ) * (((n : ℚ) + 1) + (1 : ℚ)) * (((n : ℚ) + 1) + (2 : ℚ)))) (fun n => ((-8 : ℚ) * ((n : ℚ) + 1) * (((n : ℚ) + 1) + (1 : ℚ)))) hi hj (by intro n; positivity) ha
#print axioms w410_valid
#print axioms w410_unique

def w411 (n : ℕ) : ℚ := ((((2 : ℚ) * ((2 : ℚ) ^ n)) + ((2 : ℚ) * ((3 : ℚ) ^ n))) / (((n : ℚ) + 1) * (((n : ℚ) + 1) + (2 : ℚ))))
theorem w411_valid : GeneralSecondCertificate w411 ((4 : ℚ) / 3) ((5 : ℚ) / 4) (fun n x y => (((5 : ℚ) * (((n : ℚ) + 1) + (1 : ℚ)) * (((n : ℚ) + 1) + (3 : ℚ))) * y + ((-6 : ℚ) * ((n : ℚ) + 1) * (((n : ℚ) + 1) + (2 : ℚ))) * x) / ((((n : ℚ) + 1) + (2 : ℚ)) * (((n : ℚ) + 1) + (4 : ℚ)))) := by
  apply linear_second_certificate w411 ((4 : ℚ) / 3) ((5 : ℚ) / 4) (fun n => ((((n : ℚ) + 1) + (2 : ℚ)) * (((n : ℚ) + 1) + (4 : ℚ)))) (fun n => ((5 : ℚ) * (((n : ℚ) + 1) + (1 : ℚ)) * (((n : ℚ) + 1) + (3 : ℚ)))) (fun n => ((-6 : ℚ) * ((n : ℚ) + 1) * (((n : ℚ) + 1) + (2 : ℚ))))
  · norm_num [w411]
  · norm_num [w411]
  · intro n; positivity
  · intro n
    have h0_0 : (((n : ℚ) + 1) * (((n : ℚ) + 1) + (2 : ℚ))) ≠ 0 := by positivity
    have h1_0 : ((((n + 1) : ℚ) + 1) * ((((n + 1) : ℚ) + 1) + (2 : ℚ))) ≠ 0 := by positivity
    have h2_0 : ((((n + 2) : ℚ) + 1) * ((((n + 2) : ℚ) + 1) + (2 : ℚ))) ≠ 0 := by positivity
    simp only [w411, Nat.cast_add, Nat.cast_one, pow_succ, pow_add] at *
    field_simp [h0_0, h1_0, h2_0] <;> ring
theorem w411_unique (a : ℕ → ℚ) (hi : a 0 = ((4 : ℚ) / 3)) (hj : a 1 = ((5 : ℚ) / 4))
    (ha : ∀ n : ℕ, ((((n : ℚ) + 1) + (2 : ℚ)) * (((n : ℚ) + 1) + (4 : ℚ))) * a (n + 2) = ((5 : ℚ) * (((n : ℚ) + 1) + (1 : ℚ)) * (((n : ℚ) + 1) + (3 : ℚ))) * a (n + 1) + ((-6 : ℚ) * ((n : ℚ) + 1) * (((n : ℚ) + 1) + (2 : ℚ))) * a n) :
    ∀ n, a n = w411 n := by
  apply general_second_unique w411_valid
  exact linear_second_certificate a ((4 : ℚ) / 3) ((5 : ℚ) / 4) (fun n => ((((n : ℚ) + 1) + (2 : ℚ)) * (((n : ℚ) + 1) + (4 : ℚ)))) (fun n => ((5 : ℚ) * (((n : ℚ) + 1) + (1 : ℚ)) * (((n : ℚ) + 1) + (3 : ℚ)))) (fun n => ((-6 : ℚ) * ((n : ℚ) + 1) * (((n : ℚ) + 1) + (2 : ℚ)))) hi hj (by intro n; positivity) ha
#print axioms w411_valid
#print axioms w411_unique

def w412 (n : ℕ) : ℚ := ((((5 : ℚ) * ((2 : ℚ) ^ n)) + ((2 : ℚ) * ((3 : ℚ) ^ n))) / (((n : ℚ) + 1) ^ 2))
theorem w412_valid : GeneralSecondCertificate w412 (7 : ℚ) (4 : ℚ) (fun n x y => (((5 : ℚ) * ((((n : ℚ) + 1) + (1 : ℚ)) ^ 2)) * y + ((-6 : ℚ) * (((n : ℚ) + 1) ^ 2)) * x) / ((((n : ℚ) + 1) + (2 : ℚ)) ^ 2)) := by
  apply linear_second_certificate w412 (7 : ℚ) (4 : ℚ) (fun n => ((((n : ℚ) + 1) + (2 : ℚ)) ^ 2)) (fun n => ((5 : ℚ) * ((((n : ℚ) + 1) + (1 : ℚ)) ^ 2))) (fun n => ((-6 : ℚ) * (((n : ℚ) + 1) ^ 2)))
  · norm_num [w412]
  · norm_num [w412]
  · intro n; positivity
  · intro n
    have h0_0 : (((n : ℚ) + 1) ^ 2) ≠ 0 := by positivity
    have h1_0 : ((((n + 1) : ℚ) + 1) ^ 2) ≠ 0 := by positivity
    have h2_0 : ((((n + 2) : ℚ) + 1) ^ 2) ≠ 0 := by positivity
    simp only [w412, Nat.cast_add, Nat.cast_one, pow_succ, pow_add] at *
    field_simp [h0_0, h1_0, h2_0] <;> ring
theorem w412_unique (a : ℕ → ℚ) (hi : a 0 = (7 : ℚ)) (hj : a 1 = (4 : ℚ))
    (ha : ∀ n : ℕ, ((((n : ℚ) + 1) + (2 : ℚ)) ^ 2) * a (n + 2) = ((5 : ℚ) * ((((n : ℚ) + 1) + (1 : ℚ)) ^ 2)) * a (n + 1) + ((-6 : ℚ) * (((n : ℚ) + 1) ^ 2)) * a n) :
    ∀ n, a n = w412 n := by
  apply general_second_unique w412_valid
  exact linear_second_certificate a (7 : ℚ) (4 : ℚ) (fun n => ((((n : ℚ) + 1) + (2 : ℚ)) ^ 2)) (fun n => ((5 : ℚ) * ((((n : ℚ) + 1) + (1 : ℚ)) ^ 2))) (fun n => ((-6 : ℚ) * (((n : ℚ) + 1) ^ 2))) hi hj (by intro n; positivity) ha
#print axioms w412_valid
#print axioms w412_unique

def w413 (n : ℕ) : ℚ := ((1 : ℚ) / (((6 : ℚ) * ((2 : ℚ) ^ n)) + ((-1 : ℚ) * ((n : ℚ) + 1)) + (-1 : ℚ)))
def w413_base (n : ℕ) : ℚ := (((6 : ℚ) * ((2 : ℚ) ^ n)) + ((-1 : ℚ) * ((n : ℚ) + 1)) + (-1 : ℚ))
theorem w413_base_valid : FirstCertificate w413_base (4 : ℚ) (fun n x => ((2 : ℚ) * x + ((n : ℚ) + 1)) / (1 : ℚ)) := by
  apply linear_certificate w413_base (4 : ℚ) (fun n : ℕ => (1 : ℚ)) (fun n : ℕ => (2 : ℚ)) (fun n : ℕ => ((n : ℚ) + 1))
  · norm_num [w413_base]
  · intro n; positivity
  · intro n
    simp only [w413_base, Nat.cast_add, Nat.cast_one, pow_succ, pow_add] at *
    ring
theorem w413_positive (n : ℕ) : 0 < w413_base n := by
  induction n with
  | zero => norm_num [w413_base]
  | succ n ih => rw [w413_base_valid.recurrence]; positivity
theorem w413_valid : FirstCertificate w413 ((1 : ℚ) / 4) (fun n x => (1 : ℚ) * x / ((2 : ℚ) + ((n : ℚ) + 1) * x)) := by
  have h := reciprocal_certificate w413_base_valid w413_positive (by intro n; positivity)
  have heq : w413 = (fun n => 1 / w413_base n) := by
    funext n
    simp [w413, w413_base, div_eq_mul_inv] <;> ring
  rw [heq]
  convert h.1 using 1 <;> norm_num
theorem w413_domain : (∀ n : ℕ, (2 : ℚ) + ((n : ℚ) + 1) * w413 n ≠ 0) ∧ (∀ n, w413 n ≠ 0) := by
  have h := reciprocal_certificate w413_base_valid w413_positive (by intro n; positivity)
  simpa [w413, w413_base, div_eq_mul_inv] using h.2
#print axioms w413_domain
theorem w413_unique (a : ℕ → ℚ) (ha : FirstCertificate a ((1 : ℚ) / 4) (fun n x => (1 : ℚ) * x / ((2 : ℚ) + ((n : ℚ) + 1) * x))) :
    ∀ n, a n = w413 n := first_unique w413_valid ha
#print axioms w413_valid
#print axioms w413_unique

def w414 (n : ℕ) : ℚ := ((1 : ℚ) / (((9 : ℚ) * ((3 : ℚ) ^ n)) + ((-3 : ℚ) * ((n : ℚ) + 1)) + ((-3 : ℚ) / 2)))
def w414_base (n : ℕ) : ℚ := (((9 : ℚ) * ((3 : ℚ) ^ n)) + ((-3 : ℚ) * ((n : ℚ) + 1)) + ((-3 : ℚ) / 2))
theorem w414_base_valid : FirstCertificate w414_base ((9 : ℚ) / 2) (fun n x => ((3 : ℚ) * x + ((6 : ℚ) * ((n : ℚ) + 1))) / (1 : ℚ)) := by
  apply linear_certificate w414_base ((9 : ℚ) / 2) (fun n : ℕ => (1 : ℚ)) (fun n : ℕ => (3 : ℚ)) (fun n : ℕ => ((6 : ℚ) * ((n : ℚ) + 1)))
  · norm_num [w414_base]
  · intro n; positivity
  · intro n
    simp only [w414_base, Nat.cast_add, Nat.cast_one, pow_succ, pow_add] at *
    ring
theorem w414_positive (n : ℕ) : 0 < w414_base n := by
  induction n with
  | zero => norm_num [w414_base]
  | succ n ih => rw [w414_base_valid.recurrence]; positivity
theorem w414_valid : FirstCertificate w414 ((2 : ℚ) / 9) (fun n x => (1 : ℚ) * x / ((3 : ℚ) + ((6 : ℚ) * ((n : ℚ) + 1)) * x)) := by
  have h := reciprocal_certificate w414_base_valid w414_positive (by intro n; positivity)
  have heq : w414 = (fun n => 1 / w414_base n) := by
    funext n
    simp [w414, w414_base, div_eq_mul_inv] <;> ring
  rw [heq]
  convert h.1 using 1 <;> norm_num
theorem w414_domain : (∀ n : ℕ, (3 : ℚ) + ((6 : ℚ) * ((n : ℚ) + 1)) * w414 n ≠ 0) ∧ (∀ n, w414 n ≠ 0) := by
  have h := reciprocal_certificate w414_base_valid w414_positive (by intro n; positivity)
  simpa [w414, w414_base, div_eq_mul_inv] using h.2
#print axioms w414_domain
theorem w414_unique (a : ℕ → ℚ) (ha : FirstCertificate a ((2 : ℚ) / 9) (fun n x => (1 : ℚ) * x / ((3 : ℚ) + ((6 : ℚ) * ((n : ℚ) + 1)) * x))) :
    ∀ n, a n = w414 n := first_unique w414_valid ha
#print axioms w414_valid
#print axioms w414_unique

def w415 (n : ℕ) : ℚ := ((((n : ℚ) + 1) * (((n : ℚ) + 1) + (1 : ℚ))) / ((((1 : ℚ) / 2) * ((3 : ℚ) ^ n)) + (1 : ℚ)))
def w415_base (n : ℕ) : ℚ := (((((1 : ℚ) / 2) * ((3 : ℚ) ^ n)) + (1 : ℚ)) / (((n : ℚ) + 1) * (((n : ℚ) + 1) + (1 : ℚ))))
theorem w415_base_valid : FirstCertificate w415_base ((3 : ℚ) / 4) (fun n x => (((3 : ℚ) * ((n : ℚ) + 1) * (((n : ℚ) + 1) + (1 : ℚ))) * x + (-2 : ℚ)) / ((((n : ℚ) + 1) + (1 : ℚ)) * (((n : ℚ) + 1) + (2 : ℚ)))) := by
  apply linear_certificate w415_base ((3 : ℚ) / 4) (fun n : ℕ => ((((n : ℚ) + 1) + (1 : ℚ)) * (((n : ℚ) + 1) + (2 : ℚ)))) (fun n : ℕ => ((3 : ℚ) * ((n : ℚ) + 1) * (((n : ℚ) + 1) + (1 : ℚ)))) (fun n : ℕ => (-2 : ℚ))
  · norm_num [w415_base]
  · intro n; positivity
  · intro n
    have hd0 : (((n : ℚ) + 1) * (((n : ℚ) + 1) + (1 : ℚ))) ≠ 0 := by positivity
    have he0 : ((((n + 1) : ℚ) + 1) * ((((n + 1) : ℚ) + 1) + (1 : ℚ))) ≠ 0 := by positivity
    simp only [w415_base, Nat.cast_add, Nat.cast_one, pow_succ, pow_add] at *
    field_simp [hd0, he0] <;> ring
theorem w415_positive (n : ℕ) : 0 < w415_base n := by
  unfold w415_base
  positivity
theorem w415_valid : FirstCertificate w415 ((4 : ℚ) / 3) (fun n x => ((((n : ℚ) + 1) + (1 : ℚ)) * (((n : ℚ) + 1) + (2 : ℚ))) * x / (((3 : ℚ) * ((n : ℚ) + 1) * (((n : ℚ) + 1) + (1 : ℚ))) + (-2 : ℚ) * x)) := by
  have h := reciprocal_certificate w415_base_valid w415_positive (by intro n; positivity)
  have heq : w415 = (fun n => 1 / w415_base n) := by
    funext n
    simp [w415, w415_base, div_eq_mul_inv] <;> ring
  rw [heq]
  convert h.1 using 1 <;> norm_num
theorem w415_domain : (∀ n : ℕ, ((3 : ℚ) * ((n : ℚ) + 1) * (((n : ℚ) + 1) + (1 : ℚ))) + (-2 : ℚ) * w415 n ≠ 0) ∧ (∀ n, w415 n ≠ 0) := by
  have h := reciprocal_certificate w415_base_valid w415_positive (by intro n; positivity)
  simpa [w415, w415_base, div_eq_mul_inv] using h.2
#print axioms w415_domain
theorem w415_unique (a : ℕ → ℚ) (ha : FirstCertificate a ((4 : ℚ) / 3) (fun n x => ((((n : ℚ) + 1) + (1 : ℚ)) * (((n : ℚ) + 1) + (2 : ℚ))) * x / (((3 : ℚ) * ((n : ℚ) + 1) * (((n : ℚ) + 1) + (1 : ℚ))) + (-2 : ℚ) * x))) :
    ∀ n, a n = w415 n := first_unique w415_valid ha
#print axioms w415_valid
#print axioms w415_unique

end Recurrence
