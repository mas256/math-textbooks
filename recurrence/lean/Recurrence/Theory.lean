import Mathlib

namespace Recurrence

-- Internal index 0 denotes the school-mathematics term a₁.
structure FirstCertificate (f : ℕ → ℚ) (initial : ℚ)
    (step : ℕ → ℚ → ℚ) : Prop where
  init : f 0 = initial
  recurrence : ∀ n, f (n + 1) = step n (f n)

theorem first_unique {f a : ℕ → ℚ} {initial : ℚ} {step : ℕ → ℚ → ℚ}
    (hf : FirstCertificate f initial step)
    (ha : FirstCertificate a initial step) : ∀ n, a n = f n := by
  intro n
  induction n with
  | zero => exact ha.init.trans hf.init.symm
  | succ n ih => simpa only [ha.recurrence, hf.recurrence, ih]

-- A cross-multiplied recurrence is converted only after proving P ≠ 0.
theorem linear_certificate (f : ℕ → ℚ) (initial : ℚ) (P Q R : ℕ → ℚ)
    (hi : f 0 = initial) (hp : ∀ n, P n ≠ 0)
    (hs : ∀ n, P n * f (n + 1) = Q n * f n + R n) :
    FirstCertificate f initial (fun n x => (Q n * x + R n) / P n) := by
  refine ⟨hi, ?_⟩
  intro n
  apply (eq_div_iff (hp n)).2
  simpa only [mul_comm] using hs n

-- Inversion preserves the recurrence, and the next denominator is nonzero
-- at every natural index. Finite term sampling is not used in this proof.
theorem reciprocal_certificate {v : ℕ → ℚ} {initial : ℚ} {P Q R : ℕ → ℚ}
    (hv : FirstCertificate v initial (fun n x => (Q n * x + R n) / P n))
    (hpos : ∀ n, 0 < v n) (hp : ∀ n, 0 < P n) :
    FirstCertificate (fun n => 1 / v n) (1 / initial)
      (fun n x => P n * x / (Q n + R n * x)) ∧
    (∀ n, Q n + R n * (1 / v n) ≠ 0) ∧
    (∀ n, 1 / v n ≠ 0) := by
  have hden (n : ℕ) : Q n + R n * (1 / v n) = P n * v (n + 1) / v n := by
    have hstep := (eq_div_iff (ne_of_gt (hp n))).1 (hv.recurrence n)
    apply (eq_div_iff (ne_of_gt (hpos n))).2
    field_simp
    nlinarith [hstep]
  have hn (n : ℕ) : Q n + R n * (1 / v n) ≠ 0 := by
    rw [hden n]
    exact ne_of_gt (div_pos (mul_pos (hp n) (hpos (n + 1))) (hpos n))
  refine ⟨⟨by simpa only [hv.init], ?_⟩, hn, ?_⟩
  · intro n
    rw [hden n]
    field_simp [ne_of_gt (hpos n), ne_of_gt (hpos (n + 1)), ne_of_gt (hp n)]
  · intro n
    exact one_div_ne_zero (ne_of_gt (hpos n))

structure SecondCertificate (f : ℕ → ℚ) (initial second p q : ℚ) : Prop where
  init : f 0 = initial
  second : f 1 = second
  recurrence : ∀ n, f (n + 2) = p * f (n + 1) + q * f n

theorem second_unique {f a : ℕ → ℚ} {initial second p q : ℚ}
    (hf : SecondCertificate f initial second p q)
    (ha : SecondCertificate a initial second p q) : ∀ n, a n = f n := by
  have hpair : ∀ n, a n = f n ∧ a (n + 1) = f (n + 1) := by
    intro n
    induction n with
    | zero => exact ⟨ha.init.trans hf.init.symm, ha.second.trans hf.second.symm⟩
    | succ n ih =>
      refine ⟨ih.2, ?_⟩
      simpa only [Nat.add_assoc, ha.recurrence, hf.recurrence, ih.1, ih.2]
  exact fun n => (hpair n).1

end Recurrence
