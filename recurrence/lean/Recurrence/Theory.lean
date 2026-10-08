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
    field_simp [ne_of_gt (hpos n)]
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

-- Variable coefficients and multiplicative relations use an explicit step.
structure GeneralSecondCertificate (f : ℕ → ℚ) (initial second : ℚ)
    (step : ℕ → ℚ → ℚ → ℚ) : Prop where
  init : f 0 = initial
  second : f 1 = second
  recurrence : ∀ n, f (n + 2) = step n (f n) (f (n + 1))

theorem general_second_unique {f a : ℕ → ℚ} {initial second : ℚ}
    {step : ℕ → ℚ → ℚ → ℚ}
    (hf : GeneralSecondCertificate f initial second step)
    (ha : GeneralSecondCertificate a initial second step) : ∀ n, a n = f n := by
  have hpair : ∀ n, a n = f n ∧ a (n + 1) = f (n + 1) := by
    intro n
    induction n with
    | zero => exact ⟨ha.init.trans hf.init.symm, ha.second.trans hf.second.symm⟩
    | succ n ih =>
      refine ⟨ih.2, ?_⟩
      simpa only [Nat.add_assoc, ha.recurrence, hf.recurrence, ih.1, ih.2]
  exact fun n => (hpair n).1

theorem linear_second_certificate (f : ℕ → ℚ) (initial second : ℚ)
    (P Q R : ℕ → ℚ) (hi : f 0 = initial) (hj : f 1 = second)
    (hp : ∀ n, P n ≠ 0)
    (hs : ∀ n, P n * f (n + 2) = Q n * f (n + 1) + R n * f n) :
    GeneralSecondCertificate f initial second
      (fun n x y => (Q n * y + R n * x) / P n) := by
  refine ⟨hi, hj, ?_⟩
  intro n
  apply (eq_div_iff (hp n)).2
  simpa only [mul_comm] using hs n

theorem multiplicative_certificate (base : ℚ) (E F : ℕ → ℕ)
    (hb : 0 < base) (he : ∀ n, E (n + 2) + E n = F n + 2 * E (n + 1)) :
    GeneralSecondCertificate (fun n => base ^ E n) (base ^ E 0) (base ^ E 1)
      (fun n x y => base ^ F n * y ^ 2 / x) ∧
      (∀ n, base ^ E n ≠ 0) := by
  have hn : ∀ n, base ^ E n ≠ 0 := by
    intro n
    exact ne_of_gt (pow_pos hb _)
  refine ⟨⟨rfl, rfl, ?_⟩, hn⟩
  intro n
  apply (eq_div_iff (hn n)).2
  calc
    base ^ E (n + 2) * base ^ E n = base ^ (E (n + 2) + E n) := (pow_add _ _ _).symm
    _ = base ^ (F n + 2 * E (n + 1)) := by rw [he]
    _ = base ^ F n * (base ^ E (n + 1)) ^ 2 := by
      rw [pow_add, Nat.mul_comm 2 (E (n + 1)), pow_mul]

-- Positive initial values make the displayed product relation a unique step.
theorem multiplicative_from_relation (a : ℕ → ℚ) (initial second : ℚ)
    (C : ℕ → ℚ) (hi : a 0 = initial) (hj : a 1 = second)
    (hi0 : 0 < initial) (hj0 : 0 < second) (hc : ∀ n, 0 < C n)
    (hs : ∀ n, a (n + 2) * a n = C n * a (n + 1) ^ 2) :
    GeneralSecondCertificate a initial second (fun n x y => C n * y ^ 2 / x) := by
  have hpair : ∀ n, 0 < a n ∧ 0 < a (n + 1) := by
    intro n
    induction n with
    | zero => simpa only [hi, hj] using And.intro hi0 hj0
    | succ n ih =>
      refine ⟨ih.2, ?_⟩
      change 0 < a (n + 2)
      have he := (eq_div_iff (ne_of_gt ih.1)).2 (hs n)
      rw [he]
      exact div_pos (mul_pos (hc n) (pow_pos ih.2 _)) ih.1
  refine ⟨hi, hj, ?_⟩
  intro n
  exact (eq_div_iff (ne_of_gt (hpair n).1)).2 (hs n)

structure WeightedSumCertificate (f : ℕ → ℚ) (initial : ℚ)
    (g : ℕ → ℚ) (α β : ℚ) : Prop where
  init : f 0 = initial
  scale_ne_zero : ∀ n, g n ≠ 0
  recurrence : ∀ n, f (n + 1) = g (n + 1) *
    (α * (f n / g n) + β * (∑ k ∈ Finset.range (n + 1), f k / g k))

theorem weighted_sum_unique {f a g : ℕ → ℚ} {initial α β : ℚ}
    (hf : WeightedSumCertificate f initial g α β)
    (ha : WeightedSumCertificate a initial g α β) : ∀ n, a n = f n := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    cases n with
    | zero => exact ha.init.trans hf.init.symm
    | succ n =>
      have hn := ih n (Nat.lt_succ_self n)
      have hsum : (∑ k ∈ Finset.range (n + 1), a k / g k) =
          ∑ k ∈ Finset.range (n + 1), f k / g k := by
        apply Finset.sum_congr rfl
        intro k hk
        rw [ih k (Finset.mem_range.mp hk)]
      rw [ha.recurrence, hf.recurrence, hn, hsum]

theorem second_to_sum {b : ℕ → ℚ} {initial second α β : ℚ}
    (hb : SecondCertificate b initial second (α + β + 1) (-α))
    (hboundary : second = (α + β) * initial) :
    ∀ n, b (n + 1) = α * b n + β * (∑ k ∈ Finset.range (n + 1), b k) := by
  intro n
  induction n with
  | zero =>
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, hb.init, hb.second]
    rw [hboundary]
    ring
  | succ n ih =>
    change b (n + 2) = α * b (n + 1) + β * (∑ k ∈ Finset.range (n + 1 + 1), b k)
    rw [hb.recurrence, Finset.sum_range_succ]
    nlinarith [ih]

theorem weighted_sum_from_second (f b g : ℕ → ℚ) (initial first second α β : ℚ)
    (hb : SecondCertificate b first second (α + β + 1) (-α))
    (hboundary : second = (α + β) * first) (hg : ∀ n, g n ≠ 0)
    (hf : ∀ n, f n = g n * b n) (hi : f 0 = initial) :
    WeightedSumCertificate f initial g α β := by
  have hdiv : ∀ n, f n / g n = b n := by
    intro n
    rw [hf n]
    field_simp [hg n]
  refine ⟨hi, hg, ?_⟩
  intro n
  have hsum : (∑ k ∈ Finset.range (n + 1), f k / g k) =
      ∑ k ∈ Finset.range (n + 1), b k := by
    apply Finset.sum_congr rfl
    intro k _
    exact hdiv k
  rw [hf (n + 1), hdiv n, hsum, ← second_to_sum hb hboundary n]

end Recurrence
