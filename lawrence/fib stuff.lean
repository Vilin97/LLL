import tactic
import data.real.sqrt

/- fibonacci sequence definition -/
/- here, we want N -> Z instead of N -> N because of potential issues that may come up when we try to go for (-1)^n. just makes my life easier ngl... -/
def fib : ℕ -> ℤ
| 0 := 0
| 1 := 1
| (x+2) := fib (x) + fib (x+1)

/- end of preamble thing, now we try to prove F_n * F_{n+2} - F_{n+1}^2 = (-1)^n -/

lemma fib_rule (n : ℕ) : fib(n + 2) = fib(n) + fib(n + 1) := rfl
lemma fib_rule' (n : ℕ) (hn : n > 0) : fib(n + 1) = fib(n) + fib(n - 1) :=
begin
  cases hn,
  {
    simp [fib],
  },
  {
    simp [fib],
    rw add_comm,
  }
end
lemma negative_fib_rule (n : ℕ) : fib(n + 2) - fib(n + 1) = fib (n) :=
begin
  rw [fib_rule],
  ring,
end

-- F_n * F_(n+2) - F_(n+1)^2 = (-1)^n
theorem fib_close_square (n : ℕ) : fib(n) * fib(n + 2) - fib(n + 1)^2 = (-1)^(n+1) :=
begin
  induction n,
  {
    rw [zero_add, zero_add],
    simp [fib],
  },

  have H1 : fib n_n.succ * fib n_n.succ + fib n_n.succ * fib (n_n.succ + 1) - fib (n_n.succ + 1) ^ 2 = fib n_n.succ * fib n_n.succ - fib (n_n.succ + 1) * (fib (n_n.succ + 1) - fib n_n.succ),
    { ring },

  have H2 : fib n_n.succ * fib n_n.succ - fib (n_n.succ + 1) * (fib (n_n.succ + 1) - fib n_n.succ) = fib n_n.succ * fib n_n.succ - fib (n_n.succ + 1) * fib (n_n.succ - 1),
    { rw negative_fib_rule, ring },

  have H3 : fib (n_n + 1) ^ 2 - fib n_n * fib (n_n + 2) = (-1) * (fib n_n * fib (n_n + 2) - fib (n_n + 1) ^ 2),
    { linarith, },

  have H4 : (-1 : ℤ) ^ (n_n + 2) = (-1 : ℤ) * (-1) ^ (n_n + 1),
    { conv begin to_rhs, congr, rw ←pow_one (-1 : ℤ), skip end, rw ←pow_add, conv begin to_rhs, congr, skip, rw nat.add_left_comm end, },

  {
    rw [fib_rule, mul_add],
    rw [H1, H2],
    ring_nf,
    rw [←nat.add_one],
    simp,
    rw [add_assoc],
    simp,
    -- conv begin to_lhs, congr, skip, congr, skip, congr, congr, skip, change 2, end,
    rw [H3, H4],
    linarith,
  },
end

theorem strong_induction {P : ℕ → Prop} {H : ∀ n : ℕ, (∀ m : ℕ, m < n → P m) → P n} (n : ℕ) : P n :=
begin
  have H1 : ∀ k ≤ n, P k, {
    induction n,
    {
      intros k hk,
      apply H,
      intros m hm,
      cases hk, cases hm,
    },
    {
      intros k hk,
      apply H,
      intros m hm,
      apply n_ih,
      apply nat.le_of_lt_succ,
      apply lt_of_lt_of_le,
      exact hm,
      exact hk,
    },
  },
  apply H1,
  linarith,
end

-- Fibonacci Addition Law : F_(m+n) = F_(n+1) F_m + F_n F_(m-1)
-- help from gareth ma on leanprover
theorem fib_add (m n : ℕ) (hm : 0 < m) : fib(m + n) = fib(n + 1) * fib(m) + fib(n) * fib(m - 1) :=
begin
  apply strong_induction n,
  intros k h,
  cases k,
  { simp [fib], },
  { cases k,
    {
      simp [fib, fib_rule' m hm],
    },
    { simp only [nat.succ_eq_add_one, add_assoc],
      norm_num,
      rw [← add_assoc, fib, nat.succ_eq_add_one, add_assoc m k 1],
      rw [h k _, h (k + 1) _],
      rw [fib_rule (k + 1), fib_rule k],
      ring,
      exact nat.lt_succ_self _,
      exact lt_trans (nat.lt_succ_self _) (nat.lt_succ_self _),
    },
  },
end

-- Fibonacci Divisibility : F_m | F_n if m | n.
-- help from gareth ma on leanprover
theorem fib_divide (m n : ℕ) (hm : m > 0) (hyp_div : m ∣ n) : fib(m) ∣ fib(n) :=
begin
  rcases hyp_div with ⟨k, rfl⟩,
  induction k,
  { simp only [fib, mul_zero, dvd_zero], },
  { rw [nat.succ_eq_add_one, mul_add, add_comm, mul_one, fib_add m (m * k_n) hm],
    simp only [dvd_add, dvd_mul_left, dvd_mul_of_dvd_left k_ih], },
end

-- todo: prove binet
theorem binet_formula (n : ℕ) : (fib(n) : ℝ) = (1 / real.sqrt(5)) * (((1 + real.sqrt(5)) / 2)^n + ((1 - real.sqrt(5)) / 2)^n) :=
begin
  set φ := (1 + real.sqrt(5)) / 2, 
  set τ := (1 - real.sqrt(5)) / 2,
    
  sorry,
end

--useful tactics: norm_num, norm_cast, ring

#check real.sqrt(5)