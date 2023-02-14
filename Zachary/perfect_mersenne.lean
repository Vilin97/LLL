import tactic
import data.int.basic
import data.nat.prime
import number_theory.divisors
import algebra.big_operators.basic
import number_theory.arithmetic_function
--import geom_sum

open nat.arithmetic_function


def divisor_sum : ℕ → ℕ := (λ n : ℕ, n.divisors.sum id)


lemma perfect_iff_sum_divisors_eq_two_mul' (n : ℕ) (hpos : n > 0) : nat.perfect n ↔ divisor_sum n = 2*n :=
begin
  split, {
    intro hn,
    rwa nat.perfect_iff_sum_divisors_eq_two_mul at hn,
    assumption,
  }, {
    intro hn,
    rwa nat.perfect_iff_sum_divisors_eq_two_mul,
    assumption,
  }
end


lemma divisor_sum_is_multiplicative (m n : ℕ) (h_coprime : m.coprime n) 
      : (sigma 1 (m*n) = sigma 1 (m) * sigma 1 (n)) :=
begin
  have h := is_multiplicative_sigma,
  have l := is_multiplicative.map_mul_of_coprime 
  
end

lemma finite_power_series (a k : ℕ) : (finset.range k).sum (λ (x : ℕ), (a ^ x)) = (a^k - 1)/(a-1) :=
begin
  set S := (finset.range k).sum (λ (x : ℕ), a ^ x),
  suffices hS : S = 1 + a * (S - a^(k-1)),
  sorry,
  sorry,
end

-- lemma divisor_sum_of_prime_pow {p k : ℕ } (hk : k ≥ 1) (hp : nat.prime p) : ((nat.divisors (p^(k-1))).sum id = (p^k - 1)/(p-1)) :=
-- begin
--   rw nat.sum_divisors_prime_pow hp,
--   -- power series
--   have hs1 : k - 1 + 1 = k := by linarith,
--   rw hs1,
--   rw finite_power_series p k,
-- end

-- lemma obvious_lemma (a : ℕ) (k ≥ 1) : (2 * 2 ^ (k - 1) = 2^k) :=
-- begin
--   set n := k + 1,
--   induction n with d hd,
-- end

-- ∃ k, 2^k - 1 prime → 2^(k-1) * 2^k - 1 is perfect

lemma mersenne_to_perfect (k : ℕ) (hk : k > 0) (hp : nat.prime (2^k - 1)) : (nat.perfect ( 2^(k-1) * (2^k - 1))) :=
begin
  rw perfect_iff_sum_divisors_eq_two_mul',
  { 
    rw divisor_sum_is_multiplicative,
    {
      unfold divisor_sum,
      rw nat.prime.sum_divisors hp,
      have h2 : nat.prime 2 := nat.prime_two,
      rw nat.divisors_prime_pow h2,
      simp,
      have hs : k - 1 + 1 = k := by linarith,
      rw hs,
      rw finite_power_series 2 k,


      rw ← mul_assoc,
      have hpow : 2^k ≥ 1 := nat.one_le_pow' k 1,
      have hs1: 2^k - 1 + 1 = 2^k := by linarith,
      have hs2 : 2 * 2 ^ (k - 1) = 2^k,
      {
        zify,
        sorry,
      },
      rw [hs1, hs2, mul_comm],
    },

    {
      set d : ℕ := nat.gcd (2 ^ (k - 1)) (2 ^ k - 1),
      
      
      
    },

  },

  { simpa using nat.one_lt_two_pow k hk, },


end


-- n is an even perfect number → n = 2^(k-1) * (2^k - 1) for some mersenne prime 2^k - 1