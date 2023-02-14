import tactic                 
import data.nat.lattice       -- for well-ordering for naturals 
import data.set.basic         -- for creating sets

-- Define a set for the remainder of a/b :
-- remainder_set takes a and b and returns set of all possible nonnegative remainders of a/b

def remainder_set : ℤ → ℤ → set ℕ := λ a, λ b, { y | ∃ x : ℤ, (y : ℤ) = a - b * x}

-- lemma using the definition of remainder_set (to make it easier to work with)

lemma mem_remainder_set_iff {a b : ℤ} {k : ℕ}  : (k ∈ remainder_set a b) ↔
  ∃ x : ℤ, (k : ℤ) = a - b * x :=
  begin
    split, {
      intro h,
      rw set.mem_def at h,
      exact h,
    }, {
      intro h,
      rw set.mem_def,
      exact h,
    }
  end

/-       PROOF SKETCH

  (1) Define remainder set, S
      -- let S = {a - bx : x ∈ ℤ ∧ a - bx ≥ 0}

  (2) Show S is nonempty
      -- use x = -|a|, and a + b |a| ≥ 0 to show S nonempty

  (3) Apply Well-ordering of naturals to show that S contains a minimum, r

  (4) Show r satisfies conditions of division algorithm
      -- show r < b, by contradiction if r - b ≥ 0 

  (5) Show uniqueness 

-/

lemma division_algorithm (a b : ℤ) (ha : a > 0) (hb : b > 0) : 
(∃ q r : ℤ, ((a = b * q + r) ∧ (0 ≤ r) ∧ (r < b))) :=
begin

  have hr : has_Inf.Inf (remainder_set a b) ∈ (remainder_set a b),
    {
      have hns : (remainder_set a b).nonempty,
        {
          have h1 : a + b * |a| ≥ 0,
            { 
              have h2 : |a| = a := abs_of_pos ha,
              rw h2,
              have h3 : b * a > 0 := mul_pos hb ha,
              have h4 : a + b * a > 0,
              {exact add_pos ha h3,},

              exact le_of_lt h4,
            },
          
          obtain ⟨k, hk⟩ := int.eq_coe_of_zero_le (h1),
          have hk_mem : k ∈ (remainder_set a b),
            {
              rw mem_remainder_set_iff,
              use (-|a|),
              linarith,
            },

          exact set.nonempty_of_mem hk_mem,
        },
      exact Inf_mem hns,
    },
  rw mem_remainder_set_iff at hr,
  cases hr with x hx,
  use x,
  use has_Inf.Inf (remainder_set a b),
  split, {
    finish,
  }, {
    split, {
      exact int.of_nat_nonneg (Inf (remainder_set a b)),
    }, {
      by_contra,
      simp only [not_lt, int.of_nat_eq_coe] at h,
      have j : ((has_Inf.Inf (remainder_set a b) ) - int.to_nat(b)) ∈ (remainder_set a b),
      { 
        rw mem_remainder_set_iff,
        use (x+1),
        have k : ↑(Inf (remainder_set a b)) - b = a - b * (x + 1) := by linarith,
        rw ← k,
        have hb2 : 0 ≤ b := le_of_lt hb,
        have hb3 := int.to_nat_of_nonneg hb2,
        nth_rewrite 3 ← hb3,
        have h2 : b.to_nat ≤ Inf (remainder_set a b) := by finish,
        rw int.coe_nat_sub h2,
      },
      have hle := nat.Inf_le j,
      have hg : Inf (remainder_set a b) - b.to_nat < Inf (remainder_set a b),
      { 
        have hb_nat : 0 < b.to_nat := by finish,
        have h_inf_le_b : b.to_nat ≤ Inf (remainder_set a b),
        {
          have hb2 : 0 ≤ b := le_of_lt hb,
          have hb3 := int.to_nat_of_nonneg hb2,
          have h2 : b.to_nat ≤ Inf (remainder_set a b) := by finish,
          exact h2,
        },
        exact nat.sub_lt_of_pos_le b.to_nat (Inf (remainder_set a b)) hb_nat h_inf_le_b,
      },
      exact nat.lt_le_antisymm hg hle,
    },
  },
end
 
#print division_algorithm

lemma division_algorithm_uniqueness (a b q1 q2 r1 r2 : ℤ) (hr1 : (0 ≤ r1) ∧ (r1 < b)) (hr2 : (0 ≤ r2) ∧ (r2 < b)) 
(ha : a > 0) (hb : b > 0) (hd1 : a = b * q1 + r1) (hd2 : a = b * q2 + r2) : (q1 = q2 ∧ r1 = r2) :=
begin
    have hq : q1 = q2,
    { 
      rw hd2 at hd1,
      have j : b * (q2 - q1) = r1 - r2 := by linarith,

      have k : -b < -r2 ∧ -r2 ≤ 0,
      { split, { linarith, }, { linarith, },},

      have l : -b < r1 - r2 ∧ r1 - r2 < b,
      { split, { linarith,}, { linarith,},},

      have m : -b < b*(q2 - q1) ∧ b*(q2 - q1) < b,
      { split, {linarith,}, {linarith,},},

      have i : -1 < q2 - q1 ∧ q2 - q1 < 1,
      {split, {
        cases m,
        --have hm2 : -b ≤ b * (q2 - q1) := le_of_lt m_left,
        rw (show -b = b*(-1), by linarith) at m_left,
        exact (mul_lt_mul_left hb).mp m_left,
      }, {
        cases m,
        -- ?a < ?c → ?d ≤ ?b → 0 ≤ ?c → 0 < ?d → ?a / ?b < ?c / ?d
        nth_rewrite 1 ← (mul_one b) at m_right,
        exact (mul_lt_mul_left hb).mp m_right,
      },},
      linarith,
  
    },
    split, {
      assumption,
    }, {
      rw hq at hd1,
      linarith,
    },

    
end

theorem division_algorithm' (a b : ℤ) (ha : a > 0) (hb : b > 0) : 
(∃ q r : ℤ, ((a = b * q + r) ∧ (0 ≤ r) ∧ (r < b))) :=
begin
  have h := euclidean_domain.quotient_mul_add_remainder_eq a b,
  use euclidean_domain.quotient a b,
  use euclidean_domain.remainder a b,
  sorry,
end

