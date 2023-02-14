/-
  Alex Sanchez
  This file formalizes the first ** problem in Herstein's
  celebrated text, "Topics in Algebra".
-/

import tactic -- tactics
import group_theory.subgroup.basic -- subgroups
import group_theory.order_of_element -- elemental order
import data.nat.factorization.basic -- prime factorization

variables (G : Type) [comm_group G]

-- tests
example (a : ℕ) : nat.lcm (0 : ℕ) a = (0 : ℕ) :=
begin
  exact nat.lcm_zero_left a,
end

-- proofs

theorem single_star (h h' : G) : ∃ g : G, order_of g = nat.lcm (order_of h) (order_of h') :=
begin
  --break into cases with both nonzero, otherwise etc.
  let m : ℕ := order_of h,
  let n : ℕ := order_of h',
  by_cases hyp : m = 0 ∨ n = 0, { --trivial case
    cases hyp, {
      use h,
      conv
      begin
        congr, {
          change m,
          rw hyp,
        }, {
          congr, {
            change m,
            rw hyp,
          }, {
            change n,
          }
        }
      end,
      exact (nat.lcm_zero_left n).symm,
    }, {
      use h',
      conv
      begin
        congr, {
          change n,
          rw hyp,
        }, {
          congr, {
            change m,
          }, {
            change n,
            rw hyp,
          }
        }
      end,
      exact (nat.lcm_zero_right m).symm,
    },
  }, { --nontrivial case
    -- get nice forms of assumptions
    
    -- refactor to get both
    have fin_h : m > 0 :=
    begin
      have temp : ¬m=0 :=
      begin
        rw not_or_distrib at hyp,
        exact hyp.left,
      end,
      have temp_two : m ≥ 0 := zero_le m,
      have temp_three : m > 0 ∨ m = 0 :=
      begin
        have temp_temp : m > 0 ∨ m = 0 ∨ m < 0 := trichotomous m 0,
        cases temp_temp with a b, {
          left,
          exact a,
        }, {
          cases b with c d, {
            right,
            exact c,
          }, {
            exfalso,
            apply not_lt.mpr temp_two,
            exact d,
          },
        },
      end,
      cases temp_three with a b, {
        exact a,
      }, {
        exfalso,
        exact temp b,
      },
    end,
    let ps_m := nat.factorization m,
    let ps_n := nat.factorization n,
    -- find some way to identify the finite support
    
    sorry,
  },
end

theorem double_star (H H' : subgroup G) : ∃ H'' : subgroup G, nat.card H'' = nat.lcm (nat.card H) (nat.card H') :=
begin

  sorry,
end