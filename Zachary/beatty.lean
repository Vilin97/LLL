import tactic                 
import data.set.basic  
import data.real.basic
import algebra.order.floor
import data.real.irrational
import data.set.basic




def B : ℝ → set ℤ  := λ r, { n | ∃ m : ℕ   , (m ≥ 1 ) ∧ ((n : ℤ ) = int.floor ((m : ℝ)  * r) ) }


lemma mem_b_iff {q : ℝ} {k : ℤ }  : (k ∈ (B q)) ↔ ∃ m : ℕ  , (m ≥ 1 ) ∧ (k : ℤ )  = int.floor ((m : ℝ) * q ) :=
begin
  split, 
  intro hk,
  rw set.mem_def at hk,
  exact hk,
  intro h,
  rw set.mem_def,
  assumption,
end

-- Forward direction:
-- complementary beatty sequences partition ℕ 

theorem beatty_theorem_forward ( q : ℝ ) (hq : irrational q) (h_q_gt_one : q > 1) : 
∀ n : ℕ,  (((↑n ∈ (B q)) ∨ (↑n ∈ B ( q/(q-1))))) ∧ (((B q) ∩ (B (q/(q-1)))) = ∅)
:= 
begin
  set p := (q/(q-1)),
  intro n,
  split, {
  -- by contradiction, "anti-collision" 
  rw mem_b_iff,
  rw mem_b_iff, 
  by_contra h, 
  push_neg at h;

  cases h with hnq hnp,

  -- How to do this?
  -- rw int.floor_eq_iff
  -- let m be an arbitrary integer
   
  sorry,


  }, {
  -- by contradiction, "collision"
  by_contra h, 
  change B q ∩ B p ≠ ∅ at h,
  rw ← set.nonempty_iff_ne_empty at h,
  rw set.nonempty_def at h,

  rcases h with ⟨x, hxq, hxp⟩,
  rw mem_b_iff at *,

  cases hxq with m hm,
  cases hxp with l hl,

  have hm2 := int.floor_eq_iff.mp (hm.2).symm, 
  cases hm2 with hm_le hm_gt,
  have hm_neq : ↑x ≠ ↑m * q ,
  {
    -- use irrationality
    have h_m_neq_zero : m ≠ 0 := by linarith,
    have h_m_neq_zero' : (m : ℚ)  ≠ 0 := nat.cast_ne_zero.mpr h_m_neq_zero,
    have h_rhs : irrational (↑(m : ℚ) * q) := irrational.rat_mul hq h_m_neq_zero',
    exact (irrational.ne_int h_rhs x).symm,
  },
  have hm_lt : ↑x < ↑m * q := ne.lt_of_le hm_neq hm_le,
  have hq_pos : q > 0 := by linarith,
  have hm_lt2 : ↑x/q < ↑m := (div_lt_iff hq_pos).mpr hm_lt,
  have hl_gt2 : ↑m  < (↑x + 1)/q  := (lt_div_iff hq_pos).mpr hm_gt,

  have hl2 := int.floor_eq_iff.mp (hl.2).symm,
  cases hl2 with hl_le hl_gt,
  have hl_neq : ↑x ≠ ↑l * p ,
  {
    -- use irrationality
    have hp : irrational p,
    {
      rw irrational_iff_ne_rational,
      by_contra hc, push_neg at hc,
      rcases hc with ⟨a, b, hf⟩,
      change (q / (q - 1)) = ↑a / ↑b at hf,

      have hf1 : (q - 1) * (q / (q - 1)) = (q - 1) * (↑a / ↑b) := congr_arg (has_mul.mul (q - 1)) hf,
      rw mul_div at hf1,
      rw mul_comm (q - 1) q at hf1,
      rw ← mul_div at hf1,
      rw div_self at hf1,
      rw mul_one at hf1,

      have hf12 : q * ↑b  = (q - 1) * (↑a / ↑b) * ↑b := congr_arg (has_mul.mul ↑b ) hf1,




      -- q * (↑a - ↑b) = a 
      -- show contradiction since lhs is irrational, a - b ≠ 0 
    },
    have h_l_neq_zero : l ≠ 0 := by linarith,
    have h_l_neq_zero' : (l : ℚ)  ≠ 0 := nat.cast_ne_zero.mpr h_l_neq_zero,
    have h_rhs : irrational (↑(l : ℚ) * p) := irrational.rat_mul hp h_l_neq_zero',
    exact (irrational.ne_int h_rhs x).symm,
  },
  have hl_lt : ↑x < ↑l * p := ne.lt_of_le hl_neq hl_le,
  have hp_pos : p > 0 := by sorry,
  have hl_lt2 : ↑x/p < ↑l := (div_lt_iff hp_pos).mpr hl_lt,
  have hl_gt2 : ↑l  < (↑x + 1)/p  := (lt_div_iff hp_pos).mpr hl_gt,

  have h_lt : ↑x/p + ↑x/q < ↑m + ↑l := by linarith,
  have h_gt : ↑m + ↑l  < (↑x + 1)/p + (↑x + 1)/q  := by linarith,

  have hqp : 1/p + 1/q = 1,
  {
    change  1/(q / (q - 1)) + 1/q = 1,
    sorry,
  },

  have hs0 : (↑x + 1) / p + (↑x + 1) / q = (↑x + 1) * (1 / p + 1 / q) := by sorry,
  rw hs0 at h_gt,
  rw hqp at h_gt,
  rw mul_one at h_gt,

  have hs1 : ↑x  / p + ↑x / q = ↑x  * (1 / p + 1 / q) := by sorry,
  rw hs1 at h_lt,
  rw hqp at h_lt,
  rw mul_one at h_lt,

  have h_lt' : ↑m  + ↑l < x + 1 := by sorry,
  have h_gt' : x < ↑m + ↑l  := by sorry,
  linarith,

  }


end


-- Converse direction
-- if two beatty sequence B p, B q partition ℕ, then 1/p + 1/ q = 1






-- Upensky's theorem 
-- https://mathweb.ucsd.edu/~fan/ron/papers/63_01_uspensky.pdf