import tactic                 
import data.set.basic  
import data.real.basic
import algebra.order.floor
import data.real.irrational
import data.set.basic
import data.real.basic
import data.rat.basic
import .greg_lemmas


-- TO DO
-- change beatty def to m ≥ 0 !!!
-- prove collision part



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

lemma self_div_self_sub_one_neq_one (q : ℝ ) (hq : q > 1) : q/(q-1) ≠ 1 :=
begin
  by_contra hc,
  have hc' : (q - 1) * (q / (q - 1)) = (q - 1 ) * 1 := congr_arg (has_mul.mul (q - 1)) hc,
  rw [← mul_div_assoc, mul_one, mul_comm, mul_div_assoc, div_self, mul_one] at hc',
  repeat {linarith,},
end 

lemma self_div_self_sub_one_neq_zero (q : ℝ ) (hq : q > 1) : q/(q-1) ≠ 0 :=
begin
  by_contra hc,
  have hc' : (q - 1) * (q / (q - 1)) = (q - 1 ) * 0 := congr_arg (has_mul.mul (q - 1)) hc,
  rw mul_zero at hc',
  rw ← mul_div_assoc at hc',
  rw mul_comm at hc',
  rw mul_div_assoc at hc',
  rw div_self at hc',
  rw mul_one at hc',
  linarith,
  linarith,
end 

lemma irrat_mul_sub_irrat (a b : ℤ) (q : ℝ) (hsub : (a : ℝ)  - ↑b ≠ 0) (hq : irrational q) :
  irrational (q *(↑a - ↑b)) :=
begin
  have hsub' : a - b ≠ 0,
  {
    norm_cast at *,
  },
  norm_cast,
  rw irrational_mul_int_iff,
  exact ⟨hsub', hq⟩,
end

lemma irrat_div_irrat_sub_one_irrat (q : ℝ) (hq : irrational q) (h_q_gt_one : q > 1) :
  irrational (q / (q - 1)) :=
begin
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

  have hf2 : q * ↑b  = ((q - 1) * (↑a / ↑b)) * ↑b  := congr_fun (congr_arg has_mul.mul hf1) ↑b,
  rw mul_assoc at hf2,
  rw div_mul at hf2,
  rw div_self at hf2,
  rw div_one at hf2,
  rw sub_mul at hf2,
  rw one_mul at hf2,  
  have hf3 : ↑a = q * ↑a - q * ↑b  := by linarith,
  rw ← mul_sub at hf3,
  have h_a_neq_b : (a : ℝ)  - ↑b ≠ 0 , {
    by_contra hc,
    have hr : (a : ℝ)  / ↑b = 1,
    {
      rw sub_eq_zero at hc,
      have hdiv: (b : ℝ) / ↑b = ↑a / ↑b := congr_fun (congr_arg has_div.div (eq.symm hc)) ↑b, 
      rw div_self at hdiv,
      exact hdiv.symm,
      by_contra hc,
      rw hc at hf,
      rw div_zero at hf,
      apply self_div_self_sub_one_neq_zero q h_q_gt_one,
      exact hf,
    },
    rw hr at hf,
    apply self_div_self_sub_one_neq_one q h_q_gt_one,
    exact hf,
  },    
  have h_irrational : irrational (q * (↑a - ↑b)) := irrat_mul_sub_irrat a b q h_a_neq_b hq,
  rw ← hf3 at h_irrational,
  have h_rational : ¬ (irrational ↑a) := int.not_irrational a,
  exact hq (false.rec (q ∈ set.range coe) (h_rational h_irrational)),
  tactic.swap,
  linarith,
  by_contra hc,
  rw hc at hf,
  rw div_zero at hf,
  apply self_div_self_sub_one_neq_zero q h_q_gt_one,
  exact hf,
end

lemma mul_sum_reciprocals (q p a : ℝ) : a / p + a / q = a* (1 / p + 1 / q) :=
begin
 rw mul_add,
 repeat {rw ← mul_div_assoc, rw mul_one},
end

lemma add_one_mul_sum_reciprocals (q p : ℝ) (x : ℤ) : (↑x  + 1) / p + (↑x  + 1) / q = (↑x  + 1)* (1 / p + 1 / q) :=
begin
 rw mul_add,
 repeat {rw ← mul_div_assoc, rw mul_one},
end

lemma sum_reciprocals_eq_one (q : ℝ) (hq : q > 1) : 1/ (q/(q-1)) + 1 / q = 1 :=
begin
 ring_nf,
 simp,
 rw mul_sub,
 simp,
 rwa inv_mul_cancel,
 linarith,
end

lemma beatty_theorem_forward_anti_collision ( q : ℝ ) (hq : irrational q) (h_q_gt_one : q > 1) : 
∀ n : ℕ,  (((↑n ∈ (B q)) ∨ (↑n ∈ B ( q/(q-1))))) :=
begin

  -- need n > 1 !!!

  intro n,
  rw mem_b_iff,
  rw mem_b_iff, 
  by_contra h, 
  push_neg at h;

  cases h with hnq hnp,
  
  -- let m be an arbitrary integer !!!
  
  sorry,
end

lemma beatty_theorem_forward_collision ( q : ℝ ) (hq : irrational q) (h_q_gt_one : q > 1) : 
∀ n : ℕ,  (((B q) ∩ (B (q/(q-1)))) = ∅) :=
begin
  -- by contradiction, "collision"
  intro n,
  set p := (q/(q-1)),
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
  have hm_neq : ↑x ≠ ↑m * q,
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
      change irrational (q/(q-1)),
      exact irrat_div_irrat_sub_one_irrat q hq h_q_gt_one,
    },
    have h_l_neq_zero : l ≠ 0 := by linarith,
    have h_l_neq_zero' : (l : ℚ)  ≠ 0 := nat.cast_ne_zero.mpr h_l_neq_zero,
    have h_rhs : irrational (↑(l : ℚ) * p) := irrational.rat_mul hp h_l_neq_zero',
    exact (irrational.ne_int h_rhs x).symm,
  },
  have hl_lt : ↑x < ↑l * p := ne.lt_of_le hl_neq hl_le,
  have hp_pos : p > 0 := p_is_positive q h_q_gt_one,
  have hl_lt2 : ↑x/p < ↑l := (div_lt_iff hp_pos).mpr hl_lt,
  have hl_gt2 : ↑l  < (↑x + 1)/p  := (lt_div_iff hp_pos).mpr hl_gt,

  have h_lt : ↑x/p + ↑x/q < ↑m + ↑l := by linarith,
  have h_gt : ↑m + ↑l  < (↑x + 1)/p + (↑x + 1)/q  := by linarith,

  have hqp : 1/p + 1/q = 1 := sum_reciprocals_eq_one q h_q_gt_one,

  have hs0 : (↑x + 1) / p + (↑x + 1) / q = (↑x + 1) * (1 / p + 1 / q) := add_one_mul_sum_reciprocals q p x,
  rw hs0 at h_gt,
  rw hqp at h_gt,
  rw mul_one at h_gt,

  have hs1 : ↑x  / p + ↑x / q = ↑x  * (1 / p + 1 / q) := mul_sum_reciprocals q p (x : ℝ),
  rw hs1 at h_lt,
  rw hqp at h_lt,
  rw mul_one at h_lt,

  norm_cast at *,
  linarith,
end



-- Forward direction:
-- complementary beatty sequences partition ℕ 

theorem beatty_theorem_forward ( q : ℝ ) (hq : irrational q) (h_q_gt_one : q > 1) : 
∀ n : ℕ,  (((↑n ∈ (B q)) ∨ (↑n ∈ B ( q/(q-1))))) ∧ (((B q) ∩ (B (q/(q-1)))) = ∅)
:= 
begin
  set p := (q/(q-1)),
  intro n,
  exact ⟨ beatty_theorem_forward_anti_collision q hq h_q_gt_one n, beatty_theorem_forward_collision q hq h_q_gt_one n⟩,
end


-- Converse direction
-- if two beatty sequence B p, B q partition ℕ, then 1/p + 1/ q = 1






-- Upensky's theorem 
-- https://mathweb.ucsd.edu/~fan/ron/papers/63_01_uspensky.pdf