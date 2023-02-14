
import tactic                 
import data.set.basic  
import data.real.basic
import algebra.order.floor

-- proof based on
-- https://math.stackexchange.com/questions/233670/nested-division-in-the-ceiling-function


theorem nested_ceil (m n : ℤ ) (hmpos : m > 0) (hnpos : n > 0) (x : ℝ) : ⌈x / (m * n)⌉ = ⌈(⌈x/m⌉ : ℝ) /(n : ℝ)⌉ :=
begin
  set k := ⌈x/↑m⌉,
  have h_le : ⌈x / ((m : ℝ)  * (n : ℝ)⌉  ≤ ⌈(k : ℝ) / (n : ℝ)⌉,
  {
    suffices h0 : x/(↑m * ↑n) ≤ k/↑n,
    {
      exact int.ceil_mono h0,
    },
    suffices h1 : x / ↑m ≤ ↑k,
    {
      rw ← div_div,
      have hnpos' : 0 < (n : ℝ ) := int.cast_pos.mpr hnpos,
      rwa div_le_div_right hnpos',
    },
    exact int.le_ceil (x / ↑m),

  },

  have h_ge : ⌈x / ((m : ℝ)  * (n : ℝ))⌉  ≥ ⌈(k : ℝ) / (n : ℝ)⌉,
  {
    by_contra hc, push_neg at hc,
    have h1 := int.lt.dest hc,
    cases h1 with l hl,
    rw nat.succ_eq_add_one at hl, push_cast at hl,
    
    have hl2 : ↑l ≥ 0 := zero_le ↑l,
    have hq1 :  ⌈x / (↑m * ↑n)⌉ ≤ ⌈x / (↑m * ↑n)⌉ + ↑l  := by linarith, 
    have hq2 :  ⌈x / (↑m * ↑n)⌉ + ↑l <  ⌈(k : ℝ)  / (n : ℝ)  ⌉ := by linarith,
    set q := ⌈x / (↑m * ↑n)⌉ + ↑l,
    have hq1' : x / (↑m * ↑n) ≤ q := int.ceil_le.mp hq1,
    have hq2' : (q : ℝ)  < (k : ℝ)  / (n : ℝ)  := int.lt_ceil.mp hq2,
    have hnpos' : 0 ≤ n := le_of_lt hnpos,
    have hnpos'' : 0 ≤ (n : ℝ)  := int.cast_nonneg.mpr hnpos',
    have hq'' : (x / (↑m * ↑n)) * ↑n  ≤ q * ↑n  := mul_le_mul_of_nonneg_right hq1' hnpos'',
    rw div_mul at hq'',
    have h_n_neq_zero : n  ≠ 0 := ne_of_gt hnpos,   
    have h_n_neq_zero' : ( n : ℝ )  ≠ 0 := int.cast_ne_zero.mpr h_n_neq_zero, 
    rw ← mul_div at hq'',  
    rw div_self h_n_neq_zero' at hq'',
    rw mul_one at hq'',
    have hqn : (q : ℝ) * (n : ℝ) = ↑(q * n) := (int.cast_mul q n).symm,
    have hk : ⌈(x / ↑m)⌉ ≤ (q * n),
    {
      refine int.ceil_le.mpr _,
      rw hqn at hq'',
      exact hq'',
    },

    have hq2'' := mul_lt_mul_of_pos_right hq2' (int.cast_pos.mpr hnpos),
    rw div_mul at hq2'',
    rw div_self h_n_neq_zero' at hq2'',
    rw div_one at hq2'',
    rw hqn at hq2'',
    have hk' : (⌈x / ↑m⌉ : ℝ)  ≤ ↑(q * n) := int.cast_le.mpr hk,
    linarith,
  },
  exact le_antisymm h_le h_ge,

end