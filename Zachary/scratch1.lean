import tactic                 
import data.set.basic  
import data.real.basic
import algebra.order.floor
import algebra.order.ring
import algebra.order.field.basic

-- floor function lemmas (Joe Roberts Number Theory)

lemma floor_lemma1 {α : ℝ} : (α - 1 < (⌊α⌋ : ℝ)) ∧ ((⌊α⌋ : ℝ)  ≤ α) :=
begin
  split, {
    exact int.sub_one_lt_floor α,
  }, {
    exact int.floor_le α, 
  }
end


lemma floor_lemma2 {α : ℝ} {n : ℤ} : ⌊α + (n : ℝ)⌋ = ⌊α⌋ + n  :=
begin
  exact int.floor_add_int α n,
end

lemma floor_lemma3 (m n : ℤ) (h_npos : 0 < n): (∃ r : ℝ, ((m : ℝ)  = ((⌊(m : ℝ) / (n : ℝ)⌋ * n) : ℝ)  + r ) ∧ (0 ≤ r ) ∧ (r < n)) :=
begin
 have h0 := int.floor_add_fract ((( m : ℝ)) / (n : ℝ )),
 have hfrac := int.fract_lt_one ((m : ℝ)/ (n : ℝ) ),
 have hpos := int.fract_nonneg ((m : ℝ)/ (n : ℝ) ),
 use int.fract ((( m : ℝ)) / (n : ℝ )) * (n : ℝ),
 split, {
  have h1 : ((⌊(m : ℝ)  / (n : ℝ)⌋ : ℝ)  + int.fract ((m : ℝ)  / (n : ℝ) )) * (n : ℝ) = ((m : ℝ)  / (n : ℝ)) * (n : ℝ) := congr_fun (congr_arg has_mul.mul h0) ↑n,
  rw [add_mul] at h1,
  rw div_mul at h1,
  have h_n_neq_zero : n ≠ 0 := ne_of_gt h_npos,
  have h_n_neq_zero_in_R : (n : ℝ)  ≠ 0 := int.cast_ne_zero.mpr h_n_neq_zero,
  have h2 : (n : ℝ)  / (n : ℝ)  = 1 := div_self h_n_neq_zero_in_R,
  rw h2 at h1,
  rw div_one at h1,
  linarith,
 }, {
  have h3 : (n : ℝ) > 0 := int.cast_pos.mpr h_npos,
  split, {
    exact (zero_le_mul_right h3).mpr hpos,
  }, {
    exact mul_lt_of_lt_one_left h3 hfrac,
  }
 }
end

-- lemma floor_lemma3_1 (m n : ℤ) (h_npos : 0 < n): (∃ r : ℤ, (m   = (⌊↑m   / (n : ℚ)⌋ * n)   + r ) ∧ (0 ≤ r ) ∧ (↑r  < n)) :=
-- begin
--   use (m % n) ,
--   split, {
--     have hr := nat.floor_div_eq_div
--   }, {

--   }
--   have h_n_neq_zero : n ≠ 0 := ne_of_gt h_npos,
--   have h_n_neq_zero_in_R : (n : ℝ)  ≠ 0 := int.cast_ne_zero.mpr h_n_neq_zero,
--   have h0 := int.fract_div_mul_self_add_zsmul_eq (n : ℝ) (m : ℝ)  h_n_neq_zero_in_R,
--   have hmn : ↑m / (n : ℝ)  = 1 + ((m - n) : ℝ) /(n : ℝ) := by sorry,
--   have h_int : int.fract (↑m / ↑n) * ↑n ∈ ℤ
--   sorry,
-- end

-- lemma floor_lemma4 (m n : ℤ) (h_npos : 0 < n): ((m : ℝ )  + 1)/(n : ℝ )  ≤ ⌊(m : ℝ ) /(n : ℝ )⌋ + 1 :=
-- begin

--   -- SKETCH

--   -- m/n = (k n + a) / n = k + a/n

--   -- m = ⌊m/n⌋ * n + r, 0 ≤ r < n
--   -- m/n = ⌊m/n⌋ + r/n
--   -- (m+1)/n = ⌊m/n⌋ + (r+1)/n
--   -- use that (r + 1)/n  ≤  1 
--   -- ∴ (m+1)/n ≤ ⌊m/n⌋ + 1 ∎


--   have h_n_neq_zero : n ≠ 0 := ne_of_gt h_npos,
--   have h_n_neq_zero_in_R : (n : ℝ)  ≠ 0 := int.cast_ne_zero.mpr h_n_neq_zero,

--   have h0 := floor_lemma3 m n h_npos,
--   cases h0 with r h0,
--   have h1 := (div_left_inj' h_n_neq_zero_in_R).mpr h0.1,
--   rw [add_div, mul_div_assoc] at h1,
--   rw [(div_self h_n_neq_zero_in_R), mul_one] at h1,
--   have h2 : ↑m / ↑n + 1/ (n : ℝ) = ↑⌊↑m / ↑n⌋ + r / ↑n + 1/(n : ℝ) := congr_fun (congr_arg has_add.add h1) (1 / ↑n),
--   rw ← add_div at h2, 
--   rw add_assoc at h2, 
--   rw ← add_div at h2,
--   have h3 : (r+1)/n ≤ 1, -- true since r ∈ ℤ 
--   {
--     sorry,
--   },
--   linarith,
  
-- end

-- lemma floor_lemma4_1 (m n : ℤ) (h_npos : 0 < n): ((m : ℝ )  + 1)/(n : ℝ )  ≤ ⌊(m : ℝ ) /(n : ℝ )⌋ + 1 :=
-- begin

--   -- SKETCH
--   -- m = ⌊m/n⌋ * n + r, 0 ≤ r < n
--   -- m/n = ⌊m/n⌋ + r/n
--   -- (m+1)/n = ⌊m/n⌋ + (r+1)/n
--   -- use that (r + 1)/n  ≤  1 
--   -- ∴ (m+1)/n ≤ ⌊m/n⌋ + 1 ∎
  
  
  
-- end


-- lemma floor_lemma5 {n : ℤ} (h_npos : 0 < n) (α : ℝ) : ⌊(⌊α⌋ : ℝ) /(n : ℝ)⌋  = ⌊α/(n : ℝ )⌋ :=
-- begin
--   have h_npos2 : 0 < (n : ℝ) := int.cast_pos.mpr h_npos,

--   have h0 : (⌊(⌊α⌋ : ℝ) /(n : ℝ)⌋ : ℝ)  ≤  (⌊α⌋ : ℝ) /(n : ℝ ) := int.floor_le (↑⌊α⌋ / ↑n),

--   have h1 : (⌊α⌋ : ℝ)  / (n : ℝ) ≤ α / (n : ℝ) := (div_le_div_right h_npos2).mpr (int.floor_le α),

--   have h2k0 :  α - 1 < (⌊α⌋ : ℝ)  := int.sub_one_lt_floor α,
--   have h2k1 : α <  (⌊α⌋ : ℝ) + 1 := by linarith, 
--   have h2 : α / (n : ℝ) <  (⌊α⌋ + 1) / (n : ℝ) := (div_lt_div_right h_npos2).mpr h2k1,
--   clear h2k0 h2k1,

--   have h3 := floor_lemma3 ⌊α⌋ n h_npos,

--   -- inequality shows floor 
--   have  h4 : (⌊(⌊α⌋ : ℝ) / (n : ℝ)⌋ : ℝ ) ≤ α / (n : ℝ)  := by linarith,
--   have  h5 :  α / (n : ℝ) < (⌊(⌊α⌋ : ℝ) / (n : ℝ)⌋ : ℝ ) + 1 := by linarith,
--   exact (int.floor_eq_iff.mpr ⟨h4, h5⟩).symm,

-- end

lemma nested_ceil (m n : ℤ ) (hmpos : m > 0) (hnpos : n > 0) (x : ℝ) : ⌈x / (m * n)⌉ = ⌈(⌈x/m⌉ : ℝ) /(n : ℝ)⌉ :=
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


-- define beatty sequence


def B : ℝ → set ℕ := λ r, { n | ∃ m : ℕ , ((n : ℕ) = nat.floor ((m : ℝ)  * r) ) }



lemma mem_b_iff {q : ℝ} {k : ℕ}  : (k ∈ (B q)) ↔ ∃ m : ℕ, (k : ℕ)  = nat.floor ((m : ℝ) * q ) :=
begin
  split, 
  intro hk,
  rw set.mem_def at hk,
  assumption,
  intro h,
  rw set.mem_def,
  assumption,
end

lemma floor_lemma {q : ℝ} {j n : ℕ} (hq : 1 < q ) (hj : j = nat.floor (↑n * q)) : ((j : ℝ) ≤ ↑n * q)  ∧ ↑n * q < (j : ℝ) + 1 :=
begin
  have hn : 0 ≤ n  := zero_le n, 
  have hn2 : 0 ≤ (n : ℝ) := nat.cast_nonneg n,
  have hq2 : 0 ≤ q := by linarith, 
  have hnq : 0 ≤ ↑n * q := mul_nonneg hn2 hq2, 
  exact (nat.floor_eq_iff hnq).mp (eq.symm hj),
end

-- Forward direction:
-- complementary beatty sequences partition ℕ 

theorem beatty_theorem_forward ( q : ℝ ) (hq : irrational q) (h_q_gt_one : q > 1) : ∀ n : ℕ,  (((n ∈ (B q)) ∨ (n ∈ B ( q/(q-1))))) ∧ (((B q) ∩ (B (q/(q-1)))) = ∅)
:= 
begin
  set p := (q/(q-1)),
  intro n,
  split, {
  -- by contradiction, 
  --by_contra h, push_neg at h, rw mem_b_iff at *, push_neg at h,
  sorry,


  }, {
  -- by contradiction, "collision"
  by_contra h, change B q ∩ B p ≠ ∅ at h,
  have hs : set.nonempty (B q ∩ B p) := set.ne_empty_iff_nonempty.mp h,
  rw set.nonempty_def at hs,
  rcases hs with ⟨x, hxq, hxp⟩,
  rw mem_b_iff at *,
  cases hxq with m hm,
  cases hxp with l hl,

  have h_p_gt_one : p > 1 := by sorry,

  have hpq : p + q = 1 := by sorry,

  have hm2 := floor_lemma h_q_gt_one hm,
  have hl2 := floor_lemma h_p_gt_one hl,
  sorry,
  -- have h0: ↑x / p ≤ m := by library_search,

  }
end


-- Converse direction
-- if two beatty sequence B p, B q partition ℕ, then 1/p + 1/ q = 1


