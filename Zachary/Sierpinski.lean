import data.int.gcd   
import algebra.big_operators.basic
import data.nat.interval
import tactic


open_locale big_operators -- enable notation
open finset


-- Sierpinski #8

lemma  div_eq_iff_mul_eq' (a b c : ℤ) (hb : b ≠ 0 ) :
  (a : ℚ) / (b : ℚ) = (c : ℚ) ↔ (a : ℚ) = (b : ℚ) * (c : ℚ) :=
begin
  split, {
    intro h,
    library_search,
    
    
    

  }, {

  }
end

lemma  sum_of_powers_of_a_minus_1_eq_power_of_a_minus_1 (m a : ℕ) (ha : a > 1) :
  (a^m - 1) / (a - 1) = ∑i  in finset.range (m-1), (a^(i+1) - 1) :=
begin 
  induction m with k hk,
  simp,
  have ha2 : a - 1 > 0 := tsub_pos_of_lt ha,
  have ha3 : a - 1 ≠ 0 := ne_of_gt ha2,
  have hk2 : (a ^ k - 1)  = (a - 1) * (∑ (i : ℕ) in range (k - 1), (a ^ (i + 1) - 1)) := by library_search,

end

lemma  divides_a_minus_one_a_k_minus_one (a k : ℕ) (h : a > 1) :
  a - 1 ∣ a ^ k - 1 :=
begin
  sorry,
end


theorem  gcd_of_powers_minus_one_over_minus_one_eq_gcd_of_minus_one_and_m (m a : ℕ) (ha : 1 < a) :
  int.gcd((a^m - 1) / (a - 1)) (a - 1) = int.gcd (a - 1) m := 
begin
  have h := sum_of_powers_of_a_minus_1_eq_power_of_a_minus_1 m a ha,
  set d := int.gcd ((a^m - 1) / (a - 1)) (a - 1),
  have hd : d ∣ m := by sorry,
  set δ := int.gcd (↑a - 1) m,
  by_contra hc, 
  change (d ≠ δ) at hc,
  have hc2 : d < δ ∨ d > δ := ne.lt_or_lt hc,
  cases hc2,
  {
    -- show d ∣ (a-1), d ∣ m --> d ≥ δ
    sorry,
  }, {

  }
  


end


-- Sierpinski #10

theorem  odd_gt_1_iff_dvd_sum_of_powers (n : ℕ) (hn : n > 1) :
  n ∣ ∑ i in finset.range n, i^n ↔ n % 2 = 1 :=
begin

end
