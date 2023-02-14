import tactic
import data.int.gcd   
import data.int.basic 
import data.int.modeq -- integer modular arithmetic

lemma gcd_linear_combo_signs {m n : ℤ} (h_m_pos : m > 0) (h_n_pos : n > 0) 
                            : (m.gcd_a n ≤ 0 ∧ m.gcd_b n > 0) ∨ (m.gcd_a n > 0 ∧ m.gcd_b n ≤ 0) :=
begin
  
  have hxy := (int.gcd_eq_gcd_ab m n),
  set x := m.gcd_a n,
  set y := m.gcd_b n,

  by_contra, push_neg at h,
  have m_ne_0 : m ≠ 0 := by linarith,
  have gcd_pos := int.gcd_pos_of_non_zero_left n m_ne_0,
  
  have hx : (x ≤ 0 ∨ x > 0) := le_or_lt x 0,
  cases hx with hx_nonpos hx_pos,
  { have hy_nonpos := h.1(hx_nonpos),
    have hmx : m * x ≤ 0 := linarith.mul_nonpos hx_nonpos h_m_pos,
    have hny : n * y ≤ 0 := linarith.mul_nonpos hy_nonpos h_n_pos,
    have h_combo : m * x + n * y ≤ 0 := add_nonpos hmx hny,
    rw ← hxy at h_combo,
    linarith,
  },
  { 
    -- could simplify argument

    have hy_pos := h.2(hx_pos),
    have hy2 : y ≥ 1 := by linarith,
    have hx2 : x ≥ 1 := by linarith,

    have hcn : n * y ≥ n :=  (le_mul_iff_one_le_right h_n_pos).mpr hy2,
    have hcm : m * x ≥ m :=  (le_mul_iff_one_le_right h_m_pos).mpr hx2,

    have hcmn : m * x + n * y ≥ m + n := add_le_add hcm hcn,
    rw ← hxy at hcmn,
    have h_gcd_dvd := int.gcd_dvd_left m n,
    have g_gcd_le : ↑(m.gcd n) ≤ m := int.le_of_dvd h_m_pos h_gcd_dvd,

    have hm_lt_sum : m < m + n := lt_add_of_pos_right m h_n_pos,
    linarith,
  },
end

lemma fun_coe_lemma_l {m n x y : ℤ } (h_m_nonneg : m ≥ 0) (h_n_nonneg : n ≥ 0) (hl : x ≤ 0 ∧ y > 0) (h_xy_nonneg : m * x + n * y ≥ 0)
  : (m * x + n * y).to_nat + m.to_nat * (-x).to_nat = n.to_nat * y.to_nat :=
begin
  zify,
  have hy_nonneg : y ≥ 0 := by linarith,
  have hx_neg_nonneg : -x ≥ 0 := by linarith,
  have hx := int.to_nat_of_nonneg hx_neg_nonneg,
  have hy := int.to_nat_of_nonneg hy_nonneg,
  have hm := int.to_nat_of_nonneg h_m_nonneg,
  have hn := int.to_nat_of_nonneg h_n_nonneg,
  have h := int.to_nat_of_nonneg h_xy_nonneg,
  rw [hx, hm, hn, hy, h],
  linarith,
end

lemma fun_coe_lemma_r {m n x y : ℤ } (h_m_nonneg : m ≥ 0) (h_n_nonneg : n ≥ 0) (hr : x > 0 ∧ y ≤ 0) (h_xy_nonneg : m * x + n * y ≥ 0)
  : (m * x + n * y).to_nat + n.to_nat * (-y).to_nat = m.to_nat * x.to_nat :=
begin
  zify,
  have hx_nonneg : x ≥ 0 := by linarith,
  have hy_neg_nonneg : -y ≥ 0 := by linarith,
  have hy := int.to_nat_of_nonneg hy_neg_nonneg,
  have hx := int.to_nat_of_nonneg hx_nonneg,
  have hm := int.to_nat_of_nonneg h_m_nonneg,
  have hn := int.to_nat_of_nonneg h_n_nonneg,
  have h := int.to_nat_of_nonneg h_xy_nonneg,
  rw [hx, hm, hn, hy, h],
  linarith,
end

--have hc : (↑(m.gcd n) * e).to_nat = (m.gcd n) * e.to_nat :=  sorry,

lemma fun_coe_lemma2 (n : ℕ) (e : ℤ) (hn : n ≥ 0) (he : e ≥ 0) : ((↑n * e).to_nat) = n * e.to_nat :=
begin
  zify,
  have hc1 : ↑(e.to_nat) = e := int.to_nat_of_nonneg he,
  rw hc1,
  have hc2 : ↑n * e ≥ 0,
  {
    refine mul_nonneg _ _,
    exact int.coe_zero_le n,
    linarith,
  },
  have hc3 := int.to_nat_of_nonneg hc2,
  assumption,
end

lemma a_pow_gcd_modeq_one_signs_left ( a m n : ℤ) (h_a_pos : a > 0) (h_m_pos : m > 0) (h_n_pos : n > 0) (hl : m.gcd_a n ≤ 0 ∧ m.gcd_b n > 0)
      : 1 ≡ a^(m.gcd n) [ZMOD (int.gcd (a^m.to_nat - 1) (a^n.to_nat - 1))] :=
begin
  set d := (int.gcd (a^m.to_nat - 1) (a^n.to_nat - 1)),
  have h_xy_signs := gcd_linear_combo_signs h_m_pos h_n_pos,
  have hxy := (int.gcd_eq_gcd_ab m n),
  set x := m.gcd_a n,
  set y := m.gcd_b n,
  set g := m.gcd n,

  have hx : -x ≥ 0 := by linarith,

  have hd1 : ↑d ∣ a^m.to_nat - 1 := (a ^ m.to_nat - 1).gcd_dvd_left (a ^ n.to_nat - 1),


  have hd1_mod : 1 ≡ a^m.to_nat [ZMOD d] := (int.modeq_iff_dvd).mpr hd1,

  have hd1x : 1^(int.to_nat(-x)) ≡ (a^m.to_nat)^(int.to_nat(-x)) [ZMOD d] := int.modeq.pow (-x).to_nat hd1_mod,
  simp only [one_pow] at hd1x,
  rw ← pow_mul at hd1x,

  have hd2 : ↑d ∣ a^n.to_nat - 1 := (a ^ m.to_nat - 1).gcd_dvd_right (a ^ n.to_nat - 1),
  have hd2_mod : 1 ≡ a^n.to_nat [ZMOD d] := (int.modeq_iff_dvd).mpr hd2,

  have hd2y : 1^(int.to_nat(y)) ≡ (a^n.to_nat)^(int.to_nat(y)) [ZMOD d] := int.modeq.pow (y).to_nat hd2_mod,
  simp only [one_pow] at hd2y,
  rw ← pow_mul at hd2y,

  have hd2y_dvd : ↑d ∣ a ^ (n.to_nat * y.to_nat) - 1 := (int.modeq_iff_dvd).mp hd2y,
  have hd1x_dvd : ↑d ∣ a ^ (m.to_nat * (-x).to_nat) - 1 := (int.modeq_iff_dvd).mp hd1x,

  have hd1x_dvd_mul : ↑d ∣ (a^g) * (a ^ (m.to_nat * (-x).to_nat) - 1) := dvd_mul_of_dvd_right hd1x_dvd (a^g),

  rw mul_sub at hd1x_dvd_mul,
  rw ← pow_add at hd1x_dvd_mul,
  simp only [mul_one] at hd1x_dvd_mul,

  have h_m_nonneg : m ≥ 0 := by linarith,
  have h_n_nonneg : n ≥ 0 := by linarith,
  have h_xy_nonneg : m * x + n * y ≥ 0,
  { 
    have hgcd2 : int.of_nat(g) ≥ 0 := int.of_nat_nonneg g,
    rw ← hxy,
    exact hgcd2,
  },

  have hg := fun_coe_lemma_l h_m_nonneg h_n_nonneg hl h_xy_nonneg,
  apply_fun int.to_nat at hxy,
  simp only [int.to_nat_coe_nat] at hxy,
  rw ← hxy at hg,

  have hd1x_dvd_mul_neg : ↑d ∣ -(a ^ (g + m.to_nat * (-x).to_nat) - a ^ g) := (dvd_neg ↑d (a ^ (g + int.to_nat m * (-x).to_nat) - a ^ g)).mpr hd1x_dvd_mul,
  simp only [neg_sub] at hd1x_dvd_mul_neg,
  rw hg at hd1x_dvd_mul_neg,
  have hd3 : ↑d ∣ (a ^ g - a ^ (n.to_nat * y.to_nat)) + (a ^ (n.to_nat * y.to_nat) - 1) := dvd_add hd1x_dvd_mul_neg hd2y_dvd,
  simp only [sub_add_sub_cancel] at hd3,
  exact int.modeq_of_dvd hd3,


end


lemma a_pow_gcd_modeq_one_signs_right ( a m n : ℤ) (h_a_pos : a > 0) (h_m_pos : m > 0) (h_n_pos : n > 0) (hr : m.gcd_a n > 0 ∧ m.gcd_b n ≤ 0)
      : 1 ≡ a^(m.gcd n) [ZMOD (int.gcd (a^m.to_nat - 1) (a^n.to_nat - 1))] :=
begin
  set d := (int.gcd (a^m.to_nat - 1) (a^n.to_nat - 1)),
  have h_xy_signs := gcd_linear_combo_signs h_m_pos h_n_pos,
  have hxy := (int.gcd_eq_gcd_ab m n),
  set x := m.gcd_a n,
  set y := m.gcd_b n,
  set g := m.gcd n,

  have hx : -y ≥ 0 := by linarith,

  have hd1 : ↑d ∣ a^n.to_nat - 1 := (a ^ m.to_nat - 1).gcd_dvd_right (a ^ n.to_nat - 1),
  have hd1_mod : 1 ≡ a^n.to_nat [ZMOD d] := (int.modeq_iff_dvd).mpr hd1,

  have hd1y : 1^(int.to_nat(-y)) ≡ (a^n.to_nat)^(int.to_nat(-y)) [ZMOD d] := int.modeq.pow (-y).to_nat hd1_mod,
  simp only [one_pow] at hd1y,
  rw ← pow_mul at hd1y,

  have hd2 : ↑d ∣ a^m.to_nat - 1 := (a ^ m.to_nat - 1).gcd_dvd_left (a ^ n.to_nat - 1),
  have hd2_mod : 1 ≡ a^m.to_nat [ZMOD d] := (int.modeq_iff_dvd).mpr hd2,

  have hd2x : 1^(int.to_nat(x)) ≡ (a^m.to_nat)^(int.to_nat(x)) [ZMOD d] := int.modeq.pow (x).to_nat hd2_mod,
  simp only [one_pow] at hd2x,
  rw ← pow_mul at hd2x,

  have hd2x_dvd : ↑d ∣ a ^ (m.to_nat * x.to_nat) - 1 := (int.modeq_iff_dvd).mp hd2x,
  have hd1y_dvd : ↑d ∣ a ^ (n.to_nat * (-y).to_nat) - 1 := (int.modeq_iff_dvd).mp hd1y,

  have hd1y_dvd_mul : ↑d ∣ (a^g) * (a ^ (n.to_nat * (-y).to_nat) - 1) := dvd_mul_of_dvd_right hd1y_dvd (a^g),

  rw mul_sub at hd1y_dvd_mul,
  rw ← pow_add at hd1y_dvd_mul,
  simp only [mul_one] at hd1y_dvd_mul,

  have h_m_nonneg : m ≥ 0 := by linarith,
  have h_n_nonneg : n ≥ 0 := by linarith,
  have h_xy_nonneg : m * x + n * y ≥ 0,
  { 
    have hgcd2 : int.of_nat(g) ≥ 0 := int.of_nat_nonneg g,
    rw ← hxy,
    exact hgcd2,
  },

  have hg := fun_coe_lemma_r h_m_nonneg h_n_nonneg hr h_xy_nonneg,
  apply_fun int.to_nat at hxy,
  simp only [int.to_nat_coe_nat] at hxy,
  rw ← hxy at hg,

  have hd1y_dvd_mul_neg : ↑d ∣ -(a ^ (g + n.to_nat * (-y).to_nat) - a ^ g) := (dvd_neg ↑d (a ^ (g + int.to_nat n * (-y).to_nat) - a ^ g)).mpr hd1y_dvd_mul,
  simp only [neg_sub] at hd1y_dvd_mul_neg,
  rw hg at hd1y_dvd_mul_neg,
  have hd3 : ↑d ∣ (a ^ g - a ^ (m.to_nat * x.to_nat)) + (a^ (m.to_nat * x.to_nat) - 1) := dvd_add hd1y_dvd_mul_neg hd2x_dvd,
  simp only [sub_add_sub_cancel] at hd3,
  exact int.modeq_of_dvd hd3,


end

lemma h_a_pow {a : ℤ} (h_a_pos : a > 0) (n : ℕ) : 1 ≤ a^n :=
begin
  have ha : a ≥ 1 := by linarith,
  exact one_le_pow_of_one_le ha n,
end

lemma gcd_pow {a m n : ℤ} (h_a_pos : a > 0) (h_m_pos : m > 0) (h_n_pos : n > 0) 
              : 1 ≡ a^((int.gcd m n)) [ZMOD (int.gcd (a^(m.to_nat) - 1) (a^(n.to_nat) - 1))] :=
begin
  -- g = gcd(m n); g = mx + ny; wlog y ≤ 0
  -- d = gcd(a^m - 1, a^n -1)
  -- d ∣ a^(mx) - 1 ; d ∣ a^(-ny) - 1 ; d ∣ -a^g (a^-ny - 1)
  -- d ∣ -a^g (a^-ny - 1) + a^(mx) - 1
  -- d ∣ a^g - a^(g-ny) + a^(mx) - 1 = a^g - 1

  set d := (int.gcd (a^m.to_nat - 1) (a^n.to_nat - 1)),
  have h_xy_signs := gcd_linear_combo_signs h_m_pos h_n_pos,
  have hxy := (int.gcd_eq_gcd_ab m n),
  set x := m.gcd_a n,
  set y := m.gcd_b n,
  set g := m.gcd n,

  cases h_xy_signs with hl hr,
  {
    exact a_pow_gcd_modeq_one_signs_left a m n h_a_pos h_m_pos h_n_pos hl,
  },
  {
    exact a_pow_gcd_modeq_one_signs_right a m n h_a_pos h_m_pos h_n_pos hr,
  }

end

lemma left_dvd_right (a m n : ℤ) (ha : a ≠ 1) (h_a_pos : a > 0) (h_m_pos : m > 0) (h_n_pos : n > 0) 
                    : ↑(int.gcd (a^m.to_nat - 1) (a^n.to_nat - 1)) ∣  ( a^(int.gcd m n) - 1 ) :=
 
begin
  set d := ↑(int.gcd (a^m.to_nat - 1) (a^n.to_nat - 1)),
  have hd1 : d ∣ (a^m.to_nat - 1) := (a ^ m.to_nat - 1).gcd_dvd_left (a ^ n.to_nat - 1),
  have hd2 : d ∣ (a^n.to_nat - 1) := (a ^ m.to_nat - 1).gcd_dvd_right (a ^ n.to_nat - 1),
  rw ← int.modeq_iff_dvd at hd1, 
  rw ← int.modeq_iff_dvd at hd2,
  {
    
    have h_gcd_pow := gcd_pow h_a_pos h_m_pos h_n_pos,
    
    have hk : 1 ≤ a ^ m.gcd n := h_a_pow h_a_pos (m.gcd n),
    exact int.modeq.dvd h_gcd_pow,
  },
end

lemma useful_lemma (a d e : ℤ) (h_a_pos : a > 0) : ((a^d.to_nat)^e.to_nat - 1 ≡ 0 [ZMOD a^d.to_nat - 1]) :=
begin
  have h1 : a^d.to_nat ≡ 1 [ZMOD a^d.to_nat - 1],
  {
    have hr : a^d.to_nat - 1 ∣ a^d.to_nat - 1 := dvd_rfl,
    have hz := int.modeq_zero_iff_dvd.mpr hr,
    have hr : 1 ≡ 1 [ZMOD a^d.to_nat - 1]  := int.modeq.rfl,
    have hzr : (a ^ d.to_nat - 1) + 1 ≡ 0 + 1 [ZMOD a ^ d.to_nat - 1] := int.modeq.add hz hr,
    have hl : a^d.to_nat = a^d.to_nat - 1 + 1,

    { have h_ad_pos : a^d.to_nat > 0 := pow_pos h_a_pos (int.to_nat d),
      linarith,
    },
    rwa [← hl, zero_add] at hzr,
  },
  have h2 : (a^d.to_nat)^e.to_nat ≡ 1 [ZMOD a^d.to_nat - 1],
  {
    have hp := int.modeq.pow e.to_nat h1,
    rwa one_pow e.to_nat at hp,
  },
  have hge1 : (a ^ d.to_nat) ^ e.to_nat ≥ 1,
  {
    rw ← pow_mul,
    exact h_a_pow h_a_pos (int.to_nat d * int.to_nat e),
  },
  suffices h : ((a ^ d.to_nat) ^ e.to_nat) - 1 + 1 ≡ 0 + 1 [ZMOD a ^ d.to_nat - 1],
  exact int.modeq.add_right_cancel' 1 h,
  simp,
  
  have h_ade_pos : (a^d.to_nat)^e.to_nat > 0 := pow_pos (pow_pos h_a_pos d.to_nat) e.to_nat,
  assumption,
  
end

lemma dvd_prod {d a k : ℕ} (hd : d ∣ a) : (d ∣ k * a) :=
begin
  exact dvd_mul_of_dvd_right hd k,
end


/-

proof based on:

https://math.stackexchange.com/questions/11567/gcdbx-1-by-1-b-z-1-dots-b-gcdx-y-z-dots-1 

-/

theorem gcd_pows_minus_one (a m n : ℤ) (ha : a ≠ 1) (h_a_pos : a > 0) (h_m_pos : m > 0) (h_n_pos : n > 0) 
                        : ↑(int.gcd (a^m.to_nat - 1) (a^n.to_nat - 1)) = a^(int.gcd m n) - 1 :=
begin

have left_dvd_right := left_dvd_right a m n ha h_a_pos h_m_pos h_n_pos,
have right_dvd_left : a^(int.gcd m n) - 1 ∣ ↑(int.gcd (a^m.to_nat - 1) (a^n.to_nat - 1)),
{ 
  have h1 : ↑(int.gcd m n) ∣ n := int.gcd_dvd_right m n,
  have h2 : ↑(int.gcd m n) ∣ m := int.gcd_dvd_left m n,

  have h1_d := dvd_iff_exists_eq_mul_left.mp h1,
  have h2_d := dvd_iff_exists_eq_mul_left.mp h2,

  cases h1_d with e he,
  cases h2_d with f hf,

  have h_gcd_nonneg : m.gcd n ≥ 0 := zero_le (int.gcd m n),
  have h_gcd_nonneg' : ↑(m.gcd n) ≥ 0 := zero_le ↑(int.gcd m n),

  have h_e_nonneg : e ≥ 0,
  {
    by_contra, push_neg at h,
    have he2 : e * ↑(m.gcd n) ≤ 0 * ↑(m.gcd n) := by nlinarith,
    simp only [zero_mul] at he2,
    rw ← he at he2,
    linarith,
  },

  have h_f_nonneg : f ≥ 0, 
  {
    by_contra, push_neg at h,
    have hf2 : f * ↑(m.gcd n) ≤ 0 * ↑(m.gcd n),
    {
      nlinarith,
    },
    simp only [zero_mul] at hf2,
    rw ← hf at hf2,
    linarith,
  },

  

  have h3 : a^n.to_nat - 1 = (a^(m.gcd n))^e.to_nat - 1,
  {
    nth_rewrite 0 he,
    rw mul_comm e (m.gcd n),
    suffices h : a ^ ((↑(m.gcd n) * e).to_nat) = (a ^ m.gcd n) ^ e.to_nat,
    rw h,

    --(n : ℕ) (e : ℤ) (hn : n ≥ 0) (he : e ≥ 0)

    have hc : (↑(m.gcd n) * e).to_nat = (m.gcd n) * e.to_nat := fun_coe_lemma2 (m.gcd n) e h_gcd_nonneg h_e_nonneg,
    rw hc,
    exact pow_mul a (int.gcd m n) e.to_nat,
  },
  have h4 : a^m.to_nat - 1 = (a^(m.gcd n))^f.to_nat - 1,
  {nth_rewrite 0 hf,
    rw mul_comm f (m.gcd n),
    suffices h : a ^ ((m.gcd n) * f.to_nat) = (a ^ m.gcd n) ^ f.to_nat,
    have hc : (↑(m.gcd n) * f).to_nat = (m.gcd n) * f.to_nat := fun_coe_lemma2 (m.gcd n) f h_gcd_nonneg h_f_nonneg,
    rw hc,
    simp only [sub_left_inj],
    exact pow_mul a (int.gcd m n) f.to_nat,
    exact pow_mul a (int.gcd m n) f.to_nat,
    },

  have h5 := int.modeq.symm( useful_lemma a (m.gcd n) e h_a_pos),
  have h6 := int.modeq.symm( useful_lemma a (m.gcd n) f h_a_pos),

  have hgcd: 0 ≤ m.gcd n := zero_le (int.gcd m n),
  simp at h5,
  simp at h6,
  
  rw ← h3 at h5,
  rw ← h4 at h6,

  rw int.modeq_iff_dvd at h5, simp only [sub_zero] at h5,
  rw int.modeq_iff_dvd at h6, simp only [sub_zero] at h6,
  exact int.dvd_gcd h6 h5,

},

have h_left_nonneg := int.coe_zero_le ((a ^ int.to_nat m - 1).gcd (a ^ int.to_nat n - 1)),
have h_right_nonneg1 := h_a_pow h_a_pos (int.gcd m n),
have h_right_nonneg : 0 ≤ (a^(int.gcd m n) - 1) := by linarith,

exact int.dvd_antisymm h_left_nonneg h_right_nonneg left_dvd_right right_dvd_left,

end