import tactic
import data.real.basic -- ℝ 
import data.complex.basic -- ℂ
import analysis.special_functions.trigonometric.angle -- real.angle
import analysis.special_functions.complex.arg -- complex.arg

-- noncomputable def dist (a b : ℂ) : ℝ := complex.abs(b-a) -- EY: turns out this is already built-in
noncomputable def angle (a b c : ℂ) : real.angle := ((c-b)/(a-b)).arg

def circle (center : ℂ) (radius : ℝ) := metric.sphere center radius -- EY: allowing degen circles (negative radius)
def line (a b : ℂ) := {x : ℂ | ∃ t : ℝ, x = a * t + b * (1-t)} -- EY: allowing degen lines


def Lines : set (set ℂ) := {s : set ℂ | ∃ (a b : ℂ), s = line a b } -- set of all lines 
def Circles : set (set ℂ) := {s : set ℂ | ∃ (c : ℂ) (r : ℝ), s = circle c r } -- set of all circles
lemma circle_defn (circ) : (circ ∈ Circles) → ∃ (c : ℂ), ∃ (r : ℝ), circ = circle c r  :=
begin
  intro h,
  exact has_mem.mem.out h,
end
noncomputable def circle_center (circ : set ℂ) (h : circ ∈ Circles) : ℂ := (circle_defn circ h).some
-- noncomputable def circle_radius (circ : set ℂ) (h : circ ∈ Circles) : ℝ := 

theorem angle_antisymm (a b c : ℂ) (hab: a ≠ b) (hcb: c ≠ b) : angle a b c + angle c b a = 0 :=
begin
  rw angle,
  rw angle,
  have hab' : a - b ≠ 0,
    exact sub_ne_zero.mpr hab,
  have hcb' : c - b ≠ 0,
    exact sub_ne_zero.mpr hcb,
  rw complex.arg_div_coe_angle hab' hcb',
  rw complex.arg_div_coe_angle hcb' hab',
  simp,
end

theorem angle_linear (p a b c : ℂ) (ha : a≠p) (hb: b≠p) (hc: c≠p) : angle a p b + angle b p c = angle a p c :=
begin
  rw angle,
  rw angle,
  rw angle,
  have ha : a-p ≠ 0, exact sub_ne_zero.mpr ha,
  have hb : b-p ≠ 0, exact sub_ne_zero.mpr hb,
  have hc : c-p ≠ 0, exact sub_ne_zero.mpr hc,
  rw complex.arg_div_coe_angle hb ha,
  rw complex.arg_div_coe_angle hc hb,
  rw complex.arg_div_coe_angle hc ha,
  simp,
end

lemma angle_self_zero_reducelem (x : real.angle) : x + x = x → x = 0 :=
  begin
    exact add_left_eq_self.mp,
  end
theorem angle_self_zero (p a : ℂ) (ha : a≠p) : angle a p a = 0 :=
begin
  have test,
    exact angle_linear p a a a ha ha ha,
  apply angle_self_zero_reducelem (angle a p a),
  exact test,
end

theorem line_linearcombination (a b : ℂ) (r: ℝ) : (r ≠ 1) → line a b = line a (r*a + (1-r)*b) :=
begin
  intro hr,
  rw line,
  rw line,
  apply set.eq_of_subset_of_subset,
    {
      intros x hx,
      refine set.mem_def.mpr _,
      refine set.mem_def.mpr _,
      cases has_mem.mem.out hx with t ht,
      use (r-t)/(r-1),
      rw ht,
      sorry, -- EY: this is just alg
    },
    {
      intros x hx,
      refine set.mem_def.mpr _,
      refine set.mem_def.mpr _,
      cases has_mem.mem.out hx with t ht,
      use -t*r + t + r,
      rw ht,
      sorry,  -- EY: this is just alg
    }
end

noncomputable def midpoint (a b : ℂ) := (a+b)/2

lemma this_is_that1 (v : ℂ) : ‖v‖ = complex.abs (v) :=
begin
  exact v.norm_eq_abs,
end

lemma this_is_that2 (P Q : ℂ) : dist P Q = ‖P - Q‖ :=
begin
  exact dist_eq_norm P Q,
end

lemma this_is_that3 (P Q : ℂ) : dist P Q = complex.abs (P - Q) :=
begin
  exact complex.dist_eq P Q,
end

lemma circle_lemma_1 (X : ℂ) (O : ℂ) (r : ℝ) : X ∈ circle O r → ∃ d : ℂ, ‖d‖ = r ∧ X = O + d :=
begin
  rw circle,
  intro h,
  rw mem_sphere_iff_norm at h,
  use X - O,
  split,
  {
    exact h,
  },
  {
    norm_num,
  },
end

-- show that if x y are on circle o r, then angle o x y and angle o y x are the same
lemma circle_lemma_2 (X Y : ℂ) (O : ℂ) (r : ℝ) : X ≠ Y → O ≠ X → O ≠ Y → X ∈ circle O r → Y ∈ circle O r → angle O X Y = angle O Y X :=
begin
  intros XneY OneX OneY hX hY,
  rw circle at hX,
  rw circle at hY,
  rw mem_sphere_iff_norm at hX,
  rw mem_sphere_iff_norm at hY,
  rw angle,
  rw angle,
  norm_num,
  rw complex.arg_eq_arg_iff,
  {
    rw ← this_is_that1,
    rw ← this_is_that1,
    rw norm_div,
    rw norm_div,
    rw [← this_is_that2 Y O, dist_comm Y O, this_is_that2 O Y] at hY,
    rw [← this_is_that2 X O, dist_comm X O, this_is_that2 O X] at hX,
    rw [hX, hY],
    -- simp takes so long tho!
    sorry,
  },
  {
    sorry,
  },
  {
    sorry,
  },
end

-- as a corollary, isosceles triangles have equal angles (remark - this does not prove the converse)
lemma circle_lemma_3 (A B C : ℂ) : A ≠ B → A ≠ C → B ≠ C → dist A B = dist A C → angle A B C = angle A C B :=
begin
  intros AneB AneC BneC dAB_eq_dAC,
  have h1 : B ∈ circle A (dist A B),
  {
    rw [circle, mem_sphere_iff_norm, dist_comm, this_is_that2],
  },
  have h2 : C ∈ circle A (dist A C),
  {
    rw [circle, mem_sphere_iff_norm, dist_comm, this_is_that2],
  },
  rw ← dAB_eq_dAC at h2,
  exact circle_lemma_2 B C A (dist A B) BneC AneB AneC h1 h2,
end

-- TODO

-- CIRCLES
-- show that if x, y, z are on circle o r, then 2 * angle x y z = angle x o z
-- (remark on above: this maybe annoying because idk if real.angle has_mul is true. if not, you can do angle x y z + angle x y z = angle x o z)
-- show that if w x y z are on circle o r, then angle w x y + angle w z y = pi

-- lemma circle_center_radius_decomp (circ ∈ Circles) (x : ℂ) :
-- x ∈ circ →  ∃ (d : ℂ) , (complex.abs d = 1 ∧ x = d + ) :=
-- begin

-- end

-- PERPENDICULAR BISECTOR
-- define perpendicular as angle = pi/2 or 3pi/2
-- define perpendicular bisector as the line through midpoint(a b), and midpoint(a b) + i * (a-b)
-- show that the perpendicular bisector is perpendicular to the line a b
-- show that p \in perpendicular bisector ↔ dist p a = dist p b


-- TRIANGLE CONGRUENCE
-- define triangle as an ORDERED triple of points
-- remark: DO NOT axiom triangle a b c = triangle a c b, and axiom triangle a b c = triangle b a c, AFAIK this kills stuff due to permutations!
-- define the equivalence relation (!! it needs to be an equivalence relation!!)  "direct congruence" of triangles as triangle a b c sim triangle d e f iff exists p : ℂ such that p a = d, p b = e, p c = f
-- show that it is an equivalence relation!!
-- show that angles are equal and lengths are equal for direct congruence
-- prove asa, sas, and sss congruence for direct congruence
-- define "flip congruence" as an equivalence relation (!!) such that a b c flipsim conjugate a b c
-- now you can do above steps, using 
-- define "congruence" as "direct congruent or flip congruent" and prove this is equivalence relation


-- variables (a b c : ℂ) (r : ℝ)
-- variable hab : a ≠ b
-- variable circ : circle a r
-- #check circ