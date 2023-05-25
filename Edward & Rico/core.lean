import data.real.basic
import tactic
import dirangle

open real.dirangle

structure Point : Type
structure Line : Type

axiom line_exists : ∃ l : Line, true

constant lies_on_def : Point → Line → Prop

notation (name := what_does_this_mean) p ` lies_on `:50 l:50 := lies_on_def p l

axiom line_by_two_points (p q : Point): p ≠ q → ∃ l : Line, p lies_on l ∧ q lies_on l
axiom line_by_two_points_unique (p q : Point) (l1 l2 : Line) : p ≠ q → p lies_on l1 → p lies_on l2 → q lies_on l1 → q lies_on l2 → l1 = l2
axiom exist_points_on_line (l : Line) : ∃ p q : Point, p ≠ q ∧ p lies_on l ∧ q lies_on l

-- given two distinct points, returns a line through both of them
noncomputable def make_line (p q : Point) (h0 : p ≠ q) : Line := (line_by_two_points p q h0).some

theorem intersection_unique (l1 l2 : Line) (p q : Point) : l1 ≠ l2 → p lies_on l1 → p lies_on l2 → q lies_on l1 → q lies_on l2 → p = q :=
begin
  intro lineq,
  intro ponl1,
  intro ponl2,
  intro qonl1,
  intro qonl2,
  by_contra pneq,
  change p ≠ q at pneq,
  apply lineq,
  apply line_by_two_points_unique p q l1 l2,
  exact pneq,
  exact ponl1,
  exact ponl2,
  exact qonl1,
  exact qonl2,
end

lemma points_exist : ∃ p q : Point, p ≠ q :=
begin
  have l := line_exists.some,
  have h := (exist_points_on_line l),
  cases h with x hx,
  cases hx with q hq,
  use x,
  use q,
  cases hq with h1 h2,
  assumption, -- props to @Edward Yu
end

lemma exists_line_through_point (p : Point) : ∃ l : Line, p lies_on l :=
begin
  cases points_exist with q h2,
  cases h2 with r qneqr,
  by_cases p = q,
  {
    cases line_by_two_points q r qneqr with l hl,
    use l,
    rw h,
    cases hl with hleft hright,
    exact hleft,
  },
  {
    change p ≠ q at h,
    cases line_by_two_points p q h with l hl,
    use l,
    cases hl with hleft hright,
    exact hleft,
  },
end

-- COLLINEAR

def collinear (p q r : Point) : Prop := ∃ l : Line, p lies_on l ∧ q lies_on l ∧ r lies_on l
-- Note that p q r can be equal.

lemma collinear_self_self (p : Point) : collinear p p p :=
begin
  cases exists_line_through_point p with l hl,
  use l,
  rw and_self,
  rw and_self,
  exact hl,
end

lemma collinear_self (p q : Point) : collinear p p q :=
begin
  by_cases h0 : p = q,
  {
    rw h0,
    exact collinear_self_self q,
  },
  {
    cases line_by_two_points p q h0 with l lh,
    use l,
    rw ← and_assoc,
    rw and_self,
    exact lh,
  },
end

def intersect_line_line (l1 l2 : Line) : Prop := ∃ p : Point, p lies_on l1 ∧ p lies_on l2

-- BETWEEN

constant between: Point → Point → Point → Prop
-- between p q r ↔ q is between p and r (can be equal).

axiom between_implies_collinear (p q r : Point) : between p q r → collinear p q r

-- Hilbert II.1, page 4.
axiom between_commutative (p q r : Point) : between p q r ↔ between r q p

-- I think this is necessary..?
axiom between_not_outside (p q : Point) : p ≠ q → ¬between p q p

-- EY: I just want "exactly one of these three things is true" and this feels like an ugly solution
-- Rico: I don't see any better way to do it unfortunately...

-- Hilbert II.3 (modified).
axiom between_unique (p q r : Point) : between p q r → p = q ∨ (¬ between q p r)

-- Hilbert II.3 (modified).
axiom between_exists (p q r : Point) : collinear p q r → between q p r ∨ between p q r ∨ between p r q

-- Hilbert II.2 (modified)
axiom exists_point_between (p q : Point) : p ≠ q → ∃ r : Point, r ≠ p ∧ r ≠ q ∧ between p r q

-- Hilbert II.2 (modified)
axiom exists_point_outside (p q : Point) : ∃ r : Point, r ≠ p ∧ between r p q

-- TODO axiom ii-4 in hilbert? what even is this, how do i write it nicely, why does it exist

lemma between_self_self (p : Point) : between p p p :=
begin
  have h0 : between p p p ∨ between p p p ∨ between p p p,
  {
    apply between_exists p p p,
    exact collinear_self_self p,
  },
  {
    rw or_self at h0,
    rw or_self at h0,
    exact h0,
  }
end

lemma between_self (p q : Point) : between p p q :=
begin
  have col := collinear_self p q,
  have h := between_exists p p q col,
  rw ← or_assoc at h,
  rw or_self at h,
  cases h with h0 h0,
  {
    exact h0,
  },
  {
    by_cases peq : p = q,
    {
      rw peq,
      exact between_self_self q,
    },
    {
      exfalso,
      apply between_not_outside p q peq,
      exact h0,
    },
  },
end

def same_side (o p q : Point) : Prop := o ≠ p ∧ o ≠ q ∧ (between o p q ∨ between o q p)

def opposite_side (o p q : Point) : Prop := o ≠ p ∧ o ≠ q ∧ (between p o q)

-- SEGMENT

structure Segment :=
segment :: (first : Point) (second : Point)
-- first can be equal to second.

open Segment

axiom segment_symm (p q : Point) : segment p q = segment q p

def lies_on_seg_def (p : Point) (s : Segment) : Prop := between s.first p s.second

def intersect_seg_seg (s1 s2 : Segment) : Prop := ∃ p : Point, lies_on_seg_def p s1 ∧ lies_on_seg_def p s2

def intersect_line_seg (l1 : Line) (s1 : Segment) : Prop := ∃ p : Point, p lies_on l1 ∧ lies_on_seg_def p s1

-- Hilbert II.5, page 4.
axiom intersect_part (p q r : Point) (l : Line) : intersect_line_seg l (segment p r) → intersect_line_seg l (segment p q) ∨ intersect_line_seg l (segment q r)

-- DISTANCE

axiom distance : Point → Point → ℝ

-- Implicitly defines Hilbert IV.2, page 8.
noncomputable def length (s : Segment) : ℝ := distance s.first s.second

lemma distance_is_length (p q : Point) : distance p q = length (segment p q) :=
begin
  rw length,
end

lemma distance_commutative (p q : Point) : distance p q = distance q p :=
begin
  rw distance_is_length,
  rw distance_is_length,
  rw segment_symm,
end

-- Hilbert IV.3, page 8.
axiom distance_transitive (p q r : Point) (h0 : between p q r) : distance p q + distance q r = distance p r

lemma distance_reflexive (p : Point) : distance p p = 0 :=
begin
  have col := between_self_self p,
  have trans := distance_transitive p p p col,
  linarith,
end

-- Hilbert IV.1, page 8.
axiom exists_seg_congruent_same_side (o p : Point) (l : Line) (d : ℝ) : o lies_on l → p lies_on l → o ≠ p → d > 0 → ∃ q : Point, same_side o p q ∧ distance o q = d

-- ANGLES

-- EY : oh no dirangle needs a has_zero (!!)

constant Angle : Line → Line → real.dirangle
axiom angle_line_refl (a : Line) : Angle a a = 0
axiom angle_line_addition (a b c : Line) : Angle a b + Angle b c = Angle a c
lemma angle_line_antisymm : ∀ a b : Line, Angle a b = - Angle b a :=
begin
  intros a b,
  apply add_eq_zero_iff_eq_neg.mp,
  rw angle_line_addition a b a,
  rw angle_line_refl,
end

def parallel (l1 l2 : Line) := Angle l1 l2 = 0
lemma self_parallel : ∀ a : Line, parallel a a :=
begin
  intro a,
  apply angle_line_refl a,
end

-- In order to prove parallel_postulate_unique.
axiom def_parallel (l1 l2 : Line) : parallel l1 l2 ↔ l1 = l2 ∨ ¬intersect_line_line l1 l2

-- Hilbert III, page 7.
axiom parallel_postulate (p : Point) (θ : real.dirangle) (l0 : Line) : ∃ l : Line, p lies_on l ∧ Angle l l0 = θ
lemma parallel_postulate_unique (p : Point) (l0 l1 : Line) : p lies_on l0 → p lies_on l1 → parallel l0 l1 → l0 = l1 :=
begin
  intros ponl0 ponl1 prll,
  rw def_parallel at prll,
  cases prll,
  {
    exact prll,
  },
  {
    exfalso,
    apply prll,
    use p,
    split,
    {
      exact ponl0,
    },
    {
      exact ponl1,
    },
  },
end


-- EY : this works, but I'd rather use the (unfinished) commented thing below because you'll see it's more convenient
-- Rico: then use it.
-- EY : yea uh hello it is unfinished (i.e. I'm being stupid and can't make this work)
noncomputable def Ptangle (a b c : Point) : (a≠b) → (b≠c) → real.dirangle :=
begin
  intros hab hbc,
  exact Angle (make_line a b hab) (make_line b c hbc),
end

