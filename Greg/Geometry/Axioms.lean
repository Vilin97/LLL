
import data.real.basic
import tactic


-- maybe try this? suggested by Leo
/-
class geometry :=
(line : Type)
(point : Type)
-/


-- variables {P L : Type} (p q r : P) (l m n : L)

-- A notion of a line going throuhg a point. The very closely-related notion of parallel lines is also defined
class has_goes_thru (line point : Type):=
(goes_thru : line → point → Prop)

open has_goes_thru

-- the idea of parallel lines is tied to Euclid's axioms
def parallel {line : Type} (point : Type) [inst : has_goes_thru line point] (l m : line) : Prop := (l = m) ∨ ∀ p : point, ¬(goes_thru l p ∧ goes_thru m p)

class has_euclid_post5 (line point : Type) extends has_goes_thru line point :=
(euclid_post5 : ∀ (l : line) (p: point), ∃! (m : line), parallel point l m ∧ goes_thru m p)

open has_euclid_post5

section
variables {line : Type} (point: Type) [has_goes_thru line point] (l m n : line)

theorem parallel_refl : parallel point l l := begin
  left, refl,
end

theorem parallel_symm : parallel point l m ↔ parallel point m l := begin
  split; intro h; cases h,
  left,exact h.symm,
  right,
  intros p f, specialize h p, exact h ⟨f.2, f.1⟩,
  left, exact h.symm,
  right,
  intros p f, specialize h p, exact h ⟨f.2, f.1⟩,
end

theorem parallel_trans : parallel point l m → parallel point m n → parallel point l n := begin
  intros plm pmn,
  cases plm; cases pmn,
  left,
  rwa plm,
  right,
  rwa plm,
  right,
  rwa ←pmn,
  sorry, -- we need something additional for this, I think
end
end

-- theorem parallel_refl {line : Type} (point: Type) [inst : has_goes_thru line point] (l m : line)

-- variables [has_goes_thru L P]

-- parallel lines are those which do not intersect

#check parallel
#check goes_thru
#check exists_unique

-- Euclid's fifth postulate

-- A notion of distance obeying basic laws.
class has_distance (point : Type) :=
(distance : point → point → ℝ)
(distance_nonnegative : ∀ p q : point, distance p q ≥ 0)
(distance_zero_iff_eq : ∀ p q : point, distance p q = 0 ↔ p = q)
(distance_comm : ∀ p q : point, distance p q = distance q p)
(distance_add: ∀ p q r : point, distance p q + distance q r ≥ distance p r)

open has_distance

-- a notion of "between" for points.
-- TODO depend on has_goes_thru since a point can only be between two collinear points
-- TODO move to axioms
class between (point : Type) :=
(between : point → point → point → Prop)
(between_comm : ∀ p q r : point, between p q r ↔ between r q p)
(one_between : ∀ p q r: point, ¬(between p q r ∧ between q p r))

-- basic notions that geometry should support
-- the first point is between the others

-- I'd like a way to use this in the geometry class
-- def goes_thru2 : Prop := goes_thru l p ∧ goes_thru l q


-- there is a line through any two points. If those points are different, that line is unique.
-- (line_thru_pts : ∀ p q : point, ∃ l : line, goes_thru l p ∧ goes_thru l q)
-- (uniq_line_thru_pts : ∀ (p q : point) (l m : line), goes_thru l p ∧ goes_thru l q ∧ goes_thru m p ∧ goes_thru l q → p = q ∨ l = m)

-- one point is between the two others
