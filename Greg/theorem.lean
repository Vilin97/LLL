import data.real.basic

variables (T : Type) [comm_ring T](a b : T)
-- variables (a b : ℝ)

theorem square_diff : (a^2 - b^2 = (a+b)*(a-b)) :=
begin
  rw mul_sub,
  rw add_mul,
  rw add_mul,
  rw sub_add_eq_sub_sub,
  rw mul_comm a b,
  rw add_sub_assoc,
  rw sub_self,
  rw add_zero,
  rw sq,
  rw sq,
end

theorem square_diff_by_ring : (a^2 - b^2 = (a+b)*(a-b)) :=
begin
  ring,
end


#check square_diff
#check square_diff_by_ring

-- An example of how to use library_search
lemma foo : (a^2 = a*a) := sq a
