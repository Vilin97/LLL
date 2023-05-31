import linear_algebra.basic

variables (V : Type*) [vector_space ℝ V]
variables (S T : linear_map ℝ V V)

theorem range_subset_null_implies_squared_zero : range S ⊆ null_space T → (S * T)^2 = 0 :=
begin
  intros h,
  ext v,
  simp only [linear_map.mul_apply, linear_map.comp_apply],
  have h₁ : T (S (T v)) = 0,
  {
    have h₂ : S (T v) ∈ range S,
    {
      apply mem_range_self,
    },
    have h₃ : S (T v) ∈ null_space T,
    {
      exact h h₂,
    },
    exact h₃,
  },
  simp [h₁],
end