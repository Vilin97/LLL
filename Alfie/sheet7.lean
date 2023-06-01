import analysis.calculus.mean_value
import analysis.calculus.deriv
import order.min_max
import tactic
import data.real.basic


def Rolle's_theorem (f : ℝ → ℝ) (a b : ℝ) (h₀ : a < b) 
  (h₁ : continuous_on f ({x : ℝ | a ≤ x ∧ x ≤ b})) (h₂ : differentiable_on ℝ f ({x : ℝ | a < x ∧ x < b})) 
  (h₃ : f a = 0)( h₄ : f b = 0): 
  ∃ c ∈ {x : ℝ | a < x ∧ x < b}, deriv f c = 0 := sorry

def continuous_diff (f : ℝ → ℝ) (g : ℝ → ℝ) (a b : ℝ) (h₀ : a < b)
  (h₁ : continuous_on f ({x : ℝ | a ≤ x ∧ x ≤ b})) (h₂ : continuous_on g ({x : ℝ | a ≤ x ∧ x ≤ b}))
  (h₃ h : ℝ → ℝ := λ x, f x - g x):
  continuous_on h ({x : ℝ | a ≤ x ∧ x ≤ b}) := sorry



theorem mean_value_theorem (f : ℝ → ℝ) (a b : ℝ) (h₀ : a < b) 
  (h₁ : continuous_on f ({x : ℝ | a ≤ x ∧ x ≤ b})) (h₂ : differentiable_on ℝ f ({x : ℝ | a < x ∧ x < b})) : 
  ∃ c ∈ {x : ℝ | a < x ∧ x < b}, (f b - f a)/(b - a) = deriv f c :=
  begin
    let g : ℝ → ℝ := λ x, f a + (f b - f a)/(b - a) * (x - a),
    let h : ℝ → ℝ := λ x, f x - g x, 
    have h1 : continuous_on h ({x : ℝ | a ≤ x ∧ x ≤ b}),
    { sorry,},
    have h2 : differentiable_on ℝ h  ({x : ℝ | a < x ∧ x < b}),
    { sorry,},
    have h3 : h a = 0,
    { sorry,},
    have h4 : h b = 0,
    { sorry,},
    have R := Rolle's_theorem h a b h₀ h1 h2 h3 h4,
    cases R with c R1,
    cases R1 with H1 R2,
    use c,
    split,
    {apply H1,},
    have hκ : deriv g c = (f b - f a)/(b - a),
    {sorry,},
    have f: deriv h c = deriv g c - deriv f c,
    {sorry,},
    rw R2 at f,
    rw hκ at f,
    linarith,
end