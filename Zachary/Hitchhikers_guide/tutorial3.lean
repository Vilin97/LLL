import tactic
open tactic expr

-- example : true ∧ true :=
-- by do 
--   split,
--   gs ← get_goals, 
--   gs.mmap' (λ e, trace e.to_raw_fmt)

set_option pp.instantiate_mvars false

example : ∃ x : ℕ, x = x := 
by do 
  applyc `exists.intro,
  [e1, e2] ← get_goals,
  tactic.unify e2 `(7),
  trace e2,
  trace e2.to_raw_fmt,
  e2 ← instantiate_mvars e2,
  trace e2.to_raw_fmt

-- define at meta definition for the assumption tactic
meta def assumption' : tactic unit :=
do { ctx ← local_context,
     t   ← target,
     ctx.any_of (λ h, do h_type ← infer_type h,
                         unify h_type t,
                         exact h) }

-- define a tactic that searches hypotheses for a contradiction
meta def contra : tactic unit :=
do { -- Get the local context and target.
     ctx ← local_context,
     t   ← target,
     -- Search for a hypothesis in the context that is `false`.
     ctx.any_of (λ h, do h_type ← infer_type h, -- Fixed here!
                         match h_type with
                         | `(false) := exact h
                         | _        := failed
                         end) }