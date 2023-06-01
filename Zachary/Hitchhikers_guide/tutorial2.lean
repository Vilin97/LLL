import tactic
-- 4

open tactic expr

meta def make_a_nat : tactic ℕ :=
return 14

meta def trace_nat : tactic unit :=
do n ← make_a_nat, -- asigns the result of make_a_nat to n
   trace n -- prints n

run_cmd trace_nat -- creates empty tactic state, runs trace_nat

#check @list.mmap'

meta def inspect : tactic unit :=
do t ← target,
--    trace t,
--    a_expr ← get_local `a <|> return `(0),
--    trace a_expr,
--    a_type ← infer_type a_expr,
--    trace a_type,
      ctx ← local_context,
--    trace ctx,
   ctx.mmap' (λ e, do tp ← infer_type e, trace tp)


-- example (b c : ℤ ) (q : ℕ ) : c = b :=
-- by do inspect

-- 5


meta def test_tp (hyp tgt : expr) : tactic unit :=
do hyp_tp ← infer_type hyp,
   is_def_eq hyp_tp tgt, -- succeeds if definitionally equal
   exact hyp


meta def map_over_lc (tgt : expr) : list expr → tactic unit
| [] := fail "no matching hypothesis"
| (h :: t) := 
  test_tp h tgt <|> map_over_lc t

meta def assump : tactic unit :=
-- do tgt ← target,
--    ctx ← local_context,
--    ctx.mfirst (λ e, exact e)
local_context >>= list.mfirst exact -- partial application of rhs applied to lhs

example (n : ℕ ) (hx : n + 0 = 5) : n = 5 :=
by assump

#check @list.mfirst -- returns first that works, or fails

example ( A B C : Prop) (ha : A) (hb : B) (hc : C) : C :=
by assump

-- exercises

/-!

This file contains three tactic-programming exercises of increasing difficulty.

They were (hastily) written to follow the metaprogramming tutorial at
Lean for the Curious Mathematician 2020.

If you're looking for more (better) exercises, we strongly recommend the
exercises by Blanchette et al
for the course Logical Verification at the Vrije Universiteit Amsterdam,
and the corresponding chapter of the course notes:

https://github.com/blanchette/logical_verification_2020/blob/master/lean/love07_metaprogramming_exercise_sheet.lean
https://github.com/blanchette/logical_verification_2020/raw/master/hitchhikers_guide.pdf



## Exercise 1

Write a `contradiction` tactic.
The tactic should look through the hypotheses in the local context
trying to find two that contradict each other,
i.e. proving `P` and `¬ P` for some proposition `P`.
It should use this contradiction to close the goal.

Bonus: handle `P → false` as well as `¬ P`.

This exercise is to practice manipulating the hypotheses and goal.

Note: this exists as `tactic.interactive.contradiction`.

-/

-- need to map over context, and for each hypothesis, map over context and test if it is a negation of another hypothesis


-- meta def contra_constructor_eq : list expr → tactic unit
-- | []        := return `(ff)
-- | (H :: Hs) :=
--   do t ← (extract_opt_auto_param <$> infer_type H) >>= whnf,
--      match t with
--      | `(%%lhs_0 = %%rhs_0) :=
--        do env ← get_env,
--           lhs ← whnf lhs_0,
--           rhs ← whnf rhs_0,
--           if is_constructor_app env lhs ∧
--              is_constructor_app env rhs ∧
--              const_name (get_app_fn lhs) ≠ const_name (get_app_fn rhs)
--           then do tgt    ← target,
--                   I_name ← return $ name.get_prefix (const_name (get_app_fn lhs)),
--                   pr ← mk_app (I_name <.> "no_confusion") [tgt, lhs, rhs, H],
--                   exact pr
--           else contra_constructor_eq Hs
--      | _ := contra_constructor_eq Hs
--      end

-- not sure how to do this:

-- meta def change_eq_to_false (e : expr) : tactic unit
-- | `(%%lhs_0 = %%rhs_0) := 
--   do env ← get_env,
--       tgt ← target,
--       lhs ← whnf lhs_0,
--       rhs ← whnf rhs_0,
--       try (do pr ← mk_app (I_name <.> "no_confusion") [tgt, lhs, rhs, e],
--               exact pr)
-- | _ := change_tgt_to_false t
       
  

meta def test_negation (hyp : expr) : list expr → tactic expr
| [] := return `(ff)
| (h :: t) := 
  do hyp_tp ← infer_type hyp,
     h_tp ← infer_type h,
     match h_tp with
     | `(¬ %%h_tp) := 
       do
          if (hyp_tp = h_tp) then return h
          else test_negation t
     | `(%%h_tp → false) := 
       do 
          if (hyp_tp = h_tp) then return h
          else test_negation t
     | _ := test_negation t
     end


meta def tactic.interactive.contr : tactic unit :=
do ctx ← local_context,
   ctx.mmap' (λ h, do is_neg ← test_negation h ctx,
                      if is_neg = `(ff) then skip else do trace "found match!", exact (is_neg h)) -- do something here to close the goal
  
example (P Q R : Prop) (hp : P) (hq : Q) (hr : ¬ R) (hnq : ¬ Q) : false :=
begin
  contr
end


example (P Q R : Prop) (hnq : ¬ Q) (hp : P) (hq : Q) (hr : ¬ R) : 0 = 1 :=
begin
  sorry,
end


example (P Q R : Prop) (hp : P) (hq : Q) (hr : ¬ R) (hnq : Q → false) : false :=
by contr



/-!

## Exercise 2

Write a tactic that proves a given `nat`-valued declaration is nonnegative.
The tactic should take the name of a declaration whose return type is `ℕ`
(presumably with some arguments), e.g. `nat.add : ℕ → ℕ → ℕ`
or `list.length : Π α : Type, list α → ℕ`.
It should add a new declaration to the environment which proves all applications
of this function are nonnegative,
e.g. `nat.add_nonneg : ∀ m n : ℕ, 0 ≤ nat.add m n`.

Bonus: create reasonable names for these declarations, and/or take an optional argument
for the new name.

This tactic is not useful by itself, but it's a good way to practice
querying and modifying an environment and working under binders.
It is not a tactic to be used during a proof, but rather as a command.


Hints:
* For looking at declarations in the environment, you will need the `declaration` type,
  as well as the tactics `get_decl` and `add_decl`.
* You will have to manipulate an expression under binders.
  The tactics `mk_local_pis` and `pis`, or their lambda equivalents, will be helpful here.
* `mk_mapp` is a variant of `mk_app` that lets you provide implicit arguments.
-/

#check add_decl
#check get_decl
#check mk_local_pis

meta def add_nonneg_proof_aux (n : name) : tactic unit :=
do pf ← mk_mapp 

meta def add_nonneg_proof (n : name) : tactic unit :=
by admit

-- these test cases should succeed when you're done

-- run_cmd add_nonneg_proof `nat.add
-- run_cmd add_nonneg_proof `list.length

-- #check nat.add_nonneg
-- #check list.length_nonneg


/-!

## Exercise 3 (challenge!)

The mathlib tactic `cancel_denoms` is intended to get rid of division by numerals
in expressions where this makes sense. For example,

-/

example (q : ℚ) (h : q / 3 > 0) : q > 0 :=
begin
  cancel_denoms at h, 
  exact h,
end

/-!

But it is not complete. In particular, it doesn't like nested division
or other operators in denominators. These all fail:

-/

example (q : ℚ) (h : q / (3 / 4) > 0) : false :=
begin
  linarith.cancel_denoms at h,
end

example (p q : ℚ) (h : q / 2 / 3 < q) : false :=
begin
  -- cancel_denoms at h,
  sorry
end

example (p q : ℚ) (h : q / 2 < 3 / (4*q)) : false :=
begin
  -- cancel_denoms at h,
  sorry
end

-- this one succeeds but doesn't do what it should
example (p q : ℚ) (h : q / (2*3) < q) : false :=
begin
  -- cancel_denoms at h,
  sorry
end

/-!

Look at the code in `src/tactic/cancel_denoms.lean` and try to fix it.
See if you can solve any or all of these failing test cases.

If you succeed, a pull request to mathlib is strongly encouraged!

-/


