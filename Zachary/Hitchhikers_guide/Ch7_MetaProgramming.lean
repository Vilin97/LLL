import tactic

inductive even' : ℕ → Prop
| zero : even' 0
| add_two : ∀k : ℕ, even' k → even' (k + 2)

meta def intro_and_even : tactic unit :=
     do -- entry into monad
       tactic.repeat (tactic.applyc ``and.intro), -- ‘‘ resolves name
       tactic.any_goals (tactic.solve1 (tactic.repeat
         (tactic.applyc ``even'.add_two
          <|> tactic.applyc ``even'.zero))),
        pure () -- empty tuple has type unit, only has side effects

-- <|> is the same as orelse
-- try is the same as  tactic <|> skip
-- all_goals succeeds if can apply tactic to all goals
-- any_goals succeeds if can apply tactic to any goal
-- solve1 succeds if tactic proves goal

-- tactic1; tactic2 means tactic1 then tactic2 on subgoals
-- tactic.trace prints a message
-- tactic.fail prints error

-- run_cmd runs on top level without proof context

lemma any_goals_solve1_repeat_orelse :
  even' 4 ∧ even' 7 ∧ even' 3 ∧ even' 0 :=
  begin
    tactic.trace "proving even",
    intro_and_even,
  end   



lemma even_14 : 
  even' (14 : ℕ)  :=
  by  -- enter tactic mode
    do tactic.trace "proving even",
    intro_and_even

meta def trace_goals : tactic unit :=
do
  tactic.trace "local context:", 
  ctx ← tactic.local_context, 
  tactic.trace ctx,
  tactic.trace "target:",
  P ← tactic.target,
  tactic.trace P,
  tactic.trace "all missing proofs:", Hs ← tactic.get_goals,
  tactic.trace Hs,
  τs ← list.mmap tactic.infer_type Hs, tactic.trace τs

lemma even_18_and_even_20 (α : Type) (a : α) : even' 18 ∧ even' 20 :=
by do
       tactic.applyc ``and.intro,
       trace_goals,
       intro_and_even

meta def exact_list : list expr → tactic unit
|[] := tactic.fail "no matching expression found" 
| (h :: hs) := -- h is head and hs is tail of list
  do {
    tactic.trace "trying",
    tactic.trace h,
    tactic.exact h }
  <|> exact_list hs -- try the tail of the list if head fails

meta def hypothesis : tactic unit :=
do
  hs ← tactic.local_context, 
  exact_list hs

lemma app_of_app {α : Type} {p : α → Prop} {a : α} (h : p a) :
       p a :=
     by hypothesis


-- metaprogramming types:
--- tactic- proof state, context
--- name- structured name
--- expr- term/type/proof
--- declaration- lemma/theorem/constant
--- environment- stores declarations and notations

-- backtick notation for expr
--- ` : constructs expression whith no placeholders
--- `` : constructs expression with placeholders
--- ``` : expression with no name
-- ``(_) : pre-expression, evaluated at definition
-- ```(_) :pre-expression, evaluated at runtime

--- %% is antiquotiation for imbedding expr within expr


run_cmd tactic.trace `seattle.washington

lemma one_add_two_eq_three :
       1 + 2 = 3 :=
by do
-- ea ← tactic.get_local `a,
-- eb ← tactic.get_local `b,
-- ec ← tactic.get_local `c,
`(%%a + %%b = %%c) ← tactic.target, tactic.trace a,
tactic.trace a,
tactic.trace b,
tactic.trace c,
`(@eq %%α %%l %%r) ← tactic.target, tactic.trace α,
tactic.trace l,
tactic.trace r,
       tactic.exact `(refl _ : 3 = 3)

run_cmd do
env ← tactic.get_env,
tactic.trace (environment.fold env 0 (λdecl n, n + 1))

-- conjunction destruction tactic

meta def destruct_and_helper : expr → tactic unit
| h :=
  do
  t ← tactic.infer_type h,
  match t with -- pattern matching on the type of h
  | `(%%a ∧ %%b) :=
           tactic.exact h
           <|>
           do {
              ha ← tactic.to_expr ``(and.elim_left %%h), -- elaborates pre-expression
             destruct_and_helper ha }
           <|>
            do {
                hb ← tactic.to_expr ``(and.elim_right %%h), destruct_and_helper hb }
            | _            := tactic.exact h
end

meta def destruct_and (nam : name) : tactic unit :=
     do
      h ← tactic.get_local nam, -- gets expression for given name
      destruct_and_helper h

lemma abc_b (a b c d e f : Prop) (h : (d ∧ (a ∧ (b ∧ f) )) ∧ (c ∧ e) ) : b :=
     by destruct_and `h


-- prove direct

meta def is_theorem : declaration → bool 
| (declaration.defn _ _ _ _ _ _) := ff
| (declaration.thm _ _ _ _) := tt
| (declaration.cnst _ _ _ _) := ff
| (declaration.ax _ _ _) := tt


meta def get_all_theorems : tactic (list name) :=
     do
        env ← tactic.get_env,
        pure (environment.fold env [] (λ decl nams,
         if is_theorem decl 
         then declaration.to_name decl :: nams
         else nams))


meta def prove_with_name (nam : name) : tactic unit :=
do
  tactic.applyc nam -- applies tactic with name nam to current goal
    ({ md := tactic.transparency.reducible, unify := ff }
      : tactic.apply_cfg), -- optional params for performance
  tactic.all_goals tactic.assumption, -- applies assumption to all goals
  pure ()

meta def prove_direct : tactic unit :=
     do
  nams ← get_all_theorems,
  list.mfirst (λ nam,
    do
    prove_with_name nam,
    tactic.trace ("proved by " ++ to_string nam)) nams

meta def prove_direct_symm : tactic unit :=
prove_direct
<|>
do {
  tactic.applyc `eq.symm,
  prove_direct
}

#check tactic.intro