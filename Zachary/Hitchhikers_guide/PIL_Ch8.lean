import tactic
open tactic

variables (a b : Prop)

meta def my_tac : tactic unit :=
do eh1 ← intro `h1,
  eh2 ← intro `h2,
  e ← to_expr ``(and.intro %%eh1 %%eh2),
  target >>= trace,
  local_context >>= trace,
  exact e
  

example : a → b → a ∧ b :=
by my_tac

#check nat.mul_comm
#check `nat.mul_comm

#check mk_const -- tries to convert name to expr
#check mk_fresh_name -- generates a fresh name
#check mk_mapp
#check mk_app
#check to_expr

example(a:Prop):a → a:= 
by do 
  n ← mk_fresh_name, --_fresh.3026.1214
  tactic.trace n,
  intro n,
  hyp ← get_local n, 
  exact hyp

-- takes a list of tactics and returns the first one that succeeds
meta def first {α : Type} : list (tactic α) → tactic α
| [] := tactic.fail "no tactic succeeds"
| (t :: ts) := t <|> first ts