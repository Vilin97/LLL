import tactic
import data.nat.basic
open nat

meta def hello_world : tactic unit :=
tactic.trace "Hello," >> tactic.trace "world!"

#eval hello_world

meta def is_done : tactic bool :=
(tactic.target >> return ff) <|> return tt

meta def trace_is_done : tactic unit :=
is_done >>= tactic.trace

meta def find_matching_type (e : expr) : list expr → tactic expr
| [] := tactic.failed
| (h :: hs) := do -- :: means cons, the list constructor
  t ← tactic.infer_type h, -- ← means bind, or do notation
  (tactic.unify e t >> return h) <|> find_matching_type hs 

meta def my_assumption : tactic unit :=
do  -- Get the list of local assumptions in the context
    ctx ← tactic.local_context,
    -- Get the target of the current goal
    t ← tactic.target,
    -- Find a local assumption in the context that has the same type as the target
    find_matching_type t ctx >>= tactic.exact  
    -- Fail if no local assumption matches the target
    <|> tactic.failed




set_option pp.numerals false
set_option pp.generalized_field_notation false

def n : ℕ:= 3*2
-- kernel computation works with canonical forms
-- used for type checking
#reduce n -- reduces to canonical form
#reduce (show 2 ≤ 10, by dec_trivial) 

-- faster computation is in VM, which does arithmetic, understands strings
#eval 3*2
#eval 'a'

-- def: define a function
-- meta def: define a function that is used for computation only
-- requires: add a requirement to the function
-- well-foundedness: a property of the function
meta def f : ℕ → ℕ
| n := if n = 1 then 1
else if n%2=0 then f (n/2)
else f (3*n+1)

open expr

meta def is_constant_of (l : list name) : expr → bool
| (const a a_l) := a ∈ l
| _ := ff


#eval is_constant_of [`nat, `zachary] `(ℕ) 


meta def is_app_of (l : list name) (e : expr) : bool :=
let app_name := e.get_app_fn in 
is_constant_of l app_name

#eval is_app_of [`has_le.le, `has_lt.lt] `(3 ≤ 4)

#check has_le.le

meta def mk_app (e1 e2 : expr) : expr :=
app e1 e2

#eval to_string $ to_raw_fmt $ mk_app `(nat.succ) `(nat.zero)

meta def get_lhs_rhs : expr → option (expr × expr)
| `(%%a < %%b) := some (a, b)
| `(%%a ≤ %%b) := some (a, b)
| _ := none

#eval tactic.trace $ get_lhs_rhs `(2 < 4)

constant a : ℕ

#check [`a] -- list of names
#check `a -- name
#check `(a) -- pre-expression


reflected
expr

-- define fibonacci numbers
def fib : ℕ → ℕ
| 0 := 0 -- Base case
| 1 := 1 -- Base case
| (n+2) := fib n + fib (n+1) -- Inductive step

#eval fib 10 -- 55

-- function expressions

#eval to_string $ to_raw_fmt $ (`(λ x  : ℕ , x) : expr)  

-- example: manipulate raw expressions (dangerous)

meta def succ_fn : expr → option expr
| (lam var_name bi var_type body) := 
  let new_body := mk_app `(nat.succ) body in
  lam var_name bi var_type new_body
| _ := none

#eval to_string $ succ_fn `(λ x : ℕ, x)

-- 4

open tactic

meta def make_a_nat : tactic ℕ :=
return 14

#check make_a_nat
#check @tactic.trace

meta def trace_nat : tactic unit :=
do n ← make_a_nat, -- asigns the result of make_a_nat to n
   tactic.trace n -- prints n

#check trace_nat

run_cmd trace_nat -- creates empty tactic state, runs trace_nat

meta def inspect := tactic unit :=
do t ← tactic.target,
   tactic.trace t


-- 

meta def add_single_refl (e : expr) : tactic unit :=
do tp ← infer_type e,
  guard (tp = `(ℕ)),
  --pf ← mk_app `eq.refl [e], -- make application
  pf ← to_expr ``(not_lt_of_ge (nat.zero_le %%e)), -- elaborate pre-expression
  nm ← get_unused_name e.local_pp_name, --create unique identifier
  note nm none pf, -- add to context
  return ()

meta def add_refl : tactic unit :=
do ctx ← local_context,
  ctx.mmap' (λ e,  try (add_single_refl e))

example (a b c : ℕ) (ha : a = b) : true :=
by do add_refl

-- 6

-- auxiliary function
meta def add_nonneg_proof_aux (n : expr) (h : option name) : tactic unit :=
do pf ← mk_app `nat.zero_le [n],
  nm ← get_unused_name `h,
  note (h.get_or_else nm) none pf,
  return ()


namespace tactic
namespace interactive

setup_tactic_parser

meta def add_nonneg_proof (n : parse parser.pexpr) (h : parse ident?)  :
  tactic unit :=
do n ← to_expr n,
  add_nonneg_proof_aux n h


meta def add_nonneg_proofs (l : parse pexpr_list) : tactic unit :=
do l ← l.mmap to_expr,
  l.mmap' (λ e, add_nonneg_proof_aux e none)

end interactive
end tactic 


example (n : ℕ ) : true :=
begin
  add_nonneg_proof (n + n) hx,
  add_nonneg_proofs [n, 2*n, n+3],
end

-- pattern matching

-- meta def mk_list : tactic (list ℕ) :=
-- return [1,2,3]

-- run_cmd do 
--   [a, b, c ] ← mk_list, 
--   trace a, trace b, trace c


