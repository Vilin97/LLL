import data.real.basic
import data.finset.basic
import algebra.big_operators.basic
import data.fintype.basic
import data.set.finite
import tactic
import algebra.group.defs
import group_theory.free_abelian_group


open_locale big_operators

variables α β : Type

def f := α → β 
def f' := (α → ℤ) → β 

-- define a function lifting f to f' : (α → ℤ) → β 
-- such that f' is the sum of f



def list_fin_to_list_nat {n : ℕ} (l : list (fin n)) : list ℕ :=
list.map (λ i, fin.val i) l


-- define a function that takes a set of lists and returns the set of lists such that one element is removed

def rem {n : ℕ} : set (list (fin (n + 1))) → set (list (fin n)) := 
λ s, {l : list (fin n) | ∃ (l' : list (fin (n+1))), l' ∈ s ∧ list_fin_to_list_nat l = list_fin_to_list_nat (l'.drop 1)}

