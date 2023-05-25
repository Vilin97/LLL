import tactic
import Init
import data.nat.basic


namespace hidden

def state := string → ℕ

inductive stmt : Type
| skip : stmt
| assign : string → (state → ℕ) → stmt 
| seq : stmt → stmt → stmt
| ite : (state → Prop) → stmt → stmt → stmt
| while : (state → Prop) → stmt → stmt

infixr ` ;; ` : 90 := stmt.seq

def silly_loop : stmt :=
stmt.while (λ s : state, s "x" > s "y" )
  (stmt.skip ;; stmt.assign "x" (λ s : state, s "x" - 1))

end hidden



namespace hidden

inductive PropForm
  | tr : PropForm
  | fls : PropForm
  | var : string → PropForm
  | conj : PropForm → PropForm → PropForm
  | disj : PropForm → PropForm → PropForm
  | impl : PropForm → PropForm → PropForm
  | neg : PropForm → PropForm
  | biImpl : PropForm → PropForm → PropForm


def PropAssignment := list (string × bool)

def PropForm.eval (v : PropAssignment) : PropForm → PropForm
  | var s => v.eval s
  | tr => tr
  | fls => fls
  | neg A => !(eval v A)
  | conj A B => (eval v A) && (eval v B)
  | disj A B => (eval v A) || (eval v B)
  | impl A B => !(eval v A) || (eval v B)
  | biImpl A B => (!(eval v A) || (eval v B)) && (!(eval v B) || (eval v A))


infixr ` and ` : 90 := PropForm.conj
infixr ` or ` : 90 := PropForm.disj
infixr ` => ` : 90 := PropForm.impl
infixr ` <=> ` : 90 := PropForm.biImpl
prefix ` not ` : 90 := PropForm.neg

open PropForm

#check var "x" => var "y"

end hidden

namespace PropForm






