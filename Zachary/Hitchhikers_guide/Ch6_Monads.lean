import category_theory.category.basic


def connect {α : Type} {β : Type} :
  option α → (α → option β) → option β
  | option.none f := option.none
  | (option.some x) f := f x

def sum_2_5_7 (ns : list ℕ) : option ℕ :=
do 
  n2 <- list.nth ns 1,
  n5 <- list.nth ns 4,
  n7 <- list.nth ns 6,
  pure (n2 + n5 + n7)

