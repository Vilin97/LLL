import tactic
-- definition of a reduction
def relation (t : Type) (u : Type) : Type := set (t × u)
def reduction (t : Type) := relation t t

instance {t u : Type} : has_mem (t × u) (relation t u) := set.has_mem
instance {t : Type} : has_mem (t × t) (reduction t) := set.has_mem

-- composition of relations
def compose {a b c : Type} (R : relation a b) (S : relation b c) : relation a c :=
  {t | ∃ y, (t.1, y) ∈ R ∧ (y, t.2) ∈ S}

-- some basic relations

def nat1 := {x : nat // x > 0}

section
variables {t : Type}

def identity : reduction t := {t | t.1 = t.2}

variables (r : reduction t)

def nfold : ℕ → reduction t
| nat.zero := identity
| (nat.succ n) := compose (nfold n) r

def trans_closure : reduction t :=
  {x | ∃ n, x ∈ nfold r (n + 1)}

def refl_trans_closure : reduction t :=
  {x | x ∈ @identity t ∨ x ∈ trans_closure r}

def refl_closure : reduction t :=
  {x | x ∈ r ∨ x ∈ @identity t}

def inverse : reduction t :=
  {x | (x.2, x.1) ∈ r}

def symm_closure : reduction t :=
  {x | x ∈ r ∨ x ∈ inverse r}

def trans_symm_closure := trans_closure (symm_closure r)

def refl_trans_symm_closure := refl_trans_closure (symm_closure r)
end


section
open nat
variables {t : Type}

def comp_id (a : reduction t) : compose a identity = a :=
begin
  rw compose,
  --rw identity at *,
  ext q,
  split,
  intro h,
  cases q,
  simp at h,
  rw identity at *,
  simp at h,
  exact h,
  intro h,
  simp,
  use q.snd,
  rw identity,
  simp,
  exact h,
end

def id_comp (a : reduction t) : compose identity a = a :=
begin
  rw compose,
  ext q,
  split,
  intro h,
  cases q,
  simp at h,
  rw identity at *,
  simp at h,
  exact h,
  intro h,
  simp,
  use q.fst,
  rw identity,
  simp,
  exact h,
end

def zero_id : ∀ (r : reduction t), nfold r 0 = identity := begin
  intro,
  triv,
end

def one_id (r : reduction t) : nfold r 1 = r := begin
  -- intro r,
  rw nfold,
  rw zero_id,
  rw id_comp,
end

def comp_assoc (q r s : reduction t):
  compose q (compose r s) = compose (compose q r) s :=
begin
  -- intros q r s,
  repeat {rw compose},
  simp,
  ext q,
  split,
  intro h,
  rcases h with ⟨w, x, y, z, z2⟩,
  simp,
  use y,
  use w,
  finish,
  exact z2,
  intro h,
  rcases h with ⟨w, x, y⟩,
  rcases x with ⟨z, z2⟩,
  simp,
  cases z2,
  use z,
  split,
  use z2_left,
  use w,
  split,
  exact z2_right,
  exact y,
end

end

-- so rⁿ ∘ (r ∘ rᵐ) = (rⁿ ∘ r) ∘ rᵐ

-- specialized version of associativity
section

open nat
variables {t : Type} (r : reduction t) (m n : ℕ)

def comp_succ := comp_assoc (nfold r n) (nfold r m) r

def succ_comp :
  (compose (compose (nfold r m) r)(nfold r n)) = compose (compose (nfold r m)(nfold r n)) r
  :=
begin
  induction n with h dh,
  repeat {rw zero_id},
  repeat {rw comp_id},
  rw ←comp_succ,
  rw nfold,
  rw comp_assoc,
  rw dh,
  repeat {rw comp_assoc},
end

-- addition for n-fold composition
def nfold_add : compose (nfold r m) (nfold r n) = nfold r (m + n) :=
begin
  induction m with d hd,
  rw zero_id,
  rw id_comp,
  simp,
  repeat {rw nfold},
  have h : d.succ + n = (d+n).succ,
  exact succ_add d n,
  rw h,
  rw nfold,
  rw succ_comp,
  rw hd,
end

-- commutativity of n-fold compositions should follow
-- this is provable trivially with nfold-add
def comp_comm : compose (nfold r m) (nfold r n) = compose (nfold r n) (nfold r m) :=
begin
  induction m with h dh,
  {repeat {rw zero_id}, rw id_comp, rw comp_id},
  rw nfold, rw succ_comp, rw comp_succ, rw dh,
end

end


-- some definitions
section

variables {t : Type} (r : reduction t) (x : t)

def reducible := ∃ (y : t), (x, y) ∈ r
def normal_form := ¬(reducible r x)

variables (y : t)
def has_the_normal_form := normal_form r y ∧ (x, y) ∈ refl_trans_closure r
def direct_succ := (x, y) ∈ r
def succ := (x, y) ∈ trans_closure r
def joinable := let s := refl_trans_closure r in ∃ (z : t), (x, z) ∈ s ∧ (y, z) ∈ s

end

section

variables {t : Type} (r : reduction t)

def church_rosser := ∀ (x y : t), (x, y) ∈ refl_trans_symm_closure r → joinable r x y
def confluent := ∀ (x y : t), (∃ (z : t), (z, x) ∈ refl_trans_closure r ∧ (z, y) ∈ refl_trans_closure r) → joinable r x y
def terminating := ¬(∃ (seq : ℕ → t), ∀ (n : ℕ), (seq n, seq (n + 1)) ∈ r)
def normalizing := ∀ (x : t), ∃ (y : t), has_the_normal_form r x y
def convergent := confluent r ∧ terminating r
def has_wfi := ∀ (p : t → Prop)
                 (h : ∀(x : t), (∀ (y : t), (x, y) ∈ r → p y) → p x),
                 ∀ (x : t), p x

-- def termination_impl_wfi : terminating r → has_wfi r :=
-- begin
--   intro h_,
--   by_contra,
--   rw has_wfi at *,
--   rw not_forall at h,
--   cases h with p,
--   -- there exists p
--   rw not_forall at h_h,
--   cases h_h with h,
--   -- and some x
--   rw not_forall at h_h_h,
--   cases h_h_h with x npx,
--   specialize h x,
--   have h2 := mt h npx,
--   rw not_forall at h2,
--   cases h2 with y,
--   rw not_imp at h2_h,
--   -- cases h_h_h with a b,

-- end

-- helper function is used to generate an infinte chain of functions with np
def helper
  (p : t → Prop)
  (h : (∀ (x : t), (∀ (y : t), (x, y) ∈ r → p y) → p x))
  (x : t)
  (npx : ¬ p x)
  : ∃ (y : t), (x, y) ∈ r ∧ ¬ p y :=
begin
  specialize h x,
  have h2 := mt h npx,
  rw not_forall at h2,
  cases h2 with y,
  rw not_imp at h2_h,
  use y,
  exact h2_h,
end
#check helper

def mkseq
  (p : t → Prop)
  (h : ∀ (x : t) (npx : ¬ p x), ∃ (y : t), (x, y) ∈ r ∧ ¬ p y)
  :(∃(x : t), ¬ p x) → ℕ → t --, ∀ (n : ℕ), (¬ p (seq n) ∧ (seq n, seq (n + 1))∈ r)
| hx 0 := Exists.some hx
| hx (nat.succ n) :=
begin
  cases hx with x npx,

end


def mkseq
  (p : t → Prop)
  (h : ∀ (x : t) (npx : ¬ p x), ∃ (y : t), (x, y) ∈ r ∧ ¬ p y)
  (ex : ∃(x : t), ¬ p x)
  : ℕ → t --, ∀ (n : ℕ), (¬ p (seq n) ∧ (seq n, seq (n + 1))∈ r)
| 0 := Exists.some ex
| (nat.succ n) :=
begin
  have y := (mkseq n),
  have npy : ¬ p y,
  sorry,
  specialize h y npy,
  exact h.some,
end


example (p : t → Prop) : (∃(x : t), p x) → t := by library_search
def termination_impl_wfi_help : terminating r → has_wfi r :=
begin
  intro h_,
  by_contra,
  rw terminating at h_,
  rw has_wfi at *,
  rw not_forall at h,
  cases h with p,
  -- there exists p
  rw not_forall at h_h,
  cases h_h with h,
  -- and some x
  rw not_forall at h_h_h,
  cases h_h_h with x npx,
  have find_next := helper r p h,
  let seq : t → ℕ → t :=
    begin
      intros e n,
      exact match n with
      | 0 := e
      | succ m := seq (find_next e) m
      end,
      end,
-- cases h_h_h with a b,
end




example {a b : Prop} : ¬ (a → b) → a ∧ ¬ b := by library_search

example {a b : Prop} : (a → b) →  ¬ b → ¬ a := by library_search

example {t : Type} (p : t → Prop) (h : ¬ (∀ (x : t), p x)) : ∃ (x : t), ¬ p x := by library_search


-- what's a terminating reduction? How do we formalize this notion?
#check joinable identity 3 3
