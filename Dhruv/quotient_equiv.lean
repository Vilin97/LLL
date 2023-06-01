import tactic
import group_theory.subgroup.basic
import group_theory.coset
import data.fintype.basic
import data.fintype.card

variables {G : Type} [group G] -- group setup
variables (K : subgroup G) -- subgroup setup

-- Proving that congruence mod K is an equivalence relation
def R (g h : G) : Prop :=
  ∃ (k : K), g = k * h

lemma R_def (g h : G) : R K g h ↔ ∃ (k : K), g = k * h :=
begin
  refl,
end

lemma R_reflexive : reflexive (R K) :=
begin
  unfold reflexive,
  intro x,
  rw R_def,
  use (1 : K),
  simp,
end

lemma R_symmetric : symmetric (R K) :=
begin
  unfold symmetric,
  intros x y,
  intro hRxy,
  rw R_def at hRxy ⊢,
  cases hRxy with k hk,
  use k⁻¹,
  rw hk,
  simp,
end

lemma R_transitive : transitive (R K) :=
begin
  unfold transitive,
  intros x y z,
  intros hRxy hRyz,
  rw R_def at hRxy hRyz ⊢,
  cases hRxy with k hk,
  cases hRyz with k' hk',
  use k * k',
  rw hk,
  simp,
  rw hk',
  rw ←mul_assoc,
end

lemma R_equivalence : equivalence (R K) :=
begin
  unfold equivalence,
  split,
  {
    apply R_reflexive,
  },
  split,
  {
    apply R_symmetric,
  },
  apply R_transitive,
end

-- Define the quotient G/K
def s : setoid G :=
{
  r := R K,
  iseqv := R_equivalence K,
}

notation `GmodK` := quotient s