import tactic
import ring_theory.ideal.basic
import ring_theory.ideal.operations
import .oka


variables {B: Type} [comm_ring B] (f: B → B) (x: B)


def principal_ideal_set (A : Type) [comm_ring A]: set(ideal A) := {b: ideal A | ∃(a :A), b = ideal.span({a})}

def principal_ideal_set_mem (I : ideal B) : I ∈ (principal_ideal_set B) ↔ ∃(a :B), I = ideal.span({a}) :=
begin
  refl,
end

-- #check ⊤ ∈ principal_ideal_set B

-- #check (⊤ : ideal B)

lemma top_is_principal :
  (⊤ : ideal B) ∈ principal_ideal_set B :=
begin
  rw principal_ideal_set_mem,
  use 1,
  simp,
end

lemma eq_iff (I J : ideal B) : (∀(b : B), b ∈ I ↔ b ∈ J) ↔ I = J :=
begin
  exact set_like.ext_iff.symm,
end

#check ideal.span

-- lemma span_singleton_self (x : B): x ∈ (ideal.span {x}) :=

lemma prod_quot_ideal (I J : ideal B) (h_pri : J ∈ principal_ideal_set B) (h_less : I ≤ J) : I = J * (ideal_quotient I J) :=
begin
  rw ← eq_iff,
  intro b,
  split,
  {
    intro hyp,
    rw (principal_ideal_set_mem J) at h_pri,
    cases h_pri with x hx,
    rw element_comparison at h_less,
    have hyp_j := h_less b hyp,
    rw [hx, ideal_ele_quotient_def],
    rw [hx, ideal.mem_span_singleton] at hyp_j,
    unfold has_dvd.dvd at hyp_j,
    cases hyp_j with c,
    rw mul_comm at hyp_j_h,
    rw hyp_j_h at hyp,
    rw ← ideal_ele_quotient_contains_rw at hyp,
    rw mul_comm at hyp_j_h,
    rw hyp_j_h,
    have trivial_fact : x ∈ ideal.span {x},
    {
      rw ideal.mem_span_singleton,
    },
    have goal := submodule.smul_mem_smul trivial_fact hyp,
    exact goal,
  }, {
    intro hyp,

  }
end


-- lemma prod_computation (I : ideal B) : I * I = I * I :=
-- begin
-- end

lemma principal_oka_condition : (∀ (I : ideal B),
     (∃ (a : B),
        ideal.span {a} ⊔ I ∈ principal_ideal_set B ∧ ideal_ele_quotient I a ∈ principal_ideal_set B) →
     I ∈ principal_ideal_set B) :=
begin
  intros I hyp,
  cases hyp with a hyp,
  cases hyp with hyp1 hyp2,
  sorry,
end

#check oka_family.mk (principal_ideal_set B) (top_is_principal) (principal_oka_condition)

def principal_oka_family : oka_family B :=
{
  carrier := principal_ideal_set B,
  contains_ring' := top_is_principal,
  oka_condition' := principal_oka_condition,
}