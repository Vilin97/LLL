import tactic
import ring_theory.ideal.basic
import ring_theory.ideal.operations
import .oka

variables {B: Type} [comm_ring B] (L M : ideal B)


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

lemma prod_quot_subset (I J : ideal B) : J • I.colon J ≤ I :=
begin
  rw submodule.smul_le,
  intros r hyp_r n hyp_n,
  rw submodule.mem_colon at hyp_n,
  simp at hyp_n ⊢,
  rw mul_comm,
  apply hyp_n,
  exact hyp_r,
end

lemma ideal_antisymm (I J :ideal B) : I ≤ J ∧ J ≤ I ↔ I = J := 
begin
  exact antisymm_iff,
end

lemma subset (I J : ideal B) : I ≤ J ↔ ∀(a : B), a ∈ I → a ∈ J :=
begin
  exact set_like.le_def,
end

lemma prod_quot_ideal (I J : ideal B) (h_pri : J ∈ principal_ideal_set B) (h_less : I ≤ J) : I = J * (I.colon J) :=
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
    rw hx,
    rw [hx, ideal.mem_span_singleton] at hyp_j,
    unfold has_dvd.dvd at hyp_j,
    cases hyp_j with c,
    rw mul_comm at hyp_j_h,
    rw hyp_j_h at hyp,
    rw hyp_j_h,
    rw mul_comm,
    rw ← ideal.mem_colon_singleton at hyp,
    have trivial_fact : x ∈ ideal.span {x},
    {
      rw ideal.mem_span_singleton,
    },
    have goal := submodule.smul_mem_smul trivial_fact hyp,
    exact goal,
  }, {
    intro hyp,
    rw (principal_ideal_set_mem J) at h_pri,
    cases h_pri with x hx,
    rw hx at hyp,
    rw ideal.mem_span_singleton_mul at hyp,
    rcases hyp with ⟨z, H, hyp⟩,
    rw ideal.mem_colon_singleton at H,
    rw mul_comm at H,
    rw hyp at H,
    exact H,
  }
end

-- lemma prod_computation (I : ideal B) : I * I = I * I :=
-- begin
-- end

lemma ideal_colon_element_leq (I : ideal B) (a : B) : I ≤ (ideal.span(insert a ↑I)) :=
begin
  rw subset,
  intros b hyp,
  apply ideal.subset_span,
  finish,
end

lemma colon_colon (a : B) (I: ideal B) : I.colon (ideal.span(insert a ↑I)) = I.colon (ideal.span{a}) :=
begin
  ext,
  rw ideal.mem_colon_singleton,
  split,
  {
    rw submodule.mem_colon,
    intro hyp,
    specialize hyp a,
    apply hyp,
    apply ideal.subset_span,
    apply set.mem_insert,
  }, {
    intro hyp,
    rw submodule.mem_colon,
    intro p,
    rw ideal.mem_span_insert,
    intro hyp,
    rcases hyp with ⟨l,c,H,rwp⟩,
    rw ideal.span_eq at H,
    rw rwp,
    simp,
    rw ring.left_distrib,
    apply ideal.add_mem,
    {
      rw ← mul_assoc,
      rw mul_comm x,
      rw mul_assoc,
      apply ideal.mul_mem_left,
      exact hyp,
    }, {
      apply ideal.mul_mem_left,
      exact H,
    }
  }
end

lemma principal_oka_condition : (∀ (I : ideal B),
     (∃ (a : B),
        ideal.span (insert a ↑I)∈ principal_ideal_set B ∧ I.colon (ideal.span{a}) ∈ principal_ideal_set B) →
     I ∈ principal_ideal_set B) :=
begin
  intros I hyp,
  cases hyp with a hyp,
  cases hyp with hyp1 hyp2,
  have triv_contains := ideal_colon_element_leq I a,
  rw prod_quot_ideal I (ideal.span(insert a ↑I)) hyp1 triv_contains,
  rw principal_ideal_set_mem at hyp2,
  cases hyp2 with c,
  rw colon_colon,
  rw hyp2_h,
  rw principal_ideal_set_mem at hyp1,
  cases hyp1 with d,
  rw hyp1_h,
  rw ideal.span_singleton_mul_span_singleton,
  rw principal_ideal_set_mem,
  use d * c,
end

#check oka_family.mk (principal_ideal_set B) (top_is_principal) (principal_oka_condition)

def principal_oka_family : oka_family B :=
{
  carrier := principal_ideal_set B,
  contains_ring' := top_is_principal,
  oka_condition' := principal_oka_condition,
}