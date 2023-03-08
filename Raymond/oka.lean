import tactic
import ring_theory.ideal.basic
import ring_theory.ideal.operations

variables {A: Type} [comm_ring A] {a : A} {I : ideal A}

#print submodule.colon


def is_proper := {S : ideal A| ((1:A) ∉ S)}
def all_ideals := set(ideal A)


structure oka_family (α : Type) [comm_ring α] :=
(carrier : set (ideal α))
(contains_ring' : ⊤ ∈  carrier)
(oka_condition' : ∀ (I : ideal α), 
  (∃ (a : α), (ideal.span(has_insert.insert a ↑I)) ∈ carrier ∧ (I.colon (ideal.span{a})  ∈ carrier)) → I ∈ carrier)


attribute [ext] oka_family

variables (S : oka_family A)

instance : has_mem (ideal A) (oka_family A) :=
{ mem := λ m H, m ∈ H.carrier }

instance : has_coe (oka_family A) (set (ideal A)) := 
{ coe := λ H, H.carrier }

@[simp] lemma mem_coe {g : ideal A} : g ∈ (S : set (ideal A)) ↔ g ∈ S :=
begin
  -- These two concepts just mean the same thing
  refl
end

@[ext] def ext' (H K : oka_family A) (h : ∀ g : ideal A, g ∈ H ↔ g ∈ K) : H = K :=
begin
  ext x,
  exact h x,
end

lemma contains_ring : ⊤ ∈ S :=
begin
  apply oka_family.contains_ring',
end

lemma oka_condition : ∀ (I : ideal A), 
  (∃ (a : A), (ideal.span(has_insert.insert a ↑I)) ∈ S ∧ (I.colon (ideal.span{a}) ∈ S)) → I ∈ S :=
begin
  apply oka_family.oka_condition',
end

lemma element_comparison {I J : ideal A} :
  I ≤  J ↔ ∀ (a : A), a ∈ I → a ∈ J :=
begin
  split,
  {
    intros hI,
    exact set_like.le_def.mpr hI,
  }, {
    intro h,
    exact set_like.le_def.mpr h,
  }
end

lemma element_comparison_contrapositive {I J : ideal A} :
  ¬ I ≤ J ↔ ∃(a : A), a ∈ I ∧ a ∉ J :=
begin
  rw element_comparison,
  simp,
end

lemma strict_containment_iff {I J : ideal A}:
  (I ≤ J ∧ ∃(a : A), a ∈ J ∧ a ∉ I) ↔ I < J :=
begin
  split,
  {
    intro h,
    cases h,
    rw ← element_comparison_contrapositive at h_right,
    exact lt_of_le_not_le h_left h_right,
  }, {
    intro h,
    have nleq := not_le_of_gt h,
    have leq : I ≤ J, {
      cases h,
      intro,
      apply h_left,
    },
    split,
    exact leq,
    rw ← element_comparison_contrapositive,
    exact nleq,
  },
end


lemma ssubset_gen_with_extra_element (I : ideal A) (a : A):
  a ∉ I → (I < ideal.span (insert a ↑I)) :=
begin
  have leq : I ≤ ideal.span (insert a ↑I), {
    rw element_comparison,
    intros x hyp,
    rw ideal.mem_span_insert,
    use 0,
    use x,
    split,
    {
      apply ideal.subset_span,
      use hyp,
    },
    ring_nf,
  },
  intro h,
  rw ← strict_containment_iff,
  split,
  {
    exact leq,
  }, {
    use a,
    split,
    {
      apply ideal.subset_span,
      apply set.mem_insert,
    }, {
      exact h,
    }
  }
end

lemma quot_contains_self (I : ideal A) (a : A) :
  I ≤ (I.colon (ideal.span{a})) :=
begin
  intros i h,
  rw ideal.mem_colon_singleton,
  exact ideal.mul_mem_right a I h,
end


lemma max_non_oka_is_prime (I : ideal A) (K : oka_family A) :
  I ∉ K ∧ (∀(J : ideal A), I < J → J ∈ K) → I.is_prime :=
begin
  intro h,
  cases h,
  by_contra,
  rw ideal.not_is_prime_iff at h,
  cases h,
  {
    have contradiction : I ∈ K, {
      rw h,
      exact contains_ring K,
    },
    apply h_left,
    exact contradiction,
  }, {
    cases h with x h,
    cases h with H_x h,
    cases h with y h,
    cases h with H_y h,
    have contradiction : I ∈ K, {
      apply oka_condition,
      use x,
      split,
      {
        apply h_right,
        apply ssubset_gen_with_extra_element,
        exact H_x,
      }, {
        have contains_y : y ∈ (I.colon (ideal.span({x}))), {
          rw ideal.mem_colon_singleton,
          rw mul_comm,
          exact h,
        },
        apply h_right,
        rw ← strict_containment_iff,
        split,
        {
          apply quot_contains_self,
        }, {
          use y,
          split,
          exact contains_y,
          exact H_y,
        }
      }
    },
    apply h_left,
    exact contradiction,
  }
end


