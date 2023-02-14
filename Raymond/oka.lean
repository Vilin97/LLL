import tactic
import ring_theory.ideal.basic

variables {A: Type} [comm_ring A]

-- #check (univ: set (ideal A))


-- def powerset (B : set A) : set (set A) := {C : set A | C ⊆ B}

def is_proper := {S : ideal A| ((1:A) ∉ S)}
def all_ideals := set(ideal A)

#check is_proper (⊤ : ideal(A))


def zero_is_ideal : ideal A :=
{ carrier := {(0: A)},
  zero_mem' := 
  begin
    simp,
  end,
  add_mem' :=
  begin
    intros a b ha hb,
    have ha_rw: a = 0, {
      cases ha,
      refl,
    },
    have hb_rw: b = 0, {
      cases hb,
      refl,
    },
    rw ha_rw,
    rw hb_rw,
    ring_nf,
    simp,
  end,
  smul_mem' :=
  begin
    intros c x hx,
    have rw_hx: x = 0, {
      use hx,
    },
    rw rw_hx,
    simp,
  end,
}

def set_to_ideal (eles: set A) (zero_mem : (0 : A) ∈ eles)
    (add_mem: ∀ (a b : A), a ∈ eles → b ∈ eles → a + b ∈ eles)
    (smul_mem: ∀ (c x: A), x ∈ eles → c • x ∈ eles): ideal A :=
{
  carrier := eles,
  zero_mem' := zero_mem,
  add_mem' := add_mem,
  smul_mem' := smul_mem,
}

def ideal_quotient_set (I: ideal A) (J : ideal A): set A :=
  {a| ∀ (j ∈ J), a • j ∈ I}

lemma ideal_quotient_set_contains_rw (I: ideal A) (J : ideal A) (x : A): 
  x ∈ (ideal_quotient_set I J) ↔ ∀ (j ∈ J), x • j ∈ I := 
begin
  refl,
end

lemma ideal_quotient_zero_mem (I : ideal A) (J : ideal A) : (0:A) ∈ (ideal_quotient_set I J) :=
begin
  rw ideal_quotient_set_contains_rw,
  intros j hj,
  simp,
end

lemma ideal_quotient_add_mem (I : ideal A) (J: ideal A) (a b : A) :
  a ∈ ideal_quotient_set I J → b ∈ ideal_quotient_set I J → a + b ∈ ideal_quotient_set I J :=
  begin
    intros ha hb,
    rw ideal_quotient_set_contains_rw at ha hb ⊢,
    intros j hj,
    specialize ha j hj,
    specialize hb j hj,
    simp,
    rw right_distrib,
    apply add_mem,
    exact ha,
    exact hb,
  end

lemma ideal_quotient_mul_mem (I: ideal A) (J: ideal A) (c x : A) :
  x ∈ ideal_quotient_set I J → c • x ∈ ideal_quotient_set I J :=
begin
  repeat {rw ideal_quotient_contains_rw},
  intros h j hj,
  specialize h j hj,
  simp,
  rw mul_assoc,
  apply ideal.mul_mem_left,
  exact h,
end

def ideal_quotient (I J: ideal A) : ideal A :=
{
  carrier := ideal_quotient_set I J,
  zero_mem' := ideal_quotient_zero_mem I J,
  add_mem' := ideal_quotient_add_mem I J,
  smul_mem' := ideal_quotient_mul_mem I J,
}

lemma ideal_quotient_contains_rw (I J : ideal A) (x : A):
  x ∈ (ideal_quotient I J) ↔ ∀ (j ∈ J), x • j ∈ I := 
begin
  refl,
end

def ideal_ele_quotient (I : ideal A) (a : A) : ideal A :=
  ideal_quotient I (ideal.span {a})

def ideal_ele_quotient_def (I : ideal A) (a : A) : ideal_quotient I (ideal.span {a}) = ideal_ele_quotient I a :=
begin
  refl,
end

lemma ideal_ele_quotient_rw (I : ideal A) (a : A) :
  ideal_ele_quotient I a = ideal_quotient I (ideal.span {a}) :=
begin
  refl,
end


def ideal_ele_quotient_contains_rw (I : ideal A) (a : A) (x : A) :
  x ∈ ideal_ele_quotient I a ↔ (x * a) ∈ I :=
begin
  split,
  {
    intro h,
    rw ideal_ele_quotient_rw at h,
    rw ideal_quotient_contains_rw at h,
    specialize h a,
    apply h,
    apply ideal.subset_span,
    simp,
  }, {
    intro h,
    rw ideal_ele_quotient_rw,
    rw ideal_quotient_contains_rw,
    intros j hj,
    rw ideal.mem_span_singleton at hj,
    have rw_divides := exists_eq_mul_right_of_dvd hj,
    cases rw_divides with c,
    rw rw_divides_h,
    simp,
    rw mul_comm a c,
    rw ← mul_assoc,
    rw mul_comm x c,
    rw mul_assoc,
    apply ideal.mul_mem_left,
    exact h,
  }
end

structure oka_family (α : Type) [comm_ring α] :=
(carrier : set (ideal α))
(contains_ring' : ⊤ ∈  carrier)
(oka_condition' : ∀ (I : ideal α), 
  (∃ (a : α), ((ideal.span {a}) ⊔ I) ∈ carrier ∧ (ideal_ele_quotient I a  ∈ carrier)) → I ∈ carrier)


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
  (∃ (a : A), ((ideal.span {a}) ⊔ I) ∈ S ∧ (ideal_ele_quotient I a ∈ S)) → I ∈ S :=
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
  a ∉ I → (I < (ideal.span {a}) ⊔ I) :=
begin
  have leq : I ≤ (ideal.span {a}) ⊔ I, {
    exact le_sup_right,
  },
  intro h,
  have contains : a ∈ (ideal.span {a}) ⊔ I, {
    rw ideal.mem_span_singleton_sup,
    use 1,
    use 0,
    split,
    {
      exact ideal.zero_mem I,
    }, {
      ring_nf,
    }
  },
  rw ← strict_containment_iff,
  split,
  {
    exact leq,
  }, {
    use a,
    split,
    {
      exact contains,
    }, {
      exact h,
    }
  }
end

lemma quot_contains_self (I : ideal A) (a : A) :
  I ≤ (ideal_ele_quotient I a) :=
begin
  intros i h,
  rw ideal_ele_quotient_contains_rw,
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
        have contains_y : y ∈ (ideal_ele_quotient I x), {
          rw ideal_ele_quotient_contains_rw,
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
