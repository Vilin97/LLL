import tactic
import .quotient_equiv

variables {G : Type} [group G] -- group setup
variables (K : subgroup G) -- subgroup setup

attribute [instance] s

-- WTS K x G/K -> G is an isomorphism
theorem lagrange (hFiniteGroup : fintype G) (hFiniteSubgroup : fintype K)
(hFiniteQuotient : fintype (quotient (s K))) :
(fintype.card K * fintype.card (quotient (s K)) = fintype.card G) :=
begin
  rw ←fintype.card_prod,
  -- might want some other lemma here?
  apply fintype.card_of_bijective,
end

lemma every_element_is_in_a_coset : (∀ (g : G), ∃ (a : G), g ∈ right_coset K.carrier a) :=
begin
  intro g,
  use g,
  rw mem_right_coset_iff,
  rw mul_inv_self,
  exact K.one_mem,
end

lemma card_subgroup_eq_card_coset (hKfin : fintype K) (hCosetfin : ∀ (a : G), fintype (right_coset K.carrier a)) : 
(∀ (a : G), fintype.card K = fintype.card (right_coset K.carrier a)) :=
begin
  intro a,
  rw fintype.card_eq,
  split,
  exact (subgroup.right_coset_equiv_subgroup a).symm,
end

-- TO DO:
-- show H x (G/H) -> G an isomorphism
-- conclude using card A x B = card A * card B

-- NEED THE FOLLOWING:
-- 1. |A + B| = |A| + |B| for disjoint finite A, B
-- 2. G is the (disjoint) union of all right cosets
-- 3. every right coset is either distinct or identical
-- 4. it follows from (1) that |G| = sum of right coset orders
-- 5. we can put each right coset in a bijection with the subgroup,
--    so |K| = |Ki| for all i
-- 6. we conclude that |G| = n|K|, where n is the # of right cosets



