import group_theory.subgroup.basic
import group_theory.sylow
import deprecated.subgroup
import group_theory.group_action.defs

variables {G : Type} {p : ℕ} [group G]

lemma subgroup_trans : ∀ (a b c : subgroup G), a ≤ b → b ≤ c → a ≤ c :=
begin
  intros a b c hab hbc,
  intros x hx,
  apply hbc,
  apply hab,
  exact hx,
end

lemma normal_in_group_implies_normal_in_subgroup (N : subgroup G) (H : subgroup G) (hN : N.normal) (hN' : N ≤ H) : (N.subgroup_of H).normal :=
begin
  split,
  { intros n hn x,
    have h1 := hN.conj_mem n hn x,
    exact h1,
  },
end

lemma normal_iff : ∀ (N : subgroup G), N.normal ↔ ∀ (n : G), n ∈ N → ∀ (x : G), x * n * x⁻¹ ∈ N :=
begin
  intros N,
  split,
  { intros hN n hn x,
    have h2 : x * n * x⁻¹ ∈ N := hN.conj_mem n hn x,
    exact h2, },
  { intros hN,
    split,
    { intros n hn x,
      specialize hN n hn x,
      exact hN,},
  },
end

lemma silly_lemma (p : ℕ) (K P : sylow p G) : ∀ (g : G), ∀ (h : G), ∃ (k : G), k * g = h :=
begin
  -- use that mul_action is pretransitive on sylow subgroups
  intros p k,
  have h := mul_action.exists_smul_eq G p k,
  cases h with g hg,
  use g,
  dsimp at *,
  exact hg,
end

lemma conj_of_subgroup_of_normal_is_in_normal (N : subgroup G) (P : subgroup G) (hN : N.normal) (hP : P ≤ N) (x : G) : ∀ (p : P), x * ↑p * x⁻¹ ∈ N :=
begin
  intros p,
  have h1 : ↑p ∈ N := hP p.property,
  have h2 : x * ↑p * x⁻¹ ∈ N := hN.conj_mem ↑p h1 x,
  exact h2,
end

variables g h : G

lemma sylow_subgroups_are_conj (p : ℕ) (hp : p.prime) (K P : sylow p G) [finite (sylow p G)] : ∃ (g : G), ∀ (p : P), g • P = K :=
begin
  -- use that mul_action is pretransitive on sylow subgroups
  have h := @sylow.mul_action.is_pretransitive p G (by apply_instance) ⟨hp⟩ (by apply_instance),
  have h' := @mul_action.exists_smul_eq G (sylow p G) _ h P K,
  cases h' with g hg,
  use g,
  intro P,
  exact hg,
end



lemma sylows_in_subgroup_implies_conj_by_elt_in_subgroup (p : ℕ) (hp : p.prime) (K P : sylow p G) 
(H : subgroup G) (hK : K.to_subgroup ≤ H) (hP : P.to_subgroup ≤ H) : ∃ (h : H), ∀ (p : P.to_subgroup), ↑h * ↑p * ↑h⁻¹ ∈ K :=
begin
  have hP' := P.subtype hP,
  have hK' := K.subtype hK,
  have hc := sylow_subgroups_are_conj _ _ _ _ ,
  {
   
  },
  sorry,
  


end

-- Lemma
-- K is a sylow p-subgroup of G, N is normal in G.
-- K is normal in N → K is normal in G.

theorem sylow_normal_in_normal_implies_normal (p : ℕ) (K : sylow p G) (N : subgroup G) 
(hN : N.normal) (hK : (K.to_subgroup).subgroup_of N) (hK' : ((K.to_subgroup).subgroup_of N).normal) : K.to_subgroup.normal :=
begin
  rw normal_iff,
  intros n hn x,
  -- show that g⁻¹ * k * g ∈ N ∀ g ∈ G, k ∈ K
  

  sorry,
  
end


