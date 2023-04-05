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

lemma conj_of_subgroup_of_normal_is_in_normal (N : subgroup G) (P : subgroup G) (hN : N.normal) (hP : P ≤ N) (x : G) : ∀ (p : P), x * ↑p * x⁻¹ ∈ N :=
begin
  intros p,
  have h1 : ↑p ∈ N := hP p.property,
  have h2 : x * ↑p * x⁻¹ ∈ N := hN.conj_mem ↑p h1 x,
  exact h2,
end

lemma sylow_subgroups_are_conj (p : ℕ) (K P : sylow p G) : ∃ (h : G), ∀ (p : P), h * ↑p * h⁻¹ ∈ K :=
begin
  -- use that mul_action is pretransitive on sylow subgroups
  have h : ∀ (x y : (sylow p G)), ∃ (g : G), g • x = y,
  intros x y,
  { 
    -- use exists_smul_eq
    have h1 : ∃ (g : G), g • x = y := by sorry,--mul_action.exists_smul_eq G x y,
    cases h1 with g hg,
    exact ⟨g, hg⟩,
  },
  specialize h P K,
  cases h with g hg,
  use g,
  intro p,
  sorry,
end

lemma sylows_in_subgroup_implies_conj_by_elt_in_subgroup (p : ℕ) (K P : sylow p G) 
(H : subgroup G) (hK : K.to_subgroup ≤ H) (hP : P.to_subgroup ≤ H) : ∃ (h : H), ∀ (p : P.to_subgroup), ↑h * ↑p * ↑h⁻¹ ∈ K :=
begin
  have hP' := P.subtype hP,
  have hK' := K.subtype hK,
  have hc := sylow_subgroups_are_conj p hK' hP',
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


