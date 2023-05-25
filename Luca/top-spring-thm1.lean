import tactic -- imports all the Lean tactics
import topology.continuous_function.compact -- continuous functions, compact sets
import topology.constructions
import topology.continuous_on
import topology.category.Top.epi_mono
import topology.path_connected
import data.set.lattice
import data.nat.basic
import topology.subset_properties
import topology.bases
import data.set.basic
import topology.constructions
import topology.separation
import topology.basic
import topology.sequences

variables (X: Type) [topological_space X]

lemma inter_union {X: Type} (A B C: set X) : A ∩ (B ∪ C) = (A ∩ B) ∪ (A ∩ C) :=
begin
  ext,
  split,
  {
    intro h,
    cases h,
    cases h_right,
    left,
    split,
    exact h_left,
    exact h_right,
    right,
    split,
    exact h_left,
    exact h_right,
  },
  {
    intro h,
    split,
    cases h,
    cases h,
    exact h_left,
    cases h,
    exact h_left,
    cases h,
    left,
    cases h,
    exact h_right,
    right,
    cases h,
    exact h_right,
  },
end

def g {l: Type} {X: Type} [topological_space X] (f: l → set X) (S: set X): l × bool → set X :=
  λ a, if a.snd = tt then f a.fst else S

def pi1 {a b: Type} : (a × b) → a := λ x, x.fst


lemma proj_finite {a b: Type} (s: finset (a × b)): (pi1 '' (finset.coe_emb s)).finite:=
begin
  have h: (finset.coe_emb s).finite,
  simp,
  --exact finset.finite_to_set s,
  have h1: (pi1 '' (finset.coe_emb s)).finite,
  exact set.finite.image pi1 h,
  exact h1,
end


lemma image_g_open {l: Type} {X: Type} [topological_space X] (f: l → set X) (S: set X) (h: is_open S)
  (h1: ∀ a: l, is_open (f a)) : ∀ x: l × bool, is_open (g f S x):=
begin
  intro x,
  unfold g,
  cases x.snd,
  simp,
  exact h,
  simp,
  specialize h1 x.fst,
  exact h1,
end

lemma set_split {l X : Type} [topological_space X] (S: set (l × bool)) (Y: set X) (f: l → set X) :
 (⋃ (i : l × bool)(H: i ∈ S), g f Yᶜ i) ⊆ (⋃ (i : l × bool)(H: i ∈ S), g f Yᶜ (i.fst, tt)) ∪ (⋃ (i : l × bool)(H: i ∈ S), g f Yᶜ (i.fst, ff)) :=
begin
  rw set.subset_def,
  intro x,
  simp,
  intro i,
  intro h,
  cases h,
  right,
  use i,
  left,
  exact h,
  left,
  use i,
  right,
  exact h,
  

end

lemma subset_eq {l X: Type} [topological_space X] (finS: set (l × bool)) (Y: set X) (f: l → set X) 
  (h: Y ∪ Yᶜ ⊆ ⋃ (i : l × bool) (H : i ∈ finS), g f Yᶜ i) (nonemp: ¬ is_empty l) : Y ⊆ ⋃ (i : l × bool) (H : i ∈ finS), g f Yᶜ (i.fst, tt):=
begin
  have h1: (⋃ (i : l × bool) (H : i ∈ finS), g f Yᶜ i) ⊆ (⋃ (i : l × bool) (H : i ∈ finS), g f Yᶜ (i.fst, tt)) ∪ (⋃ (i : l × bool) (H : i ∈ finS), g f Yᶜ (i.fst, ff)),
  exact set_split finS Y f,
  have h2: Y ∪ Yᶜ ⊆ (⋃ (i : l × bool) (H : i ∈ finS), g f Yᶜ (i.fst, tt)) ∪ (⋃ (i : l × bool) (H : i ∈ finS), g f Yᶜ (i.fst, ff)),
  exact set.subset.trans h h1,
  have h3: Y ∩ (Y ∪ Yᶜ) ⊆ Y ∩ ((⋃ (i : l × bool) (H : i ∈ finS), g f Yᶜ (i.fst, tt)) ∪ (⋃ (i : l × bool) (H : i ∈ finS), g f Yᶜ (i.fst, ff))),
  exact set.inter_subset_inter_right Y h2,


  unfold g at h3,
  simp at h3,
  have h4: (⋃ (i : l × bool) (x : i ∈ finS), Yᶜ) ⊆ Yᶜ,
  {
    simp,
    rw set.subset_def,
    intro i,
    intro b,
    intro ib,
    intro x,
    simp,
  },
  cases h3 with h3 h5,
  have h6: (⋃ (i : l × bool) (x : i ∈ finS), f i.fst) ∪ (⋃ (i : l × bool) (x : i ∈ finS), Yᶜ) ⊆ (⋃ (i : l × bool) (x : i ∈ finS), f i.fst) ∪ Yᶜ,
  exact (⋃ (i : l × bool) (x : i ∈ finS), f i.fst).union_subset_union_right h4,
  have h7: Y ⊆ (⋃ (i : l × bool) (x : i ∈ finS), f i.fst) ∪ Yᶜ,
  exact set.subset.trans h5 h6,
  have h8: Y ∩ Y ⊆ Y ∩ ((⋃ (i : l × bool) (x : i ∈ finS), f i.fst) ∪ Yᶜ),
  exact set.inter_subset_inter h3 h7,
  rw inter_union Y (⋃ (i : l × bool) (x : i ∈ finS), f i.fst) Yᶜ at h8,
  simp at h8,
  cases h8 with h8 h9,
  unfold g,
  simp,
  exact h9,

end

theorem close_subspace_compact (Y : set X): 
  is_compact (set.univ : set X) ∧ is_closed Y → is_compact Y :=
begin
  intro h,
  cases h with h1 h2,
  rw is_compact_iff_finite_subcover at ⊢ h1,
  intro l,
  intro f,
  specialize h1 (g f Yᶜ),
  rw ← is_open_compl_iff at h2,
  intro h3,
  specialize h1 (image_g_open f Yᶜ h2 h3),
  intro claim_y,
  have incl: (⋃ (i : l), f i) ⊆ (⋃ (i : l × bool), g f Yᶜ i),
  {
    simp,
    intro i,
    have h4: f i = g f Yᶜ (i, tt),
    {
      unfold g,
      simp,
    },
    have h5: (g f Yᶜ (i, tt)) ⊆ set.Union (g f Yᶜ),
    {exact set.subset_Union (g f Yᶜ) (i, tt)},
    rw h4,
    exact h5,
  },
  have h5: set.univ = Y ∪ Yᶜ,
  {simp},
  have case_l: is_empty l ∨ (¬ is_empty l),
  {exact em (is_empty l)},
  cases case_l,
  {
    have emp: (⋃ (i : l), f i) = ∅,
    {
      simp,
      intro i,
      rw is_empty_iff at case_l,
      exact congr_fun (false.rec (f = λ (i : l), ∅) (case_l i)) i,
    },
    rw emp at claim_y,
    rw set.subset_empty_iff at claim_y,
    rw claim_y,
    simp,
  },
  have h4: set.univ ⊆ ⋃ (i : l × bool), g f Yᶜ i,
  {
    rw h5,
    have h6: Yᶜ ⊆ (⋃ (i : l × bool), g f Yᶜ i),
    {
      simp,
      let i: l,
      {
        simp at case_l,
        exact nonempty.some case_l,
      },
      have y_compl: Yᶜ = g f Yᶜ (i, ff),
      {
        unfold g,
        simp,
      },
      have h6: g f Yᶜ (i, ff) ⊆ set.Union (g f Yᶜ),
      {exact set.subset_Union (g f Yᶜ) (i, ff)},
      rw ← y_compl at h6,
      exact h6,
      
    },
    have h7: Y ⊆ ⋃ (i : l × bool), g f Yᶜ i,
    {exact set.subset.trans claim_y incl},
    exact set.union_subset h7 h6,
  },
  specialize h1 h4,
  cases h1 with finS h1,
  rw h5 at h1,
  have h6: (pi1 '' (finset.coe_emb finS)).finite,
  {exact proj_finite finS},
  let k:= h6.to_finset,
  use k,
  have h7: ∀ (i: l),(i ∈ k) → (∃ j: (l × bool), j ∈ finS ∧ pi1 j = i),
  {
    intro i,
    intro ik,
    have h8: i ∈ pi1 '' finset.coe_emb finS,
    exact (set.finite.mem_to_finset h6).mp ik,
    simp at h8,
    simp,
    exact h8,
  },
  have h8: Y ⊆ ⋃ (i : l × bool) (H : i ∈ finS), g f Yᶜ (i.fst, tt),
  {exact subset_eq finS Y f h1 case_l},
  unfold g at h8,
  simp at h8,
  have h9: (⋃ (i : l × bool) (x : i ∈ finS), f i.fst) ⊆ (⋃ (i : l) (H : i ∈ k), f i),
  {
    rw set.subset_def,
    intro x,
    intro hx,
    simp at hx ⊢,
    cases hx with i l,
    use i,
    split,
    {
      use i,
      cases l with l1 l2, 
      left,
      split,
      cases l1 with l1 l3,
      exact l1,
      unfold pi1,
      right,
      split,
      cases l2 with l2 l3,
      exact l2,
      unfold pi1,
      
    },
    {
      cases l,
      cases l_1 with l1 l2,
      exact l2,
      cases l_1 with l1 l2,
      exact l2,
    },
  },
  exact set.subset.trans h8 h9,
end