import tactic -- imports all the Lean tactics
import topology.continuous_function.compact -- continuous functions, compact sets
import topology.constructions
import topology.continuous_on
import data.set.lattice
import data.nat.basic
import topology.subset_properties
import data.set.basic
import topology.basic
import topology.sequences
import data.set.finite
import order.hom.basic
import data.finite.defs

variables (X: Type) [metric_space X]

def accu [metric_space X] (A: set X) := {x : X | ∀ ε > (0: ℝ), (((metric.ball x ε) ∩ A) \ {x}) ≠ ∅}

-- constant fn is convergent
lemma constant_fn {X: Type} [metric_space X] (u: ℕ → X) (h: ∀ (n : ℕ), u n ∈ (set.univ: set X))
  (h1: (∃ (x: X) (φ : ℕ → ℕ), strict_mono φ ∧ (∀ n: ℕ, (u ∘ φ) n = x))): 
  ∃ (x : X) (H : x ∈ (set.univ: set X)) (φ : ℕ → ℕ), strict_mono φ ∧ filter.tendsto (u ∘ φ) filter.at_top (nhds x) :=
begin
  cases h1 with x h1,
  use x,
  split,
  simp,
  cases h1 with fn h1,
  use fn,
  cases h1 with h1 h2,
  split,
  exact h1,
  rw filter.tendsto_def,
  intro s,
  intro hs,
  --unfold filter.at_top,
  have claim: u ∘ fn ⁻¹' s = (set.univ: set ℕ),
  ext y,
  split,
  intro hy,
  exact set.mem_univ y,
  intro hy,
  simp,
  have h3: x ∈ s,
  exact mem_of_mem_nhds hs,
  specialize h2 y,
  exact set.mem_of_eq_of_mem h2 h3,
  rw claim,
  exact filter.univ_mem,
end


lemma finite_of_sdiff_singleton_finite {α: Type} {S : set α} (a : α) :
(S \ {a}).finite → S.finite :=
begin
  intros h,
  have h1: set.finite {a} := set.finite_singleton a,
  have h2: set.finite ((S \ {a}) ∪ {a}),
  exact set.finite.union h h1,
  have h3: S ⊆ (S \ {a}) ∪ {a},
  exact set.subset_diff_union S {a},
  exact set.finite.subset h2 h3,
end


noncomputable def min {S : set ℕ} : ℕ := Inf S

def min_seq' (S : set ℕ) : ℕ → set ℕ
| 0 := S
| (n + 1) := (min_seq' n) \ {Inf (min_seq' n)}

noncomputable def min_seq (S : set ℕ) (n : ℕ) : ℕ := Inf (min_seq' S n)


instance (S : set ℕ) [infinite S] (n : ℕ) : infinite (min_seq' S n) :=
begin
  induction n,
  unfold min_seq',
  exact _inst_2,
  unfold min_seq',
  by_contra,
  have h2: (min_seq' S n_n).infinite,
  exact set.infinite_coe_iff.mp n_ih,
  have h3: ¬ (min_seq' S n_n).finite,
  apply h2,
  apply h3,
  rw set.infinite_coe_iff at h,
  simp at h,
  exact finite_of_sdiff_singleton_finite (Inf (min_seq' S n_n)) h,

end


def index_set [metric_space X] (f: ℕ → X) (x: X) : set ℕ := {i : ℕ | f i = x ∧ i >= 1}


-- If the set is not bdd_above, it has infinite many elements
lemma not_bdd_infi [metric_space X] (x: X) (u: ℕ → X): ¬ bdd_above (index_set X u x)
  → infinite (index_set X u x) :=
begin
  intro h1,
  -- rw not_bdd_above_iff at h,
  rw set.infinite_coe_iff,
  by_contra,
  simp at h,
  have h2: bdd_above (index_set X u x),
  exact set.finite.bdd_above h,
  exact h1 h2,
end



lemma min_seq_pos [metric_space X] (x: X) (u: ℕ → X) (n: ℕ) (h: infinite (index_set X u x)): 
  ∀ a ∈ (min_seq' (index_set X u x) n), a >= 1 :=
begin
  --unfold min_seq,
  have h1: infinite (min_seq' (index_set X u x) n),
  exact min_seq'.infinite (index_set X u x) n,
  have h2: ∀ a ∈ (min_seq' (index_set X u x) n), a >= 1,
  intro a,
  intro ha,
  unfold index_set at ha,
  induction n,
  unfold min_seq' at ha,
  simp at ha,
  cases ha with ha1 ha2,
  exact ha2,
  unfold min_seq' at ha,
  simp at ha,
  have h3: infinite ↥(min_seq' (index_set X u x) n_n),
  exact min_seq'.infinite (index_set X u x) n_n,
  specialize n_ih h3,
  cases ha with ha1 ha2,
  specialize n_ih ha1,
  exact n_ih,
  exact h2,

  
end


lemma min_seq_mono_nb [metric_space X] (x: X) (u: ℕ → X) (n: ℕ) (h: infinite (index_set X u x)): 
  (min_seq (index_set X u x) (n)) <= (min_seq (index_set X u x) (n + 1)) :=
begin
  unfold min_seq,

  have h2: ∀ a ∈ (min_seq' (index_set X u x) n), a >= 1,
  exact min_seq_pos X x u n h,
  have h3: ∀ a ∈ (min_seq' (index_set X u x) (n + 1)), a >= 1,
  exact min_seq_pos X x u (n + 1) h,

  have h4: (min_seq' (index_set X u x) n).nonempty,
  exact set.nonempty_of_nonempty_subtype,
  have h5: (min_seq' (index_set X u x) (n + 1)).nonempty,
  exact set.nonempty_of_nonempty_subtype,
  have inclu: (min_seq' (index_set X u x) (n + 1)) ⊆ (min_seq' (index_set X u x) n),
  unfold min_seq',
  simp,
  have h6: bdd_below (min_seq' (index_set X u x) n),
  exact order_bot.bdd_below (min_seq' (index_set X u x) n),
  have h7: bdd_below (min_seq' (index_set X u x) (n + 1)),
  exact bdd_below.mono inclu h6,
  exact cInf_le_cInf h6 h5 inclu,
end

lemma min_seq_mono_neq [metric_space X] (x: X) (u: ℕ → X) (n: ℕ) (h: infinite (index_set X u x)): 
  (min_seq (index_set X u x) (n)) ≠ (min_seq (index_set X u x) (n + 1)) :=
begin
  
  unfold min_seq,
  intro h1,
  have h2: (min_seq' (index_set X u x) n).nonempty,
  exact set.nonempty_of_nonempty_subtype,

  have h3: Inf (min_seq' (index_set X u x) n) ∈ (min_seq' (index_set X u x) n),
  exact Inf_mem h2,
  have h4: (min_seq' (index_set X u x) (n + 1)).nonempty,
  exact set.nonempty_of_nonempty_subtype,
  have h5: Inf (min_seq' (index_set X u x) (n + 1)) ∈ (min_seq' (index_set X u x) (n + 1)),
  exact Inf_mem h4,
  rw ← h1 at h5,
  have h6: Inf (min_seq' (index_set X u x) n) ∉ min_seq' (index_set X u x) (n + 1),
  unfold min_seq',
  simp,
  apply h6,
  exact h5,
  
end

-- strictly increasing
lemma min_seq_mono_str [metric_space X] (x: X) (u: ℕ → X) (n: ℕ) (h: infinite (index_set X u x)): 
  (min_seq (index_set X u x) (n)) < (min_seq (index_set X u x) (n + 1)) :=
begin
  have h1: (min_seq (index_set X u x) (n)) ≤ (min_seq (index_set X u x) (n + 1)),
  exact min_seq_mono_nb X x u n h,
  have h2: (min_seq (index_set X u x) (n)) < (min_seq (index_set X u x) (n + 1)) ∨ (min_seq (index_set X u x) (n)) = (min_seq (index_set X u x) (n + 1)),
  exact lt_or_eq_of_le h1,
  cases h2,
  exact h2,
  have h3: (min_seq (index_set X u x) (n)) ≠ (min_seq (index_set X u x) (n + 1)),
  exact min_seq_mono_neq X x u n h,
  exfalso,
  apply h3,
  exact h2,
end

lemma min_seq_mono [metric_space X] (x: X) (u: ℕ → X) (h: infinite (index_set X u x)): strict_mono (min_seq (index_set X u x)) :=
begin
  have h1: ∀ n: ℕ, (min_seq (index_set X u x) (n)) < (min_seq (index_set X u x) (n + 1)),
  intro n,
  exact min_seq_mono_str X x u n h,
  exact strict_mono_nat_of_lt_succ h1,
end

lemma equal_x [metric_space X] (x: X) (u: ℕ → X) (h: infinite (index_set X u x)): ∀ (n : ℕ), (u ∘ min_seq (index_set X u x)) n = x :=
begin
  intro n,

  simp,
  unfold min_seq,
  have h1: (min_seq' (index_set X u x) n).nonempty,
  exact set.nonempty_of_nonempty_subtype,

  unfold index_set,

  simp,
  have h3: min_seq' (index_set X u x) n ⊆ (index_set X u x),
  induction n,
  unfold min_seq',
  have h4: (min_seq' (index_set X u x) n_n).nonempty,
  exact set.nonempty_of_nonempty_subtype,
  specialize n_ih h4,
  unfold min_seq',
  have h5: min_seq' (index_set X u x) n_n \ {Inf (min_seq' (index_set X u x) n_n)} ⊆ min_seq' (index_set X u x) n_n,
  exact (min_seq' (index_set X u x) n_n).diff_subset {Inf (min_seq' (index_set X u x) n_n)},
  exact set.subset.trans h5 n_ih,

  have h2: Inf (min_seq' (index_set X u x) n) ∈ (min_seq' (index_set X u x) n),
  exact Inf_mem h1,

  have h4: (Inf (min_seq' (index_set X u x) n)) ∈ (index_set X u x),
  exact h3 h2,
  unfold index_set at h4,
  simp at h4,
  cases h4 with h4 h5,
  exact h4,
end

-- If no constant subsequence, index set finite.
lemma nocons_finite_index_set {X: Type} [metric_space X] (u: ℕ → X) (x: X)
  (h1: ¬ (∃ (φ : ℕ → ℕ), strict_mono φ ∧ (∀ n: ℕ, (u ∘ φ) n = x))):
  (index_set X u x).finite :=
begin
  by_contra,
  rw ← set.not_infinite at h,
  rw not_not at h,
  have h2: infinite (index_set X u x),
  exact set.infinite_coe_iff.mpr h,
  apply h1,
  use min_seq (index_set X u x),
  split,
  exact min_seq_mono X x u h2,
  exact equal_x X x u h2,

end

-- all the index set form ℕ
lemma form_N [metric_space X] (u: ℕ → X): (set.univ: set ℕ) = (⋃ (x: X) (H: x ∈ u '' (set.univ: set ℕ)), index_set X u x) ∪ {0} :=
begin
  ext a,
  split,
  {
    cases a,
    intro ha,
    simp,
    intro ha,
    have h1: a.succ ∈ index_set X u (u a.succ),
    unfold index_set,
    simp,
    have h2: a.succ = a + 1,
    exact rfl,
    rw h2,
    exact le_add_self,
    simp,
    use a.succ,
    exact h1,
  },
  {
    intro ha,
    cases ha with ha ha0,
    rw set.mem_Union at ha,
    cases ha with i ha,
    unfold index_set at ha,
    simp at ha0,
  },
end

-- no constant subseq → infinite
lemma noncons_infinite {X: Type} [metric_space X] (u: ℕ → X) 
  (h1: ¬(∃ (x: X) (φ : ℕ → ℕ), strict_mono φ ∧ (∀ n: ℕ, (u ∘ φ) n = x))):  
  (u '' (set.univ: set ℕ)).infinite :=
begin
  by_contra,
  rw set.not_infinite at h,

  have h2: (set.univ: set ℕ) = (⋃ (x: X) (H: x ∈ u '' (set.univ: set ℕ)), index_set X u x) ∪ {0},
  exact form_N X u,
  have h3: ∀ x: X, (index_set X u x).finite,
  intro x,
  have h4: ¬ ∃ (φ : ℕ → ℕ), strict_mono φ ∧ ∀ (n : ℕ), (u ∘ φ) n = x,
  {intro h5,
  apply h1,
  use x,
  exact h5,},
  exact nocons_finite_index_set u x h4,

  have h4: (⋃ (i : X) (H: i ∈ u '' (set.univ: set ℕ)), index_set X u i).finite,
  {
    have h5: ∀ (i : X), i ∈ (u '' (set.univ: set ℕ)) → (index_set X u i).finite,
    intro i,
    intro hi,
    exact h3 i,

    exact set.finite.bUnion h h5,

  },
  simp at h4,
  simp at h2,
  have h5: (insert 0 (⋃ (y : ℕ), index_set X u (u y))).finite,
  exact set.finite.insert 0 h4,
  rw ← h2 at h5,
  have h6: (set.univ: set ℕ ).infinite,
  exact set.infinite_univ,
  apply h6,
  exact h5,


end

-- def min_seq' (S : set ℕ) : ℕ → set ℕ
-- | 0 := S
-- | (n + 1) := (min_seq' n) \ {Inf (min_seq' n)}

def index_with_small_r [metric_space X] (r: ℝ) (h: r > 0)(u: ℕ → X) (x: X) := {n : ℕ | dist x (u n) < r ∧ n > 0 ∧ (u n) ≠ x}

noncomputable
def min_index_with_small_r [metric_space X] (r: ℝ) (h: r > 0) (u: ℕ → X) (x: X) := Inf (index_with_small_r X r h u x)

lemma nonempty_min_index [metric_space X] (r: ℝ) (u: ℕ → X) (x: X) (h: x ∈ accu X (u '' set.univ)) (h1: r > 0):
  (min_index_with_small_r X r h1 u x) ≠ 0 :=
begin
  unfold min_index_with_small_r,
  unfold index_with_small_r,
  simp,
  unfold accu at h,
  simp at h,
  specialize h r,
  specialize h h1,
  intro h2,
  apply h,
  ext y,
  split, 
  {
    intro hy,
    cases hy with hy1 hy2,
    cases hy1 with hy1 hy3,
    simp at hy3,
    cases hy3 with n hy3,
    have h3: n ∈ {n : ℕ | dist x (u n) < r ∧ 0 < n ∧ ¬u n = x},
    {
      simp,
      split,
      unfold metric.ball at hy1,
      simp at hy1,
      rw hy3,
      rw dist_comm,
      exact hy1,
      split,
      sorry,
    },
  },
  sorry,
end

-- def seq (u: ℕ → X) (x: X) : ℕ → (ℝ × ℕ)
-- | 0 := (dist x (u 0), 0)
-- | (n + 1) := (Inf ({1 / n} ⋃ (⋃ (i ∈ [0, (seq u x n).snd]), dist x (u n))))

-- Thm: Every infinite subset of X has a cluster point → X sequential compact
example {X: Type} [metric_space X] (h: ∀ A: set X, A.infinite → (accu X A).nonempty): is_seq_compact (set.univ: set X) :=
begin
  unfold is_seq_compact,
  intro u,
  intro set_in_x,
  have case: (∃ (x: X) (φ : ℕ → ℕ), strict_mono φ ∧ (∀ n: ℕ, (u ∘ φ) n = x)) ∨ ¬(∃ (x: X) (φ : ℕ → ℕ), strict_mono φ ∧ (∀ n: ℕ, (u ∘ φ) n = x)),
  exact em (∃ (x : X) (φ : ℕ → ℕ), strict_mono φ ∧ ∀ (n : ℕ), (u ∘ φ) n = x),
  cases case with case1 case2,
  exact constant_fn u set_in_x case1,
  have infin: (u '' set.univ).infinite,
  exact noncons_infinite u case2,
  specialize h (u '' set.univ),
  specialize h infin,
  rw set.nonempty_def at h,
  cases h with x h,
  use x,
  split,
  {exact set.mem_univ x},
  sorry,

end
