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

-- Winter 2022

variables (X Y : Type) [topological_space X] [topological_space Y]

-- let S be a subset of X
variable (S : set X)

-- Let `f : X → Y` be a function
variables (f : X → Y) 


lemma singleton_fun {X: Type} {Y: Type} (f: X → Y) (x: X):
  f '' {x} = {f x}:=
begin
  ext y,
  split,
  intro hy,
  simp,
  rw set.mem_image_iff_bex at hy,
  cases hy with x1 hy,
  cases hy with h hy,
  simp at h,
  exact (eq.symm hy).trans (congr_arg f h),
  intro hy,
  simp at hy,
  rw set.mem_image_iff_bex,
  use x,
  split,
  simp,
  rw hy,
end


-- Thm: Let f: X → Y be a quotient map, if each set f⁻¹({y}) is connected and if Y is connected, then X is connected.
example (h1: quotient_map f) (h2: is_connected (set.univ: set Y)) (h3: ∀ y : Y, is_connected (f⁻¹' {y})):
  is_connected (set.univ: set X) :=
begin
  unfold is_connected at h2 ⊢ h3,
  split,
  {
    cases h2 with h2_nonempty h2,
    have y: Y,
    exact set.nonempty.some h2_nonempty,
    specialize h3 y,
    cases h3 with h3_nonempty h3,
    have h4: f⁻¹' {y} ⊆ (set.univ: set X),
    exact (f ⁻¹' {y}).subset_univ,
    exact set.nonempty.mono h4 h3_nonempty,
    
  },
  {
    unfold is_preconnected,
    intro u,
    intro v,
    intro openu,
    intro openv,
    intro hypo,
    intro nonemptyu,
    intro nonemptyv,
    by_contra,
    rw set.not_nonempty_iff_eq_empty at h,
    simp at nonemptyu nonemptyv h,
    cases h2 with nonemptyy h2,
    have splitX: u ∪ v = (set.univ: set X),
    exact set.univ_subset_iff.mp hypo,
    have preim_subset: ∀ y: Y, f⁻¹'{y} ⊆ u ∪ v,
    intro y,
    rw splitX,
    exact (f ⁻¹' {y}).subset_univ,
    have disj: disjoint u v,
    exact set.disjoint_iff_inter_eq_empty.mpr h,
    have h4: ∀ y: Y, f⁻¹' {y} ⊆ u ∨ f⁻¹' {y} ⊆ v,
    intro y,
    specialize preim_subset y,
    specialize h3 y,
    cases h3 with h3nonempty h3,
    exact is_preconnected.subset_or_subset openu openv disj preim_subset h3,

    -- build Yu an Yv
    let Yu := {y : Y | f⁻¹' {y} ⊆ u},
    let Yv := {y : Y | f⁻¹' {y} ⊆ v},
    have h5: (set.univ: set Y) ⊆ Yu ∪ Yv,
    intro y,
    intro y_elem,
    specialize h4 y,
    cases h4 with h4u h4v,
    left,
    simp,
    exact h4u,
    right,
    simp,
    exact h4v,
    have yuy: Yu ⊆ (set.univ: set Y),
    exact set.subset_univ Yu,
    have yvy: Yv ⊆ (set.univ: set Y),
    exact set.subset_univ Yv,
    have yuyvy: Yu ∪ Yv ⊆ (set.univ: set Y),
    exact (Yu ∪ Yv).subset_univ,
    have splitY: Yu ∪ Yv = (set.univ: set Y),
    ext,
    split,
    intro x1,
    triv,
    intro x1,
    exact h5 x1,
    have disjointyuyv: Yu ∩ Yv = ∅,
    ext,
    split,
    intro xy,
    simp at xy,
    cases xy with xyu xyv,
    have xyuv: f ⁻¹' {x} ⊆ u ∩ v,
    exact set.subset_inter xyu xyv,
    rw h at xyuv,
    have surf: function.surjective f,
    exact quotient_map.surjective h1,
    unfold function.surjective at surf,
    specialize surf x,
    cases surf with a surf,
    rw set.subset_empty_iff at xyuv,
    have fa: a ∈ f ⁻¹' {x},
    exact surf,
  
    rw xyuv at fa,
    exact fa,
    intro h6,
    exfalso,
    exact h6,

    

    -- f⁻¹ yu = u
    have hypo_yu: f ⁻¹' Yu = u,
    ext,

    have hx: {x} ⊆ f ⁻¹' (f '' {x}),
    exact set.subset_preimage_image f {x},
    have eqset: f '' {x} = {f x},
    exact singleton_fun f x,


    split,

    intro xyu,
    simp at xyu,
    
    
    
    rw eqset at hx,
    rw ← set.singleton_subset_iff,
    exact set.subset.trans hx xyu,
    intro xu,
    have hxu: f x ∈ Yu ∪ Yv,
    rw splitY,
    simp,
    have hyv: f x ∈ Yu,
    cases hxu,
    exact hxu,
    simp at hxu,
    rw ← eqset at hxu,
    have hx2: {x} ⊆ v,
    exact set.subset.trans hx hxu,
    simp at hx2,
    have huv: x ∈ u ∩ v,
    exact set.mem_inter xu hx2,
    rw h at huv,
    exfalso,
    exact huv,

    rw eqset at hx,
    rw set.singleton_subset_iff at hx,
    rw ← set.singleton_subset_iff at hyv,
    have fyu: f ⁻¹' {f x} ⊆ f ⁻¹' Yu,
    rw set.subset_def,
    intro x1,
    intro hx1,
    have hx1_1: f x1 ∈ {f x},
    exact set.mem_preimage.mp hx1,
    simp at hx1_1,
    rw ← hx1_1 at hyv,
    rw set.singleton_subset_iff at hyv,
    
    have hx1_2: f x1 ∈ f '' (f ⁻¹' Yu),
    have surf: function.surjective f,
    exact quotient_map.surjective h1,
    rw set.image_preimage_eq,
    exact hyv,
    exact surf,
    have hypox: f '' {x1} = {f x1},
    exact singleton_fun f x1,
    rw set.mem_preimage,
    exact hyv,
    exact fyu hx,

    -- f ⁻¹' Yv = v
    have hypo_yv: f ⁻¹' Yv = v,
    ext,

    have eqset: f '' {x} = {f x},
    exact singleton_fun f x,
    have hx1: {x} ⊆ f ⁻¹' (f '' {x}),
    exact set.subset_preimage_image f {x},
    rw set.singleton_subset_iff at hx1,
    split,
    intro xyv,
    have hx: x ∈ u ∪ v,
    rw splitX,
    simp,
    cases hx,
    rw ← hypo_yu at hx,
    simp at xyv hx,
    have xuv: f ⁻¹' {f x} ⊆ u ∩ v,
    exact set.subset_inter hx xyv,
    rw h at xuv,
    exfalso,
    rw ← eqset at xuv,
    
    have hx2: x ∈ ∅,
    exact xuv hx1,
    exact hx2,
    exact hx,

    intro xv,
    rw set.mem_preimage,
    have hfx: (f x) ∈ Yu ∪ Yv,
    rw splitY,
    simp,
    cases hfx,
    simp at hfx,
    rw ← eqset at hfx,
    have hx: x ∈ u,
    exact hfx hx1,
    have xuv: x ∈ u ∩ v,
    exact set.mem_inter (hfx hx1) xv,
    rw h at xuv,
    exfalso,
    exact xuv,
    exact hfx,

    -- Yu Yv open
    rw quotient_map_iff at h1,
    cases h1 with h1 hopen,
    have hopen2: ∀ (s : set Y), is_open s ↔ is_open (f ⁻¹' s),
    exact hopen,
    specialize hopen Yu,
    rw hypo_yu at hopen,
    rw ← hopen at openu,
    specialize hopen2 Yv,
    rw hypo_yv at hopen2,
    rw ← hopen2 at openv,

    -- nonempty yu yv
    have noneyu: Yu.nonempty,
    by_contra yuem,
    rw set.not_nonempty_iff_eq_empty at yuem,
    rw yuem at splitY,
    simp at splitY,
    rw yuem at hypo_yu,
    simp at hypo_yu,
    have h6: ¬u ⊆ ∅,
    exact set.nonempty.not_subset_empty nonemptyu,
    apply h6,
    exact (eq.symm hypo_yu).subset,

    have noneyv: Yv.nonempty,
    by_contra yvem,
    rw set.not_nonempty_iff_eq_empty at yvem,
    rw yvem at splitY,
    simp at splitY,
    rw yvem at hypo_yv,
    simp at hypo_yv,
    have h6: ¬v ⊆ ∅,
    exact set.nonempty.not_subset_empty nonemptyv,
    apply h6,
    exact (eq.symm hypo_yv).subset,

    unfold is_preconnected at h2,
    specialize h2 Yu Yv,
    specialize h2 openu,
    specialize h2 openv,
    specialize h2 h5,
    simp at h2,
    specialize h2 noneyu,
    specialize h2 noneyv,
    have h6: ¬ (Yu ∩ Yv ⊆ ∅),
    exact set.nonempty.not_subset_empty h2,
    apply h6,
    exact eq.subset disjointyuyv,
  },
end


-- If S is open set and intersects closure of U, S intersects U.
lemma closure_inter {X: Type} [topological_space X] (U: set X) (S: set X) (h1: (closure U ∩ S).nonempty) (h2: is_open S): 
(U ∩ S).nonempty :=
begin
  rw set.nonempty_def at h1,
  cases h1 with x h1,
  cases h1 with hu hs,
  rw mem_closure_iff at hu,
  specialize hu S,
  specialize hu h2,
  specialize hu hs,
  rw set.nonempty_def at hu ⊢,
  cases hu with y hu,
  use y,
  cases hu with hu1 hu2,
  split,
  exact hu2,
  exact hu1,
end


-- Thm: If a set is connected, then its closure is connected
example (A: set X) (h1: is_connected A) : (is_connected (closure A)) :=
begin
  have sub: A ⊆ closure A,
  exact subset_closure,
  unfold is_connected at h1 ⊢,
  cases h1 with h1 h2,
  split,
  {
    exact set.nonempty.mono sub h1,
  },
  {
    unfold is_preconnected at h2 ⊢,
    intro u,
    intro v,
    intro openu,
    intro openv,
    intro contain,
    intro nonem_u,
    intro nonem_v,
    specialize h2 u,
    specialize h2 v,
    specialize h2 openu,
    specialize h2 openv,
    have h3: A ⊆ u ∪ v,
    exact has_subset.subset.trans sub contain,
    specialize h2 h3,
    have nonem_Au: (A ∩ u).nonempty,
    exact closure_inter A u nonem_u openu,
    have nonem_Av: (A ∩ v).nonempty,
    exact closure_inter A v nonem_v openv,
    specialize h2 nonem_Au,
    specialize h2 nonem_Av,
    rw set.nonempty_def at h2 ⊢,
    cases h2 with x h2,
    use x,
    cases h2 with h21 h22,
    split,
    apply sub,
    exact h21,
    exact h22,

  },
end

-- big theorem

def accu [metric_space X] (A: set X) := {x : X | ∀ ε > (0: ℝ), (((metric.ball x ε) ∩ A) \ {x}) ≠ ∅}

def accu_compl [metric_space X] (A: set X) := {x: X | ∃ ε > (0: ℝ), ((metric.ball x ε) ∩ A) ⊆ {x}}

def small_rad [metric_space X] (A: set X) (x: X) := {ε : ℝ | (ε >= 0) ∧ ((metric.ball x ε) ∩ A) ⊆ {x} ∧ (ε < 1)}

noncomputable theory
def one_rad [metric_space X] (A: set X): X → ℝ := λ x, (has_Sup.Sup (small_rad X A x)) / 2

def x_ball_rad [metric_space X] (A: set X): X → set X := λ x, metric.ball x (one_rad X A x)

lemma zero_in_rad {X: Type} [metric_space X] (A: set X) (x: X): (0: ℝ) ∈ (small_rad X A x) :=
begin
  unfold small_rad,
  simp,
  intro y,
  intro dist,
  intro h2,
  have h3: has_dist.dist y x ≥ 0,
  exact dist_nonneg,
  have h4: ¬has_dist.dist y x < 0,
  exact not_lt.mpr h3,
  exfalso,
  apply h4,
  exact dist,
end

-- small_rad X A x nonempty and bdd above
lemma has_sup_rad {X: Type} [metric_space X] (A: set X) (x: X):  (small_rad X A x).nonempty ∧ bdd_above (small_rad X A x):=
begin
  have h: (small_rad X A x).nonempty,
  have h1: (0: ℝ) ∈ (small_rad X A x),
  exact zero_in_rad A x,
  exact set.nonempty_of_mem h1,

  have h1: bdd_above (small_rad X A x),
  unfold bdd_above,
  have h2: (1: ℝ) ∈ upper_bounds (small_rad X A x),
  unfold small_rad,
  unfold upper_bounds,
  simp,
  intro a,
  intro ha,
  intro h3,
  intro h4,
  exact le_of_lt h4,
  exact set.nonempty_of_mem h2,
  
  exact ⟨h, h1⟩,

  
end



-- if b in small_rad X A x and 0 ≤ a < b, then a also in.
lemma set_contain_less_dist {X: Type} [metric_space X] (A: set X) (x: X) (a: ℝ) (b: ℝ) : 
  (a ≥ 0 ∧ b ∈ small_rad X A x ∧ a < b) → a ∈ small_rad X A x :=
begin
  intro h,
  cases h with h1 h2,
  cases h2 with h2 h3,
  unfold small_rad at h2,
  simp at h2,
  cases h2 with h21 h22,
  cases h22 with h22 h23,
  unfold small_rad,
  simp,
  split,
  exact h1,
  split,
  intro y,
  
  specialize h22 y,
  intro h4,
  have h5: dist y x < b,
  linarith,
  specialize h22 h5,
  exact h22,
  linarith,

end

lemma larger_than_or_equal_split (a: ℝ) (b: ℝ): a ≥ b ↔ (a > b) ∨ (a = b) :=
begin

  have h3: a = b ↔ b = a,
  exact eq_comm,
  have h2: a > b ↔ b < a,
  exact iff.rfl,
  split,
  intro h,
  have h1: b ≤ a,
  exact h,
  
  rw h2,
  rw h3,
  exact lt_or_eq_of_le h,
  
  rw h2,
  rw h3,
  intro h,
  have claim: b ≤ a,
  exact le_of_lt_or_eq h,
  exact claim,
end

-- Sup (small_rad X A x) >= 0
lemma sup_small_rad_nonneg {X: Type} [metric_space X] (A: set X) (x: X): Sup (small_rad X A x) ≥ 0 :=
begin
  have h5: ∀ (a : ℝ), a ∈ (small_rad X A x) → 0 ≤ a,
  intro a,
  intro ha,
  unfold small_rad at ha,
  simp at ha,
  cases ha with ha ha1,
  exact ha,
  exact real.Sup_nonneg (small_rad X A x) h5,
end

-- one_rad X A x ≥ 0
lemma one_rad_nonneg {X: Type} [metric_space X] (A: set X) (x: X): one_rad X A x ≥ 0 :=
begin
  unfold one_rad,
  have h: Sup (small_rad X A x) ≥ 0,
  exact sup_small_rad_nonneg A x,
  linarith,
end

-- one_rad X A x ∈ small_rad X A x
lemma one_rad_in_small_rad {X: Type} [metric_space X] (A: set X) (x: X): one_rad X A x ∈ small_rad X A x :=
begin
  have h: (small_rad X A x).nonempty ∧ bdd_above (small_rad X A x),
  exact has_sup_rad A x,
  cases h with h1 h2,
  have claim: ∀ ε < 0, ∃ (a: ℝ) (H: a ∈ small_rad X A x), has_Sup.Sup (small_rad X A x) + ε < a,
  intro ε,
  intro ε0,
  exact real.add_neg_lt_Sup h1 ε0,
  have h4: Sup (small_rad X A x) ≥  0,
  exact sup_small_rad_nonneg A x,
  rw larger_than_or_equal_split (Sup (small_rad X A x)) 0 at h4,
  cases h4,
  have h3: -Sup (small_rad X A x) / 2 < 0,
  linarith,
  unfold one_rad,
  specialize claim (-Sup (small_rad X A x) / 2),
  specialize claim h3,
  cases claim with a claim,
  cases claim with H claim,
  have claim2: Sup (small_rad X A x) / 2 < a,
  linarith,
  have claim3: Sup (small_rad X A x) / 2 ≥ 0 ∧ a ∈ small_rad X A x ∧ Sup (small_rad X A x) / 2 < a,
  split,
  linarith,
  exact ⟨H, claim2⟩,
  exact set_contain_less_dist A x (Sup (small_rad X A x) / 2) a claim3,
  unfold one_rad,
  rw h4,
  simp,
  exact zero_in_rad A x,


end

-- If a positive number is in small_rad X A x, then one_rad X A x > 0
lemma positive_sup_positive {X: Type} [metric_space X] (A: set X) (x: X) (h: ∃ a : ℝ, a > 0 ∧ a ∈ small_rad X A x):
  one_rad X A x > 0 :=
begin
  cases h with a h,
  cases h with h1 h2,
  have claim: one_rad X A x ≥ 0,
  exact one_rad_nonneg A x,
  rw larger_than_or_equal_split at claim,
  cases claim,
  exact claim,
  unfold one_rad at claim,
  simp at claim,
  have h: (small_rad X A x).nonempty ∧ bdd_above (small_rad X A x),
  exact has_sup_rad A x,
  cases h with nonem bdd,
  have h3: ∀ (ε : ℝ), ε < 0 → (∃ (y : ℝ) (H : y ∈ (small_rad X A x)), a + ε < y),
  intro ε,
  intro neg,
  use a,
  split,
  exact h2,
  linarith,
  rw ← real.le_Sup_iff bdd nonem at h3,
  rw claim at h3,
  exfalso,
  have h4: a < a,
  exact gt_of_gt_of_ge h1 h3,
  simp at h4,
  exact h4,
end

-- if x ∈ accu_compl X A, then x ∈ (metric.ball x (one_rad X A x))
lemma accu_compl_x_in_small_rad {X: Type} [metric_space X] (A: set X) (x: X) (h: x ∈ accu_compl X A): 
  x ∈ (metric.ball x (one_rad X A x)) :=
begin
  unfold accu_compl at h,
  simp at h,
  cases h with a h,
  cases h with pos h,
  have H: a < 1 ∨ a ≥ 1,
  exact lt_or_ge a 1,
  cases H,
  have h1: ∃ a : ℝ, a > 0 ∧ a ∈ small_rad X A x,
  use a,
  split,
  exact pos,
  unfold small_rad,
  simp,
  split,
  exact le_of_lt pos,
  split,
  exact h,
  exact H,
  simp,
  exact positive_sup_positive A x h1,

  have h1: (0.5: ℝ) ∈ small_rad X A x,
  unfold small_rad,
  simp,
  split,
  intro y,
  specialize h y,
  intro dist,
  have h2: (0.5: ℝ) < a,
  linarith,
  simp at h2,
  have h3: has_dist.dist y x < a,
  linarith,
  specialize h h3,
  exact h,
  have h4: (1 / 2 : ℝ) = (2⁻¹: ℝ),
  exact one_div 2,
  rw ← h4,
  exact one_half_lt_one,
  --unfold one_rad,
  simp,
  have h5: ∃ a : ℝ, a > 0 ∧ a ∈ small_rad X A x,
  use (1 / 2: ℝ),
  split,
  exact one_half_pos,
  exact h1,
  exact positive_sup_positive A x h5,

end

-- x ∈ accu_compl X A → x ∈ x_ball_rad X A x
lemma accu_compl_x_in_ball_rad {X: Type} [metric_space X] (A: set X) (x: X) (h: x ∈ accu_compl X A): 
  x ∈ x_ball_rad X A x :=
begin
  unfold x_ball_rad,
  exact accu_compl_x_in_small_rad A x h,
end

-- if accu is empty, all elements are in accu_compl
lemma accu_empty_accu_compl {X: Type} [metric_space X] (A: set X) (h: accu X A = ∅): ∀ x: X, x ∈ accu_compl X A :=
begin
  intro x,
  have h1: x ∉ accu X A,
  exact set.eq_empty_iff_forall_not_mem.mp h x,
  unfold accu_compl,
  unfold accu at h1,
  simp,
  simp at h1,
  cases h1 with e h1,
  use e,
  cases h1 with h1 h2,

  split,
  exact h1,
  intro y,
  intro h3,
  intro hy,
  have claim: y ∈ metric.ball x e ∩ A,
  split,
  exact metric.mem_ball.mpr h3,
  exact hy,
  have claim2: metric.ball x e ∩ A ⊆ {x},
  exact set.diff_eq_empty.mp h2,
  have claim3: y ∈ {x},
  exact claim2 claim,
  simp at claim3,
  exact claim3,
end


lemma inter_bUnion {X: Type} (A: set X) (S: set X) (B: set X →  X → set X) : 
  (A ∩ ⋃ (i : X) (H : i ∈ S), B A i) = ⋃ (i : X) (H : i ∈ S), A ∩ B A i := 
begin
  ext y,
  split,
  {
    intro h,
    cases h with h1 h2,
    rw set.mem_bUnion_iff at h2 ⊢,
    cases h2 with z h2,
    use z,
    cases h2 with hz h2,
    split,
    
    exact hz,
    split,
    exact h1,
    exact h2,
    
  },
  {
    intro h,
    rw set.mem_bUnion_iff at h,
    cases h with z h,
    cases h with hz h,
    cases h with ha hb,
    split,
    exact ha,
    rw set.mem_bUnion_iff,
    use z,
    exact ⟨hz, hb⟩,

  },
end

-- A ∩ x_ball_rad X A x ⊆ {x}
lemma x_ball_rad_inter_A {X: Type} [metric_space X] (A: set X): ∀ x: X, A ∩ x_ball_rad X A x ⊆ {x} :=
begin
  intro x,
  have h2: one_rad X A x ∈ small_rad X A x,
  exact one_rad_in_small_rad A x,
  unfold small_rad at h2,
  simp at h2,
  cases h2 with h2 h3,
  cases h3 with h3 h4,
  simp,
  intro hy,
  specialize h3 hy,
  intro hya,
  intro h4,
  specialize h3 h4,
  apply h3,
  exact hya,

end

-- y ∈ A ∩ x_ball_rad X A x → y = x
lemma mem_x_ball_rad_inter_A {X: Type} [metric_space X] (A: set X) (x: X) (y: X) (h: y ∈ A ∩ x_ball_rad X A x):
  y = x:=
begin
  have h1: ∀ x: X, A ∩ x_ball_rad X A x ⊆ {x},
  exact x_ball_rad_inter_A A,
  specialize h1 x,
  have h2: y ∈ {x},
  exact h1 h,
  exact set.mem_singleton_iff.mp h2,
end

-- X is compact → Every infinite subset of X has a cluster point
example {X: Type} [metric_space X] (h: is_compact (set.univ: set X)) (A: set X) (h1: infinite A) : ((accu X A).nonempty) :=
begin
  by_contra hypo,
  rw set.not_nonempty_iff_eq_empty at hypo,
  rw is_compact_iff_finite_subcover at h,
  specialize h (x_ball_rad X A: X → set X),
  have metric_open: ∀ (i : X), is_open (x_ball_rad X A i),
  intro x,
  unfold x_ball_rad,
  exact metric.is_open_ball,
  specialize h metric_open,

  have claim: ∀ x: X, x ∈ accu_compl X A,
  exact accu_empty_accu_compl A hypo,
  have cover: set.univ ⊆ ⋃ (i : X), x_ball_rad X A i,
  rw set.subset_def,
  intro x,
  intro hx,
  have h2: x ∈ x_ball_rad X A x,
  specialize claim x,
  exact accu_compl_x_in_ball_rad A x claim,
  have ball_subset: x_ball_rad X A x ⊆ ⋃ (i : X), x_ball_rad X A i,
  exact set.subset_Union (x_ball_rad X A) x,
  exact ball_subset h2,
  specialize h cover,
  cases h with S h,
  have inter_A: A ∩ set.univ ⊆ A ∩ ⋃ (i : X) (H : i ∈ S), x_ball_rad X A i,
  exact set.inter_subset_inter_right A h,
  rw set.inter_univ A at inter_A,
  --rw inter_bUnion A S (x_ball_rad X A) at h,
  have h2: (A ∩ ⋃ (i : X) (H : i ∈ S), (x_ball_rad X A) i) = ⋃ (i : X) (H : i ∈ S), A ∩ (x_ball_rad X A) i,
  exact inter_bUnion A S (x_ball_rad X),
  rw h2 at inter_A,
  have h3: ∀ i: X, A ∩ x_ball_rad X A i ⊆ {i},
  exact x_ball_rad_inter_A A,

  have h4: (⋃ (i : X) (H : i ∈ S), A ∩ x_ball_rad X A i) ⊆ ⋃ (i : X) (H : i ∈ S), {i},
  rw set.subset_def,
  intro x,
  intro hx,
  simp,
  simp at hx,
  cases hx with i hx,
  cases hx with hx1 hx2,

  have hx3: x ∈ A ∩ x_ball_rad X A i,
  exact (set.mem_inter_iff x A (x_ball_rad X A i)).mpr hx2,
  have hx4: x = i,
  exact mem_x_ball_rad_inter_A A i x hx3,
  rw hx4,
  exact hx1,
  have hA: A ⊆ ⋃ (i : X) (H : i ∈ S), {i},
  exact set.subset.trans inter_A h4,
  have h5:  (⋃ (i : X) (H : i ∈ S), {i} ).infinite,
  apply set.infinite.mono hA,
  exact set.infinite_coe_iff.mp h1,
  apply h5,
  let t: X → (set X) := λ t, {t},
  have h6: ∀ (i : X), i ∈ S → (t i).finite,
  intro i,
  intro hi,
  exact set.finite_singleton i,
  have h7: (⋃ (i : X) (H : i ∈ S), {i})= ⋃ (i : X) (H : i ∈ S), t i,
  exact rfl,
  rw h7,
  
  have h8: ∀ (x : X), (x ∈ ⋃ (i : X) (H : i ∈ S), t i) ↔ x ∈ S,
  intro x,
  simp,
  have h9: (coe S: set X).finite,
  exact finset.finite_to_set S,
  exact set.finite.bUnion h9 h6,
end

