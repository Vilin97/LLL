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

variables (X Y : Type) [topological_space X] [topological_space Y]

-- let S be a subset of X
variable (S : set X)

-- Let `f : X → Y` be a function
variables (f : X → Y) 

-- AUTUMN 2022 (WINTER 2022 starts on line 491)

-- X, Y are path connected space, then their product is path connected
example (h: path_connected_space X) (h1: path_connected_space Y):
  path_connected_space (X × Y) :=
begin
  rw path_connected_space_iff_univ at h h1 ⊢,
  unfold is_path_connected at h1 h ⊢,
  cases h with x hx,
  cases hx with h hx,
  cases h1 with y hy,
  cases hy with h1 hy,
  use (x, y),
  split,
  exact set.mem_univ (x, y),
  intro xy,
  have h2: xy.fst ∈ (set.univ: set X),
  exact set.mem_univ xy.fst,
  specialize hx h2,
  have h3: xy.snd ∈ (set.univ: set Y),
  exact set.mem_univ xy.snd,
  specialize hy h3,
  intro xyuniv,
  have h4: xy = (xy.fst, xy.snd),
  exact prod.ext rfl rfl,
  rw h4,
  unfold joined_in at hx hy ⊢,
  cases hy with p1 hy,
  cases hx with p2 hx,
  
  let p := path.prod p2 p1,
  use p,
  intro interval,
  specialize hx interval,
  specialize hy interval,
  exact set.mem_univ (p interval),
end

-- Show that if U is open in X and A is closed in X, then U − A is open in X, and
-- A − U is closed in X.
example (U : set X) (A : set X): 
  is_open U ∧ is_closed A → is_open (U ∩ Aᶜ) ∧ is_closed (A ∩ Uᶜ) :=
begin
  intro h,cases h with h1 h2,
  split,
  {
    have claim: is_open Aᶜ,
    exact is_open_compl_iff.mpr h2,
    exact is_open.inter h1 claim,
  },
  {
    have claim: is_closed Uᶜ,
    exact is_closed_compl_iff.mpr h1,
    exact is_closed.inter h2 claim,
  },
end

-- a set u is open iff for all element x in it, there exist a neighborhood
-- of x that is contained in u.
lemma is_open_iff_nhds' (u: set Y):
  (∀ x ∈ u, (∃ v ∈ nhds x, v ⊆ u)) ↔ is_open u:=
begin
  split,
  {
    intro y,
    rw ← is_closed_compl_iff,
    rw is_closed_iff_nhds,
    intro x,
    specialize y x,
    intro h,
    change x ∈ u → false,
    intro xu,
    specialize y xu,
    cases y with v y,
    specialize h v,
    cases y with H y,
    specialize h H,
    exact set.inter_compl_nonempty_iff.mp h y,
  },
  {
    intro h,
    intro x,
    intro xu,
    use u,
    split,
    exact is_open.mem_nhds h xu,
    refl,
  }, 
end

-- if an element x is not in a subset u, then {x} and u are disjoint
lemma singleton_not_in {X: Type} (x: X) (u: set X):
  x ∉ u ↔ {x} ∩ u = ∅:=
begin
  split,
  intro hx,
  ext y,
  split,
  {
    intro hy,
    simp,
    change x ∈ u → false at hx,
    apply hx,
    cases hy with hyx hyu,
    cases hyx with hyx1 hyx2,
    exact hyu,
    
  },
  {
    intro h,
    exfalso,
    exact h,
  },

  exact set.singleton_inter_eq_empty.mp,

end

-- if u1 and u2 are disjoint and u3 subset of u2, then u1 and u3 are disjoint
lemma inter_empty_subset {X: Type} (u1: set X) (u2: set X) (u3: set X) :
  u1 ∩ u2 = ∅ ∧ u3 ⊆ u2 → u1 ∩ u3 = ∅ :=
begin
  intro h,
  cases h with h1 h2,
  ext x,
  split,
  {
    intro h3,
    cases h3 with h3 h4,
    have h5: x ∈ u2,
    exact h2 h4,
    have h6: x ∈ u1 ∩ u2,
    split,
    exact h3,
    exact h5,
    rw h1 at h6,
    exact h6,
  },
  {
    intro h,
    exfalso,
    exact h,
  },
end

-- X, Y topological space, if Y is compact, then projection map π1 is closed map
lemma projection_compact_closed (h: is_compact (set.univ: set Y)):
  (is_closed_map (@prod.fst X Y)):=
begin
  unfold is_closed_map,
  intro u,
  intro hu,
  -- want to show complement open
  -- enough to show for each element x in complement, 
  -- there exists nhds of x contained in complement
  rw ← is_open_compl_iff,
  rw ← is_open_iff_nhds',
  intro x,
  intro hx,
  -- we can do this by using tube lemma 
  -- WTS: there exists open v s.t. {x} x Y ⊆ v x Y ⊆ uᶜ
  -- To use tube lemma: we need
  -- 1. is_compact {x}
  -- 2. is_compact Y (we have it in h)
  -- 3. is_open uᶜ
  -- 4. {x} x Y ⊆ uᶜ
  have h1: is_compact {x}, -- 1
  refine is_compact_singleton,

  rw ← is_open_compl_iff at hu, -- 3

  -- we have x ∈ π1(u)ᶜ, WTS: {x} x Y ⊆ uᶜ
  have h2: set.prod {x} (set.univ: set Y) ⊆ uᶜ, -- 4
  rw set.subset_compl_iff_disjoint,
  rw set.mem_compl_iff at hx,
  have h3: set.prod {x} (set.univ: set Y) = prod.fst⁻¹' {x},
  refine set.prod_univ,
  exact X,
  exact set.has_singleton,
  rw h3,
  have h4: disjoint {x} (prod.fst '' u),
  exact set.disjoint_singleton_left.mpr hx,
  have h5: disjoint (prod.fst⁻¹' {x}) (prod.fst⁻¹' (prod.fst '' u)),
  refine disjoint.preimage prod.fst h4,
  exact Y,
  have h6: u ⊆ prod.fst⁻¹' (prod.fst '' u),
  exact set.subset_preimage_image prod.fst u,
  rw set.disjoint_iff_inter_eq_empty at h5,
  rw inter_empty_subset (prod.fst ⁻¹' {x}) (prod.fst ⁻¹' (prod.fst '' u)) u,
  split,
  exact h5,
  exact h6,

  -- use tube lemma (h3 is the result of tube lemma)
  have h3: ∃ (u1 : set X) (v1 : set Y), is_open u1 ∧ is_open v1 ∧ {x} ⊆ u1 ∧ (set.univ: set Y) ⊆ v1 ∧ set.prod u1 v1 ⊆ uᶜ,
  exact generalized_tube_lemma h1 h hu h2,

  cases h3 with u1 h3,
  use u1,
  cases h3 with v1 h3,
  cases h3 with hu1 h3,
  cases h3 with hv1 h3,
  cases h3 with hx1 h3,
  cases h3 with h3 h4,
  split,
  rw mem_nhds_iff,
  use u1,
  split,
  refl,
  split,
  exact hu1,
  exact set.singleton_subset_iff.mp hx1,
  -- prove u1 ⊆ π1(u)ᶜ 
  have h5: v1 = (set.univ: set Y),
  rw ← set.univ_subset_iff,
  exact h3,
  rw h5 at h4,
  rw set.subset_compl_iff_disjoint at h4 ⊢,
  
  ext x1,
  split,
  {
    intro hx2,
    cases hx2 with hx2 hx3,
    -- WTS: if x1 ∈ u1 ∩ π1(u), ∃ x2 ∈ u1 x Y ∩ u = ∅
    have h6: ∃ x2 ∈ u, prod.fst x2 = x1, -- preimage
    exact set.mem_image_iff_bex.mp hx3,
    cases h6 with x2 h6,
    cases h6 with h6 h7,
    have h8: x2.fst ∈ u1,
    exact set.mem_of_eq_of_mem h7 hx2,
    have h9: x2.snd ∈ (set.univ: set Y),
    exact set.mem_univ x2.snd,
    have h10: (x2.fst, x2.snd) ∈ u1.prod set.univ, 
    exact set.mk_mem_prod h8 h9,
    have h11: x2 = (x2.fst, x2.snd),
    exact prod.ext rfl rfl,
    rw ← h11 at h10,
    have h12: x2 ∈ u1.prod set.univ ∩ u,
    exact set.mem_inter h10 h6,
    rw h4 at h12,
    exfalso,
    exact h12,
  },
  {
    intro hx1,
    exfalso,
    exact hx1,
  },
end



def graph {X: Type} {Y: Type} (f: X → Y): set (X × Y) := {(x, f x)| x: X}

-- f: X → Y, Y compact Hausdorff
-- Then f is cts iff the graph of f is closed in X x Y.
lemma cts_map_closed_graph (h1: is_compact (set.univ: set Y)) (h2: t2_space Y):
  continuous f ↔ is_closed (graph f) :=
begin
  split,
  {
    intro h,
    rw ← is_open_compl_iff,
    rw ← is_open_iff_nhds',
    intro xy,
    intro hxy,
    have h3: xy = (xy.fst, xy.snd),
    exact prod.ext rfl rfl,
    rw h3 at hxy,
    have h4: xy.snd ≠ f xy.fst,
    intro h4,
    unfold graph at hxy,
    simp at hxy,
    specialize hxy xy.fst,
    rw h3 at hxy,
    apply hxy,
    rw h4,
    have h5: ∃ (u v : set Y), is_open u ∧ is_open v ∧ xy.snd ∈ u ∧ (f xy.fst) ∈ v ∧ (u ∩ v = ∅),
    exact t2_separation h4,
    cases h5 with u h5,
    cases h5 with v h5,
    cases h5 with hu h5,
    cases h5 with hv h5,
    cases h5 with hxyu h5,
    cases h5 with hxyv h5,
    have h6: is_open (f ⁻¹' u),
    exact continuous_def.mp h u hu,
    have h7: is_open (f ⁻¹' v),
    exact continuous_def.mp h v hv,
    have h8: is_open (set.prod (f ⁻¹' v) u),
    exact is_open.prod h7 hu,
    have claim: xy ∈ set.prod (f ⁻¹' v) u,
    simp,
    exact ⟨hxyv, hxyu⟩,
    use set.prod (f ⁻¹' v) u,
    split,
    exact is_open.mem_nhds h8 claim,
    rw set.subset_compl_iff_disjoint,
    unfold graph,
    ext a,
    split,
    {
      intro ha,
      cases ha with ha1 ha2,
      simp at ha2,
      cases ha2 with afst ha2,
      have ha3: afst = a.fst,
      exact (congr_arg prod.fst ha2).congr_right.mp rfl,
      rw ha3 at ha2,
      rw ← ha2 at ha1,
      simp at ha1,
      cases ha1 with ha ha1,
      have ha4: f a.fst ∈ u ∩ v,
      exact set.mem_inter ha1 ha,
      rw h5 at ha4,
      exact ha4,
    },
    {
      intro ha,
      exfalso,
      exact ha,
    },
  },
  { 
    -- for x in X, v nhds of f(x), Gf ∩ X x (Y - v) closed
    -- π1(Gf ∩ X x (Y - v)) is closed and its compl = f ⁻¹ (v)
    intro h,
    rw continuous_def,
    intro s,
    intro hs,
    have h3: is_closed (set.prod (set.univ: set X) (sᶜ)),
    apply is_closed.prod,
    exact is_closed_univ,
    exact is_closed_compl_iff.mpr hs,
    let u: set (X × Y) := ((set.prod (set.univ: set X) (sᶜ)) ∩ graph f),
    have h4: is_closed u,
    exact is_closed.inter h3 h,
    have h5: is_closed_map (@prod.fst X Y),
    exact projection_compact_closed X Y h1,
    have h6: is_closed (prod.fst '' u),
    exact h5 u h4,
    have h7: prod.fst '' u = (f ⁻¹' s)ᶜ,
    ext x,
    split,
    {
      intro hx,
      intro hx1,
      rw set.mem_preimage at hx1,
      have h8: (x, f x) ∈ graph f,
      unfold graph,
      simp,
      have h11: ∃ a ∈ u, prod.fst a = x,
      exact set.mem_image_iff_bex.mp hx,
      cases h11 with a h11,
      cases h11 with ha h11,
      have h12: a = (a.fst, a.snd),
      exact prod.ext rfl rfl,
      have h13: a.snd = f x,

      rw h11 at h12,
      rw h12 at ha,
      have h10: (x, a.snd) ∈ graph f,
      exact set.mem_of_mem_inter_right ha,
      unfold graph at h10,
      simp at h10,
      exact eq.symm h10,
      rw [h11, h13] at h12,
      rw h12 at ha,
      cases ha with ha1 ha2,
      simp at ha1,
      exact ha1 hx1,
    },
    {
      intro hx,
      simp at hx,
      simp,
      use f x,
      split,
      exact hx,
      unfold graph,
      simp,
    },
    rw ← is_closed_compl_iff,
    rw ← h7,
    exact h6,
  },
end


example (h1: is_open_map f) (h2: function.surjective f) (h3: continuous f) :
  quotient_map f :=
begin
  exact is_open_map.to_quotient_map h1 h3 h2,
end

-- if f : X → Y is continuous, where X is compact and Y is Hausdorff,
-- then f is a closed map
example (h1: continuous f) (h2: is_compact (set.univ: set X)) (h3: t2_space Y) :
  is_closed_map f :=
begin
  unfold is_closed_map,
  intro u,
  intro closeu,
  have h4: u ⊆ (set.univ: set X),
  exact set.subset_univ u,
  have h5: is_compact u,
  exact compact_of_is_closed_subset h2 closeu h4,
  have h6: is_compact (f '' u),
  exact is_compact.image h5 h1,
  exact is_compact.is_closed h6,
end

--example (h1: t2_space X) (A: set X) (B: set X) (h2: is_compact A) (h3: is_compact B) (h4: disjoint A B):
--  ∃ (u v : set X), is_open u ∧ is_open v ∧ A ⊆ u ∧ B ⊆ v ∧ disjoint u v :=
--begin
--  sorry,
--end

example (h1: t2_space X) (A: set X) (B: set X) (h2: is_compact A) (x ∈ B) (h3: disjoint A B):
  ∃ (u: set X), is_open u ∧ x ∈ u ∧ disjoint u B :=
begin
  rw is_compact_iff_finite_subcover at h2,
  sorry,
end

example (h1: quotient_map f) (y: Y) (h2: is_connected (set.univ: set Y)) (h3: is_connected (f⁻¹' {y})):
  is_connected (set.univ: set X) :=
begin
  have h4: continuous f,
  exact quotient_map.continuous h1,
  unfold is_connected at h2 ⊢ h3,
  split,
  {
    cases h3,
    have h5: f⁻¹' {y} ⊆ (set.univ: set X),
    exact (f ⁻¹' {y}).subset_univ,
    exact set.nonempty.mono h5 h3_left,
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
    cases h3,
    simp at h,
    rw ← set.disjoint_iff_inter_eq_empty at h,
    have h5: f⁻¹' {y} ⊆ set.univ,
    exact (f ⁻¹' {y}).subset_univ,
    have h6: f⁻¹' {y} ⊆ u ∪ v,
    exact set.subset.trans h5 hypo,
    have h6: f⁻¹' {y} ⊆ u ∨ f⁻¹' {y} ⊆ v,
    exact is_preconnected.subset_or_subset openu openv h h6 h3_right,
    sorry,
  },
  


end


-- Winter 2022

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


-- Let f: X → Y be a quotient map, if each set f⁻¹({y}) is connected and if Y is connected, then X is connected.
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


-- If a set is connected, then its closure is connected
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

def accu [metric_space X] (A: set X) := {x : X | ∀ ε > (0: ℝ), (((metric.ball x ε) ∩ A) \ {x}) ≠ ∅}

def accu_compl [metric_space X] (A: set X) := {x: X | ∃ ε > (0: ℝ), ((metric.ball x ε) ∩ A) ⊆ {x}}

def small_rad [metric_space X] (A: set X) (x: X) := {ε : ℝ | (ε > 0) → ((metric.ball x ε) ∩ A) ⊆ {x}}

-- def g [metric_space X](A: set X)  : X → ℝ
-- | x := 
--   if x ∈ accu_compl X A then  (small_rad X A x)
--   else 0



example [metric_space X] (h: compact_space X) (A: set X) (h1: infinite A) : ((accu X A).nonempty) :=
begin
  by_contra hypo,
  rw set.not_nonempty_iff_eq_empty at hypo,
  --unfold accu at hypo,
  rw ← is_compact_univ_iff at h,
  rw is_compact_iff_finite_subcover at h,


  have claim: ∀ (x: X), ∃ ε > 0, (metric.ball x ε) ∩ A ⊆ {x},
  {
    intro x,
    have h2: x ∉ accu X A,
    exact set.eq_empty_iff_forall_not_mem.mp hypo x,
    unfold accu at h2,
    simp at h2,
    cases h2 with e h2,
    use e,
    cases h2 with h2 h3,
    split,
    exact h2,
    exact set.diff_eq_empty.mp h3,
  },
  have claim2: ∀ (x: X), x ∈ accu_compl X A,
  {
    unfold accu_compl,
    intro x,
    specialize claim x,
    simp,
    simp at claim,
    exact claim,
  },

  have claim3: ∀ (x: X), x ∈ accu_compl X A,
  exact claim2,


  
  

  -- --specialize h ℕ,
  let U: X → set X := λ x, ((ε: ℝ) ∈ small_rad A x claim2) metric.ball x ε 
  sorry,

  
end

-- example [metric_space X] (h: compact_space X) (A: set X) (h1: infinite A) : ((accu X A).nonempty) :=

example [metric_space X] [metric_space Y] (h: compact_space X) (f: X → Y): continuous f ↔ is_compact (graph f) :=
begin
  split,
  {
    intro fcts,
    sorry,
  },
end

