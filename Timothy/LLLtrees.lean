/- Lines 1-74 Written By Kevin Buzzard 2022 -/

import tactic -- imports all the Lean tactics
import combinatorics.simple_graph.connectivity -- paths and walks etc
import data.set.finite

/-

# Trees

A graph is a tree if it's nonempty and for every pair of vertices
there's a unique path between them.

In this file I show that trees have no cycles.

-/

universe u₀

namespace simple_graph

/-- A graph is a tree if it's nonempty and for every pair of vertices
  there's a unique path between them. -/
def is_tree {V : Type u₀} (G : simple_graph V) : Prop :=
nonempty V ∧ ∀ u v : V, ∃! p : G.walk u v, p.is_path

/-- A graph is connected if it's nonempty and for every pair of vertices
  there's a path between them. -/
def is_connected {V : Type u₀} (G : simple_graph V) : Prop :=
nonempty V ∧ ∀ u v : V, ∃ p : G.walk u v, p.is_path

namespace is_tree

variables {V : Type u₀} {G : simple_graph V}

/-- Trees are connected. -/
lemma is_connected {V : Type u₀} {G : simple_graph V} 
  (h : G.is_tree) : G.is_connected :=
begin
  exact ⟨h.1, λ u v, exists_unique.exists (h.2 u v)⟩,
end

open simple_graph.walk

/-- A tree has no cycles. -/
lemma no_cycles [decidable_eq V] (hG : G.is_tree) (u : V) (p : G.walk u u) :
¬ p.is_cycle :=
begin
  intro hp,
  cases p with _ _ v _ huv q,
  { exact hp.ne_nil rfl, },
  { set w1 := cons huv nil with hw1,
    set w2 := q.reverse with hw2,
    have hw1path : w1.is_path,
    { simp,
      intro h,
      rw h at huv,
      exact G.loopless v huv },
    have hw2path : w2.is_path,
    { apply is_path.reverse,
      rw is_path_def,
      simpa using hp.support_nodup },
    have hw := exists_unique.unique (hG.2 u v) hw1path hw2path,
    rw [hw1, hw2] at hw,
    apply_fun reverse at hw,
    rw reverse_reverse at hw,
    rw ← hw at hp,
    simp at hp,
    replace hp := is_circuit.to_trail (is_cycle.to_circuit hp),
    rw is_trail_def at hp,
    simp at hp,
    apply hp,
    apply sym2.rel.swap },    
end


--Timothy Tran, Spring 2023
def vertex_degree_one (v : V) :=
  ∃! (u : V), u ≠ v ∧ G.adj v u


--lemma verticeDeg2andMore_isCycle (v : V) (u : V) (vertices : v ∈ G.support) (h : ¬ (@vertex_degree_one V G u))
lemma verticeDeg2andMore_isCycle (v : V) (u : V) (vDeg2plus : u ∈ G.support ∧ ¬ (@vertex_degree_one V G u))
    : ∃ (p : G.walk u u), true :=
    --"exists vertex u that has degree at least 2 such that there exists a walk from u to u"
begin
  sorry,
end


-- every tree has at least one vertex with degree 1
lemma tree_exists_vertexDegreeOne (v : V) (hg : G.is_tree) (hfin : fintype G.support) (vertices : v ∈ G.support)
          : (∃ w ∈ G.support, @vertex_degree_one V G w) := --where w is that vertex with degree 1
begin
  by_contra,
  push_neg at h,
  --need to define where if not degree 1, then move to another vertex
  --NOTE: below are random tactics, does not represent actual mathematical approach
  specialize h v,
  apply h,
  
  exact vertices,
  have H := h vertices,
  sorry,

  --expanding out definitions of vertex_degree_one
  -- change v ∈ G.support → ¬ (∃! (u : V), u ≠ v ∧ G.adj v u) at h,
  -- change (∃! (u : V), u ≠ v ∧ G.adj v u),
end

-- every tree on n vertices has exactly n - 1 edges
-- G.support : set of vertices that form edges in G
-- G.edge_set : the edges of G
theorem tree_n_minus_1_edges (hG : G.is_tree) (hfin : fintype G.support) (hfin : fintype G.edge_set)  
                    : fintype.card G.support - 1 = fintype.card G.edge_set :=
begin
  sorry,
end

end is_tree
end simple_graph
