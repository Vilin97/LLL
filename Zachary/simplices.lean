import data.real.basic
import data.finset.basic
import algebra.big_operators.basic
import data.fintype.basic
import data.set.finite
import tactic
import group_theory.free_abelian_group

open_locale big_operators
noncomputable theory

--1

-- define n-simplex as formal linear combination of n+1 vertices with coefficients summing to 1
-- https://leanprover-community.github.io/mathematics_in_lean/06_Abstract_Algebra.html

structure simplex' (n : ℕ) :=
(v : fin (n + 1) → ℝ)
(sum_eq_one : ∑ i, v i = 1)
(nonneg : ∀ i, v i ≥ 0)

-- A simplicial complex is a family of sets such that for each set X in the family Δ,
-- there exists a set Y in the family Δ such that X is a subset of Y
-- define a simplex as a structure given the above definition

-- for all sets in the family, any subset is also in the family

structure simplicial_complex (n : ℕ) :=
(family : set (set (fin (n + 1))))
(prop : ∀ X ∈ family, ∀ Y ∈ set.powerset X, Y ∈ family)


-- a face X of a simplicial complex is a set in the family of the simplex
-- define a face of an n-simplex given the definition above

def is_face_of_complex {n : ℕ} (Δ : simplicial_complex n) (X : set (fin (n + 1))) : Prop := X ∈ Δ.family

-- a face X is a face of Y if X is a subset of Y
-- define is_face_of_face given the above definition

def is_face_of_face (n : ℕ) (X Y : set (fin (n + 1))) : Prop := X ⊆ Y

-- the vertices of a simplex is the union of all of the faces of a simplex

def vertices (n : ℕ) (Δ : simplicial_complex n) : set (fin (n + 1)) := ⋃ X ∈ Δ.family, X

-- The dimension of a face X in Δ is defined as dim(X) = |X| − 1
-- define dimension of a face given the above definition

-- A simplicial map is a function  f  that maps the vertices of Δ to the vertices of 
-- Γ and that has the property that for any face X of Δ, the image  f (X) is a face of Γ
-- define simplicial map given the above definition

def is_simplicial_map {m n : ℕ} (Δ : simplicial_complex n) (Γ : simplicial_complex m) (f : fin (n + 1) → fin (m + 1)) : Prop := 
(∀ X ∈ Δ.family, is_face_of_complex Γ (f '' X))

-- an ordered simplicial complex is a simplicial complex with a total order on the vertices
-- create a structure oriented_simplicial_complex extending the structure of simplicial_complex with the above definition

structure oriented_simplicial_complex (n : ℕ) extends simplicial_complex n := -- redundant
(order : fin (n + 1) → fin (n + 1) → Prop)
(total : ∀ i j, order i j ∨ order j i)
(antisymmetric : ∀ i j, order i j → order j i → i = j)
(transitive : ∀ i j k, order i j → order j k → order i k)
(reflexive : ∀ i, order i i)

-- define an oriented face of an oriented simplicial complex

def is_oriented_face_of_complex {n : ℕ} (Δ : oriented_simplicial_complex n) (X : set (fin (n + 1))) : Prop := X ∈ Δ.family -- ∧ card is m for m-face

-- the set of oriented faces of a simplicial complex K is the set of subsets of K that are oriented faces of K

def oriented_faces (n : ℕ) (Δ : oriented_simplicial_complex n) : set (set (fin (n + 1))) := {X | is_oriented_face_of_complex Δ X}



-- Given a set An1, . . . , Ank of arbitrarily oriented n-simplices of a complex K and an 
-- abelian group G, we define an n-chain x with coefficients in G as a formal sum of faces in K with coefficients in the integers

def chain (n : ℕ) (Δ : oriented_simplicial_complex n) := oriented_faces n Δ → ℤ

variables Δ : oriented_simplicial_complex 5
variables C C' : oriented_faces 5 Δ → ℤ
#check C →+ C'

variables (α : Type 2) (β : Type 1) [add_comm_group β]
variables (f g : α → β)
#check -g

example : [2,3,5] ⊆ [5,4,3,2,1] :=
begin
  simp,
end

def d (n) : (oriented_faces n Δ → ℤ) Σ i : fin (n), (-1)^i oriented_faces (n - 1) Δ → ℤ)

-- an n_chain_group is the group formed by the set of all n-chains with coefficients in G, 
-- where addition is given by the sum of the coefficients of the oriented faces, and the identity is the zero map.#check
-- define a structure n_chain_group based on the above that satisfies the group axioms

structure chain_group (n : ℕ) (Δ : oriented_simplicial_complex n) :=
(add : ∀ x y : chain n Δ, chain n Δ)
(add_assoc : ∀ x y z : chain n Δ, add (add x y) z = add x (add y z))
(zero : chain n Δ)
(zero_add : ∀ x : chain n Δ, add zero x = x)
(add_zero : ∀ x : chain n Δ, add x zero = x)
(inv : chain n Δ → chain n Δ)
(add_left_neg : ∀ x : chain n Δ, add x (inv x) = zero)
(add_comm : ∀ x y : chain n Δ, add x y = add y x)


-- define the n_chain group as the free add group on the set of oriented faces of the simplicial complex 
-- using the free abelian group library

def chain_group (n : ℕ) (Δ : oriented_simplicial_complex n) : Type := 
free_add_group (oriented_faces n Δ)

-- the boundary operator is a group homomorphism mapping a chain to the alternating sum of the oriented faces of the chain
-- define the boundary operator given the above definition

def is_oriented_subcomplex {m n : ℕ} (Γ : oriented_simplicial_complex m) (Δ : oriented_simplicial_complex n) := 
(∀ X ∈ Γ.family, is_oriented_face_of_complex Δ X) -- !!! need to lift fin (m + 1) to fin (n + 1)

structure oriented_subcomplex (m n : ℕ) (Δ : oriented_simplicial_complex n) extends oriented_simplicial_complex n :=
(sub : oriented_simplicial_complex m)
(parent : oriented_simplicial_complex n)
(le : m ≤ n)
(is_oriented_subcomplex : is_oriented_subcomplex sub parent)
(to_oriented_complex : oriented_simplicial_complex m)

-- define boundary operator inductively on the dimension of the simplicial complex

inductive boundary (n : ℕ) (Δ : oriented_simplicial_complex (n + 1)) (Γ : oriented_subcomplex n (n+1) Δ) : chain (n+1) Δ → chain n Γ.to_oriented_complex :=
| zero : boundary 0 (λ x, 0)
| one : boundary 1 (λ x, 0)
| n : -- !!!



-- a m-subcomplex of an oriented n-complex is the simplicial complex formed by the union of the m-faces of the oriented n-complex
-- define m_subcomplex as the above

def is_subcomplex (m n : ℕ) (Γ : oriented_simplicial_complex m) (Δ : oriented_simplicial_complex n) := 
(∀ X ∈ Γ.family, is_oriented_face_of_complex Δ X)


-- define the boundary operator on n_chain_group taking an element and mapping the n faces to (n-1) faces
-- use the definition above
-- how to define boundary??






-- the boundary operator on an n chain maps the n chain to a chain formed by the sum of the boundaries of the oriented faces of the n chain
















-- define prop_situated as the condition for two simplices to either have empty intersection, or
-- have intersection a face of both simplices

-- define simplicial complex

--2

-- define orientation on a simplex

-- define n-chains











