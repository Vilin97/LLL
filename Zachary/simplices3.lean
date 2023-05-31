import data.real.basic
import data.finset.basic
import algebra.big_operators.basic
import data.fintype.basic
import data.set.finite
import tactic
import algebra.group.defs
import group_theory.free_abelian_group



open_locale big_operators
open list
noncomputable theory

--def vertices (n : ℕ) := fin (n + 1)
def simplex (n : ℕ) := list (fin (n + 1))

structure simplicial_complex (n : ℕ) :=
(family : list (list (fin (n + 1))))
(prop : ∀ X ∈ family, ∀ Y ⊆ X, Y ∈ family)


-- function that converts a list of fin n to a list of ℕ
def list_fin_to_list_nat {n : ℕ} (l : list (fin n)) : list ℕ :=
list.map (λ i, fin.val i) l

-- define an m-face of a simplicial n complex as the list where (n+1) - m elements have been removed
def face (m : ℕ) {n : ℕ} (indices : list (fin (n+1-m))) (S : simplex n) := 
list.foldr (λ i l, list.remove_nth l i) S (list_fin_to_list_nat indices)

-- the faces of a simplex is the set of all faces of the simplices in the complex
def faces (m : ℕ) {n : ℕ} (Δ : simplicial_complex n) := { X | ∃ l : list (fin (n+1-m)), ∃ S ∈ Δ.family, X = face m l S}


--- define an n-chain of simplices in a simplicial m-complex
def chain (n : ℕ) {m : ℕ} (Δ : simplicial_complex m) := faces n Δ → ℤ


-- show that n-chains form an add_comm_group
instance chain_group (n : ℕ) {m : ℕ} (Δ : simplicial_complex m) : add_comm_group (chain n Δ) := 
begin
  exact pi.add_comm_group,
end


-- natural map taking a face to a chain
def face_to_chain {n m : ℕ} (Δ : simplicial_complex m) : faces n Δ → chain n Δ 
:=  λ f, ( λ g, (if g = f then (1 : ℤ)  else 0))


def max_face_of_face {n : ℕ} {m : ℕ} (Δ : simplicial_complex m) : faces n Δ → faces (n-1) Δ :=
begin
  sorry,
end

-- define boundary operator on a face of a complex
def face_boundary  {m : ℕ} (Δ : simplicial_complex m) : faces m Δ → chain (m-1) Δ
:= λ (f : faces m Δ), 
      finset.sum (finset.range m) (λ (i : ℕ), 
      (if (i % 2 =  0) then (face_to_chain Δ (max_face_of_face Δ f)) 
      else -(face_to_chain Δ (max_face_of_face Δ f)))


-- define boundary operator on a chain as sum of boundary operator on faces
def boundary (n : ℕ) {m : ℕ} (Δ : simplicial_complex m) : chain n Δ → chain (n-1) Δ 
:= λ (c : chain n Δ), 
      finset.sum (finset.range (n + 1)) (λ (i : ℕ), 
      (if (i % 2 =  0) then (face_boundary -----) !!!!!!!!!!!!!!!
      else -(face_boundary -- ))
 


-- type check
variables Δ' : simplicial_complex 3
variables l : list (fin 4)
#check l ∈ faces 1 Δ' 



-- - TO DO:
-- show that boundary is a homomorphism
-- show that boundary composed with itself is zero
-- define homology groups of a chain complex
-- define exact sequences of chain complexes






