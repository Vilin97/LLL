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

-- define the ith maximal face of a list as the list with the ith element removed


def maximal_face {n : ℕ} (i : fin (n+1)) (S : simplex n) := list.remove_nth S i

-- define an m-face of a simplicial n complex as the list where (n+1) - m elements have been removed

-- define a function that converts a list of fin n to a list of ℕ

def list_fin_to_list_nat {n : ℕ} (l : list (fin n)) : list ℕ :=
list.map (λ i, fin.val i) l

-- define an m-face of a simplicial n complex as the list where (n+1) - m elements have been removed

def face (m : ℕ) {n : ℕ} (indices : list (fin (n+1-m))) (S : simplex n) := 
list.foldr (λ i l, list.remove_nth l i) S (list_fin_to_list_nat indices)

def maximal_faces {n : ℕ} (Δ : simplicial_complex n) := { X | ∃ i : fin (n+1), ∃ S ∈ Δ.family, X = maximal_face i S}

def faces (m : ℕ) {n : ℕ} (Δ : simplicial_complex n) := { X | ∃ l : list (fin (n+1-m)), ∃ S ∈ Δ.family, X = face m l S}

-- faces n Δ → faces (n-1)
def maximal_face_of_face (n : ℕ) {m : ℕ} (Δ : simplicial_complex m)  :=
λ F, {l : list (fin (m+1)) | ∃ (l' : list (fin (m + 1))), (l' ⊆ F) ∧ (list_fin_to_list_nat l = list_fin_to_list_nat (l'.drop 1))}

-- show that maximal_face_of_face is a function from faces n Δ → faces (n-1)
lemma maximal_face_of_face_is_function (n : ℕ) {m : ℕ} (Δ : simplicial_complex m) : ∀ F ∈ faces n Δ, maximal_face_of_face n Δ F ⊆ faces (n-1) Δ :=
begin
  sorry,
end

variables m j k l : ℕ  
variables Δ' : simplicial_complex m
#check faces l Δ'
#check ([j, k] : list (fin (m+1))) ∈ (faces l Δ')

--- define an n-chain of simplices in a simplicial m-complex

def chain (n : ℕ) {m : ℕ} (Δ : simplicial_complex m) := faces n Δ → ℤ

def maximal_chain {m : ℕ} (Δ : simplicial_complex m) := maximal_faces Δ → ℤ

-- show that n-chains form an add_comm_group

instance chain_group (n : ℕ) {m : ℕ} (Δ : simplicial_complex m) : add_comm_group (chain n Δ) := 
begin
  exact pi.add_comm_group,
end

#check ↥

instance maximal_chain_group  {m : ℕ} (Δ : simplicial_complex m) : add_comm_group (maximal_chain Δ) := 
begin
  exact pi.add_comm_group,
end

-- check that this works



variables a b : chain 2 Δ' 
#check - a + b

variables c d : maximal_chain Δ' 
#check c - d



-- define boundary operator on a face of a complex 

-- def face_boundary (n : ℕ) {m : ℕ} (Δ : simplicial_complex m) : faces n Δ → chain (n - 1) Δ 
-- := 

-- map from faces to chains
def maximal_face_to_chain {m : ℕ} (Δ : simplicial_complex m) : maximal_faces Δ → maximal_chain Δ 
:=  λ f, ( λ g, (if g = f then (1 : ℤ)  else 0))

def face_to_chain {n m : ℕ} (Δ : simplicial_complex m) : faces n Δ → chain n Δ 
:=  λ f, ( λ g, (if g = f then (1 : ℤ)  else 0))



-- define boundary operator on a face of a complex
def face_boundary  {m : ℕ} (Δ : simplicial_complex m) : faces m Δ → chain (m-1) Δ
:= λ (f : faces m Δ), 
      finset.sum (finset.range m) (λ (i : ℕ), 
      (if (i % 2 =  0) then (face_to_chain Δ (face_of_face (m-1) f)) 
      else -(face_to_chain Δ (face_of_face (m-1) f)))

-- define boundary operator on a chain as sum of boundary operator on faces

def boundary (n : ℕ) {m : ℕ} (Δ : simplicial_complex m) : chain n Δ → chain (n-1) Δ 
:= λ (c : chain n Δ), 
      finset.sum (finset.range (n + 1)) (λ (i : ℕ), 
      (if (i % 2 =  0) then (face_boundary Δ) 
      else -(face_boundary Δ)))
 



-- type check
variables const_chain : maximal_chain Δ'
#check finset.sum (finset.range (3 + 1)) (λ (i : ℕ ), (0 : maximal_chain Δ'))
#check (0 : maximal_chain Δ')
#check faces 2 Δ'

variables l : list (fin 1)
#check l ∈ faces 2 Δ' 




--- define a simplicial map

--- !!!






