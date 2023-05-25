import tactic
import group_theory.quotient_group
import data.fintype.card
import group_theory.coset
import data.fintype.basic
-- Prove Lagrange's Theorem in Lean

open_locale classical

variables {G : Type} [group G] (H : set G) [fintype G] [decidable_pred (∈ H)]


-- First we prove the lemma that the left cosets of H partition G
lemma left_cosets_partition : ∀ g : G, ∃! (S : set G), g ∈ S ∧ ∀ x ∈ S, left_coset x H = S :=
begin
  intro g,
  use left_coset g H,
  split,
  { split,
    { exact mem_left_coset g H },
    { intros x hx,
      rw ←hx,
      exact left_coset_eq_left_coset g H } },
  { intros S hS,
    split,
    { exact hS.left },
    { intros x hx,
      rw ←hx,
      exact hS.right x hx } }
end

-- Now we prove Lagrange's Theorem
theorem lagrange : fintype.card G = fintype.card H * fintype.card (quotient H) :=
begin
  classical,
  have h : ∀ g : G, fintype.card {x // left_coset x H = left_coset g H} = fintype.card H :=
  begin
    intro g,
    apply fintype.card_congr,
    use λ x, ⟨g * x, by rw [left_coset_eq_left_coset g H, left_coset_eq_left_coset]⟩,
    { intros x y hxy,
      simpa [left_coset_eq_left_coset] using hxy },
    { intros y,
      use y * g⁻¹,
      simp },
  end,
  have h' : fintype.card H * fintype.card (quotient_group.quotient H) = fintype.card (set G) :=
  begin
    rw ←fintype.card_congr (quotient_group.quotient H),
    apply fintype.card_congr,
    use quotient_group.mk',
    { intros x y hxy,
      simpa using hxy },
    { intros y,
      use y.val,
      simp },
  end,
  rw [fintype.card_congr (left_cosets_partition H), fintype.card_sigma],
  simp [h, h'],
end
