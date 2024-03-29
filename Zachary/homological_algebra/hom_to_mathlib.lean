/-
Copyright (c) 2020 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/

import category_theory.category.basic
import category_theory.limits.shapes.equalizers
import category_theory.limits.shapes.zero_objects
import category_theory.limits.shapes.zero_morphisms
import category_theory.limits.shapes.kernels
import category_theory.limits.shapes.pullbacks
import category_theory.limits.shapes.regular_mono

open category_theory
open category_theory.limits

universes v u
variables {C : Type u} [𝒞 : category.{v} C]
include 𝒞

section
variables [has_zero_morphisms.{v} C] {X Y : C} (f : X ⟶ Y)

def kernel.lift'' [has_limit (parallel_pair f 0)]
  {Z : C} (g : Z ⟶ X) (h : g ≫ f = 0) : ∃! l, l ≫ kernel.ι f = g :=
⟨kernel.lift f g h, by erw limit.lift_π; refl, λ k hk, begin
  apply is_limit.uniq _ (kernel_fork.of_ι g h),
  intro j,
  cases j,
  exact hk,
  rw ←fork.app_zero_left,
  rw ←category.assoc,
  erw hk,
  refl,
end⟩

def kernel.transport' [has_limit (parallel_pair f 0)]
  {Z : C} (l : X ⟶ Z) (i : Z ≅ Y) (h : l ≫ i.hom = f) :
  is_limit (kernel_fork.of_ι (kernel.ι f) $ show kernel.ι f ≫ l = 0,
    by rw [←(iso.comp_inv_eq i).2 h.symm, ←category.assoc,
      kernel.condition, has_zero_morphisms.zero_comp]) :=
fork.is_limit.mk _
  (λ s, kernel.lift f (fork.ι s) $
    by erw [←h, ←category.assoc, fork.condition, has_zero_morphisms.comp_zero,
      has_zero_morphisms.zero_comp])
  (λ s, by erw limit.lift_π; refl)
  (λ s m h, by ext; rw limit.lift_π; exact h walking_parallel_pair.zero)

def cokernel.transport' [has_colimit (parallel_pair f 0)]
  {Z : C} (l : Z ⟶ Y) (i : X ≅ Z) (h : i.hom ≫ l = f) :
  is_colimit (cokernel_cofork.of_π (cokernel.π f) $ show l ≫ cokernel.π f = 0,
  by rw [(iso.eq_inv_comp i).2 h, category.assoc, cokernel.condition, has_zero_morphisms.comp_zero]) :=
cofork.is_colimit.mk _
  (λ s, cokernel.desc f (cofork.π s) $
    by erw [←h, category.assoc, cofork.condition,
      has_zero_morphisms.zero_comp, has_zero_morphisms.comp_zero])
  (λ s, by erw colimit.ι_desc; refl)
  (λ s m h, by ext; rw colimit.ι_desc; exact h walking_parallel_pair.one)

def kernel.transport [has_limit (parallel_pair f 0)]
  {Z : C} (l : Z ⟶ X) (i : Z ≅ kernel f) (h : i.hom ≫ kernel.ι f = l) :
  is_limit (kernel_fork.of_ι l $
    by rw [←h, category.assoc, kernel.condition, has_zero_morphisms.comp_zero]) :=
fork.is_limit.mk _
  (λ s, (kernel.lift f (fork.ι s) (kernel_fork.condition s)) ≫ i.inv)
  (λ s, begin
    rw category.assoc,
    erw (iso.inv_comp_eq i).2 h.symm,
    rw limit.lift_π,
    refl,
  end)
  (λ s m h', begin
    apply (iso.eq_comp_inv i).2,
    ext,
    simp only [limit.lift_π, fork.of_ι_app_zero, category.assoc],
    rw h,
    exact h' walking_parallel_pair.zero,
  end)

def cokernel.transport [has_colimit (parallel_pair f 0)]
  {Z : C} (l : Y ⟶ Z) (i : cokernel f ≅ Z) (h : cokernel.π f ≫ i.hom = l) :
  is_colimit (cokernel_cofork.of_π l $
    by rw [←h, ←category.assoc, cokernel.condition, has_zero_morphisms.zero_comp]) :=
cofork.is_colimit.mk _
  (λ s, i.inv ≫ (cokernel.desc f (cofork.π s) (cokernel_cofork.condition s)))
  (λ s, begin
    rw ←category.assoc,
    erw ←(iso.eq_comp_inv i).2 h,
    rw colimit.ι_desc,
    refl,
  end)
  (λ s m h', begin
    apply (iso.eq_inv_comp i).2,
    ext,
    simp only [category_theory.limits.cofork.of_π_app_one, colimit.ι_desc],
    rw ←category.assoc,
    rw h,
    exact h' walking_parallel_pair.one,
  end)

end
