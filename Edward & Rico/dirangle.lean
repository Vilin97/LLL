/-
Copyright (c) 2019 Calle Sönne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Calle Sönne
-/
import data.real.basic
import analysis.special_functions.trigonometric.basic
import analysis.normed.group.add_circle
import algebra.char_zero.quotient
import topology.instances.sign

/-!
# The type of dirangles

In this file we define `real.dirangle` to be the quotient group `ℝ/φℤ` and prove a few simple lemmas
about trigonometric functions and dirangles.
-/


open_locale real

noncomputable theory

namespace real

def φ : ℝ := π/2

/-- The type of dirangles -/
@[derive [normed_add_comm_group, inhabited, has_coe_t ℝ]]
def dirangle : Type := add_circle (2 * φ)

namespace dirangle

@[continuity] lemma continuous_coe : continuous (coe : ℝ → dirangle) :=
continuous_quotient_mk

/-- Coercion `ℝ → dirangle` as an additive homomorphism. -/
def coe_hom : ℝ →+ dirangle := quotient_add_group.mk' _

@[simp] lemma coe_coe_hom : (coe_hom : ℝ → dirangle) = coe := rfl

/-- An induction principle to deduce results for `angle` from those for `ℝ`, used with
`induction θ using real.dirangle.induction_on`. -/
@[elab_as_eliminator]
protected lemma induction_on {p : dirangle → Prop} (θ : dirangle) (h : ∀ x : ℝ, p x) : p θ :=
quotient.induction_on' θ h

@[simp] lemma coe_zero : ↑(0 : ℝ) = (0 : dirangle) := rfl
@[simp] lemma coe_add (x y : ℝ) : ↑(x + y : ℝ) = (↑x + ↑y : dirangle) := rfl
@[simp] lemma coe_neg (x : ℝ) : ↑(-x : ℝ) = -(↑x : dirangle) := rfl
@[simp] lemma coe_sub (x y : ℝ) : ↑(x - y : ℝ) = (↑x - ↑y : dirangle) := rfl
lemma coe_nsmul (n : ℕ) (x : ℝ) : ↑(n • x : ℝ) = (n • ↑x : dirangle) := rfl
lemma coe_zsmul (z : ℤ) (x : ℝ) : ↑(z • x : ℝ) = (z • ↑x : dirangle) := rfl

@[simp, norm_cast] lemma coe_nat_mul_eq_nsmul (x : ℝ) (n : ℕ) :
  ↑((n : ℝ) * x) = n • (↑x : dirangle) :=
by simpa only [nsmul_eq_mul] using coe_hom.map_nsmul x n

@[simp, norm_cast] lemma coe_int_mul_eq_zsmul (x : ℝ) (n : ℤ) :
  ↑((n : ℝ) * x : ℝ) = n • (↑x : dirangle) :=
by simpa only [zsmul_eq_mul] using coe_hom.map_zsmul x n

lemma dirangle_eq_iff_two_pi_dvd_sub {ψ θ : ℝ} : (θ : dirangle) = ψ ↔ ∃ k : ℤ, θ - ψ = 2 * φ * k :=
by simp only [quotient_add_group.eq, add_subgroup.zmultiples_eq_closure,
  add_subgroup.mem_closure_singleton, zsmul_eq_mul', (sub_eq_neg_add _ _).symm, eq_comm]

@[simp] lemma coe_two_pi : ↑(2 * φ : ℝ) = (0 : dirangle) :=
dirangle_eq_iff_two_pi_dvd_sub.2 ⟨1, by rw [sub_zero, int.cast_one, mul_one]⟩

@[simp] lemma neg_coe_pi : -(φ : dirangle) = φ :=
begin
  rw [←coe_neg, dirangle_eq_iff_two_pi_dvd_sub],
  use -1,
  simp [two_mul, sub_eq_add_neg]
end

@[simp] lemma two_nsmul_coe_div_two (θ : ℝ) : (2 : ℕ) • (↑(θ / 2) : dirangle) = θ :=
by rw [←coe_nsmul, two_nsmul, add_halves]

@[simp] lemma two_zsmul_coe_div_two (θ : ℝ) : (2 : ℤ) • (↑(θ / 2) : dirangle) = θ :=
by rw [←coe_zsmul, two_zsmul, add_halves]

@[simp] lemma two_nsmul_neg_pi_div_two : (2 : ℕ) • (↑(-φ / 2) : dirangle) = φ :=
by rw [two_nsmul_coe_div_two, coe_neg, neg_coe_pi]

@[simp] lemma two_zsmul_neg_pi_div_two : (2 : ℤ) • (↑(-φ / 2) : dirangle) = φ :=
by rw [two_zsmul, ←two_nsmul, two_nsmul_neg_pi_div_two]

lemma sub_coe_pi_eq_add_coe_pi (θ : dirangle) : θ - φ = θ + φ :=
by rw [sub_eq_add_neg, neg_coe_pi]

@[simp] lemma two_nsmul_coe_pi : (2 : ℕ) • (φ : dirangle) = 0 :=
by simp [←coe_nat_mul_eq_nsmul]

@[simp] lemma two_zsmul_coe_pi : (2 : ℤ) • (φ : dirangle) = 0 :=
by simp [←coe_int_mul_eq_zsmul]

@[simp] lemma coe_pi_add_coe_pi : (φ : real.dirangle) + φ = 0 :=
by rw [←two_nsmul, two_nsmul_coe_pi]

lemma zsmul_eq_iff {ψ θ : dirangle} {z : ℤ} (hz : z ≠ 0) :
  z • ψ = z • θ ↔ (∃ k : fin z.nat_abs, ψ = θ + (k : ℕ) • (2 * φ / z : ℝ)) :=
quotient_add_group.zmultiples_zsmul_eq_zsmul_iff hz

lemma nsmul_eq_iff {ψ θ : dirangle} {n : ℕ} (hz : n ≠ 0) :
  n • ψ = n • θ ↔ (∃ k : fin n, ψ = θ + (k : ℕ) • (2 * φ / n : ℝ)) :=
quotient_add_group.zmultiples_nsmul_eq_nsmul_iff hz

lemma two_zsmul_eq_iff {ψ θ : dirangle} : (2 : ℤ) • ψ = (2 : ℤ) • θ ↔ (ψ = θ ∨ ψ = θ + φ) :=
by rw [zsmul_eq_iff two_ne_zero, int.nat_abs_bit0, int.nat_abs_one,
    fin.exists_fin_two, fin.coe_zero, fin.coe_one, zero_smul, add_zero, one_smul,
    int.cast_two, mul_div_cancel_left (_ : ℝ) two_ne_zero]

lemma two_nsmul_eq_iff {ψ θ : dirangle} : (2 : ℕ) • ψ = (2 : ℕ) • θ ↔ (ψ = θ ∨ ψ = θ + φ) :=
by simp_rw [←coe_nat_zsmul, int.coe_nat_bit0, int.coe_nat_one, two_zsmul_eq_iff]

lemma two_nsmul_eq_zero_iff {θ : dirangle} : (2 : ℕ) • θ = 0 ↔ (θ = 0 ∨ θ = φ) :=
by convert two_nsmul_eq_iff; simp

lemma two_nsmul_ne_zero_iff {θ : dirangle} : (2 : ℕ) • θ ≠ 0 ↔ θ ≠ 0 ∧ θ ≠ φ :=
by rw [←not_or_distrib, ←two_nsmul_eq_zero_iff]

lemma two_zsmul_eq_zero_iff {θ : dirangle} : (2 : ℤ) • θ = 0 ↔ (θ = 0 ∨ θ = φ) :=
by simp_rw [two_zsmul, ←two_nsmul, two_nsmul_eq_zero_iff]

lemma two_zsmul_ne_zero_iff {θ : dirangle} : (2 : ℤ) • θ ≠ 0 ↔ θ ≠ 0 ∧ θ ≠ φ :=
by rw [←not_or_distrib, ←two_zsmul_eq_zero_iff]

lemma eq_neg_self_iff {θ : dirangle} : θ = -θ ↔ θ = 0 ∨ θ = φ :=
by rw [←add_eq_zero_iff_eq_neg, ←two_nsmul, two_nsmul_eq_zero_iff]

lemma ne_neg_self_iff {θ : dirangle} : θ ≠ -θ ↔ θ ≠ 0 ∧ θ ≠ φ :=
by rw [←not_or_distrib, ←eq_neg_self_iff.not]

lemma neg_eq_self_iff {θ : dirangle} : -θ = θ ↔ θ = 0 ∨ θ = φ :=
by rw [eq_comm, eq_neg_self_iff]

lemma neg_ne_self_iff {θ : dirangle} : -θ ≠ θ ↔ θ ≠ 0 ∧ θ ≠ φ :=
by rw [←not_or_distrib, ←neg_eq_self_iff.not]

lemma two_nsmul_eq_pi_iff {θ : dirangle} : (2 : ℕ) • θ = φ ↔ (θ = (φ / 2 : ℝ) ∨ θ = (-φ / 2 : ℝ)) :=
begin
  have h : (φ : dirangle) = (2 : ℕ) • (φ / 2 : ℝ), { rw [two_nsmul, ←coe_add, add_halves] },
  nth_rewrite 0 h,
  rw [two_nsmul_eq_iff],
  congr',
  rw [add_comm, ←coe_add, ←sub_eq_zero, ←coe_sub, add_sub_assoc, neg_div, sub_neg_eq_add,
      add_halves, ←two_mul, coe_two_pi]
end

lemma two_zsmul_eq_pi_iff {θ : dirangle} : (2 : ℤ) • θ = φ ↔ (θ = (φ / 2 : ℝ) ∨ θ = (-φ / 2 : ℝ)) :=
by rw [two_zsmul, ←two_nsmul, two_nsmul_eq_pi_iff]
end dirangle

end real
