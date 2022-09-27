import linear_algebra.matrix.ldl
import linear_algebra.matrix.block
import missing.analysis.inner_product_space.gram_schmidt_ortho

variables {𝕜 : Type*} [is_R_or_C 𝕜]
variables {n : Type*} [linear_order n] [is_well_order n (<)] [locally_finite_order_bot n]

local notation `⟪`x`, `y`⟫` :=
@inner 𝕜 (n → 𝕜) (pi_Lp.inner_product_space (λ _, 𝕜)).to_has_inner x y

open matrix
open_locale matrix

variables {S : matrix n n 𝕜} [fintype n] (hS : S.pos_def)

@[simp] lemma LDL.lower_inv_diagonal (i : n) :
  LDL.lower_inv hS i i = 1 :=
begin
  rw [LDL.lower_inv_eq_gram_schmidt_basis, basis.to_matrix],
  simpa only [gram_schmidt_basis, basis.coe_mk]
    using @repr_gram_schmidt_diagonal 𝕜 (n → 𝕜) _
      (inner_product_space.of_matrix hS.transpose) n _ _ _ i (pi.basis_fun 𝕜 n)
end

@[simp] lemma LDL.det_lower_inv :
  (LDL.lower_inv hS).det = 1 :=
begin
  rw [det_of_lower_triangular (LDL.lower_inv hS) (by apply LDL.lower_inv_triangular),
    finset.prod_eq_one],
  intros,
  rw LDL.lower_inv_diagonal,
end

@[simp] lemma LDL.det_lower :
  (LDL.lower hS).det = 1 :=
by simp [LDL.lower]
