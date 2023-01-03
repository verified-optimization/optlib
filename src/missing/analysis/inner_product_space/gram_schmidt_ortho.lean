import analysis.inner_product_space.gram_schmidt_ortho

section gram_schmidt

variables (𝕜 : Type*) {E : Type*} [is_R_or_C 𝕜] [inner_product_space 𝕜 E]
variables {ι : Type*} [linear_order ι] [locally_finite_order_bot ι] [is_well_order ι (<)]

local attribute [instance] is_well_order.to_has_well_founded

local notation `⟪`x`, `y`⟫` := @inner 𝕜 _ _ x y

lemma repr_gram_schmidt_diagonal {i : ι} (b : basis ι 𝕜 E) :
  b.repr (gram_schmidt 𝕜 b i) i = 1 :=
begin
  rw [gram_schmidt_def, linear_equiv.map_sub, finsupp.sub_apply, basis.repr_self,
    finsupp.single_eq_same, sub_eq_self, linear_equiv.map_sum, finsupp.coe_finset_sum,
    finset.sum_apply, finset.sum_eq_zero],
  intros j hj,
  rw finset.mem_Iio at hj,
  simp [orthogonal_projection_singleton, gram_schmidt_triangular hj],
end

end gram_schmidt
