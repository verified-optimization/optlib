import linear_algebra.matrix.spectrum

namespace linear_map

variables {𝕜 : Type*} [is_R_or_C 𝕜] [decidable_eq 𝕜]
variables {E : Type*} [inner_product_space 𝕜 E]
variables [finite_dimensional 𝕜 E]
variables {n : ℕ} (hn : finite_dimensional.finrank 𝕜 E = n)
variables {T : E →ₗ[𝕜] E}

-- TODO: move analysis.inner_product_space.spectrum
-- TODO: can be used to prove version 2.
/-- *Diagonalization theorem*, *spectral theorem*; version 3: A self-adjoint operator `T` on a
finite-dimensional inner product space `E` acts diagonally on the identification of `E` with
Euclidean space induced by an orthonormal basis of eigenvectors of `T`. -/
lemma spectral_theorem' (v : E) (i : fin n)
  (xs : orthonormal_basis (fin n) 𝕜 E) (as : fin n → ℝ)
  (hxs : ∀ j, module.End.has_eigenvector T (as j) (xs j)) :
  xs.repr (T v) i = as i * xs.repr v i :=
begin
  suffices : ∀ w : euclidean_space 𝕜 (fin n),
    T (xs.repr.symm w) = xs.repr.symm (λ i, as i * w i),
  { simpa only [linear_isometry_equiv.symm_apply_apply, linear_isometry_equiv.apply_symm_apply]
      using congr_arg (λ (v : E), (xs.repr) v i) (this ((xs.repr) v)) },
  intros w,
  simp_rw [← orthonormal_basis.sum_repr_symm, linear_map.map_sum,
    linear_map.map_smul, λ j, module.End.mem_eigenspace_iff.mp (hxs j).1, smul_smul, mul_comm]
end

end linear_map
