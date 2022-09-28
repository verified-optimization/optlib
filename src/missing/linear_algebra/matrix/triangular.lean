/-
Copyright (c) 2022 Alexander Bentkamp. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Bentkamp
-/
import missing.linear_algebra.matrix.block

/-
# Triangular Matrices
This file defines upper and lower triangular matrices. The definitions are based on
`matrix.block_triangular`. All properties should ideally be proved for `matrix.block_triangular` in
general and then specialized to (nonblock)-triangular matrices here.
-/

namespace matrix
open_locale big_operators
open_locale matrix
variables {α m n : Type*}
variables {R : Type*} [comm_ring R] {M N : matrix m m R}

/-- An upper triangular matrix is a matrix whose entries are zero below the diagonal. -/
def upper_triangular [has_lt m] (M : matrix m m R) :=
  M.block_triangular id

/-- A lower triangular matrix is a matrix whose entries are zero above the diagonal. -/
def lower_triangular [has_lt m] (M : matrix m m R) :=
  M.block_triangular order_dual.to_dual

/-- The inverse of an upper triangular matrix is upper triangular -/
lemma upper_triangular_inv_of_upper_triangular [fintype m] [linear_order m] [invertible M]
  (hM : upper_triangular M) : upper_triangular M⁻¹ :=
block_triangular_inv_of_block_triangular hM

/-- The inverse of a lower triangular matrix is lower triangular -/
lemma lower_triangular_inv_of_lower_triangular [fintype m] [linear_order m] [invertible M]
  (hM : lower_triangular M) : lower_triangular M⁻¹ :=
block_triangular_inv_of_block_triangular hM

/-- Multiplication of upper triangular matrices is upper triangular -/
lemma upper_triangular.mul [fintype m] [linear_order m]
  (hM : upper_triangular M) (hN : upper_triangular N) : upper_triangular (M ⬝ N) :=
block_triangular.mul hM hN

/-- Multiplication of lower triangular matrices is lower triangular -/
lemma lower_triangular.mul [fintype m] [linear_order m]
  (hM : lower_triangular M) (hN : lower_triangular N) : lower_triangular (M ⬝ N) :=
block_triangular.mul hM hN

/-- Transpose of lower triangular matrix is upper triangular -/
lemma lower_triangular.transpose [fintype m] [linear_order m]
  (hM : lower_triangular M) : upper_triangular Mᵀ :=
hM.transpose

/-- Transpose of upper triangular matrix is lower triangular -/
lemma upper_triangular.transpose [fintype m] [linear_order m]
  (hM : upper_triangular M) : lower_triangular Mᵀ :=
hM.transpose

lemma diag_inv_mul_diag_eq_one_of_upper_triangular [fintype m] [linear_order m] [invertible M]
  (hM : upper_triangular M) (k : m) : M⁻¹ k k * M k k = 1 :=
begin
  letI : unique {a // id a = k} := ⟨⟨⟨k, rfl⟩⟩, λ j, subtype.ext j.property⟩,
  simpa [matrix.mul, dot_product, fintype.sum_unique] using
    congr_fun (congr_fun (to_square_block_inv_mul_to_square_block_eq_one hM k) ⟨k, rfl⟩) ⟨k, rfl⟩,
end

lemma diag_inv_mul_diag_eq_one_of_lower_triangular [fintype m] [linear_order m] [invertible M]
  (hM : lower_triangular M) (k : m) : M⁻¹ k k * M k k = 1 :=
begin
  letI : unique {a // order_dual.to_dual a = k} := ⟨⟨⟨k, rfl⟩⟩, λ j, subtype.ext j.property⟩,
  simpa [matrix.mul, dot_product, fintype.sum_unique] using
    congr_fun (congr_fun (to_square_block_inv_mul_to_square_block_eq_one hM k) ⟨k, rfl⟩) ⟨k, rfl⟩,
end

end matrix
