import linear_algebra.eigenspace
import tactic.linear_combination

universes u v w
namespace module
namespace End

variables {K R : Type v} {V M : Type w}
  [comm_ring R] [add_comm_group M] [module R M] [field K] [add_comm_group V] [module K V]

lemma eigenspace_add {f g : End R M} {a b : R} :
  eigenspace f a ⊓ eigenspace g b ≤ eigenspace (f + g) (a + b) :=
begin
  rintros x ⟨hf, hg⟩,
  simp only [eigenspace, set_like.mem_coe, linear_map.mem_ker, linear_map.sub_apply,
    algebra_map_End_apply] at hf hg,
  simp only [eigenspace, map_add, linear_map.mem_ker, linear_map.sub_apply, linear_map.add_apply,
    algebra_map_End_apply],
  rw [←add_sub, add_comm (a • x), ←sub_sub, hg, add_sub, add_zero, hf],
end

lemma eigenspace_one : eigenspace (1 : End R M) 1 = ⊤ :=
begin
  apply eq_top_iff.2,
  intros x _,
  simp only [mem_eigenspace_iff, linear_map.one_apply, one_smul],
end

lemma has_eigenvector_add {f g : End R M} {a b : R} {x : M}
    (hf : has_eigenvector f a x) (hg : has_eigenvector g b x):
  has_eigenvector (f + g) (a + b) x :=
⟨eigenspace_add ⟨hf.1, hg.1⟩, hf.2⟩

lemma has_eigenvector_one {x : M} (hx : x ≠ 0) : has_eigenvector (1 : End R M) 1 x :=
⟨by { rw eigenspace_one, apply submodule.mem_top }, hx⟩

end End
end module
