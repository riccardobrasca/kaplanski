import algebra.module.submodule.lattice
import ring_theory.ideal.basic
import ring_theory.ideal.operations
import data.set.basic

variables (R : Type*) [comm_ring R] (S : submonoid R)

def foo := {I : ideal R | (I : set R) ∩ S = ∅}

lemma foo_def (P : ideal R) : P ∈ foo R S ↔ (P : set R) ∩ S = ∅ :=
iff.rfl

example : preorder (foo R S) :=
begin
  apply_instance
end

variables (P : ideal R) (hP : P ∈ foo R S) (hmax : ∀ I ∈ foo R S, P ≤ I → P = I)

include hP hmax

theorem P_neq_top : P ≠ ⊤ :=
begin
  intro h,
  rw foo_def at hP,

  have h₂ : 1 ∈ (P : set R) ∩ S :=
  begin
    rw set.mem_inter_iff _ _ _,
    split,
    {
      rw ideal.eq_top_iff_one at h,
      exact h,
    },
    {
      exact submonoid.one_mem S,
    },
  end,

  have h₃ : (P : set R) ∩ S ≠ ∅ := 
  begin
    intro h₄,
    rw set.eq_empty_iff_forall_not_mem at h₄,
    specialize h₄ 1,
    contradiction,
  end,

  contradiction,
end

lemma gt_inter_S {I : ideal R} {h : P < I} : (I : set R) ∩ S ≠ ∅ :=
begin
  intro h₂,
  specialize hmax I,
  rw ← foo_def at h₂, 
  rw lt_iff_le_and_ne at h,
  cases h with h₃ h₄,
  have hmax₂ := hmax h₂ h₃,
  contradiction,
end

-- Already in the library (I don't know how to update the version of mathlib on my computer)
theorem ideal.span_singleton_le_iff_mem (I : ideal R) {x : R} :
ideal.span {x} ≤ I ↔ x ∈ I := submodule.span_singleton_le_iff_mem _ _
theorem set.nonempty_iff_ne_empty {s : set R} :
s.nonempty ↔ s ≠ ∅ := set.not_nonempty_iff_eq_empty.not_right

-----------------------

theorem mem_or_mem' : ∀ {x y : R}, x * y ∈ P → x ∈ P ∨ y ∈ P :=
begin
  rintro x y hxy,
  by_contra,
  push_neg at h,
  cases h with h' h'',
  let I := P ⊔ ideal.span {x},
  let J := P ⊔ ideal.span {y},

  have h₁ : P < I :=
  begin
    refine lt_of_le_of_ne' le_sup_left _,
    intro hI,
    apply h',
    rw [← hI, ← ideal.span_singleton_le_iff_mem _],
    exact le_sup_right,
    exact hP,
    exact hmax,
  end,

  have h₂ : P < J :=
  begin
    refine lt_of_le_of_ne' le_sup_left _, 
    intro hJ,
    apply h'',
    rw [← hJ, ← ideal.span_singleton_le_iff_mem _],
    exact le_sup_right,
    exact hP,
    exact hmax,
  end,

  have h₃ : (I : set R) ∩ S ≠ ∅ := 
  begin
    refine gt_inter_S R S P hP hmax,
    exact h₁,
  end,

  have h₄ : (J : set R) ∩ S ≠ ∅ :=
  begin
    refine gt_inter_S R S P hP hmax,
    exact h₂,
  end,

  rw [← set.nonempty_iff_ne_empty, set.inter_nonempty] at h₃,
  rw [← set.nonempty_iff_ne_empty, set.inter_nonempty] at h₄,
  rcases h₃ with ⟨s, ⟨h₅, h₆⟩⟩,
  rcases h₄ with ⟨t, ⟨h₇, h₈⟩⟩,

  have h₉ : s*t ∈ I*J := ideal.mul_mem_mul h₅ h₇,
  rw [ideal.mul_sup _ _ _, ideal.sup_mul _ _ _, ideal.sup_mul _ _ _] at h₉,
    
  have h₁₀ : ideal.span {x} * ideal.span {y} ≤ P :=
  begin
    rw ideal.span_singleton_mul_le_iff,
    rintro z hz,
    rw ideal.mem_span_singleton' at hz,
    cases hz with a ha,
    rw [← ha, ← mul_assoc x a y, mul_comm x a, mul_assoc a x y],
    exact ideal.mul_mem_left P a hxy,
  end,

  have h₁₁ : P * P ⊔ ideal.span {x} * P ⊔ (P * ideal.span {y} ⊔ ideal.span {x} * ideal.span {y}) ≤ P := sup_le (sup_le ideal.mul_le_right ideal.mul_le_left) (sup_le ideal.mul_le_right h₁₀),
  
  have h₁₂ : s*t ∈ (P : set R) ∩ S := set.mem_inter (h₁₁ h₉) (submonoid.mul_mem S h₆ h₈),

  have h₁₃ : (P : set R) ∩ S ≠ ∅ :=
  begin
    intro h₁₄,
    rw set.eq_empty_iff_forall_not_mem at h₁₄,
    specialize h₁₄ (s*t),
    contradiction,
  end,

  contradiction,
  exact hP,
  exact hmax,
  exact hP,
  exact hmax,
end

theorem theo3 {x y : R} (h : x * y ∈ P) : P.is_prime :=
begin
  fconstructor,
  {
    refine P_neq_top R S P hP hmax,
  },
  {
   apply mem_or_mem',
   exact hP,
   exact hmax,
  },
end