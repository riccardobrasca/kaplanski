import algebra.module.submodule.lattice
import ring_theory.ideal.basic
import ring_theory.ideal.operations
import data.set.basic

variables {R : Type*} [comm_ring R] (S : submonoid R)

def foo := {I : ideal R | (I : set R) ∩ S = ∅}

lemma foo_def (P : ideal R) : P ∈ foo S ↔ (P : set R) ∩ S = ∅ :=
iff.rfl

variables {P : ideal R} {S} (hP : P ∈ foo S) (hmax : ∀ I ∈ foo S, P ≤ I → P = I)

include hP hmax

theorem P_neq_top : P ≠ ⊤ :=
begin
  intro h,
  have h₂ : 1 ∈ (P : set R) ∩ S := ⟨(ideal.eq_top_iff_one _).1 h, submonoid.one_mem _⟩,
  exact (λ h₄, (set.eq_empty_iff_forall_not_mem.1 h₄) 1 h₂) hP,
end

lemma gt_inter {I : ideal R} (h : P < I) : (I : set R) ∩ S ≠ ∅ := λ h₂, (lt_iff_le_and_ne.1 h).2 ((hmax I) h₂ (lt_iff_le_and_ne.1 h).1)

theorem mem_or_mem' : ∀ {x y : R}, x * y ∈ P → x ∈ P ∨ y ∈ P :=
begin
  rintro x y hxy,
  by_contra,
  push_neg at h,
  cases h with h' h'',
  let I := P ⊔ ideal.span {x},
  let J := P ⊔ ideal.span {y},

  have h₁ : (I : set R) ∩ S ≠ ∅ :=
  begin
    refine gt_inter hP hmax (lt_of_le_of_ne' le_sup_left _),
    intro hI,
    rw [← hI, ← ideal.span_singleton_le_iff_mem _] at h',
    exact h' le_sup_right,
  end,

  have h₂ : (J : set R) ∩ S ≠ ∅ :=
  begin
    refine gt_inter hP hmax (lt_of_le_of_ne' le_sup_left _),
    intro hJ,
    rw [← hJ, ← ideal.span_singleton_le_iff_mem _] at h'',
    exact h'' le_sup_right,
  end,

  rcases (set.inter_nonempty.1 (set.nonempty_iff_ne_empty.2 h₁)) with ⟨s, ⟨h₅, h₆⟩⟩,
  rcases (set.inter_nonempty.1 (set.nonempty_iff_ne_empty.2 h₂)) with ⟨t, ⟨h₇, h₈⟩⟩,

  have h₉ : s*t ∈ I*J := ideal.mul_mem_mul h₅ h₇,
  rw [ideal.mul_sup _ _ _, ideal.sup_mul _ _ _, ideal.sup_mul _ _ _] at h₉,

  have h₁₀ : ideal.span {x} * ideal.span {y} ≤ P :=
  begin
    refine ideal.span_singleton_mul_le_iff.2 (λ z hz, _),
    cases (ideal.mem_span_singleton'.1 hz) with a ha,
    rw [← ha, ← mul_assoc _ _ _, mul_comm x a, mul_assoc _ _ _],
    exact ideal.mul_mem_left _ _ hxy,
  end,

  have h₁₁ : P * P ⊔ ideal.span {x} * P ⊔ (P * ideal.span {y} ⊔ ideal.span {x} * ideal.span {y}) ≤ P := sup_le (sup_le ideal.mul_le_right ideal.mul_le_left) (sup_le ideal.mul_le_right h₁₀),

  have h₁₂ : s*t ∈ (P : set R) ∩ S := set.mem_inter (h₁₁ h₉) (submonoid.mul_mem S h₆ h₈),

  have h₁₃ : (P : set R) ∩ S ≠ ∅ := λ h₁₄, ((set.eq_empty_iff_forall_not_mem.1 h₁₄) (s*t)) h₁₂,

  contradiction,
end

theorem theo3 {x y : R} (h : x * y ∈ P) : P.is_prime :=
begin
  fconstructor,
  refine P_neq_top hP hmax,
  apply mem_or_mem',
  exact hP,
  exact hmax,
end

section existence

omit hP hmax

lemma condition_Zorns_lemma (C : set (ideal R)) (hC : C ⊆ foo S) (hC₂ : is_chain (≤) C) :
  ∃ (P : ideal R) (H : P ∈ foo S), ∀ (z : ideal R), z ∈ C → z ≤ P :=
begin
  let f : C → ideal R := λ J, J,
  let I : ideal R := supr f,
  use I,
  split,
  { by_contra,
    rw [foo_def, ← set.not_nonempty_iff_eq_empty] at h,
    push_neg at h,
    rcases h with ⟨x, ⟨hx₁, hx₂⟩⟩,

    have hx₃ : ∃ J ∈ C, x ∈ J :=
    begin
      haveI : nonempty C := sorry,
      rw [set_like.mem_coe, submodule.mem_supr_of_directed] at hx₁,
      { obtain ⟨⟨J, hJmem⟩, hJ⟩ := hx₁,
        exact ⟨J, hJmem, hJ⟩ },
      { rw [← directed_on_iff_directed],
        refine is_chain.directed_on hC₂ }
    end,
    rcases hx₃ with ⟨J, ⟨hJ₁, hJ₂⟩⟩,

    have hx₄ : (J : set R) ∩ S ≠ ∅ :=
    begin
      rw [← set.nonempty_iff_ne_empty, set.inter_nonempty],
      use x,
      refine ⟨hJ₂, hx₂⟩,
    end,

    have hx₅ : J ∈ foo S := hC hJ₁,

    contradiction, },
  { rintro z hz,

    have hz₂ : set.range f = C :=
    begin
      refine subset_antisymm _ _,
      { intro x,
        unfold set.range,
        rw set.mem_set_of,
        intro hx,
        cases hx with y hy,
        have hy₂ : (y : ideal R) ∈ C :=
        begin
          sorry,
        end,
        have hy₃ : f y = y := rfl,
        rw [← hy₃, hy] at hy₂,
        exact hy₂, },
      { rintro x hx,
        unfold set.range,
        rw set.mem_set_of,
        use x,
        exact hx,
        constructor, },
    end,

    have hz₃ : z ≤ I ↔ ∀ (y : R), y ∈ z → y ∈ I :=
    begin
      split,
      { rintro hz₄ y,
        rw ← hz₂ at hz,
        exact ideal.mem_Sup_of_mem hz, },
      { rw set_like.coe_subset_coe.symm,
        rintro hy y,
        exact hy y, },
    end,

    rw hz₃,
    intro y,
    rw ← hz₂ at hz,
    exact ideal.mem_Sup_of_mem hz, },
end

lemma prop_2 : ∃ P ∈ foo S,  ∀ I ∈ foo S, P ≤ I → P = I :=
begin
  obtain ⟨I, hImem, hI⟩ := zorn_preorder₀ (foo S) (condition_Zorns_lemma),
  exact ⟨I, ⟨hImem, λ J hJ hJI, le_antisymm hJI (hI J hJ hJI)⟩⟩,
end

end existence
