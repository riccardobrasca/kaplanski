import algebra.module.submodule.lattice
import ring_theory.ideal.basic
import ring_theory.ideal.operations
import data.set.basic
import ring_theory.unique_factorization_domain
import ring_theory.principal_ideal_domain

variables {R : Type*} [comm_ring R] (S : submonoid R)

def foo := {I : ideal R | (I : set R) ∩ S = ∅}

lemma foo_def (P : ideal R) : P ∈ foo S ↔ (P : set R) ∩ S = ∅ :=
iff.rfl

variables {P : ideal R} {S} (hP : P ∈ foo S) (hmax : ∀ I ∈ foo S, P ≤ I → P = I)

section basic

theorem P_neq_top (hP : P ∈ foo S) : P ≠ ⊤ :=
begin
  intro h,
  have h₂ : 1 ∈ (P : set R) ∩ S := ⟨(ideal.eq_top_iff_one _).1 h, submonoid.one_mem _⟩,
  exact (λ h₄, (set.eq_empty_iff_forall_not_mem.1 h₄) 1 h₂) hP,
end

include hmax

lemma gt_inter {I : ideal R} (h : P < I) : (I : set R) ∩ S ≠ ∅ := λ h₂, (lt_iff_le_and_ne.1 h).2 ((hmax I) h₂ (lt_iff_le_and_ne.1 h).1)

include hP

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
    refine gt_inter hmax (lt_of_le_of_ne' le_sup_left _),
    intro hI,
    rw [← hI, ← ideal.span_singleton_le_iff_mem _] at h',
    exact h' le_sup_right,
  end,

  have h₂ : (J : set R) ∩ S ≠ ∅ :=
  begin
    refine gt_inter hmax (lt_of_le_of_ne' le_sup_left _),
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

theorem theo3 : P.is_prime :=
begin
  fconstructor,
  refine P_neq_top hP,
  apply mem_or_mem',
  exact hP,
  exact hmax,
end

end basic

section existence

lemma condition_Zorns_lemma (C : set (ideal R)) (hC : C ⊆ foo S)
  (hC₂ : is_chain (≤) C) (I : ideal R) (hI : I ∈ C) :
  (∃ (P : ideal R) (H : P ∈ foo S), ∀ (J : ideal R), J ∈ C → J ≤ P) :=
begin
  refine ⟨Sup C, _, λ z hz, le_Sup hz⟩,
  by_contra,
  rw [foo_def, ← set.not_nonempty_iff_eq_empty] at h,
  push_neg at h,
  rcases h with ⟨x, hx₁, hx₂⟩,
  rcases (submodule.mem_Sup_of_directed ⟨_, hI⟩ hC₂.directed_on).1 hx₁ with ⟨J, hJ₁, hJ₂⟩,
  have hx₄ : (J : set R) ∩ S ≠ ∅,
  { rw [← set.nonempty_iff_ne_empty],
    exact ⟨x, hJ₂, hx₂⟩ },
  exact hx₄ (hC hJ₁),
end

lemma prop_2 (hS : (0 : R) ∉ S) : ∃ P ∈ foo S,  ∀ I ∈ foo S, P ≤ I → I = P :=
begin
  set x : ideal R := 0 with hx,
  have hx : x ∈ foo S,
  { rw [foo_def, set.eq_empty_iff_forall_not_mem],
    rintro y ⟨hy₁, hy₂⟩,
    rw [hx, set_like.mem_coe, ideal.zero_eq_bot, ideal.mem_bot] at hy₁,
    rw hy₁ at hy₂,
    exact hS hy₂ },
  rcases zorn_nonempty_partial_order₀ (foo S) condition_Zorns_lemma x hx with
    ⟨J, ⟨hJ, ⟨hJ₂, hJ₃⟩⟩⟩,
  exact ⟨J, hJ, hJ₃⟩,
end

end existence

section Kaplansky

variables [is_domain R]

lemma multiset.prod_mem_ideal [unique_factorization_monoid R] {I : ideal R} (s : multiset R) (hI : I.is_prime) : s.prod ∈ I ↔ ∃ (p : R) (H : p ∈ s), p ∈ I :=
begin
  classical,
  split,
  { intro hs,
    by_contra,
    push_neg at h,

    have hs₃ : s.prod ∉ I,
    refine multiset.prod_induction _ _ _ _ h,
    { rintro a b ha hb,
      by_contra,
      cases ((ideal.is_prime_iff.1 hI).2) h with hI₂ hI₃,
      exact ha hI₂,
      exact hb hI₃, },
    exact λ h₂, (ideal.is_prime_iff.1 hI).1 ((ideal.eq_top_iff_one _).2 h₂),

    exact hs₃ hs, },
  { intro hs,
    rcases hs with ⟨p, ⟨hs₂, hs₃⟩⟩,
    rw ← multiset.prod_erase hs₂,
    exact ideal.mul_mem_right _ _ hs₃, },
end

theorem theo1_droite [unique_factorization_monoid R] {I : ideal R} (hI : nontrivial I) (hI₂ : I.is_prime) :
  ∃ x ∈ I, prime x :=
begin
  classical,
  have ha : ∃ (a : R), a ∈ I ∧ a ≠ 0,
  cases exists_ne (0 : I) with y hI₃,
  refine ⟨y, y.2, _⟩,
  rw [ne.def, subtype.ext_iff_val] at hI₃,
  exact hI₃,

  rcases ha with ⟨a, ⟨ha₁, ha₂⟩⟩,
  cases (unique_factorization_monoid.factors_prod ha₂) with u ha₃,
  rw ← ha₃ at ha₁,
  cases ((ideal.is_prime.mem_or_mem hI₂) ha₁) with ha₄ ha₅,
  { rcases ((multiset.prod_mem_ideal (unique_factorization_monoid.factors a) hI₂).1 ha₄) with ⟨p, ⟨ha₅, ha₆⟩⟩,
    refine ⟨p, ha₆, unique_factorization_monoid.prime_of_factor p ha₅⟩, },
  { exfalso,
    exact (ideal.is_prime_iff.1 hI₂).1 (ideal.eq_top_of_is_unit_mem _ ha₅ (units.is_unit u)), },
end

theorem theo1_gauche (H : ∀ (I : ideal R) (hI : I ≠ 0) (hI₂ : I.is_prime), ∃ x ∈ I, prime x) :
  unique_factorization_monoid R :=
begin
  sorry
end

theorem theo1' : unique_factorization_monoid R ↔
  ∀ (I : ideal R) (hI : nontrivial I) (hI₂ : I.is_prime), ∃ (J : ideal R), nontrivial J ∧ J.is_prime ∧ submodule.is_principal (J : submodule R R) ∧ J ≤ I :=
begin
  classical,
  refine ⟨_, _⟩,
  { introI h,
    rintro I hI hI₂,
    resetI,

    have ha : ∃ (a : R), a ∈ I ∧ a ≠ 0,
    cases exists_ne (0 : I) with y hI₃,
    refine ⟨y, y.2, _⟩,
    rw [ne.def, subtype.ext_iff_val] at hI₃,
    exact hI₃,

    rcases ha with ⟨a, ⟨ha₁, ha₂⟩⟩,
    cases (unique_factorization_monoid.factors_prod ha₂) with u ha₃,
    rw ← ha₃ at ha₁,
    cases ((ideal.is_prime.mem_or_mem hI₂) ha₁) with ha₄ ha₅,
    { rcases ((multiset.prod_mem_ideal (unique_factorization_monoid.factors a) hI₂).1 ha₄) with ⟨p, ⟨ha₅, ha₆⟩⟩,

      have ha₇ := (unique_factorization_monoid.prime_of_factor p) ha₅,
      have ha₈ := prime.ne_zero ha₇,

      refine ⟨ideal.span {p}, _, (ideal.span_singleton_prime ha₈).2 ha₇, (submodule.is_principal_iff _).2 ⟨p, eq.symm ideal.submodule_span_eq⟩, (ideal.span_singleton_le_iff_mem _).2 ha₆⟩,

      rw nontrivial_iff,
      refine ⟨⟨(0 : R), ideal.zero_mem (ideal.span {p})⟩, ⟨p, ideal.mem_span_singleton_self _⟩, _⟩,
      rw [ne.def, subtype.mk_eq_mk],
      exact ne.symm ha₈, },
    { exfalso,
      exact (ideal.is_prime_iff.1 hI₂).1 (ideal.eq_top_of_is_unit_mem _ ha₅ (units.is_unit u)), },
  },
  {
    sorry
  }
end

end Kaplansky
