import algebra.module.submodule.lattice
import ring_theory.ideal.basic
import ring_theory.ideal.operations
import data.set.basic
import ring_theory.unique_factorization_domain
import ring_theory.principal_ideal_domain
import absorbing

variables {R : Type*} [comm_ring R] (S : submonoid R)

/-- Explication -/
def foo := {I : ideal R | (I : set R) ∩ S = ∅}

lemma foo_def (P : ideal R) : P ∈ foo S ↔ (P : set R) ∩ S = ∅ :=
iff.rfl

variables {P : ideal R} {S} (hP : P ∈ foo S) (hmax : ∀ I ∈ foo S, P ≤ I → I = P)

section basic

theorem P_neq_top (hP : P ∈ foo S) : P ≠ ⊤ := λ h, ((set.disjoint_left.1 (set.disjoint_iff_inter_eq_empty.2 ((foo_def _ _).1 hP))) (P.eq_top_iff_one.1 h)) S.one_mem

include hmax

lemma gt_inter {I : ideal R} (h : P < I) : ∃ (x : R), x ∈ (I : set R) ∩ S := set.inter_nonempty.1 (set.nonempty_iff_ne_empty.2 (λ h₂, (lt_iff_le_and_ne.1 h).2 (eq.symm ((hmax I) h₂ (lt_iff_le_and_ne.1 h).1))))

include hP

theorem mem_or_mem' : ∀ {x y : R}, x * y ∈ P → x ∈ P ∨ y ∈ P :=
begin
  rintro x y hxy,
  by_contra,
  push_neg at h,
  cases h with h' h'',
  let I := P ⊔ ideal.span {x},
  let J := P ⊔ ideal.span {y},

  have h₁ : ∃ (x : R), x ∈ (I : set R) ∩ S :=
  begin
    refine gt_inter hmax (lt_of_le_of_ne' le_sup_left _),
    intro hI,
    rw [← hI, ← ideal.span_singleton_le_iff_mem _] at h',
    exact h' le_sup_right,
  end,

  have h₂ : ∃ (x : R), x ∈ (J : set R) ∩ S :=
  begin
    refine gt_inter hmax (lt_of_le_of_ne' le_sup_left _),
    intro hJ,
    rw [← hJ, ← ideal.span_singleton_le_iff_mem _] at h'',
    exact h'' le_sup_right,
  end,

  rcases ⟨h₁, h₂⟩ with ⟨⟨s, ⟨hs, hs'⟩⟩, ⟨t, ⟨ht, ht'⟩⟩⟩,

  have h₃ : I*J ≤ P :=
  begin
    rw [ideal.mul_sup _ _ _, ideal.sup_mul _ _ _, ideal.sup_mul _ _ _, ideal.span_singleton_mul_span_singleton],
    exact sup_le (sup_le ideal.mul_le_right ideal.mul_le_left) (sup_le ideal.mul_le_right ((ideal.span_singleton_le_iff_mem _).2 hxy)),
  end,

  exact set.eq_empty_iff_forall_not_mem.1 hP (s*t) ⟨h₃ (ideal.mul_mem_mul hs ht), S.mul_mem hs' ht'⟩,
end

theorem theo3 : P.is_prime := ⟨P_neq_top hP, λ x y, mem_or_mem' hP hmax⟩

end basic

section existence

lemma condition_Zorns_lemma (C : set (ideal R)) (hC : C ⊆ foo S)
  (hC₂ : is_chain (≤) C) (I : ideal R) (hI : I ∈ C) :
  (∃ (P : ideal R) (H : P ∈ foo S), ∀ (J : ideal R), J ∈ C → J ≤ P) :=
begin
  refine ⟨Sup C, _, λ z hz, le_Sup hz⟩,
  rw [foo_def, set.eq_empty_iff_forall_not_mem],
  rintro x hx,
  rcases (submodule.mem_Sup_of_directed ⟨_, hI⟩ hC₂.directed_on).1 hx.1 with ⟨J, hJ₁, hJ₂⟩,
  have hx₂ : (J : set R) ∩ S ≠ ∅ := set.nonempty_iff_ne_empty.1 ⟨x, hJ₂, hx.2⟩,
  exact hx₂ (hC hJ₁),
end

lemma prop_2 (hS : (0 : R) ∉ S) : ∃ P ∈ foo S,  ∀ I ∈ foo S, P ≤ I → I = P :=
begin
  have hx : (0 : ideal R) ∈ foo S,
  { rw [foo_def, set.eq_empty_iff_forall_not_mem],
    rintro y ⟨hy₁, hy₂⟩,
    rw [set_like.mem_coe, ideal.zero_eq_bot, ideal.mem_bot] at hy₁,
    rw hy₁ at hy₂,
    exact hS hy₂ },
  rcases zorn_nonempty_partial_order₀ _ condition_Zorns_lemma 0 hx with
    ⟨J, ⟨hJ, ⟨hJ₂, hJ₃⟩⟩⟩,
  exact ⟨J, hJ, hJ₃⟩,
end

end existence

section Kaplansky

lemma multiset.prod_mem_ideal {I : ideal R} (s : multiset R) (hI : I.is_prime) : s.prod ∈ I ↔ ∃ (p : R) (H : p ∈ s), p ∈ I :=
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

variable (R)

/-- The set of prime elements. -/
def primes := {r : R | prime r}

variables [is_domain R]

variable {R}

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

variable (R)

lemma primes_mem_mul : (submonoid.closure (primes R)).absorbing :=
begin
  classical,
  rw [submonoid.absorbing_iff_of_comm],
  intros a b hab,
  obtain ⟨m, hm⟩ := submonoid.exists_multiset_of_mem_closure hab,
  revert hm a b,
  apply m.strong_induction_on,

  rintros s hind b a hab ⟨hprime, hprod⟩,
  rcases s.empty_or_exists_mem with (hempty | ⟨i, hi⟩),
  { simp [hempty] at hprod,
    exact ⟨1, submonoid.one_mem _, associated_one_of_mul_eq_one _ hprod.symm⟩ },

  rw [← multiset.prod_erase hi] at hprod,
  rcases (hprime i hi).dvd_or_dvd ⟨(s.erase i).prod, hprod.symm⟩ with (⟨x, hxb⟩ | ⟨x, hxa⟩),

  { suffices : ∃ z ∈ submonoid.closure (primes R), associated x z,
    { obtain ⟨z, hz, hzx⟩ := this,
      refine ⟨z * i, submonoid.mul_mem _ hz (submonoid.subset_closure (hprime _ hi)), _⟩,
      rw [hxb, mul_comm z i],
      exact associated.mul_left i hzx },

    rw [hxb, mul_assoc] at hprod,
    replace hprod := (is_domain.mul_left_cancel_of_ne_zero (hprime _ hi).ne_zero hprod),

    have hxamem : x * a ∈ submonoid.closure (primes R),
    { rw [← hprod],
      exact submonoid.multiset_prod_mem _ _ (λ x hx, submonoid.subset_closure (hprime _ (multiset.erase_subset _ _ hx))) },

    exact hind (s.erase i) (multiset.erase_lt.2 hi) _ _ hxamem ⟨λ y hy, hprime y ((s.erase_subset _) hy), hprod⟩ },

  { rw [hxa, ← mul_assoc, mul_comm b i, mul_assoc] at hprod,
    replace hprod := (is_domain.mul_left_cancel_of_ne_zero (hprime i hi).ne_zero hprod),

    have hbxmem : b * x ∈ submonoid.closure (primes R),
    { rw [← hprod],
      exact submonoid.multiset_prod_mem _ _ (λ x hx, submonoid.subset_closure (hprime _ (multiset.erase_subset _ _ hx))) },

    exact hind (s.erase i) (multiset.erase_lt.2 hi) _ _ hbxmem ⟨λ y hy, hprime y ((s.erase_subset _) hy), hprod⟩ },
end

variable {R}

theorem theo1_gauche (H : ∀ (I : ideal R) (hI : I ≠ 0) (hI₂ : I.is_prime), ∃ x ∈ I, prime x) :
  unique_factorization_monoid R :=
begin
  let S := submonoid.closure (primes R),
  have hzero : (0 : R) ∉ S,
  intro h,
  rcases (submonoid.exists_multiset_of_mem_closure h) with ⟨l, ⟨hl, hprod⟩⟩,
  exact not_prime_zero (hl 0 (multiset.prod_eq_zero_iff.1 hprod)),

  refine unique_factorization_monoid.of_exists_prime_factors (λ a ha, _),

  have ha₂ : ideal.span {a} ∉ foo S,
  { intro h,
    rcases prop_2 hzero with ⟨P, ⟨hP, hP₂⟩⟩,
    have hP₃ : P ≠ 0,
    { intro h₂,
      rw [h₂, ideal.zero_eq_bot] at hP₂,
      exact ha (ideal.span_singleton_eq_bot.1 (hP₂ (ideal.span {a}) h (zero_le (ideal.span {a})))) },
    rcases ((H P) hP₃ (theo3 hP hP₂)) with ⟨x, ⟨H₃, H₄⟩⟩,
    rw [foo_def, set.eq_empty_iff_forall_not_mem] at hP,
    exact hP x ⟨H₃, (submonoid.subset_closure H₄)⟩ },

  rw [foo_def, ← ne.def] at ha₂,
  rcases set.nonempty_iff_ne_empty.2 ha₂ with ⟨x, ⟨hx, hx₂⟩⟩,
  cases ideal.mem_span_singleton'.1 (set_like.mem_coe.1 hx) with b hb,
  rw [← hb, mul_comm] at hx₂,

  obtain ⟨z, hzmem, hass⟩ := (submonoid.absorbing_iff_of_comm.1 (primes_mem_mul _) _ _ hx₂),
  obtain ⟨m, hprime, hprod⟩ := submonoid.exists_multiset_of_mem_closure hzmem,
  refine ⟨m, hprime, _⟩,
  rwa [hprod, associated.comm],
end

end Kaplansky
