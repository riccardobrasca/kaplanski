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

variable (R)

def primes := {r : R | prime r}

variable {R}

lemma unique_factorization_monoid_of_factorization
  (H : ∀ (r : R), r ≠ 0 → ¬(is_unit r) →  r ∈ submonoid.closure (primes R)) :
  unique_factorization_monoid R :=
begin
  apply unique_factorization_monoid.of_exists_prime_factors,
  intros a ha,
  specialize H a ha,
  by_cases  hu : is_unit a,
  { use ∅,
    split,
    { intros b hb,
      exfalso,
      simpa using hb },
    { simp,
      rw [associated.comm],
      exact associated_one_iff_is_unit.2 hu } },
  { specialize H hu,
    rcases submonoid.exists_multiset_of_mem_closure H with ⟨M, hM, hMprod⟩,
    use M,
    split,
    { intros b hb,
      exact hM b hb },
    { rw [hMprod], } }
end

lemma submonoid.closure_exists_multiset {x : R} (hx : x ∈ submonoid.closure (primes R)): (∃ (n : ℕ) (f : multiset R) (hf : f.card = n + 1), (∀ (y : R), y ∈ f → prime y) ∧ x = f.prod) ∨ x = 1 :=
begin
  apply submonoid.closure_induction hx _ _,

  rintro x y h₁ h₂,
  rcases h₁ with ⟨n, ⟨f₁, hf₁, ⟨hf₂, hf₃⟩⟩⟩,
  rcases h₂ with ⟨m, ⟨g₁, hg₁, ⟨hg₂, hg₃⟩⟩⟩,
  use n + m + 1,
  use f₁ + g₁,
  refine ⟨_, λ y hy, _, _⟩,
  rw [multiset.card_add _ _, hf₁, hg₁],
  ring,
  cases multiset.mem_add.1 hy with hy₁ hy₂,
  exact hf₂ y hy₁,
  exact hg₂ y hy₂,
  rw [multiset.prod_add _ _, hf₃, hg₃],

  left,
  rw [h₂, mul_one _],
  exact ⟨n, f₁, hf₁, hf₂, hf₃⟩,

  rw [h₁, one_mul _],
  rcases h₂ with ⟨m, ⟨g₁, hg₁, ⟨hg₂, hg₃⟩⟩⟩,
  left,
  exact ⟨m, g₁, hg₁, hg₂, hg₃⟩,
  right,
  exact h₂,

  rintro z hz,
  left,
  refine ⟨0, {z}, multiset.card_singleton _, λ y hy, _, eq.symm (multiset.prod_singleton _)⟩,
  rw ← multiset.mem_singleton.1 hy at hz,
  exact hz,

  right,
  refl,
end

theorem theo1_gauche (H : ∀ (I : ideal R) (hI : I ≠ 0) (hI₂ : I.is_prime), ∃ x ∈ I, prime x) :
  unique_factorization_monoid R :=
begin
  let S := submonoid.closure (primes R),
  have hzero : (0 : R) ∉ S,
  { suffices : ∀ s ∈ S, s ≠ (0 : R),
    { intro h,
      specialize this 0 h,
      contradiction },
    intros s hs,
    apply submonoid.closure_induction hs,
    { intros x hx,
      exact hx.ne_zero },
    { exact ne_zero.ne 1 },
    { intros x y hx hy,
      exact mul_ne_zero hx hy } },
  apply unique_factorization_monoid_of_factorization,
  intros a ha haunit,

  have ha₂ : ideal.span {a} ∉ foo S,
  by_contra,
  rcases prop_2 hzero with ⟨P, ⟨hP, hP₂⟩⟩,

  have hP₃ : P ≠ 0,
  by_contra h₂,

  have ha₂ : a ∈ ideal.span {a},
  rw ideal.mem_span_singleton',
  use 1,
  rw one_mul,

  rw [h₂, ideal.zero_eq_bot, ← ideal.span_zero] at hP₂,
  rw [((hP₂ (ideal.span {a}) h) ((ideal.span_singleton_le_iff_mem (ideal.span {a})).2 (ideal.zero_mem (ideal.span {a})))), ideal.span_zero] at ha₂,
  exact ha (ideal.mem_bot.1 ha₂),

  rcases ((H P) hP₃ (theo3 hP hP₂)) with ⟨x, ⟨H₃, H₄⟩⟩,
  have hx : x ∉ S,
  by_contra h₂,
  have h₃ : x ∈ (P : set R) ∩ S := ⟨(set_like.mem_coe.1 H₃), (set_like.mem_coe.1 h₂)⟩,
  rw (foo_def _ _).1 hP at h₃,
  exact (set.mem_empty_iff_false x).1 h₃,

  exact hx ((submonoid.closure_singleton_le_iff_mem _ _).1 (submonoid.closure_mono (set.singleton_subset_iff.2 H₄))),

  rw [foo_def, ← ne.def] at ha₂,
  rcases set.nonempty_iff_ne_empty.2 ha₂ with ⟨x, ⟨hx, hx₂⟩⟩,
  cases ideal.mem_span_singleton'.1 (set_like.mem_coe.1 hx) with b hb,
  rw ← hb at hx₂,

  cases submonoid.closure_exists_multiset hx₂ with hab hab₂,
  rcases hab with ⟨n, f, hf, ⟨hf₂, hab⟩⟩,
  induction n with d hd generalizing f b x,
  {
    rw zero_add at hf,
    cases multiset.card_eq_one.1 hf with y hy,
    rw [hy, multiset.prod_singleton _] at hab,
    rw hy at hf₂,
    specialize hf₂ y (multiset.mem_singleton_self _),
    have hf₃ := prime.irreducible hf₂,
    rw ← hab at hf₃,
    cases of_irreducible_mul hf₃,

    rw mul_comm _ _ at hab,
    have hab₂ : associated y (y * ring.inverse b),
    use ring.inverse b,
    exact b,
    exact ring.inverse_mul_cancel _ h,
    exact ring.mul_inverse_cancel _ h,
    refl,
    rw ← (ring.eq_mul_inverse_iff_mul_eq _ _ _ h).2 hab at hab₂,
    exact submonoid.subset_closure ((hab₂.prime_iff).1 hf₂),

    exfalso,
    exact haunit h,
  },
  {
    classical,
    by_cases h : ∃ (p : R), p ∈ f ∧ p ∣ b,

    rcases h with ⟨p, ⟨hp₁, hp₂⟩⟩,
    cases dvd_iff_exists_eq_mul_left.1 hp₂ with c hp₂,
    rw [hp₂, ← multiset.prod_erase hp₁, mul_comm c p, mul_assoc _ _ _] at hab,
    replace hab := is_domain.mul_left_cancel_of_ne_zero (prime.ne_zero (hf₂ p hp₁)) hab,
    have ha₃ : (f.erase p).prod ∈ (ideal.span {a}) :=
    begin
      rw ← hab,
      rw ideal.mem_span_singleton',
      use c,
    end,
    have ha₄ : c * a ∈ ↑S :=
    begin
      rw [submonoid.closure_eq_image_prod _, set.mem_image _ _ _],
      refine ⟨((f.erase p).to_list), set.mem_set_of.1 (λ y hy, hf₂ y (multiset.mem_of_le (f.erase_le p) (multiset.mem_to_list.1 hy))), _⟩,
      rw multiset.prod_to_list _,
      exact eq.symm hab,
    end,
    have ha₅ : multiset.card (f.erase p) = d + 1 := sorry,
    have ha₆ : ∀ (y : R), y ∈ f.erase p → prime y := λ y hy, hf₂ y ((multiset.mem_of_le (multiset.erase_le _ _)) hy),
    exact hd (f.erase p) c (f.erase p).prod ha₃ hab ha₄ ha₅ ha₆ hab,

    have ha₇ : f.prod ∣ a :=
    begin
      refine multiset.prod_primes_dvd _ hf₂ _ _,
      rintro p hp,
      sorry,
      sorry,
    end,
    sorry,
  },

  exfalso,
  rw mul_comm at hab₂,
  exact haunit (is_unit_of_mul_eq_one _ _ hab₂),
end

theorem theo1' : unique_factorization_monoid R ↔
  ∀ (I : ideal R) (hI : nontrivial I) (hI₂ : I.is_prime), ∃ (J : ideal R), nontrivial J ∧ J.is_prime ∧ submodule.is_principal (J : submodule R R) ∧ J ≤ I :=
begin
  classical,
  refine ⟨_, _⟩,
  { rintro h I hI hI₂,
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
