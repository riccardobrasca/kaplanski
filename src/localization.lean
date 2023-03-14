import kaplanski
import ring_theory.localization.ideal

example {R S : Type*} [comm_ring R] [comm_ring S] [algebra R S] [is_domain R] {M : submonoid R}
  [is_localization M S] (hM : M ≤ non_zero_divisors R) : is_domain S :=
is_localization.is_domain_of_le_non_zero_divisors _ hM

example {R : Type*} [comm_ring R] [is_domain R] : cancel_comm_monoid_with_zero R :=
begin
  refine is_domain.to_cancel_comm_monoid_with_zero,
end

example {R S : Type*} [comm_ring R] [comm_ring S] [algebra R S] [is_domain R] {M : submonoid R}
  [is_localization M S] (hM : M ≤ non_zero_divisors R) [unique_factorization_monoid R] :
  @unique_factorization_monoid S (@is_domain.to_cancel_comm_monoid_with_zero S _
    (is_localization.is_domain_of_le_non_zero_divisors _ hM)) :=
begin
  haveI : is_domain S := is_localization.is_domain_of_le_non_zero_divisors _ hM,
  refine theo1_gauche (λ J hJzero hJprime, _),
  set I := J.comap (algebra_map R S) with Idef,
  have hIprime : I.is_prime := ((is_localization.is_prime_iff_is_prime_disjoint M S J).1 hJprime).1,
  have hI : I ≠ ⊥,
  { intro h,
    refine hJzero _,
    rw [← is_localization.map_comap M S J, ← Idef, h, ideal.map_bot] },
  obtain ⟨p, hpI, hp⟩ := theo1_droite hI hIprime,
  refine ⟨algebra_map R S p, ideal.mem_comap.mp hpI, _⟩,
  have hpzero : algebra_map R S p ≠ 0 :=
    (map_ne_zero_iff (algebra_map R S) (is_localization.injective S hM)).2 hp.ne_zero,
  rw [← ideal.span_singleton_prime hpzero, ← set.image_singleton, ← ideal.map_span],
  refine is_localization.is_prime_of_is_prime_disjoint M S _
    ((ideal.span_singleton_prime hp.ne_zero).2 hp) _,
  refine set.disjoint_of_subset_right _
    (((is_localization.is_prime_iff_is_prime_disjoint M S J).1 hJprime).2),
  simp only [set_like.coe_subset_coe],
  exact (ideal.span_singleton_le_iff_mem _).2 hpI,
end
