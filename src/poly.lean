import ring_theory.nilpotent
import data.polynomial.erase_lead
import data.polynomial.eval
import algebra.geom_sum
import data.polynomial.lifts

variables {R : Type*} [comm_ring R]

open_locale polynomial big_operators

open finset

theorem is_unit_of_is_nilpotent_sub_one {r : R} (hnil : is_nilpotent r) :
  is_unit (r - 1) :=
begin
  obtain ⟨n, hn⟩ := hnil,
  rw [is_unit_iff_exists_inv],
  use -(∑ i in range n, r ^ i),
  rw [mul_neg, mul_comm, geom_sum_mul, hn],
  simp
end

theorem is_unit_of_is_unit_add_is_nilpotent {u r : R} (hu : is_unit u) (hnil : is_nilpotent r) :
  is_unit (u + r) :=
begin
  obtain ⟨v, hv⟩ := is_unit.exists_right_inv hu,
  suffices : is_unit (v * (u + r)),
  { exact is_unit_of_mul_is_unit_right this },
  rw [mul_add, mul_comm v u, hv],
  replace hnil : is_nilpotent (-v * r),
  { rw [← mem_nilradical] at ⊢ hnil,
    exact (nilradical R).mul_mem_left (-v) hnil },
  rw [← is_unit.neg_iff, neg_add, add_comm, ← sub_eq_add_neg, ← neg_mul],
  exact is_unit_of_is_nilpotent_sub_one hnil
end

namespace polynomial

theorem is_nilpotent.C_mul_X_pow {r : R} (n : ℕ) (hnil : is_nilpotent r) :
  is_nilpotent ((C r) * X ^ n) :=
begin
  have hCnil : is_nilpotent (C r) := is_nilpotent.map hnil C,
  apply commute.is_nilpotent_mul_left,
  { exact commute.all (C r) (X ^ n) },
  { assumption }
end

theorem is_unit_of_is_unit_of_is_nilpotent {P : R[X]} (hunit : is_unit (P.coeff 0))
  (hnil : ∀ i ≠ 0, is_nilpotent (P.coeff i)) : is_unit P :=
begin
  induction h : P.nat_degree using nat.strong_induction_on with k hind generalizing P,
  by_cases hdeg : P.nat_degree = 0,
  { have hCunit : is_unit (C (P.coeff 0)) := is_unit.map C hunit,
    rw polynomial.eq_C_of_nat_degree_eq_zero hdeg,
    apply hCunit },
  let P₁ := P.erase_lead,
  suffices : is_unit P₁,
  { rw [← erase_lead_add_monomial_nat_degree_leading_coeff P],
    apply is_unit_of_is_unit_add_is_nilpotent this _,
    rw [← C_mul_X_pow_eq_monomial],
    apply is_nilpotent.C_mul_X_pow,
    apply hnil,
    exact hdeg },
  have hdegk : P₁.nat_degree < k,
  { rw [← h],
    apply lt_of_le_of_lt (erase_lead_nat_degree_le P),
    rw [← nat.pred_eq_sub_one],
    exact nat.pred_lt hdeg },
  have hP₁unit : is_unit (P₁.coeff 0),
  { rw [erase_lead_coeff_of_ne],
    { exact hunit },
    { intro h,
      exact hdeg h.symm } },
  have hP₁nilpotent : ∀ i ≠ 0, is_nilpotent (P₁.coeff i),
  { intros i hi,
    by_cases H : i ≤ P₁.nat_degree,
    { rw [erase_lead_coeff_of_ne],
      { exact hnil i hi },
      { linarith } },
    { rw [coeff_eq_zero_of_nat_degree_lt],
      { exact is_nilpotent.zero },
      { linarith } }},
  exact hind _ hdegk hP₁unit hP₁nilpotent rfl,
end

theorem is_unit.coeff {P : R[X]} (hunit : is_unit P) :
  is_unit (P.coeff 0) ∧ (∀ i ≠ 0, is_nilpotent (P.coeff i)) :=
begin
  obtain ⟨Q, hQ⟩ := is_unit.exists_right_inv hunit,
  split,
  { let V := P * Q, --let u := polynomial.constant_coeff (V),
    have v1 : polynomial.constant_coeff (P * Q) = 1,
    { rw hQ,
      rw polynomial.constant_coeff_apply, simp },
    suffices : (polynomial.constant_coeff (P)) * (polynomial.constant_coeff (Q)) = 1,
    { exact is_unit_of_mul_eq_one (coeff P 0) (constant_coeff Q) this },
    simp at v1, simp, apply v1 },
  { intros n hn,
    rw [nilpotent_iff_mem_prime],
    intros I hI,
    let f := polynomial.map_ring_hom (ideal.quotient.mk I),
    have hPQ : (f P) * (f Q) = 1,
    { rw [← map_mul, hQ, map_one] },
    replace hPQ := congr_arg degree hPQ,
    haveI : is_domain (R ⧸ I),
    { rw [ideal.quotient.is_domain_iff_prime],
      exact hI },
    simp only [nat.with_bot.add_eq_zero_iff, degree_mul, degree_one] at hPQ,
    have hcoeff : (f P).coeff n = 0,
    { apply polynomial.coeff_eq_zero_of_degree_lt,
      rw [hPQ.1, with_bot.coe_pos],
      exact ne.bot_lt hn },
    rw [coe_map_ring_hom, polynomial.coeff_map, ← ring_hom.mem_ker, ideal.mk_ker] at hcoeff,
    exact hcoeff }
end

theorem is_unit_iff (P : R[X]) : is_unit P ↔
  is_unit (P.coeff 0) ∧ (∀ i ≠ 0, is_nilpotent (P.coeff i)) :=
begin
  split,
  { intro hunit,
    exact is_unit.coeff hunit },
  { intro H,
    exact is_unit_of_is_unit_of_is_nilpotent H.1 H.2 }
end

end polynomial
