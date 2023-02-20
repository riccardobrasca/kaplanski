import ring_theory.nilpotent
import data.polynomial.erase_lead

variables {R : Type*} [comm_ring R]

open_locale polynomial big_operators

theorem is_unit_of_is_unit_add_is_nilpotent {u r : R} (hu : is_unit u) (hnil : is_nilpotent r) :
  is_unit (u + r) :=
begin
sorry
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
  {
    sorry
  },
  let P₁ := P.erase_lead,
  suffices : is_unit P₁,
  { sorry },
  have hdeg : P₁.nat_degree < k,
  { rw [← h],
    sorry /-ça doit être dans mathlib-/ },
  have hP₁unit : is_unit (P₁.coeff 0),
  {
    sorry
  },
  have hP₁nilpotent : ∀ i ≠ 0, is_nilpotent (P₁.coeff i),
  { --par disjonction de cas, si i ≤ P₁.nat_degree le coeff est le même
    sorry
  },
  exact hind _ hdeg hP₁unit hP₁nilpotent rfl,
  --have hCunit : is_unit (C (P.coeff 0)) := is_unit.map C hunit,
end

theorem is_unit.coeff {P : R[X]} (hunit : is_unit P) :
  is_unit (P.coeff 0) ∧ (∀ i ≠ 0, is_nilpotent (P.coeff i)) :=
begin
  sorry
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
