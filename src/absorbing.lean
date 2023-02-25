import group_theory.submonoid.basic
import algebra.divisibility.basic
import group_theory.submonoid.membership
import algebra.associated

namespace submonoid

variables {M : Type*} [comm_monoid M]

def absorbing (S : submonoid M) : Prop :=
  ∀ x y, x * y ∈ S → ∃ z ∈ S, associated x z ∧ ∃ z ∈ S, associated y z

section basic

lemma absorbing_def {S : submonoid M} :
  absorbing S ↔ ∀ x y, x * y ∈ S → ∃ z ∈ S, associated x z ∧ ∃ z ∈ S, associated y z :=
iff.rfl

variable (M)

lemma top_absorbing : (⊤ : submonoid M).absorbing := λ x y hxy, ⟨x, submonoid.mem_top _, associated.refl _, y, submonoid.mem_top _, associated.refl _⟩

lemma bot_absorbing : (⊥ : submonoid M).absorbing := λ x y hxy, ⟨1, (⊥ : submonoid M).one_mem, associated_one_of_mul_eq_one _ (submonoid.mem_bot.1 hxy), 1, (⊥ : submonoid M).one_mem, associated_one_of_mul_eq_one _ (submonoid.mem_bot.1 (by rwa mul_comm at hxy))⟩

lemma is_unit.submonoid_absorbing : (is_unit.submonoid M).absorbing := λ x y hxy, ⟨x, is_unit_of_mul_is_unit_left hxy, associated.refl _, y, is_unit_of_mul_is_unit_right hxy, associated.refl _⟩

end basic

section comm_monoid

lemma absorbing_iff_of_comm {S : submonoid M} :
  absorbing S ↔ ∀ x y, x * y ∈ S → ∃ z ∈ S, associated x z :=
begin
  refine ⟨_, _⟩,

  { rintro hS x y hxy,
    rcases (hS x y hxy) with ⟨z, hz, hz₂, hS⟩,
    exact ⟨z, hz, hz₂⟩ },

  {
    rintro h x y hxy,
    obtain ⟨z, hz, hz₂⟩ := (h x y hxy),
    refine ⟨z, hz, hz₂, _⟩,

    rw mul_comm at hxy,
    exact (h y x hxy) },
end

end comm_monoid

end submonoid
