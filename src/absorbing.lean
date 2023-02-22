import group_theory.subsemigroup.basic
import algebra.divisibility.basic
import group_theory.submonoid.membership
import algebra.associated

namespace submonoid

variables {M : Type*} [monoid M]

def absorbing (S : submonoid M) : Prop :=
  ∀ x y, x * y ∈ S → ∃ z ∈ S, associated x z ∧ ∃ z ∈ S, associated y z

section basic

lemma absorbing_def {S : submonoid M} :
  absorbing S ↔ ∀ x y, x * y ∈ S → ∃ z ∈ S, associated x z ∧ ∃ z ∈ S, associated y z :=
iff.rfl

variable (M)

lemma top_absorbing : (⊤ : submonoid M).absorbing := sorry

lemma bot_absorbing : (⊥ : submonoid M).absorbing := sorry

end basic

section comm_monoid

lemma absorbing_iff_of_comm {S : submonoid M} :
  absorbing S ↔ ∀ x y, x * y ∈ S → ∃ z ∈ S, associated x z := sorry

end comm_monoid

end submonoid
