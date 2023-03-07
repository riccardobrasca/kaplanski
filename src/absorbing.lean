import group_theory.submonoid.basic
import algebra.divisibility.basic
import group_theory.submonoid.membership
import algebra.associated

namespace submonoid

variables {M N : Type*} [comm_monoid M] [comm_monoid N]

def absorbing (S : submonoid M) : Prop :=
  ∀ x y, x * y ∈ S → ∃ z ∈ S, associated x z ∧ ∃ z ∈ S, associated y z

section basic

lemma absorbing_def {S : submonoid M} :
  absorbing S ↔ ∀ x y, x * y ∈ S → ∃ z ∈ S, associated x z ∧ ∃ z ∈ S, associated y z :=
iff.rfl

variable (M)
variable (N)

lemma top_absorbing : (⊤ : submonoid M).absorbing :=
  λ x y hxy, ⟨x, submonoid.mem_top _, associated.refl _, y, submonoid.mem_top _, associated.refl _⟩

lemma bot_absorbing : (⊥ : submonoid M).absorbing :=
  λ x y hxy, ⟨1, (⊥ : submonoid M).one_mem,
  associated_one_of_mul_eq_one _ (submonoid.mem_bot.1 hxy), 1, (⊥ : submonoid M).one_mem,
  associated_one_of_mul_eq_one _ (submonoid.mem_bot.1 (by rwa mul_comm at hxy))⟩

lemma is_unit.submonoid_absorbing : (is_unit.submonoid M).absorbing :=
  λ x y hxy, ⟨x, is_unit_of_mul_is_unit_left hxy, associated.refl _,
  y, is_unit_of_mul_is_unit_right hxy, associated.refl _⟩

lemma associated.prod (x z : M × N) : associated x z ↔ associated x.1 z.1 ∧ associated x.2 z.2 :=
begin
  refine ⟨_, λ ⟨⟨u₁, hu₁⟩, ⟨u₂, hu₂⟩⟩, ⟨mul_equiv.prod_units.inv_fun (u₁, u₂),
  prod.eq_iff_fst_eq_snd_eq.2 ⟨hu₁, hu₂⟩⟩⟩,

  rintro ⟨u, hu⟩,
  cases u.is_unit.exists_right_inv with b hb,
  rw [prod.mul_def, prod.mk_eq_one] at hb,
  rw [← hu, prod.fst_mul, prod.snd_mul],
  refine ⟨(associated_mul_is_unit_right_iff (is_unit_of_mul_eq_one _ _ hb.1)).2 (associated.refl _),
  (associated_mul_is_unit_right_iff (is_unit_of_mul_eq_one _ _ hb.2)).2 (associated.refl _)⟩,
end

lemma submonoid.prod_absorbing (s : submonoid M) (t : submonoid N) :
  (s.prod t).absorbing ↔ absorbing s ∧ absorbing t :=
begin
  refine ⟨_, _⟩,
  { intro h,
    refine ⟨_, _⟩,
    { rintro x y hxy,
      specialize h (x,1) (y,1),
      rw prod.mk_one_mul_mk_one at h,
      rcases (h (submonoid.mem_prod.2 ⟨hxy, t.one_mem⟩)) with ⟨a, ha, ha₂, ⟨b, hb, hb₂⟩⟩,
      exact ⟨a.1, (submonoid.mem_prod.1 ha).1, ((associated.prod _ _ _ _).1 ha₂).1,
      b.1, (submonoid.mem_prod.1 hb).1, ((associated.prod _ _ _ _).1 hb₂).1⟩ },
    { rintro x y hxy,
      specialize h (1,x) (1,y),
      rw prod.one_mk_mul_one_mk at h,
      rcases (h (submonoid.mem_prod.2 ⟨s.one_mem, hxy⟩)) with ⟨a, ha, ha₂, ⟨b, hb, hb₂⟩⟩,
      exact ⟨a.2, (submonoid.mem_prod.1 ha).2, ((associated.prod _ _ _ _).1 ha₂).2,
      b.2, (submonoid.mem_prod.1 hb).2, ((associated.prod _ _ _ _).1 hb₂).2⟩ } },

  { rintro ⟨hs, ht⟩ x y hxy,
    rcases (hs x.1 y.1 hxy.1) with ⟨z, hz, hz₂, ⟨z', hz', hz'₂⟩⟩,
    rcases (ht x.2 y.2 hxy.2) with ⟨w, hw, hw₂, ⟨w', hw', hw'₂⟩⟩,
    exact ⟨(z,w), submonoid.mem_prod.2 ⟨hz, hw⟩, (associated.prod _ _ _ _).2 ⟨hz₂, hw₂⟩,
    (z',w'), submonoid.mem_prod.2 ⟨hz', hw'⟩, (associated.prod _ _ _ _).2 ⟨hz'₂, hw'₂⟩⟩ },
end

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
