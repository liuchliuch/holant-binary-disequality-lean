import Holant.Projective.FiniteGroupFacts.Conjugacy
import Holant.Certificates.PlatonicBridgeInterface.ProjectiveGroup

/-! Transport to the literal sixty projective classes of complex icosahedral
matrices, whose group law was already proved to be induced by matrix product. -/
namespace Holant.Projective.FiniteGroupFacts
open Holant.Certificates.PlatonicBridgeInterface

noncomputable section

/-- Element-order fibers are invariant under a genuine group isomorphism. -/
def orderFiberEquiv {G H : Type*} [Group G] [Group H] (e : G ≃* H) (n : ℕ) :
    {g : G // orderOf g = n} ≃ {h : H // orderOf h = n} where
  toFun g := ⟨e g, by simpa using g.property⟩
  invFun h := ⟨e.symm h, by simpa using h.property⟩
  left_inv g := Subtype.ext (e.symm_apply_apply _)
  right_inv h := Subtype.ext (e.apply_symm_apply _)

theorem actual_icosahedral_simple : IsSimpleGroup ProjectiveClass := by
  have : IsSimpleGroup A5 := a5_simple
  exact projective_iso_A5.isSimpleGroup

theorem actual_icosahedral_no_index_two (H : Subgroup ProjectiveClass) : H.index ≠ 2 := by
  have h := a5_no_index_two (H.map projective_iso_A5.toMonoidHom)
  rwa [Subgroup.index_map_of_bijective projective_iso_A5.bijective] at h

theorem actual_icosahedral_orders (g : ProjectiveClass) :
    orderOf g = 1 ∨ orderOf g = 2 ∨ orderOf g = 3 ∨ orderOf g = 5 := by
  simpa using a5_orders_exhaustive (projective_iso_A5 g)

theorem actual_icosahedral_order_distribution :
    Nat.card {g : ProjectiveClass // orderOf g = 1} = 1 ∧
    Nat.card {g : ProjectiveClass // orderOf g = 2} = 15 ∧
    Nat.card {g : ProjectiveClass // orderOf g = 3} = 20 ∧
    Nat.card {g : ProjectiveClass // orderOf g = 4} = 0 ∧
    Nat.card {g : ProjectiveClass // orderOf g = 5} = 24 := by
  have he (n : ℕ) (hn : 0 < n) :
      Nat.card {g : ProjectiveClass // orderOf g = n} = orderCount A5 n := by
    rw [Nat.card_congr (orderFiberEquiv projective_iso_A5 n), Nat.card_eq_fintype_card,
      ← orderCount_eq n hn]
  simpa only [he 1 (by omega), he 2 (by omega), he 3 (by omega), he 4 (by omega),
    he 5 (by omega)] using a5_order_distribution

theorem actual_icosahedral_involutions_one_class (g h : ProjectiveClass)
    (hg : Involution g) (hh : Involution h) : IsConj g h := by
  have hi (x : ProjectiveClass) (hx : Involution x) : Involution (projective_iso_A5 x) := by
    rw [involution_iff_orderOf, projective_iso_A5.orderOf_eq]
    exact (involution_iff_orderOf x).mp hx
  obtain ⟨c, hc⟩ := isConj_iff.mp
    (a5_involutions_one_class _ _ (hi g hg) (hi h hh))
  rw [isConj_iff]
  refine ⟨projective_iso_A5.symm c, projective_iso_A5.injective ?_⟩
  simpa using hc

theorem actual_icosahedral_involution_centralizer (g : ProjectiveClass) (hg : Involution g) :
    IsKleinFour (Subgroup.centralizer {g}) := by
  have hi : Involution (projective_iso_A5 g) := by
    rw [involution_iff_orderOf, projective_iso_A5.orderOf_eq]
    exact (involution_iff_orderOf g).mp hg
  have hk := a5_involution_centralizer_kleinFour _ hi
  let e := centralizerEquiv projective_iso_A5 g
  exact ⟨(Nat.card_congr e.toEquiv).trans hk.card_four,
    (Monoid.exponent_eq_of_mulEquiv e).trans hk.exponent_two⟩

end
end Holant.Projective.FiniteGroupFacts
