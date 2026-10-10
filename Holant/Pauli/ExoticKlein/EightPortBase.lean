import Holant.Pauli.ExoticKlein.EightPortPermutation
import Holant.Pauli.ExoticKlein.FiberTheorem

/-! Full eight-port base from actual pair safety. The permutation-fiber form
is derived from the original tensor by full fixed ruling and fiber dichotomy;
no stipulated normal form remains in the public theorem hypotheses. -/
namespace Holant.Pauli.ExoticKlein
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace MatchingCard

theorem eight_port_factor_of_pairSafe (f : Signature ℂ 8) (hf : f ≠ 0) (hs : PairSafe f) :
    Fiber.HasProperTensorFactor f := by
  by_contra hp
  obtain ⟨s,M,weight,labels,hfirst,he,hzero,hsize⟩ :=
    common_full_fiber 1 (by decide) f hf ((pairSafe_iff_ordered f).mp hs)
  have hcard := M.port_card
  simp only [Fintype.card_fin] at hcard
  have hs3 : s = 3 := by omega
  subst s
  have hsafe : PairSafe (Fiber.tensor M weight labels) := by rwa [←he]
  have hnonzero : Fiber.tensor M weight labels ≠ 0 := by rwa [←he]
  have hprime : ¬ Fiber.HasProperTensorFactor (Fiber.tensor M weight labels) := by rwa [←he]
  obtain ⟨hw,hbij⟩ := Fiber.dichotomy M (by decide) weight labels 0 hfirst hsafe hnonzero hprime
  let perms : Fin 4 → Equiv.Perm Label := fun e => Equiv.ofBijective (fun a => labels a e) (hbij e)
  exact Fiber.permutation_fiber_obstruction M weight perms hfirst hw hsafe

end MatchingCard
end
end Holant.Pauli.ExoticKlein
