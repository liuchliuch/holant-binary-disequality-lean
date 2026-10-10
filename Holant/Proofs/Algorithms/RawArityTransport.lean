import Holant.Complexity.BinaryCompose.OutputBound
import Holant.Complexity.ClosedNetworkSemantics
import Holant.Complexity.FixedFieldMachines.PairEncoding
import Holant.Kernel


namespace Holant.LocalDrafts.MainChain.RawArityTransport
open Computability Holant.Complexity Holant.Complexity.BinaryCompose
open Holant.Complexity.FixedFieldMachines
noncomputable section
variable {s b : ℕ} {a c : ℕ → ℕ} (h : ∀ i : Fin s, a i.val=c i.val)

include h in
theorem wellFormed_iff (r : RawClosedNetwork) : r.WellFormed s b a ↔ r.WellFormed s b c := by
  constructor
  · rintro ⟨hv,he,hp⟩
    refine ⟨fun v => ⟨(hv v).1,?_⟩,he,hp⟩
    exact (hv v).2.trans (h ⟨_,(hv v).1⟩)
  · rintro ⟨hv,he,hp⟩
    refine ⟨fun v => ⟨(hv v).1,?_⟩,he,hp⟩
    exact (hv v).2.trans (h ⟨_,(hv v).1⟩).symm

def input (r : {r : RawClosedNetwork // r.WellFormed s b a}) :
    {r : RawClosedNetwork // r.WellFormed s b c} := ⟨r.val,(wellFormed_iff h r.val).mp r.property⟩

def computes : Computes (RawClosedNetwork.validatedEncoding s b a)
    (RawClosedNetwork.validatedEncoding s b c) (input h) := by
  apply recode (identityComputes (RawClosedNetwork.validatedEncoding s b a)) id (fun _ => rfl)
  intro r
  rfl

def signatures {K : Type*} (G : (i : Fin s) → Signature K (a i.val)) :
    (i : Fin s) → Signature K (c i.val) := fun i x => G i (fun j => x (Fin.cast (h i) j))

theorem route_same (r : RawClosedNetwork) (ha : r.WellFormed s b a)
    (hc : r.WellFormed s b c) (v : Fin r.vertices.length)
    (j : Fin (a (r.vertices.get v).1)) :
    r.route hc ⟨v,Fin.cast (h (r.signatureLabel ha v)) j⟩=r.route ha ⟨v,j⟩ := by
  apply Prod.ext
  · apply Fin.ext
    rfl
  · rfl

theorem denote {K : Type*} [CommSemiring K]
    (G : (i : Fin s) → Signature K (a i.val)) (E : Fin b → Kernel K)
    (r : {r : RawClosedNetwork // r.WellFormed s b a}) :
    ((input h r).val.realize (input h r).property (signatures h G) E).denote Fin.elim0=
      (r.val.realize r.property G E).denote Fin.elim0 := by
  simp only [Network.denote,RawClosedNetwork.realize,NetworkShape.assignment,
    RawClosedNetwork.shape_ports,Sum.elim_inr]
  apply Finset.sum_congr rfl
  intro z _
  apply congrArg₂ (· * ·)
  · apply Finset.prod_congr rfl
    intro v _
    change G (r.val.signatureLabel r.property v)
      (fun j => z (r.val.route (input h r).property
        ⟨v,Fin.cast (h (r.val.signatureLabel r.property v)) j⟩)) =
      G (r.val.signatureLabel r.property v) (fun j => z (r.val.route r.property ⟨v,j⟩))
    congr 1
  · rfl

end
end Holant.LocalDrafts.MainChain.RawArityTransport
