import Holant.Dihedral.EndpointSaturation.Coefficients

/-! Endpoint-support saturation from the literal aligned complementary-axis
coefficient data of the remaining branch. No full support, affine coset,
matching-code equality or self-duality is an input. -/
noncomputable section
namespace Holant.Dihedral.EndpointSaturation
open Holant Holant.Dihedral.EndpointParallelogram Holant.ReedMuller.LowArity
set_option backward.isDefEq.respectTransparency false
variable {K : Type*} [Field K] {r n : ℕ}

/-- The already classified C/C branch in coefficients: one original matching,
one common designated edge, fixed monomial parities, and four nonzero
complementary endpoint coordinates. Fixed weights may even differ between
endpoints; requiring common coefficient lines is unnecessary for saturation. -/
structure EndpointProducts (q : Signature K (n+2)) (order : Equiv.Perm (Fin (n+2))) where
  ports : (Fin r × Bool) ≃ Fin n
  varying : Fin r
  parity : Fin r → ZMod 2
  weights : Bool → Bool → Fin r → Bool → K
  weights_ne_zero : ∀ a b j,j ≠ varying → ∀ z,weights a b j z ≠ 0
  coefficient : Bool → Bool → K
  coefficient_ne_zero : ∀ a b,coefficient a b ≠ 0
  evenLeft : ZMod 2
  evenRight : ZMod 2
  oddLeft : ZMod 2
  oddRight : ZMod 2
  first_even : slice q order false false=fun x =>
    endpointProduct ports varying parity (weights false false) (coefficient false false)
      evenLeft evenRight ((bitsEquiv (Fin n)).symm x)
  second_even : slice q order true true=fun x =>
    endpointProduct ports varying parity (weights true true) (coefficient true true)
      (evenLeft+1) (evenRight+1) ((bitsEquiv (Fin n)).symm x)
  first_odd : slice q order false true=fun x =>
    endpointProduct ports varying parity (weights false true) (coefficient false true)
      oddLeft oddRight ((bitsEquiv (Fin n)).symm x)
  second_odd : slice q order true false=fun x =>
    endpointProduct ports varying parity (weights true false) (coefficient true false)
      (oddLeft+1) (oddRight+1) ((bitsEquiv (Fin n)).symm x)

 def EndpointProducts.L {q : Signature K (n+2)} {o : Equiv.Perm (Fin (n+2))}
    (D : EndpointProducts (r:=r) q o) : BinaryCode n := fixedCode D.ports D.varying
 def EndpointProducts.a00 {q : Signature K (n+2)} {o : Equiv.Perm (Fin (n+2))}
    (D : EndpointProducts (r:=r) q o) : BinaryVector n :=
  endpointOffset D.ports D.varying D.parity D.evenLeft D.evenRight
 def EndpointProducts.a11 {q : Signature K (n+2)} {o : Equiv.Perm (Fin (n+2))}
    (D : EndpointProducts (r:=r) q o) : BinaryVector n :=
  endpointOffset D.ports D.varying D.parity (D.evenLeft+1) (D.evenRight+1)
 def EndpointProducts.a01 {q : Signature K (n+2)} {o : Equiv.Perm (Fin (n+2))}
    (D : EndpointProducts (r:=r) q o) : BinaryVector n :=
  endpointOffset D.ports D.varying D.parity D.oddLeft D.oddRight
 def EndpointProducts.a10 {q : Signature K (n+2)} {o : Equiv.Perm (Fin (n+2))}
    (D : EndpointProducts (r:=r) q o) : BinaryVector n :=
  endpointOffset D.ports D.varying D.parity (D.oddLeft+1) (D.oddRight+1)

 theorem EndpointProducts.full_slices {q : Signature K (n+2)} {o : Equiv.Perm (Fin (n+2))}
    (D : EndpointProducts (r:=r) q o) :
    fullCoset (slice q o false false) D.L D.a00 ∧
    fullCoset (slice q o false true) D.L D.a01 ∧
    fullCoset (slice q o true false) D.L D.a10 ∧
    fullCoset (slice q o true true) D.L D.a11 := by
  refine ⟨?_,?_,?_,?_⟩
  · rw [D.first_even]
    exact endpointProduct_full _ _ _ _ _ _ _ (D.weights_ne_zero false false) (D.coefficient_ne_zero false false)
  · rw [D.first_odd]
    exact endpointProduct_full _ _ _ _ _ _ _ (D.weights_ne_zero false true) (D.coefficient_ne_zero false true)
  · rw [D.second_odd]
    exact endpointProduct_full _ _ _ _ _ _ _ (D.weights_ne_zero true false) (D.coefficient_ne_zero true false)
  · rw [D.second_even]
    exact endpointProduct_full _ _ _ _ _ _ _ (D.weights_ne_zero true true) (D.coefficient_ne_zero true true)

/-- The exact source endpoint displacements, parallelogram, and matching
extension are all derived on this one original residual coordinate set. -/
 theorem EndpointProducts.directions {q : Signature K (n+2)} {o : Equiv.Perm (Fin (n+2))}
    (D : EndpointProducts (r:=r) q o) :
    D.a00+D.a11 ∉ D.L ∧ D.a01+D.a10 ∉ D.L ∧
    extension D.L (D.a00+D.a11)=(Pairing.ofPorts D.ports).code ∧
    extension D.L (D.a01+D.a10)=(Pairing.ofPorts D.ports).code ∧
    D.a00+D.a01+D.a10+D.a11 ∈ D.L ∧ SelfDual (Pairing.ofPorts D.ports).code :=
  complementary_extensions D.ports D.varying D.parity D.evenLeft D.evenRight D.oddLeft D.oddRight

/-- **Source Lemma 6.16**, algebraic saturation with actual original-port card
sums and representative scalars. Its remaining-branch coefficient interface
is explicit, and every asserted nonzero support word is proved from a product
of nonzero entries. -/
 theorem source_endpoint_support_saturation {q : Signature K (n+2)}
    {o : Equiv.Perm (Fin (n+2))} (D : EndpointProducts (r:=r) q o) :
    fullCoset (slice q o false false) D.L D.a00 ∧
    fullCoset (slice q o false true) D.L D.a01 ∧
    fullCoset (slice q o true false) D.L D.a10 ∧
    fullCoset (slice q o true true) D.L D.a11 ∧
    D.a00+D.a11 ∉ D.L ∧ D.a01+D.a10 ∉ D.L ∧
    extension D.L (D.a00+D.a11)=(Pairing.ofPorts D.ports).code ∧
    extension D.L (D.a01+D.a10)=(Pairing.ofPorts D.ports).code ∧
    D.a00+D.a01+D.a10+D.a11 ∈ D.L ∧
    SelfDual (Pairing.ofPorts D.ports).code ∧
    ∀ t κ : K,t ≠ 0 → κ ≠ 0 →
      CardMatching (card q o false t κ) (Pairing.ofPorts D.ports) D.a00 ∧
      CardMatching (card q o true t κ) (Pairing.ofPorts D.ports) D.a01 ∧
      card q o false t κ ≠ 0 ∧ card q o true t κ ≠ 0 := by
  obtain ⟨h00,h01,h10,h11⟩ := D.full_slices
  obtain ⟨he,ho,hME,hMO,hpar,hdual⟩ := D.directions
  refine ⟨h00,h01,h10,h11,he,ho,hME,hMO,hpar,hdual,?_⟩
  intro t κ ht hκ
  have hE : CardMatching (card q o false t κ) (Pairing.ofPorts D.ports) D.a00 := by
    intro x
    change card q o false t κ ((bitsEquiv (Fin n)).symm x) ≠ 0 ↔ _
    rw [card_even,←hME]
    exact pencil_support D.L D.a00 D.a11 _ _ h00 h11 he t κ ht hκ x
  have hO : CardMatching (card q o true t κ) (Pairing.ofPorts D.ports) D.a01 := by
    intro x
    change card q o true t κ ((bitsEquiv (Fin n)).symm x) ≠ 0 ↔ _
    rw [card_odd,←hMO]
    exact pencil_support D.L D.a01 D.a10 _ _ h01 h10 ho t κ ht hκ x
  refine ⟨hE,hO,?_,?_⟩
  · intro hz
    apply pencil_nonzero D.L D.a00 D.a11 _ _ h00 h11 he t κ ht hκ
    funext x
    rw [←card_even,hz]
    rfl
  · intro hz
    apply pencil_nonzero D.L D.a01 D.a10 _ _ h01 h10 ho t κ ht hκ
    funext x
    rw [←card_odd,hz]
    rfl

end Holant.Dihedral.EndpointSaturation
