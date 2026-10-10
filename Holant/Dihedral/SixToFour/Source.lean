import Holant.Dihedral.SixToFour.FourFlat
import Holant.Certificates.NormalizedDihedralQ6.Interface

/-! Main-text Lemma 6.14, structural and physical part. The source four-flat
hypothesis is transported back to original port IDs before choosing the actual
I/X loop. Protocol successor/complexity claims require the protocol separately. -/
namespace Holant.Dihedral.SixToFour
open Holant Holant.Marked Holant.Certificates.NormalizedDihedralQ6
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

/-- The output certificate refers to the original h, pair and residual order.
The selected edge is one of the actual permitted I/X resources. -/
structure Lowering (D : FourFlatData) (h : Signature Scalar 6) where
  pair : Pair
  distinct : pair.1 ≠ pair.2
  parity : Bool
  size : ℕ
  size_six_eight : size = 6 ∨ size = 8
  injective : injectiveProjection D.support pair parity
  output_card : coefficientSupportCard (contractAt h pair distinct parity) = size
  output_nonzero : contractAt h pair distinct parity ≠ 0
  not_matching_product : ¬ TwoMonomialProduct (contractAt h pair distinct parity)
  realizes : Gadget.Realizes ({⟨6,h⟩} : SignatureFamily Scalar) (parityEdge parity)
    (contractAt h pair distinct parity)
  physical_kernel : (parityEdge parity = .equality ∧ parityKernel (K := Scalar) parity = Signature.equality) ∨
    (parityEdge parity = .disequality ∧ parityKernel (K := Scalar) parity = Signature.disequality)
  support_exact : ∀ x, contractAt h pair distinct parity x ≠ 0 ↔
    x ∈ (slice D.support pair parity).image (externalWord pair distinct)
  coefficient_exact : ∀ x, x ∈ (slice D.support pair parity).image (externalWord pair distinct) →
    ∃ ab : Bool × Bool, summand h pair distinct parity x ab ≠ 0 ∧
      (∀ cd, summand h pair distinct parity x cd ≠ 0 → cd = ab) ∧
      contractAt h pair distinct parity x = h (joinWord pair distinct ab.1 ab.2 x)

/-- The certificate is realized by one original vertex and one selected loop,
with the undeleted original ports in increasing order. -/
theorem Lowering.incidence {D : FourFlatData} {h : Signature Scalar 6} (L : Lowering D h) :
    (contractionNetwork h L.pair L.distinct L.parity).shape.vertices = 1 ∧
    (contractionNetwork h L.pair L.distinct L.parity).shape.edges = 1 ∧
    (∀ v, (contractionNetwork h L.pair L.distinct L.parity).vertex v = h) ∧
    (contractionNetwork h L.pair L.distinct L.parity).shape.ports.symm (.inr ((0 : Fin 1),false)) =
      ⟨(0 : Fin 1),L.pair.1⟩ ∧
    (contractionNetwork h L.pair L.distinct L.parity).shape.ports.symm (.inr ((0 : Fin 1),true)) =
      ⟨(0 : Fin 1),L.pair.2⟩ ∧
    (∀ i : Fin 4, (contractionNetwork h L.pair L.distinct L.parity).shape.ports.symm (.inl i) =
      ⟨(0 : Fin 1),(remainingEquiv L.pair L.distinct i).val⟩) ∧
    StrictMono (fun i : Fin 4 => (remainingEquiv L.pair L.distinct i).val) :=
  ⟨rfl,rfl,fun _ => rfl,rfl,rfl,fun _ => rfl,remainingEquiv_strictMono _ _⟩

private theorem card_ne_zero {f : Signature Scalar 4} {n : ℕ}
    (hc : coefficientSupportCard f = n) (hn : n = 6 ∨ n = 8) : f ≠ 0 := by
  intro hf
  rw [hf] at hc
  have hz : coefficientSupportCard (0 : Signature Scalar 4) = 0 := by
    simp [coefficientSupportCard]
  rw [hz] at hc
  omega

/-- The source equations alone give the exact matching alternative or an actual
nonzero six/eight-support quaternary. Every off-support output coefficient is
zero, and every supported output is one unchanged nonzero original coefficient. -/
theorem source_six_to_four (D : FourFlatData) (h : Signature Scalar 6)
    (hs : ∀ x, h x ≠ 0 ↔ D.Holds x) :
    matchingCoset D.support ∨ Nonempty (Lowering D h) := by
  classical
  have hsupport : ∀ x, h x ≠ 0 ↔ x ∈ D.support :=
    fun x => (hs x).trans (D.mem_support x).symm
  by_cases hm : matchingCoset (support (sector D.even) (sector D.odd))
  · exact Or.inl (matchingCoset_transform _ _ _ hm)
  · have hb := nonmatching_lowering (sector D.even) (sector D.odd) hm
    have hex : ∃ n : ℕ, (n = 6 ∨ n = 8) ∧
        HasMaximum (support (sector D.even) (sector D.odd)) n := by
      rcases hb with hb | hb
      · exact ⟨6,Or.inl rfl,hb⟩
      · exact ⟨8,Or.inr rfl,hb⟩
    rcases hex with ⟨n,hn,⟨p,γ,hp,hi,hcard⟩,_⟩
    let q : Pair := (D.ports p.1,D.ports p.2)
    have hq : q.1 ≠ q.2 := fun he => hp (D.ports.injective he)
    have hiq : injectiveProjection D.support q γ := by
      have hh := injectiveProjection_transform_iff D.ports.symm (fun _ => false)
        (support (sector D.even) (sector D.odd)) q γ
      have hpull : (D.ports.symm q.1,D.ports.symm q.2) = p := by
        simp only [q,Equiv.symm_apply_apply]
      rw [hpull] at hh
      simp only [Bool.xor_false] at hh
      exact hh.mpr hi
    have hslice : (slice D.support q γ).card =
        (slice (support (sector D.even) (sector D.odd)) p γ).card := by
      simpa [FourFlatData.support,q] using slice_card_transform D.ports.symm (fun _ => false)
        (support (sector D.even) (sector D.odd)) q γ
    have hproj : (projected D.support q γ).card = n :=
      ((injectiveProjection_iff _ _ _).mp hiq).trans
        (hslice.trans (((injectiveProjection_iff _ _ _).mp hi).symm.trans hcard))
    have hout : coefficientSupportCard (contractAt h q hq γ) = n := by
      exact (contractAt_support_card h _ hsupport q hq γ hiq).trans hproj
    refine Or.inr ⟨{
      pair := q, distinct := hq, parity := γ, size := n, size_six_eight := hn,
      injective := hiq, output_card := hout, output_nonzero := card_ne_zero hout hn,
      not_matching_product := not_twoMonomialProduct_of_six_or_eight hn hout,
      realizes := contraction_realizes h q hq γ,
      physical_kernel := ?_,
      support_exact := contractAt_support h _ hsupport q hq γ hiq,
      coefficient_exact := ?_ }⟩
    · cases γ
      · exact Or.inl ⟨rfl,rfl⟩
      · exact Or.inr ⟨rfl,rfl⟩
    · intro x hx
      obtain ⟨ab,hab,hu,he,hv⟩ := cancellation_free h _ hsupport q hq γ hiq x hx
      exact ⟨ab,hab,hu,he.trans hv⟩

/-- A missing coefficient is excluded by the literal source hypothesis; the
identically zero six-port tensor does not enter the claimed nonzero branch. -/
theorem source_nonzero (D : FourFlatData) (h : Signature Scalar 6)
    (hs : ∀ x, h x ≠ 0 ↔ D.Holds x) : h ≠ 0 := by
  have hc := D.card
  have hn : D.support.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨x,hx⟩ := hn
  intro he
  have hz := (hs x).mpr ((D.mem_support x).mp hx)
  exact hz (congrFun he x)

end Holant.Dihedral.SixToFour
