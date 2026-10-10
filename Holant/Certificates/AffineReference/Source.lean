import Holant.Certificates.AffineReference.PlaneNetwork

/-! Complete direct-use Theorem A.5. Its input is the normalized affine
reference and one of exactly the support shapes supplied by A.4. This result
does not assume or claim the separate 36,720-state/core classification A.2/A.4. -/
namespace Holant.Certificates.AffineReference
open Holant Holant.Tractable Holant.Certificates.FourthRootOdd
open EightVertex.ProductAnchor
noncomputable section
set_option backward.isDefEq.respectTransparency false

def endpointSupport (h : Signature AlgebraicComplex 4) : Prop :=
  ∀ x,h x≠0 ↔ x=(fun _ => false) ∨ x=(fun _ => true)
def fullEvenSupport (h : Signature AlgebraicComplex 4) : Prop :=
  ∀ x,h x≠0 ↔ evenWord x=true
def ReferenceSupport (h : Signature AlgebraicComplex 4) : Prop :=
  endpointSupport h ∨ (∃ b : Fin 3,PlaneSupport h b) ∨ fullEvenSupport h
def supportSize (h : Signature AlgebraicComplex 4) : ℕ :=
  (Finset.univ.filter fun x : Fin 4 → Bool => h x≠0).card

theorem endpoint_reference_pure (h : Signature AlgebraicComplex 4) (hs : endpointSupport h) :
    PureEquality h := by
  apply pure_of_pair_support h (fun _ => false)
  · exact (hs _).mpr (Or.inl rfl)
  · exact (hs _).mpr (Or.inr rfl)
  · intro x hx hy
    by_contra hn
    rcases (hs x).mp hn with h | h
    · exact hx h
    · exact hy (by simpa using h)

theorem endpoint_support_size (h : Signature AlgebraicComplex 4) (hs : endpointSupport h) :
    supportSize h=2 := (endpoint_reference_pure h hs).support_card

theorem plane_support_size (h : Signature AlgebraicComplex 4) (b : Fin 3) (hs : PlaneSupport h b) :
    supportSize h=4 := by
  have he : (Finset.univ.filter fun x : Fin 4 → Bool => h x≠0)=
      Finset.univ.filter (OnPlane b) := by
    ext x
    simp only [Finset.mem_filter,Finset.mem_univ,true_and]
    exact hs x
  unfold supportSize
  rw [he]
  fin_cases b <;> decide

theorem full_even_support_size (h : Signature AlgebraicComplex 4) (hs : fullEvenSupport h) :
    supportSize h=8 := by
  have he : (Finset.univ.filter fun x : Fin 4 → Bool => h x≠0)=
      Finset.univ.filter (fun x : Fin 4 → Bool => evenWord x=true) := by
    ext x
    simp only [Finset.mem_filter,Finset.mem_univ,true_and]
    exact hs x
  unfold supportSize
  rw [he]
  decide

/-- Every original two-block port ordering is one of the three exact pairing
predicates. No physical port permutation is added as a supplied signature. -/
theorem original_pairing_complete : ∀ p : Equiv.Perm (Fin 4), ∃ b : Fin 3, ∀ x : Fin 4 → Bool,
    OnPlane b x ↔ x (p 0)=x (p 1) ∧ x (p 2)=x (p 3) := by decide

def PlaneConclusions (h : Signature AlgebraicComplex 4) (b : Fin 3) : Prop :=
  let f := planeTable h b
  (f ![false,false]*f ![true,true]/(f ![false,true]*f ![true,false])=1 ∨
   f ![false,false]*f ![true,true]/(f ![false,true]*f ![true,false])= -1) ∧
  (f ![false,false]*f ![true,true]=f ![false,true]*f ![true,false] → TwoWeightedEqualities h) ∧
  (f ![false,false]*f ![true,true]= -(f ![false,true]*f ![true,false]) →
    PureEquality (twoCopyNative h (complementaryPair b)) ∧
    Gadget.Realizes ({⟨4,h⟩} : SignatureFamily AlgebraicComplex) .disequality
      (twoCopyNative h (complementaryPair b)))

def FullEvenConclusions (h : Signature AlgebraicComplex 4) : Prop :=
  DenseForm h ∨
  (∃ e : Fin 6,
    (Matrix.of (fun a b : Bool => ((nativeContract (K := AlgebraicComplex) h e ![a,b] : AlgebraicComplex) : ℂ))).rank=1 ∧
    Gadget.Realizes ({⟨4,h⟩} : SignatureFamily AlgebraicComplex) .disequality (nativeContract h e)) ∨
  ∃ e : Fin 3,EqualCopiesProduct (crossedCopies h e) ∧
    Gadget.Realizes ({⟨4,h⟩} : SignatureFamily AlgebraicComplex) .disequality (crossedCopies h e)

/-- Theorem A.5, all three support branches, with exact literal graph outputs.
The physical assertions are actual realization; analytic factors are explicitly
tensor decompositions, never claimed as independently supplied resources. -/
theorem source_affine_reference_gadgets (h : Signature AlgebraicComplex 4)
    (ha : Affine h) (h0 : h (fun _ => false)=1) (hs : ReferenceSupport h) :
    (supportSize h=2 → PureEquality h) ∧
    (supportSize h=4 → ∃ b : Fin 3,PlaneSupport h b ∧ PlaneConclusions h b) ∧
    (supportSize h=8 → FullEvenConclusions h) := by
  have hc : supportSize h=2 ∨ supportSize h=4 ∨ supportSize h=8 := by
    rcases hs with h | ⟨b,h⟩ | h
    · exact Or.inl (endpoint_support_size _ h)
    · exact Or.inr (Or.inl (plane_support_size _ b h))
    · exact Or.inr (Or.inr (full_even_support_size _ h))
  refine ⟨?_,?_,?_⟩
  · intro hn
    rcases hs with h | ⟨b,h⟩ | h
    · exact endpoint_reference_pure _ h
    · have := plane_support_size _ b h;omega
    · have := full_even_support_size _ h;omega
  · intro hn
    rcases hs with h | ⟨b,h⟩ | h
    · have := endpoint_support_size _ h;omega
    · exact ⟨b,h,plane_cross_ratio _ b ha h,plane_positive_factor _ b h,plane_negative_exit _ b h⟩
    · have := full_even_support_size _ h;omega
  · intro hn
    rcases hs with h | ⟨b,h⟩ | h
    · have := endpoint_support_size _ h;omega
    · have := plane_support_size _ b h;omega
    · exact full_even_reference_exits _ ha h h0

end
end Holant.Certificates.AffineReference
