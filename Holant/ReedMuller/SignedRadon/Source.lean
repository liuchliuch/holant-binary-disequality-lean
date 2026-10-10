import Holant.ReedMuller.SignedRadon.BoundaryTransition
import Holant.ReedMuller.RadonAccess.Source

/-! Source Lemma 7.22: actual signed Radon cards. The source's fixed graph is
retained, one original g is attached through X, the actual ordered Bell is
attached through two X edges, and every nonzero scalar and complement is kept.
The final transition theorems include the quotient affine isometry and the
linear sign character, with its constant absorbed into a nonzero scalar. -/
namespace Holant.ReedMuller.SignedRadon
open Holant Holant.ReedMuller.LowArity Holant.ReedMuller.FlatNetwork
open Holant.ReedMuller.RadonAccess Holant.ReedMuller.CharacterFlat
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ}

/-- The literal source formula at every original-input hyperplane
representative, in the remaining graph-output coordinates. -/
theorem source_signed_radon_formula {κ : ZMod 2 → ZMod 2 → ℂ}
    (F : RadonAccess.RadonFrame (n+2)) (Γ : ActualGraph κ F.A)
    (g : Signature ℂ (n+2)) (d l : ZMod 2) (x : F.Hyperplane d) :
    (signedNetwork F Γ g d l).denote
      (wordVector (RadonFrame.boundaryAffine F d (F.orbit d x)))=
      (Γ.scalar*κ d l)*sign (l*F.A x.1 F.i)*
        (g (wordVector x.1)+sign l*g (wordVector (x.1+F.v))) := by
  rw [signedNetwork_denote]
  simp only [Pi.smul_apply,smul_eq_mul,RadonFrame.boundaryCard,vector_word,
    AffineEquiv.symm_apply_apply,RadonFrame.signedCard_orbit]
  ring

/-- Removing precisely the recorded nonzero graph/Bell scalar and the
exterior Bell sign gives the two original orbit numerators. -/
theorem source_strip_signed_radon {κ : ZMod 2 → ZMod 2 → ℂ}
    (hκ : ∀ d l,κ d l≠0) (F : RadonAccess.RadonFrame (n+2)) (Γ : ActualGraph κ F.A)
    (g : Signature ℂ (n+2)) (d l : ZMod 2) (x : F.Hyperplane d) :
    (Γ.scalar*κ d l)⁻¹*sign (l*F.A x.1 F.i)*
      (signedNetwork F Γ g d l).denote
        (wordVector (RadonFrame.boundaryAffine F d (F.orbit d x)))=
      g (wordVector x.1)+sign l*g (wordVector (x.1+F.v)) := by
  rw [source_signed_radon_formula]
  have hs := mul_ne_zero Γ.scalar_ne (hκ d l)
  calc
    _=((Γ.scalar*κ d l)⁻¹*(Γ.scalar*κ d l))*
      (sign (l*F.A x.1 F.i)*sign (l*F.A x.1 F.i))*
      (g (wordVector x.1)+sign l*g (wordVector (x.1+F.v))) := by ring
    _=_ := by rw [inv_mul_cancel₀ hs,sign_square,one_mul,one_mul]

/-- Plus and minus are literal original-input sums and differences after the
specified scalar/sign stripping, even when either card is identically zero. -/
theorem source_plus_minus_numerators {κ : ZMod 2 → ZMod 2 → ℂ}
    (hκ : ∀ d l,κ d l≠0) (F : RadonAccess.RadonFrame (n+2)) (Γ : ActualGraph κ F.A)
    (g : Signature ℂ (n+2)) (d : ZMod 2) (x : F.Hyperplane d) :
    ((Γ.scalar*κ d 0)⁻¹*(signedNetwork F Γ g d 0).denote
      (wordVector (RadonFrame.boundaryAffine F d (F.orbit d x)))=
        g (wordVector x.1)+g (wordVector (x.1+F.v))) ∧
    ((Γ.scalar*κ d 1)⁻¹*sign (F.A x.1 F.i)*(signedNetwork F Γ g d 1).denote
      (wordVector (RadonFrame.boundaryAffine F d (F.orbit d x)))=
        g (wordVector x.1)-g (wordVector (x.1+F.v))) := by
  constructor
  · simpa using source_strip_signed_radon hκ F Γ g d 0 x
  · simpa [sub_eq_add_neg] using source_strip_signed_radon hκ F Γ g d 1 x

/-- The fixed-graph statement: exact syntax, actual resource membership,
native edges, scalar and graph size are all checked, with no g transformation
or arbitrary graph-signature vertex. -/
theorem source_signed_radon_fixed_graph {κ : ZMod 2 → ZMod 2 → ℂ}
    (hκ : ∀ d l,κ d l≠0) (F : RadonAccess.RadonFrame (n+2)) (Γ : ActualGraph κ F.A)
    (g : Signature ℂ (n+2)) (d l : ZMod 2) :
    ∃ N : Network ℂ n,
      N=signedNetwork F Γ g d l ∧ Uses (cardFamily κ g) N ∧
      (∀ e,N.edge e=Signature.disequality) ∧
      N.denote=(Γ.scalar*κ d l) • RadonFrame.boundaryCard F d l g ∧
      Γ.scalar*κ d l≠0 ∧
      N.shape.vertices=Γ.network.shape.vertices+2 ∧
      N.shape.edges=Γ.network.shape.edges+(n+2)+2 ∧
      Gadget.RealizesUpTo (cardFamily κ g) .disequality (RadonFrame.boundaryCard F d l g) := by
  refine ⟨signedNetwork F Γ g d l,rfl,signedNetwork_uses F Γ g d l,
    signedNetwork_native F Γ g d l,signedNetwork_denote F Γ g d l,
    mul_ne_zero Γ.scalar_ne (hκ d l),signedNetwork_vertices F Γ g d l,
    signedNetwork_edges F Γ g d l,?_⟩
  refine ⟨Γ.scalar*κ d l,mul_ne_zero Γ.scalar_ne (hκ d l),?_⟩
  have hr := Gadget.realizes_network (signedNetwork F Γ g d l) (cardFamily κ g) .disequality
    (signedNetwork_uses F Γ g d l) (signedNetwork_native F Γ g d l)
  rw [signedNetwork_denote F Γ g d l] at hr
  exact hr

/-- Recorded accessible-direction data from Lemma 7.15 and a constructed
actual graph support all four signed cards with the same chosen graph. -/
theorem source_accessible_signed_radon (κ : ZMod 2 → ZMod 2 → ℂ)
    (hκ : ∀ d l,κ d l≠0) (g : Signature ℂ (n+2))
    (v : BinaryVector (n+2)) (hv : Accessible v) :
    ∃ (p : GenerationProgram (n+2)) (F : RadonAccess.RadonFrame (n+2))
      (Γ : ActualGraph κ F.A),
      F.A=p.orthogonalMap ∧ F.v=v ∧
      F.A.matrix.transpose.mulVec (unitWord F.i+unitWord F.j)=v ∧
      ∀ d l : ZMod 2,
        Uses (cardFamily κ g) (signedNetwork F Γ g d l) ∧
        (∀ e,(signedNetwork F Γ g d l).edge e=Signature.disequality) ∧
        (signedNetwork F Γ g d l).denote=(Γ.scalar*κ d l) • RadonFrame.boundaryCard F d l g ∧
        Γ.scalar*κ d l≠0 := by
  obtain ⟨p,F,hA,hv,_,_,hm,_⟩ := source_accessible_radon g v hv
  let Γ := Classical.choice (exists_actualGraph κ hκ F.A)
  refine ⟨p,F,Γ,hA,hv,hm,?_⟩
  intro d l
  exact ⟨signedNetwork_uses F Γ g d l,signedNetwork_native F Γ g d l,
    signedNetwork_denote F Γ g d l,mul_ne_zero Γ.scalar_ne (hκ d l)⟩

/-- The source's explicit affine isometry uses exactly the surviving graph
output coordinates in the recorded original-port order. -/
theorem source_signed_radon_quotient_isometry (F : RadonAccess.RadonFrame (n+2)) (d : ZMod 2) :
    ∃ θ : F.Orbit d ≃ᵃ[ZMod 2] BinaryVector n,
      (∀ w z : F.complement,dot (θ.linear w) (θ.linear z)=dot (w : BinaryVector (n+2)) z) ∧
      (∀ (x : F.Hyperplane d) (k : Fin n),
        θ (F.orbit d x) k=F.A (x.1+ones (n+2)) (F.pairRemainingOrder k).1) :=
  ⟨RadonFrame.boundaryAffine F d,RadonFrame.boundaryAffine_isometry F d,
    RadonFrame.boundaryAffine_orbit F d⟩

/-- The entire final change-of-choice clause, packaged with the actual affine
isometry, linear sign character and recorded nonzero network scalar. -/
theorem source_signed_radon_choice_independence {κ : ZMod 2 → ZMod 2 → ℂ}
    (F G : RadonAccess.RadonFrame (n+2)) (h : F.v=G.v)
    (ΓF : ActualGraph κ F.A) (ΓG : ActualGraph κ G.A)
    (g : Signature ℂ (n+2)) (d l : ZMod 2) :
    ∃ (T : BinaryVector n ≃ᵃ[ZMod 2] BinaryVector n) (ell : Character n) (c : ℂ),
      c≠0 ∧ (∀ w z,dot (T.linear w) (T.linear z)=dot w z) ∧
      ∀ x : BinaryVector n,
        (signedNetwork G ΓG g d l).denote (wordVector (T x))=
          c*sign (ell x)*(signedNetwork F ΓF g d l).denote (wordVector x) := by
  obtain ⟨c,hc,he⟩ := signedNetwork_change_choice F G h ΓF ΓG g d l
  exact ⟨RadonFrame.boundaryTransition F G h d,RadonFrame.boundaryCharacter F G l,c,hc,
    RadonFrame.boundaryTransition_isometry F G h d,he⟩

end
end Holant.ReedMuller.SignedRadon
