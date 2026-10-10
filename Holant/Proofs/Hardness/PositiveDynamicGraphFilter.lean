import Holant.Proofs.Hardness.PositiveDynamicQueries
import Holant.Proofs.Hardness.PositiveDynamicSeparation
import Holant.Proofs.Hardness.ThreeModeGraphFilter

/-! Exact finite differences on mixed original-q/dynamic-stage graphs. The
unmarked rows retain the original signature; only the marked E rows carry the
input-dependent spectral sequence. All oracle queries are literal original-q
networks, and the fixed positive scalar data derive the full denominator. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.PositiveDynamicGraphFilter
open Holant Holant.Complexity FixedGadgetSubstitution
open scoped BigOperators
namespace Q
export PositiveDynamicQueries (count value sequenceSignatures value_value)
export ExactTwoChainQueries (Input)
end Q
namespace G
export ThreeModeGraphEvaluation (originalNetwork modes projector projector_sum desired_denote
  sourceSignatures sourceValue targetValue kernels)
end G
namespace A
export ThreeModeAnnihilator (rootIndices mode denominator differenceFilter)
end A
namespace D
export PositiveDynamicSeparation (lam mu nu denominator_nonzero)
end D
namespace RP
export Holant.LocalDrafts.BinaryInterpolation.RawPolynomial (marked marked_card)
end RP
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
variable {K : Type} [Field K] [CharZero K] (a b c : K)

def eigenvalues (n : ℕ) : Fin 3→K := ![D.lam a b n,D.mu a b c n,D.nu a b c n]

theorem projector_sum (n k : ℕ) :
    (fun x=>∑i : Fin 3,eigenvalues a b c n i^(k+1)*G.projector (K:=K) i x)=
      ThreeModeSignatures.spectral
        ((PositiveDynamicStage.A a b n)^(k+1))
        ((PositiveDynamicStage.B a b n+PositiveDynamicStage.C c n)^(k+1))
        ((PositiveDynamicStage.B a b n-PositiveDynamicStage.C c n)^(k+1)) :=
  by
    simpa only [eigenvalues,ThreeModeGraphEvaluation.eigenvalues,D.lam,D.mu,D.nu,
      PositiveDynamicSeparation.chainA,PositiveDynamicSeparation.chainB,
      PositiveDynamicStage.A,PositiveDynamicStage.B,PositiveDynamicStage.C,add_comm] using
      G.projector_sum (PositiveDynamicStage.C c n) (PositiveDynamicStage.B a b n)
        (PositiveDynamicStage.A a b n) k

/-- The underlying unmarked network is original q, independent of n. -/
theorem sequence_denote (r : Q.Input) (n k : ℕ) :
    (ThreeModeExpansion.sequenceNetwork (G.originalNetwork a b c r)
      (RP.marked r.val 1) (G.modes a b c r) (eigenvalues a b c n) k).denote=
      (r.val.realize r.property (Q.sequenceSignatures a b c n k) G.kernels).denote := by
  apply Network.denote_congr (r.val.shape r.property)
  · intro v x
    change (if v∈RP.marked r.val 1 then
      ∑i : Fin 3,eigenvalues a b c n i^(k+1)*G.projector i x else
        G.sourceSignatures a b c (r.val.signatureLabel r.property v) x)=
      Q.sequenceSignatures a b c n k (r.val.signatureLabel r.property v) x
    rw [congrFun (projector_sum a b c n k) x]
    by_cases hv : (r.val.vertices.get v).1=1 <;>
      simp_all [RP.marked,G.sourceSignatures,Q.sequenceSignatures,RawClosedNetwork.signatureLabel]
  · intros
    rfl

variable (d : PositiveDynamicParameters.Data)

def roots (r : Q.Input) : List K := (A.rootIndices (Q.count r)).map
  (A.mode (Q.count r) (D.lam a b (d.length (Q.count r)))
    (D.mu a b c (d.length (Q.count r))) (D.nu a b c (d.length (Q.count r))))

def queryValue (r : Q.Input) (k : ℕ) : K := G.targetValue a b c (Q.value d (k,r))

/-- Literal-E numerator identity for the actual original-q query sequence. -/
theorem difference_identity (r : Q.Input) :
    A.differenceFilter (roots a b c d r) (queryValue a b c d r) 0=
      G.sourceValue a b c r*A.denominator (Q.count r)
        (D.lam a b (d.length (Q.count r))) (D.mu a b c (d.length (Q.count r)))
        (D.nu a b c (d.length (Q.count r))) := by
  have h := ThreeModeGraphFilter.network_difference (G.originalNetwork a b c r)
    (RP.marked r.val 1) (G.modes a b c r)
    (eigenvalues a b c (d.length (Q.count r))) Fin.elim0
  simp_rw [sequence_denote a b c r] at h
  rw [G.desired_denote a b c r,RP.marked_card r.val 1] at h
  change A.differenceFilter (roots a b c d r)
    (fun k=>(r.val.realize r.property
      (Q.sequenceSignatures a b c (d.length (Q.count r)) k) G.kernels).denote Fin.elim0) 0=
      G.sourceValue a b c r*A.denominator (Q.count r)
        (D.lam a b (d.length (Q.count r))) (D.mu a b c (d.length (Q.count r)))
        (D.nu a b c (d.length (Q.count r))) at h
  have he : queryValue a b c d r=(fun k=>(r.val.realize r.property
      (Q.sequenceSignatures a b c (d.length (Q.count r)) k) G.kernels).denote Fin.elim0) :=
    funext (Q.value_value a b c d r)
  rw [←he] at h
  exact h

variable (σ : K→+*ℝ) (ha : σ a=d.a) (hb : σ b=d.b) (hc : σ c=d.c)

include ha hb hc in
theorem recovery (r : Q.Input) :
    A.differenceFilter (roots a b c d r) (queryValue a b c d r) 0/
      A.denominator (Q.count r) (D.lam a b (d.length (Q.count r)))
        (D.mu a b c (d.length (Q.count r))) (D.nu a b c (d.length (Q.count r)))=
      G.sourceValue a b c r := by
  rw [difference_identity,mul_div_cancel_right₀ _
    (D.denominator_nonzero σ a b c d ha hb hc (Q.count r))]

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.PositiveDynamicGraphFilter
